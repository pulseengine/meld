#!/usr/bin/env python3
"""The two decisions behind meld's Mythos gate, kept out of YAML so they are tested.

aggregate  (mythos-auto.yml): turn the per-file scan results into one verdict.
    PASS only when every Tier-5 file the detect job listed has a result, the
    scan jobs all succeeded, and no result is a FINDING. Anything less is
    INCOMPLETE, never a pass: on #594 a superseded run's cancelled scans
    reached the aggregate with zero results and it reported "NO FINDINGS
    across 0 Tier-5 file(s)" (#595).

gate  (mythos-gate.yml): decide the required "Mythos delta-pass gate" check.
    Passes when no Tier-5 file is touched; when the auto verdict for THIS head
    commit is a complete PASS (commit status `mythos/auto-verdict` = success);
    or when the maintainer applied `mythos-pass-done` as an override. The
    override is cleared on every push, so it always refers to the code it was
    given for.

Usage:
  mythos_decide.py aggregate --expected '<json list>' --results-dir DIR --scan-result RESULT
      prints a JSON object: verdict (PASS|FAIL|INCOMPLETE), reviewed, expected,
      missing, findings, rows (file, verdict, hypothesis)
  mythos_decide.py gate --tier5 true|false --labels '<json list of names>' --status STATE
      prints PASS or FAIL and a reason on the second line; exit 0 / 1
  mythos_decide.py --self-test
"""

import json
import os
import sys

LABEL = "mythos-pass-done"


def aggregate(expected, results, scan_result):
    """expected: list of file paths; results: list of dicts from the per-file
    JSONs; scan_result: needs.scan.result ('success', 'failure', 'cancelled',
    'skipped')."""
    rows = []
    seen = set()
    findings = 0
    unknown = []
    for r in results:
        f = r.get("file") or ""
        if not f:
            raise ValueError("a per-file result carries no .file")
        seen.add(f)
        v = r.get("verdict")
        if v == "FINDING":
            findings += 1
        elif v != "NO_FINDINGS":
            unknown.append(f)
        rows.append({"file": f, "verdict": v, "hypothesis": r.get("hypothesis") or ""})
    missing = sorted(set(expected) - seen)
    if findings:
        verdict = "FAIL"
    elif scan_result != "success" or missing or unknown or not expected:
        verdict = "INCOMPLETE"
    else:
        verdict = "PASS"
    return {
        "verdict": verdict,
        "reviewed": len(seen & set(expected)),
        "expected": len(expected),
        "missing": missing,
        "unknown": unknown,
        "findings": findings,
        "scan_result": scan_result,
        "rows": rows,
    }


def gate(tier5, labels, status):
    """tier5: bool; labels: list of label names live on the PR; status: the
    state of commit status `mythos/auto-verdict` on the PR head ('' if none)."""
    if not tier5:
        return True, "no Tier-5 file touched"
    if status == "success":
        return True, "the auto verdict for this commit is a complete NO FINDINGS"
    if LABEL in labels:
        return True, "maintainer override: %s applied after the last push" % LABEL
    if status == "failure":
        return False, "the auto verdict for this commit reports a finding; fix it, or apply %s to override" % LABEL
    if status == "error":
        return False, "the auto verdict for this commit is incomplete; re-run mythos-auto, or apply %s to override" % LABEL
    return False, "no auto verdict for this commit yet (mythos-auto re-runs this check when it posts one)"


def _load_results(d):
    out = []
    if os.path.isdir(d):
        for name in sorted(os.listdir(d)):
            if name.endswith(".json"):
                with open(os.path.join(d, name)) as fh:
                    out.append(json.load(fh))
    return out


def self_test():
    a, b = "meld-core/src/parser.rs", "meld-core/src/adapter/fact.rs"
    ok = {"verdict": "NO_FINDINGS"}
    # complete and clean
    r = aggregate([a, b], [dict(ok, file=a), dict(ok, file=b)], "success")
    assert r["verdict"] == "PASS" and r["reviewed"] == 2, r
    # #595: superseded run, all scans cancelled, zero results
    r = aggregate([a, b], [], "cancelled")
    assert r["verdict"] == "INCOMPLETE" and r["missing"] == sorted([a, b]), r
    # one scan missing although the job result says success
    r = aggregate([a, b], [dict(ok, file=a)], "success")
    assert r["verdict"] == "INCOMPLETE" and r["missing"] == [b], r
    # all results present but a scan job failed
    r = aggregate([a, b], [dict(ok, file=a), dict(ok, file=b)], "failure")
    assert r["verdict"] == "INCOMPLETE", r
    # a finding is reported even when the set is incomplete
    r = aggregate([a, b], [{"file": a, "verdict": "FINDING", "hypothesis": "h"}], "cancelled")
    assert r["verdict"] == "FAIL" and r["findings"] == 1, r
    # a verdict the schema does not allow is not a clean result
    r = aggregate([a], [{"file": a, "verdict": "MAYBE"}], "success")
    assert r["verdict"] == "INCOMPLETE" and r["unknown"] == [a], r
    # nothing expected is never a pass (detect said any=true)
    assert aggregate([], [], "success")["verdict"] == "INCOMPLETE"
    # a nameless result is an error, not a row
    try:
        aggregate([a], [{"verdict": "NO_FINDINGS"}], "success")
        raise AssertionError("nameless result accepted")
    except ValueError:
        pass

    assert gate(False, [], "")[0]
    assert gate(True, [], "success")[0]
    assert gate(True, [LABEL], "")[0]
    assert gate(True, [LABEL], "failure")[0]  # the override is the point of the label
    assert not gate(True, [], "")[0]
    assert not gate(True, [], "failure")[0]
    assert not gate(True, [], "error")[0]
    assert not gate(True, [], "pending")[0]
    assert not gate(True, ["mythos"], "")[0]  # only the exact label overrides
    print("mythos_decide self-test: ok")


def main(argv):
    if argv[1:] == ["--self-test"]:
        self_test()
        return 0
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    args = dict(zip(argv[2::2], argv[3::2]))
    if argv[1] == "aggregate":
        r = aggregate(json.loads(args["--expected"]), _load_results(args["--results-dir"]), args["--scan-result"])
        print(json.dumps(r))
        return 0
    if argv[1] == "gate":
        ok, why = gate(args["--tier5"] == "true", json.loads(args["--labels"]), args.get("--status", ""))
        print("PASS" if ok else "FAIL")
        print(why)
        return 0 if ok else 1
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
