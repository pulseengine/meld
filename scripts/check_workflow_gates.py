#!/usr/bin/env python3
"""Assert that the proof gate's own checks are still in the script that runs.

Why this exists
---------------
A gate's checks live inside a YAML block scalar (`run: |`). That block ends at
the first non-blank line indented LESS than the block's content indentation —
so one under-indented line, even a COMMENT, silently truncates the script and
drops every check after it.

This is not hypothetical. It happened while building this gate (#447): an
under-indented comment ended the census step's `run:` block just above the
four floor assertions. In that instance the leftover shell did not parse as
YAML, so GitHub rejected the file and the breakage was loud.

It does not have to be loud. De-indent where the remainder still parses and
the step runs a SHORTER script and passes — a floor check, or the `Admitted`
check, simply ceases to exist. A vacuous gate produced by whitespace, with a
green tick on it. Which is #447's own defect, one more level down.

So the assertions below run against the EXTRACTED block text, applying the
same indentation rule YAML does, because that rule is what produces the
truncation. Checking the raw file with grep would not see it.

Stdlib only, matching tools/check_release_targets.py and
tools/check_record_citations.py: these gates must not be able to fail for want
of a third-party import. Lives in scripts/ and not tools/ because ci.yml's
paths-ignore skips `tools/*.py`, so a guard there could be weakened in a PR
that never runs CI at all.
"""
import pathlib
import re
import sys

WORKFLOW = ".github/workflows/proofs.yml"


def extract_run_blocks(text):
    """Map step name -> `run:` block text, by YAML's block-scalar rule.

    The content indentation is set by the block's first non-blank line; the
    block ends at the first non-blank line indented less than that. This is
    deliberately the real rule and not "everything more-indented than the
    key", because the difference is exactly the truncation being guarded.
    """
    lines = text.splitlines()
    out, name = {}, None
    i = 0
    while i < len(lines):
        line = lines[i]
        m_name = re.match(r"\s*-\s+name:\s*(.+?)\s*$", line)
        if m_name:
            name = m_name.group(1).strip("'\"")
        if re.match(r"\s*run:\s*\|\s*$", line):
            body, indent = [], None
            j = i + 1
            while j < len(lines):
                cur = lines[j]
                if not cur.strip():
                    body.append("")
                    j += 1
                    continue
                cur_indent = len(cur) - len(cur.lstrip())
                if indent is None:
                    indent = cur_indent
                elif cur_indent < indent:
                    break
                body.append(cur[indent:])
                j += 1
            out[name] = "\n".join(body)
            i = j
            continue
        i += 1
    return out


def find_duplicate_keys(text):
    """Duplicate keys at the TOP LEVEL only.

    GitHub Actions rejects a file with duplicate keys outright, which presents
    as an early failure with no job attached and no annotation — worth naming,
    even though it is loud rather than silent.

    Restricted to indent 0 deliberately. A nested check needs real parent
    scoping: `paths:` legitimately appears under both `push:` and
    `pull_request:` in this very file, and a depth-blind comparison reports it
    as a duplicate — a checker that fails on a healthy tree, which is the same
    mistake the census step's unguarded `grep -c` made. Top-level keys have
    exactly one scope, so there is nothing to get wrong.
    """
    dups, seen = [], {}
    for n, line in enumerate(text.splitlines(), 1):
        m = re.match(r"^([A-Za-z][\w-]*):", line)
        if not m:
            continue
        key = m.group(1)
        if key in seen:
            dups.append(f"duplicate top-level key {key!r} at lines {seen[key]} and {n}")
        else:
            seen[key] = n
    return dups


def extract_seq(text, key):
    """The YAML sequence under `key:` — items at a deeper indent, `- value`.

    Stdlib, like the rest of this file, and only as clever as it needs to be:
    these are flat lists of quoted path globs.
    """
    lines = text.splitlines()
    out, indent = None, None
    for line in lines:
        if out is None:
            m = re.match(rf"^(\s*){re.escape(key)}:\s*$", line)
            if m:
                out, indent = [], len(m.group(1))
            continue
        if not line.strip():
            continue
        cur = len(line) - len(line.lstrip())
        if cur <= indent:
            break
        item = re.match(r"^\s*-\s*(.+?)\s*$", line)
        if item:
            out.append(item.group(1).strip("'\""))
        else:
            break
    return out or []


def _top_level_on(text):
    """The lines of the top-level `on:` block (stdlib, indentation-based)."""
    lines, out, inside = text.splitlines(), [], False
    for line in lines:
        if re.match(r"^on:\s*$", line):
            inside = True
            continue
        if inside:
            if line and not line[0].isspace() and not line.startswith("#"):
                break
            out.append(line)
    return out


def _trigger_block(on_lines, trigger):
    """The lines under `  <trigger>:` inside the `on:` block, or None if absent."""
    block, inside = None, False
    for line in on_lines:
        m = re.match(r"^  ([A-Za-z_]+):", line)
        if m:
            if inside:
                break
            if m.group(1) == trigger:
                block, inside = [], True
            continue
        if inside:
            block.append(line)
    return block


def check_queue_triggers(fails):
    """Required contexts must report on every PR AND in the merge queue.

    ci.yml and proofs.yml used to carry `pull_request` path filters, with stub
    workflows (ci-docs-stub.yml, proofs-stub.yml) posting the same required
    context names as instant successes on the complementary paths. In a merge
    queue that pairing does not hold, so the filters moved into a `changes` job
    (scripts/ci/classify_changes.py) and the stubs were deleted. What keeps
    that safe is asserted here:

    1. every workflow emitting a required context triggers on `merge_group`.
       Without it the queue waits on a check nothing reports;
    2. neither ci.yml nor proofs.yml puts `paths`/`paths-ignore` back on
       `pull_request`, because a path-filtered required workflow never starts;
    3. no stub reporting a required context's name comes back;
    4. the classifier's glob lists equal the push filters, so the PR/queue path
       and the push path cannot drift apart. This replaces the stub alignment
       check, which asserted the same thing about the stubs.
    """
    required = {
        ".github/workflows/ci.yml": "Test/Clippy/Format",
        ".github/workflows/proofs.yml": "Rocq proofs",
        ".github/workflows/verification-gate.yml": "LS-N verification gate",
        ".github/workflows/release-readiness.yml": "Release readiness",
        ".github/workflows/scry-gate.yml": "Scry sound-AI (fused meld output)",
        ".github/workflows/witness-gate.yml": "Witness MC/DC (fused meld seam)",
        ".github/workflows/mythos-gate.yml": "Mythos delta-pass gate",
    }
    for wf, ctx in required.items():
        p = pathlib.Path(wf)
        if not p.exists():
            fails.append(f"{ctx}: {wf} is missing")
            continue
        on = _top_level_on(p.read_text())
        if _trigger_block(on, "merge_group") is None:
            fails.append(f"{ctx}: {wf} has no merge_group trigger -- the merge queue "
                         "would wait on a context nothing reports")
        if wf.endswith(("/ci.yml", "/proofs.yml")):
            pr = _trigger_block(on, "pull_request")
            if pr is None:
                fails.append(f"{ctx}: {wf} has no pull_request trigger")
            elif any(re.match(r"^\s+(paths|paths-ignore):", l) for l in pr):
                fails.append(f"{ctx}: {wf} filters pull_request by path -- a required "
                             "context then never reports on the other paths; gate by "
                             "the `changes` job instead")
    for stub in (".github/workflows/ci-docs-stub.yml", ".github/workflows/proofs-stub.yml"):
        if pathlib.Path(stub).exists():
            fails.append(f"{stub} is back -- it posts trivially-green duplicates of "
                         "required contexts, which the merge queue cannot tell apart")

    sys.path.insert(0, str(pathlib.Path("scripts/ci")))
    try:
        import classify_changes as cc
    except Exception as e:  # noqa: BLE001 -- any import failure is a failure
        fails.append(f"scripts/ci/classify_changes.py does not import: {e}")
        return
    for wf, key, lst, name in (
        (".github/workflows/ci.yml", "paths-ignore", cc.DOCS_ONLY, "DOCS_ONLY"),
        (".github/workflows/proofs.yml", "paths", cc.PROOFS, "PROOFS"),
    ):
        push = _trigger_block(_top_level_on(pathlib.Path(wf).read_text()), "push") or []
        got = extract_seq("\n".join(push), key)
        if not got or not lst:
            fails.append(f"{wf}: could not read push.{key} ({len(got)} items) or "
                         f"classify_changes.{name} ({len(lst)} items) -- the parse found "
                         "nothing, which is a failure and not an alignment")
        elif got != lst:
            fails.append(f"{wf}: push.{key} and classify_changes.{name} have drifted -- "
                         f"only in the workflow: {sorted(set(got) - set(lst))}; only in "
                         f"the classifier: {sorted(set(lst) - set(got))}")


def check(path=WORKFLOW):
    fails = []

    def want(cond, msg):
        if not cond:
            fails.append(msg)

    text = pathlib.Path(path).read_text()
    fails.extend(find_duplicate_keys(text))
    blocks = extract_run_blocks(text)

    def block(needle):
        for k, v in blocks.items():
            if k and needle in k:
                return v
        fails.append(f"no step whose name contains {needle!r}")
        return ""

    census = block("Proof census")
    # Four floors: .v files, Qed, rocq_proof_test targets, verify_all members.
    n = census.count("-ge")
    want(
        n == 4,
        f"census step has {n} floor assertions, expected 4 — a floor was removed, "
        "or an under-indented line truncated the run block above them",
    )
    want(
        "admitted" in census and "-ne 0" in census,
        "census step no longer fails on a non-zero Admitted count",
    )
    # Counters must tolerate grep's exit 1 on zero matches, or the step aborts
    # on a healthy tree. This bit once, on the Admitted counter itself.
    g = census.count("|| true")
    want(
        g >= 4,
        f"census step has {g} guarded counters, expected >= 4 — an unguarded "
        "counter aborts the step on a tree with zero matches",
    )

    gate = block("Re-check the proofs")
    want("exit 4" in gate, "gate step no longer treats bazel's exit 4 as a failure")
    for tol in ("|| true", "-eq 4 ]", "|| :"):
        want(
            tol not in gate,
            f"gate step contains {tol!r} — tolerating exit 4 is how a proof gate "
            "passes while selecting nothing (synth#945)",
        )

    cov = block("inside the gate")
    want("bazel query" in cov, "coverage step no longer queries the dependency closure")
    want(
        "potency control failed" in cov,
        "coverage step lost its positive control — an empty query would then read "
        "as 'every file is an orphan' for an invisible reason",
    )
    want("gate-exclusions.txt" in cov, "coverage step no longer reads the exclusion list")

    check_queue_triggers(fails)
    check_traceability_gate(fails)

    return fails


TRACEABILITY = ".github/workflows/traceability.yml"


def check_traceability_gate(fails):
    """The traceability ratchet's own checks (#412).

    Its exit code carries the verdict, and `rc=0` has two meanings: rivet
    compared the trees and found nothing new, or rivet never compared anything.
    The second would pass the gate while checking nothing, so the step demands
    evidence of a comparison. Asserted here so that control cannot be dropped
    silently — the same reason the proofs census's floors are asserted above.
    """
    p = pathlib.Path(TRACEABILITY)
    if not p.exists():
        fails.append(f"{TRACEABILITY} is missing")
        return
    run = extract_run_blocks(p.read_text()).get("No new traceability diagnostics", "")
    if not run:
        fails.append(f"{TRACEABILITY}: no 'No new traceability diagnostics' step with a run block")
        return
    for needle, why in (
        ("--fail-on info", "the threshold dropped below info, where the backlink rule lives"),
        ("New diagnostics since", "the potency control is gone: an exit 0 with nothing compared would pass"),
        ("--new-since", "the ratchet became an absolute threshold"),
    ):
        if needle not in run:
            fails.append(f"{TRACEABILITY}: {why} (missing {needle!r})")
    # `$?` must read rivet's own status, not a pipeline's last command.
    if "out=$(rivet validate" not in run:
        fails.append(
            f"{TRACEABILITY}: rivet's output is no longer captured into a variable, so $? may "
            "be some other command's status — the confusion that has produced a wrong verdict "
            "in this repo's CI more than once"
        )
    # Actions runs `run:` blocks under `bash -e`, so a failing command
    # substitution aborts the step before a following `rc=$?` can run, and the
    # diagnostics are never printed. The status must be taken on the same line.
    if "--fail-on info 2>&1) || rc=$?" not in run:
        fails.append(
            f"{TRACEABILITY}: rivet's exit status is not captured with `|| rc=$?` on the "
            "assignment itself; under the runner's `bash -e`, a failing rivet aborts the step "
            "before the diagnostics are printed"
        )


if __name__ == "__main__":
    target = sys.argv[1] if len(sys.argv) > 1 else WORKFLOW
    problems = check(target)
    if problems:
        print(f"{target}: the gate's own checks have been weakened\n", file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        print(
            "\n  A likely cause is a line indented LESS than the first line of a\n"
            "  `run: |` block — even a comment — which ends the block early and\n"
            "  silently drops every check below it.",
            file=sys.stderr,
        )
        sys.exit(1)
    print(f"{target}: census floors, exit-4 intolerance and coverage control all present")
