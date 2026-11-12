#!/usr/bin/env python3
"""Which required workflows would a change run? A model of GitHub's path
filters, for temper's gate probe (.github/gate-probe.json).

meld has no change-detector script: GitHub's `paths` / `paths-ignore`
filters decide whether `ci.yml` (Test, Clippy, Format) and `proofs.yml`
(Rocq proofs) run, and a skipped required check counts as passing. This
script answers the same question, so the probe can feed it control paths
and see whether each filter fails closed.

It reads the patterns from the workflow files themselves (via the
extractor scripts/check_workflow_gates.py uses), so there is no second copy
of the lists to drift. What it cannot guarantee is that its glob matching is
GitHub's, so it is a model and not the filter. It follows GitHub's
documented rules: `*` does not cross `/`, `**` does, and later `!` patterns
re-include. A path filter decides on the whole change: `paths-ignore` skips
the run only if every changed file is ignored, and `paths` runs it if any
file matches.

Changed files come from `GATE_PROBE_FILES` (one path per line), or from
arguments when that is unset. It writes `ci=` and `proofs=` (`true` = the
workflow runs) to `$GITHUB_OUTPUT`, and to stdout when that is unset.

Lives in scripts/, not tools/: ci.yml ignores tools/*.py, so a change that
weakened this model would itself skip CI.
"""
import os
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))
from check_workflow_gates import extract_seq  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent


def glob_to_regex(pattern):
    out, i = [], 0
    while i < len(pattern):
        c = pattern[i]
        if pattern.startswith("**/", i):
            out.append("(?:.*/)?")
            i += 3
        elif pattern.startswith("**", i):
            out.append(".*")
            i += 2
        elif c == "*":
            out.append("[^/]*")
            i += 1
        elif c == "?":
            out.append("[^/]")
            i += 1
        else:
            out.append(re.escape(c))
            i += 1
    return re.compile("^" + "".join(out) + "$")


def matched(path, patterns):
    """GitHub's rule: the last pattern that matches decides; `!` negates."""
    hit = False
    for p in patterns:
        neg = p.startswith("!")
        if glob_to_regex(p[1:] if neg else p).match(path):
            hit = not neg
    return hit


def workflow_runs(files, workflow, key):
    pats = extract_seq((ROOT / workflow).read_text(), key)
    if not pats:
        raise SystemExit("%s: no %s list found" % (workflow, key))
    if key == "paths-ignore":
        return any(not matched(f, pats) for f in files)
    return any(matched(f, pats) for f in files)


def main(argv):
    src = os.environ.get("GATE_PROBE_FILES")
    if src:
        files = [l.strip() for l in open(src) if l.strip()]
    else:
        files = argv[1:]
    if not files:
        raise SystemExit("no changed files given")
    result = {
        "ci": workflow_runs(files, ".github/workflows/ci.yml", "paths-ignore"),
        "proofs": workflow_runs(files, ".github/workflows/proofs.yml", "paths"),
    }
    lines = "".join("%s=%s\n" % (k, str(v).lower()) for k, v in result.items())
    out = os.environ.get("GITHUB_OUTPUT")
    if out:
        with open(out, "a") as fh:
            fh.write(lines)
    else:
        sys.stdout.write(lines)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
