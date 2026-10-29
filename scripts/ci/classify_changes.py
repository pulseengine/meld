#!/usr/bin/env python3
"""Classify a change for ci.yml and proofs.yml: docs-only? proof-relevant?

This replaces the two stub workflows (ci-docs-stub.yml, proofs-stub.yml). They
reported `Test`/`Clippy`/`Format` and `Rocq proofs` as instant successes on
the paths the real workflows' `pull_request` filters skipped. In a merge queue
that is a hazard. A queue run has no PR path filter, and a stub posting a
trivially green duplicate of a required context is indistinguishable from the
real verdict. So the filter moved into a job: the real workflows always run on
pull_request and merge_group, a `changes` job runs this script, and the
expensive jobs skip by job-level `if:`. A skipped job still REPORTS its context;
a workflow that never starts does not.

Outputs (to $GITHUB_OUTPUT, else stdout):
  docs_only=true|false  every changed path matches DOCS_ONLY (ci.yml's old
                        paths-ignore, still the push filter)
  proofs=true|false     some changed path matches PROOFS (proofs.yml's old
                        paths, still the push filter)

FAILS CLOSED. Any event but pull_request/merge_group, an empty base, a failed
or empty diff gives docs_only=false, proofs=true. Everything runs.

The two lists must equal the workflows' push filters, which
scripts/check_workflow_gates.py asserts, so the PR path and the push path
cannot drift apart. Stdlib only, like that checker.
"""
import argparse
import os
import re
import subprocess
import sys

# == ci.yml `push.paths-ignore`
DOCS_ONLY = [
    "**/*.md",
    "safety/**",
    "scripts/mythos/**",
    "tools/*.py",
]
# == proofs.yml `push.paths`
PROOFS = [
    "proofs/**",
    ".github/workflows/proofs.yml",
    "MODULE.bazel",
    "MODULE.bazel.lock",
    ".bazelrc",
    ".bazelversion",
]


def glob_re(g):
    """GitHub's filter-pattern glob: `*` stops at `/`, `**` does not."""
    out, i = "", 0
    while i < len(g):
        if g.startswith("**/", i):
            out += "(?:.*/)?"
            i += 3
        elif g.startswith("**", i):
            out += ".*"
            i += 2
        elif g[i] == "*":
            out += "[^/]*"
            i += 1
        elif g[i] == "?":
            out += "[^/]"
            i += 1
        else:
            out += re.escape(g[i])
            i += 1
    return re.compile(out + r"\Z")


def matches(path, globs):
    return any(glob_re(g).match(path) for g in globs)


def classify(changed):
    """(docs_only, proofs) for a list of changed paths. Empty = fail closed."""
    if not changed:
        return False, True
    return (all(matches(p, DOCS_ONLY) for p in changed),
            any(matches(p, PROOFS) for p in changed))


def emit(docs_only, proofs, why):
    out = os.environ.get("GITHUB_OUTPUT")
    lines = f"docs_only={'true' if docs_only else 'false'}\nproofs={'true' if proofs else 'false'}\n"
    if out:
        with open(out, "a") as f:
            f.write(lines)
    sys.stdout.write(lines)
    print(f"-> {why}")


def self_test():
    cases = [
        (["README.md"], (True, False)),
        (["docs/a/b.md", "safety/stpa/x.yaml"], (True, False)),
        (["tools/run_ls_verification.py"], (True, False)),
        (["tools/sub/x.py"], (False, False)),          # `*` stops at `/`
        (["scripts/mythos/rank.md", "meld-core/src/lib.rs"], (False, False)),
        (["proofs/x/y.v"], (False, True)),
        (["MODULE.bazel", "README.md"], (False, True)),
        ([".github/workflows/ci.yml"], (False, False)),
        (["MODULE.bazel.lock.bak"], (False, False)),   # anchored at the end
        ([], (False, True)),                           # empty diff: fail closed
    ]
    bad = 0
    for changed, want in cases:
        got = classify(changed)
        ok = got == want
        bad += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} {changed} -> {got} (want {want})")
    print("self-test PASS" if not bad else f"self-test FAIL ({bad})")
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        return self_test()
    event = os.environ.get("EVENT_NAME", "")
    base = os.environ.get("BASE_SHA", "")
    if event not in ("pull_request", "merge_group"):
        emit(False, True, f"event {event or '<none>'}: run everything")
        return 0
    if not base:
        emit(False, True, "no base sha: run everything")
        return 0
    r = subprocess.run(["git", "diff", "--name-only", f"{base}...HEAD"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stderr, file=sys.stderr)
        emit(False, True, f"git diff failed against {base}: run everything")
        return 0
    changed = [p for p in r.stdout.splitlines() if p.strip()]
    print("changed files:\n  " + "\n  ".join(changed))
    if not changed:
        emit(False, True, "git diff returned no paths: run everything")
        return 0
    d, p = classify(changed)
    emit(d, p, f"docs_only={d} proofs={p}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
