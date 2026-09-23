#!/usr/bin/env python3
"""The release matrix and the assets gate must name the same targets (#432).

Two files decide what a release ships:

    .github/workflows/release.yml              builds one archive per target
    .github/workflows/release-assets-gate.yml  requires one archive per target

They are independent lists, and the gate's own comment asks a human to
remember that "both lists change together". That comment has been the only
thing holding them in sync. The failure it invites is quiet in both
directions:

  * a target built but not required — it can silently stop building and the
    gate still passes, which is #395 all over again, one platform at a time;
  * a target required but not built — every release fails the gate after
    publication, which is loud but only reaches anyone once the release is
    already public.

Neither is caught by any test today, and the gate itself only runs *after* a
release is published. This runs on the pull request, where a drift is still
free to fix.

Usage: python3 tools/check_release_targets.py [--quiet]
Exit 1 naming the offending targets, 0 when the two lists agree.
"""

# rivet: verifies SR-84

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
RELEASE = ROOT / ".github/workflows/release.yml"
GATE = ROOT / ".github/workflows/release-assets-gate.yml"

# `- target: x86_64-unknown-linux-musl` in the build matrix.
MATRIX_TARGET = re.compile(r"^\s*-\s*target:\s*(\S+)\s*$")

# The gate's `for target in \ ... do` block, whose body is a backslash-folded
# whitespace-separated list of triples.
GATE_LOOP = re.compile(r"for target in\s*\\\n(.*?)\n\s*do\b", re.DOTALL)


def matrix_targets() -> set:
    return {
        m.group(1)
        for m in (MATRIX_TARGET.match(line) for line in RELEASE.read_text().splitlines())
        if m
    }


def gate_targets() -> set:
    m = GATE_LOOP.search(GATE.read_text())
    if not m:
        # Absence must fail: an empty set would otherwise agree with an empty
        # matrix, and a renamed loop would read as "nothing required".
        print(
            f"error: no `for target in ...` list found in {GATE.relative_to(ROOT)} — "
            "the gate's required-target list moved or was renamed, and this check "
            "cannot silently pass without it",
            file=sys.stderr,
        )
        sys.exit(1)
    return set(m.group(1).replace("\\", " ").split())


def main() -> int:
    quiet = "--quiet" in sys.argv
    built = matrix_targets()
    required = gate_targets()

    if not built:
        print(f"error: no `- target:` entries found in {RELEASE.relative_to(ROOT)}", file=sys.stderr)
        return 1

    unrequired = sorted(built - required)
    unbuilt = sorted(required - built)

    for target in unrequired:
        print(
            f"error: {target} is built by release.yml but not required by the assets "
            f"gate — it can stop shipping without anything noticing",
            file=sys.stderr,
        )
    for target in unbuilt:
        print(
            f"error: {target} is required by the assets gate but not built by "
            f"release.yml — every release will fail the gate after it is published",
            file=sys.stderr,
        )

    if unrequired or unbuilt:
        print(
            "\nBoth lists change together: the matrix in release.yml and the "
            "`for target in` list in release-assets-gate.yml.",
            file=sys.stderr,
        )
        return 1

    if not quiet:
        print(f"release matrix and assets gate agree on {len(built)} targets:")
        for target in sorted(built):
            print(f"  {target}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
