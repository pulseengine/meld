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

A third consumer joined in #442: the PyPI wheels and npm packages are repacked
from the release archives, one per target, from the table in
python/pyproject.toml ([tool.meld-dist.targets.*]). A target built but absent
there silently never reaches pip/npm users; a target there that is not built
makes every publish fail after the GitHub release is already public. This
script checks that table against the same matrix.

Neither is caught by any test today, and the gate itself only runs *after* a
release is published. This runs on the pull request, where a drift is still
free to fix.

Usage: python3 tools/check_release_targets.py [--quiet]
Exit 1 naming the offending targets, 0 when the two lists agree.
"""

# rivet: verifies SR-84

import json
import pathlib
import re
import sys
try:
    import tomllib
except ModuleNotFoundError:  # Python < 3.11, e.g. macOS /usr/bin/python3 (3.9)
    try:
        import tomli as tomllib
    except ModuleNotFoundError:
        sys.exit("check_release_targets.py: needs Python 3.11+ (tomllib) or the tomli package")

ROOT = pathlib.Path(__file__).resolve().parent.parent
RELEASE = ROOT / ".github/workflows/release.yml"
GATE = ROOT / ".github/workflows/release-assets-gate.yml"
DIST = ROOT / "python/pyproject.toml"
NPM_ROOT = ROOT / "npm/package.json"

# Per-target keys every row of the distribution table must carry.
DIST_KEYS = {"os", "wheel-arch", "npm-platform", "npm-os", "npm-cpu"}

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


def dist_problems(built: set) -> list:
    """Wheel/npm target table vs the release matrix; returns error strings."""
    rel = DIST.relative_to(ROOT)
    try:
        data = tomllib.loads(DIST.read_text())
        dist = data["tool"]["meld-dist"]
        table = dist["targets"]
    except (OSError, KeyError, tomllib.TOMLDecodeError) as e:
        # Absence must fail, for the same reason as the gate list above.
        return [f"error: cannot read [tool.meld-dist.targets] from {rel}: {e!r}"]

    problems = []
    listed = set(table)
    for target in sorted(built - listed):
        problems.append(
            f"error: {target} is built by release.yml but has no wheel/npm row in {rel} "
            f"- pip and npm users silently never get it"
        )
    for target in sorted(listed - built):
        problems.append(
            f"error: {target} has a wheel/npm row in {rel} but release.yml does not build it "
            f"- every PyPI/npm publish would fail after the release is public"
        )
    for target, row in sorted(table.items()):
        missing = DIST_KEYS - set(row)
        if missing:
            problems.append(f"error: {rel} [{target}] is missing {sorted(missing)}")
        if "linux" in target and row.get("os") == "linux" and not {"libc", "npm-libc"} <= set(row):
            problems.append(f"error: {rel} [{target}] is a linux row without libc / npm-libc")
    platforms = [row.get("npm-platform") for row in table.values()]
    if len(platforms) != len(set(platforms)):
        problems.append(f"error: {rel} has duplicate npm-platform values: {sorted(platforms)}")
    wheel_keys = [(row.get("os"), row.get("libc"), row.get("wheel-arch")) for row in table.values()]
    if len(wheel_keys) != len(set(wheel_keys)):
        problems.append(f"error: {rel} has two rows that would produce the same wheel tag")
    try:
        npm_name = json.loads(NPM_ROOT.read_text())["name"]
        if npm_name != dist.get("npm-name"):
            problems.append(
                f"error: {NPM_ROOT.relative_to(ROOT)} name {npm_name!r} != npm-name "
                f"{dist.get('npm-name')!r} in {rel}"
            )
    except (OSError, KeyError, json.JSONDecodeError) as e:
        problems.append(f"error: cannot read {NPM_ROOT.relative_to(ROOT)}: {e!r}")
    return problems


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

    dist_errors = dist_problems(built)
    for line in dist_errors:
        print(line, file=sys.stderr)

    if dist_errors:
        print(
            "\nThe PyPI/npm table (python/pyproject.toml) changes together with the "
            "release.yml matrix too.",
            file=sys.stderr,
        )
        return 1

    if unrequired or unbuilt:
        print(
            "\nBoth lists change together: the matrix in release.yml and the "
            "`for target in` list in release-assets-gate.yml.",
            file=sys.stderr,
        )
        return 1

    if not quiet:
        print(f"release matrix, assets gate and wheel/npm table agree on {len(built)} targets:")
        for target in sorted(built):
            print(f"  {target}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
