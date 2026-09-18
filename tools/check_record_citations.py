#!/usr/bin/env python3
"""Every test cited by the safety record must exist in the source tree (#411).

A citation to a *missing* test is visibly broken the moment anyone checks. A
citation to a test whose name states a *refuted* invariant reads as coherent
evidence. #411 found four of both kinds, three of which named behaviour the
codebase had since deliberately inverted. This is the mechanical check that
would have caught all four:

    every `module::path::test_name` cited in the record resolves to a name that
    appears in some .rs file in the workspace

Resolution is "the name appears as a word in a .rs file", not "there is a `fn`
with that name", because tests are also produced by macros (`runtime_test!`)
and citations legitimately point at test *modules* (`segments.rs::ordeal_fold_proof`).
Known limit: a name that appears only in a comment would resolve. The check is
aimed at citations that resolve to nothing at all, which is what drift produces.

Usage: python3 tools/check_record_citations.py [--quiet]
Exit 1 with the offenders named, 0 when every citation resolves.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

RECORD_FILES = [
    "safety/requirements/sw-verifications.yaml",
    "safety/requirements/traceability.yaml",
    "docs/verification-matrix.md",
]

# A test-ish identifier: lower snake_case with at least one underscore.
NAME = r"[a-z][a-z0-9_]*_[a-z0-9_]+"


def source_words() -> set[str]:
    words: set[str] = set()
    for path in ROOT.rglob("*.rs"):
        if "target/" in str(path.relative_to(ROOT)):
            continue
        words.update(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", path.read_text(errors="ignore")))
    return words


def citations(text: str) -> dict[str, int]:
    """Cited test names -> offset of first mention."""
    found: dict[str, int] = {}
    # `module::path::test_name` in backticks (yaml prose, markdown tables)
    for m in re.finditer(r"`([^`]*::[^`]+)`", text):
        parts = m.group(1).split("::")
        # `Type::field` is a prose reference to a struct field, not a test path.
        if len(parts) >= 2 and parts[-2].strip()[:1].isupper():
            continue
        seg = parts[-1].strip()
        if re.fullmatch(NAME, seg):
            found.setdefault(seg, m.start())
    # path/to/file.rs::test_name, with or without backticks
    for m in re.finditer(r"\.rs::(" + NAME + r")", text):
        found.setdefault(m.group(1), m.start())
    # bare YAML list item: "- module::path::test_name" (any number of segments;
    # the prefix must allow ':' or multi-segment paths are missed silently)
    for m in re.finditer(r"(?m)^\s*-\s+([A-Za-z0-9_./:-]+::" + NAME + r")\s*$", text):
        found.setdefault(m.group(1).split("::")[-1], m.start())
    return found


def main() -> int:
    quiet = "--quiet" in sys.argv
    words = source_words()
    if len(words) < 1000:  # guard the guard: the scan must have read the tree
        print(f"ERROR: only {len(words)} identifiers found in .rs sources; scan is broken")
        return 1

    total, unresolved = 0, []
    for rel in RECORD_FILES:
        text = (ROOT / rel).read_text()
        cites = citations(text)
        if not cites:
            print(f"ERROR: no citations extracted from {rel}; the extractor is broken")
            return 1
        total += len(cites)
        for name, pos in sorted(cites.items(), key=lambda kv: kv[1]):
            if name not in words:
                unresolved.append((rel, text[:pos].count("\n") + 1, name))

    if unresolved:
        print(f"{len(unresolved)} cited test(s) do not exist in the source tree (#411):\n")
        for rel, line, name in unresolved:
            print(f"  {rel}:{line}: {name}")
        print(
            "\nRe-point each at the test that exists and RE-READ its assertions: in #411 three of\n"
            "four renames accompanied a deliberate inversion, so the successor may verify the\n"
            "opposite of what the requirement claims."
        )
        return 1

    if not quiet:
        print(f"OK: {total} cited tests across {len(RECORD_FILES)} record files all resolve")
    return 0


if __name__ == "__main__":
    sys.exit(main())
