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

    return fails


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
