#!/usr/bin/env python3
"""Generate docs/verification-matrix.md — the requirement -> test mapping.

WHY (meld#303 / SR-44, the visibility half): the SR -> test/proof mapping lives
in `safety/requirements/traceability.yaml`'s `verification-status:` block, which
rivet does NOT ingest into its trace graph (those fields are not in the
requirement schema). So `rivet matrix`/`trace` cannot show it — this script is
the only way to *see*, per requirement, which tests/proofs verify it and at what
status. This is the rendering half; the *enforced* `verifies`-link half awaits
the v0.36 traceability-model decision (#303).

Run: python3 scripts/gen-verification-matrix.py  (regenerates docs/verification-matrix.md)
"""
import sys
import pathlib
import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
TRACE = ROOT / "safety/requirements/traceability.yaml"
REQS = ROOT / "safety/requirements/safety-requirements.yaml"
OUT = ROOT / "docs/verification-matrix.md"


def load(p):
    with open(p) as f:
        return yaml.safe_load(f)


def main():
    trace = load(TRACE) or {}
    reqs = load(REQS) or {}
    vstatus = trace.get("verification-status", {}) or {}

    # SR id -> title (from the requirements file's list structure).
    titles = {}
    for r in (reqs.get("requirements") or reqs.get("artifacts") or []):
        if isinstance(r, dict) and r.get("id"):
            titles[r["id"]] = r.get("title", "")
    # Fallback: some repos nest requirements under a top-level key list.
    if not titles:
        for v in reqs.values() if isinstance(reqs, dict) else []:
            if isinstance(v, list):
                for r in v:
                    if isinstance(r, dict) and r.get("id"):
                        titles[r["id"]] = r.get("title", "")

    def sr_key(k):
        try:
            return (0, int(k.split("-")[1]))
        except (IndexError, ValueError):
            return (1, k)

    rows = []
    status_counts = {}
    for sr in sorted(vstatus, key=sr_key):
        e = vstatus[sr] or {}
        status = e.get("status", "?")
        status_counts[status] = status_counts.get(status, 0) + 1
        tests = e.get("tests") or []
        proofs = e.get("proofs") or []
        tests_md = "<br>".join(f"`{t}`" for t in tests) if tests else "—"
        proofs_md = ", ".join(f"`{p}`" for p in proofs) if proofs else "—"
        rows.append((sr, titles.get(sr, ""), status, tests_md, proofs_md))

    lines = []
    lines.append("# Verification matrix (requirement → test/proof)")
    lines.append("")
    lines.append(
        "> **Generated** by `scripts/gen-verification-matrix.py` from "
        "`safety/requirements/traceability.yaml` (`verification-status:`). "
        "Do not edit by hand."
    )
    lines.append(">")
    lines.append(
        "> This renders the mapping rivet's graph does not carry "
        "(`verification-status` fields are outside the requirement schema — see "
        "#303/SR-44). `status` here is the **self-asserted** verification state; "
        "the *enforced* `verifies`-link trace awaits the v0.36 model decision. "
        "`partial` = a test exists but does not fully discharge the requirement."
    )
    lines.append("")
    total = len(rows)
    summary = " · ".join(f"{k}: {v}" for k, v in sorted(status_counts.items()))
    lines.append(f"**{total} requirements** — {summary}")
    lines.append("")
    lines.append("| Req | Title | Status | Tests (verifies) | Proofs |")
    lines.append("|-----|-------|--------|------------------|--------|")
    for sr, title, status, tests_md, proofs_md in rows:
        title = title.replace("|", "\\|")
        lines.append(f"| {sr} | {title} | {status} | {tests_md} | {proofs_md} |")
    lines.append("")

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(lines) + "\n")
    print(f"wrote {OUT.relative_to(ROOT)} — {total} requirements, {summary}")


if __name__ == "__main__":
    sys.exit(main())
