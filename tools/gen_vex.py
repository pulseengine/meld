#!/usr/bin/env python3
"""Generate a CycloneDX VEX for a release, scoped to what the release ships (#433).

## The question this document answers

A consumer pinned to a meld release asks: *is advisory RUSTSEC-XXXX-YYYY
present in what I am actually running?* An SBOM cannot answer that — it says
what is in the product, not what an advisory means for it. That is VEX.

## Scope follows the SBOM, deliberately

meld's published `meld-<version>.cdx.json` contains **only shipped
dependencies** — 62 components at v0.59.0, with no `wasmtime`, `criterion`,
`proptest` or `crossbeam-epoch`. Auditing the whole lockfile reports 20
vulnerabilities, 19 of them in `wasmtime`/`wasmtime-wasi`, every one a
dev-dependency used to *execute* fused modules in tests and never to fuse them.

Those 19 are not in the SBOM, so a consumer scanning it never sees them, so
this document does not list them. Emitting 20 `component_not_present` entries
about components the SBOM does not mention would be answering a question
nobody asked, and would bury any entry that mattered.

An advisory is in scope here when its package appears in the SBOM.

## A judgement is never generated

`not_affected` with a justification like `vulnerable_code_not_in_execute_path`
is a claim about this source tree. A generated one is a false statement signed
into a release. So:

  * the MATCH LIST is mechanical — `cargo audit` against the tag's lockfile;
  * the JUDGEMENTS are hand-authored in `safety/supply-chain/vex-judgements.yaml`;
  * an in-scope advisory with no judgement is a **hard failure**, not an
    omission and not a default `not_affected`.

That last rule is the whole point. A generator that quietly emitted
`not_affected` for an advisory nobody had looked at would produce a signed
document asserting safety that no human had assessed.

Usage:
    python3 tools/gen_vex.py --sbom meld-0.59.0.cdx.json --version 0.59.0 \\
        --out meld-0.59.0.vex.json

Exit 1 when an in-scope advisory lacks a judgement, naming it.
"""

# rivet: verifies SR-87

import argparse
import datetime
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
JUDGEMENTS = ROOT / "safety/supply-chain/vex-judgements.yaml"

# CycloneDX 1.5 allowed values, so a typo in the judgements file is caught here
# rather than by a consumer's parser.
STATES = {"resolved", "exploitable", "in_triage", "false_positive", "not_affected", "affected"}
JUSTIFICATIONS = {
    "code_not_present",
    "code_not_reachable",
    "requires_configuration",
    "requires_dependency",
    "requires_environment",
    "protected_by_compiler",
    "protected_at_runtime",
    "protected_at_perimeter",
    "protected_by_mitigating_control",
}


def sbom_component_names(path: pathlib.Path) -> set:
    doc = json.loads(path.read_text())
    return {c["name"] for c in doc.get("components", []) if "name" in c}


def sbom_serial(path: pathlib.Path) -> str:
    return json.loads(path.read_text()).get("serialNumber", "")


def audit() -> list:
    """Every advisory `cargo audit` matches against the committed lockfile.

    The lockfile is the one at this commit, which for a release job is the
    tag's — the exact dependency set that was built, not whatever `main` holds
    when the job runs.
    """
    proc = subprocess.run(
        ["cargo", "audit", "--json"], capture_output=True, text=True, cwd=ROOT
    )
    if not proc.stdout.strip():
        print(f"error: `cargo audit --json` produced no output\n{proc.stderr}", file=sys.stderr)
        sys.exit(1)
    data = json.loads(proc.stdout)
    out = []
    for item in data.get("vulnerabilities", {}).get("list", []):
        adv, pkg = item.get("advisory", {}), item.get("package", {})
        out.append(
            {
                "id": adv.get("id"),
                "package": pkg.get("name"),
                "version": pkg.get("version"),
                "title": adv.get("title", ""),
                "url": adv.get("url") or f"https://rustsec.org/advisories/{adv.get('id')}",
            }
        )
    # `unsound` warnings are judgement-worthy too: RUSTSEC-2026-0190 (anyhow
    # `Error::downcast_mut`) arrived as a warning, was in the shipped graph, and
    # was a real fix. Ignoring warnings would have hidden it.
    for kind, items in (data.get("warnings") or {}).items():
        if kind not in ("unsound", "unmaintained"):
            continue
        for item in items:
            adv, pkg = item.get("advisory") or {}, item.get("package", {})
            if not adv.get("id"):
                continue
            out.append(
                {
                    "id": adv["id"],
                    "package": pkg.get("name"),
                    "version": pkg.get("version"),
                    "title": adv.get("title", ""),
                    "url": adv.get("url") or f"https://rustsec.org/advisories/{adv['id']}",
                    "kind": kind,
                }
            )
    return out


def load_judgements() -> dict:
    """Minimal parser for the judgements file — stdlib only, like the other checkers.

    Shape, one block per advisory:

        RUSTSEC-2026-0190:
          state: not_affected
          justification: code_not_present
          detail: >
            free text, which lands in the published document
    """
    if not JUDGEMENTS.is_file():
        return {}
    out, cur, key = {}, None, None
    for raw in JUDGEMENTS.read_text().splitlines():
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        m = re.match(r"^([A-Z]+-\d{4}-\d{4}):\s*$", raw)
        if m:
            cur = {}
            out[m.group(1)] = cur
            key = None
            continue
        if cur is None:
            continue
        m = re.match(r"^\s+([a-z_]+):\s*(.*)$", raw)
        if m:
            key = m.group(1)
            val = m.group(2).strip()
            cur[key] = "" if val in (">", "|") else val
        elif key:
            cur[key] = (cur[key] + " " + raw.strip()).strip()
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sbom", required=True)
    ap.add_argument("--version", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    sbom = pathlib.Path(args.sbom)
    if not sbom.is_file():
        print(f"error: SBOM not found at {sbom}", file=sys.stderr)
        return 1
    shipped = sbom_component_names(sbom)
    if not shipped:
        # An empty component list would make every advisory out of scope and
        # produce a vacuously clean VEX. Refuse.
        print(
            f"error: {sbom} lists no components — a VEX generated against it would "
            "declare every advisory out of scope and assert safety it never checked",
            file=sys.stderr,
        )
        return 1

    findings = audit()
    in_scope = [f for f in findings if f["package"] in shipped]
    out_of_scope = [f for f in findings if f["package"] not in shipped]

    judgements = load_judgements()
    unjudged = [f for f in in_scope if f["id"] not in judgements]
    if unjudged:
        print(
            "error: advisories affect components in this release's SBOM and have no "
            "judgement in safety/supply-chain/vex-judgements.yaml:",
            file=sys.stderr,
        )
        for f in unjudged:
            print(f"  {f['id']}  {f['package']} {f['version']}  {f['title'][:70]}", file=sys.stderr)
        print(
            "\nA judgement is a human assessment of this source tree. This generator will "
            "not default one, because a generated `not_affected` is a false statement "
            "signed into a release. Assess each one and record it.",
            file=sys.stderr,
        )
        return 1

    vulns = []
    for f in in_scope:
        j = judgements[f["id"]]
        state = j.get("state", "")
        just = j.get("justification", "")
        if state not in STATES:
            print(f"error: {f['id']} has state {state!r}, not a CycloneDX state", file=sys.stderr)
            return 1
        if state == "not_affected" and just not in JUSTIFICATIONS:
            print(
                f"error: {f['id']} is not_affected but its justification {just!r} is not a "
                "CycloneDX justification — a consumer's parser would drop it",
                file=sys.stderr,
            )
            return 1
        analysis = {"state": state}
        if just:
            analysis["justification"] = just
        if j.get("detail"):
            analysis["detail"] = j["detail"]
        vulns.append(
            {
                "id": f["id"],
                "source": {"name": "RUSTSEC", "url": f["url"]},
                "affects": [{"ref": f"pkg:cargo/{f['package']}@{f['version']}"}],
                "description": f["title"],
                "analysis": analysis,
            }
        )

    now = datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0).isoformat()
    doc = {
        "bomFormat": "CycloneDX",
        "specVersion": "1.5",
        "version": 1,
        "metadata": {
            "timestamp": now,
            "component": {
                "type": "application",
                "name": "meld",
                "version": args.version,
                "purl": f"pkg:cargo/meld-cli@{args.version}",
            },
            "properties": [
                {
                    "name": "meld:vex:scope",
                    "value": (
                        "Advisories affecting the components listed in this release's SBOM, "
                        "which contains shipped dependencies only. Dev-dependency advisories "
                        "are out of scope and not listed: they are absent from the SBOM, so "
                        "a consumer scanning it never matches them."
                    ),
                },
                {"name": "meld:vex:sbom-components", "value": str(len(shipped))},
                {"name": "meld:vex:advisories-out-of-scope", "value": str(len(out_of_scope))},
            ],
        },
        "vulnerabilities": vulns,
    }
    serial = sbom_serial(sbom)
    if serial:
        doc["metadata"]["properties"].append({"name": "meld:vex:bom-link", "value": serial})

    pathlib.Path(args.out).write_text(json.dumps(doc, indent=2) + "\n")
    print(
        f"wrote {args.out}: {len(vulns)} in-scope advisory judgement(s), "
        f"{len(out_of_scope)} out of scope (not in the SBOM), "
        f"{len(shipped)} shipped components"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
