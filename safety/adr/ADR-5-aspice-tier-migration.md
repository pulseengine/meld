# ADR-5 — ASPICE SWE tier migration for the requirement model (#303, v0.36)

**Status:** accepted (design) — execution in progress
**Date:** 2026-06-24
**Supersedes the model choice in:** #303 / SR-44 enforcement discussion

## Context

v0.36 enforces requirement→verification traceability. The chosen approach
(maintainer decision, 2026-06-24) is the **full ASPICE SWE tier migration**,
not a generic-`requirement` clean-up. The rivet `aspice@0.2.0` schema models
the V as a typed tier:

```
stakeholder-req (SYS.1)
   └─derives-from→ system-req (SYS.2)         [derived-from REQUIRED]
        └─derives-from→ sw-req (SWE.1)        [derived-from → system-req REQUIRED]
             ←verifies─ sw-verification (SWE.6) [verifies → sw-req REQUIRED on the verification]
```

Hard (error-level) constraints from the schema:
- every `system-req` MUST `derives-from` a `stakeholder-req` (one-or-many);
- every `sw-req` MUST `derives-from` a `system-req` (or `system-arch-component`);
- a `sw-verification` MUST `verifies` a `sw-req`.
- `swe1-has-verification` (every sw-req verified) is **warning** severity — so
  the verification layer is needed for V-closure but does not block `validate`.

meld today has 44 `type: requirement` SRs (deriving from STPA `CC-*`/`LS-*`),
no stakeholder/system tier, and verification encoded as free-text
`fields.verification-method` (not typed `sw-verification`).

## Decision

Migrate to the ASPICE tier in phases, oracle-gated on `rivet validate` (run
with the #570-fixed rivet) after each phase.

### Proposed hierarchy

**Stakeholder requirements (2):**
- `STK-1` — Fused output is functionally equivalent to the composed input.
- `STK-2` — Fused output is fit for functional-safety deployment (traceable,
  attested, deterministic, sound-by-construction).

**System requirements (11)** — each `derives-from` a stakeholder-req; every SR
maps to exactly one:

| sys-req | theme | SRs |
|---|---|---|
| SYS-1 | Faithful component ingestion (parse) | SR-1,2,3,4,6 |
| SYS-2 | Sound index-space merging | SR-5,7,8,9,10,11,26,31 |
| SYS-3 | Correct Canonical-ABI cross-component adapters | SR-12,13,14,15,16,17,18,22,23,24,25,40,41,42 |
| SYS-4 | Valid component wrapping / output | SR-21 |
| SYS-5 | Async / P3 fusion support | SR-32,33,34,43 |
| SYS-6 | Memory-strategy / isolation soundness | SR-37 |
| SYS-7 | DWARF debug-info preservation | SR-35,36,38 |
| SYS-8 | Cross-input linking (import internalisation) | SR-39 |
| SYS-9 | Deterministic, fail-fast operation | SR-19,20 |
| SYS-10 | Attestation integrity | SR-27,28,29,30 |
| SYS-11 | Traceability / verification governance | SR-44 |

STK-1 ← SYS-1,2,3,4,5,7,8; STK-2 ← SYS-6,9,10,11 (a sys-req derives from one
stakeholder-req; the split is by "equivalence" vs "safety-fitness").

### Phases (each oracle-gated)

0. **Prerequisite hygiene** (mostly done — 77→39): UCA `uca-type`, host
   controllers, status enum (commit 1a52863). Remaining: 4 dangling
   `caused-by-uca` (author UCA-F-2/F-3/CP-1 — STPA, tracked separately) and
   the GitHub-issue provenance links (handled in Phase 2's per-SR pass).
1. **Foundation** (this ADR's companion commit): author
   `safety/requirements/system-requirements.yaml` with STK-1/2 + SYS-1..11.
   Additive; adds no errors (only `sys2-has-verification` warnings).
2. **Flip** (per-SR pass over `safety-requirements.yaml`): `type: requirement`
   → `type: sw-req`; add `derived-from → SYS-n` per the map; convert the
   `tracked-by: "#N"` / `derives-from: "#N"` GitHub refs to `cited-source`
   (kind: github) — preserving provenance, removing the dangling/undeclared
   links. Drives the remaining errors down; surfaces the sw-req coverage
   warnings.
3. **Verification layer** (V-closure): author typed `sw-verification` artifacts
   from the existing `verification-matrix` data (`verifies → SR-n`,
   `method: automated-test|formal-verification|...`). Clears the
   `swe1-has-verification` warnings; closes the right side of the V.
4. **Gate**: wire `rivet validate` (must pass) as the v0.36 enforcement gate
   once rivet releases the #570 fix and meld's CI consumes it.

## Consequences

- Strongest standards alignment (ASPICE SWE.1/.6); requirement→verification
  becomes a typed, enforced trace, not a rendered matrix.
- Largest effort: ~13 new tier artifacts + 44 SR rewrites + ~N verification
  artifacts; multi-phase, each verified against the oracle.
- The `cited-source` choice for GitHub issues is deliberate: issues are not
  trace-graph artifacts, so provenance belongs in `cited-source`, not in
  `derives-from`/`tracked-by` edges.
