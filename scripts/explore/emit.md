You are emitting a new design ADR (Architecture Decision Record) under
the parent question in `safety/adr/{{adr-id}}.md`. The schema for ADRs
is `safety/adr/schema.yaml` — consult it for the exact field set and
allowed values. Do not invent fields.

Input:
- Confirmed prototype report (from prototype.md, validated by validate.md)
- Validator's locus-of-fix assignment
- Validator's generalization assessment
---
{{confirmed_report}}
LOCUS-OF-FIX: {{locus}}
GENERALIZATION: {{generalization}}
PARENT-ADR: {{adr-id}}
---

## Rules

1. **Grouping invariant**: ADRs in this repository are grouped under
   parent design questions. If `safety/adr/` already contains an ADR-N
   linked to `{{adr-id}}` via `parent`, this new finding becomes a
   SIBLING ADR-M with the same parent, NOT a new top-level ADR.
   Each sibling expresses a distinct alternative to the same problem.

2. **The new id** must be the next unused `ADR-N` by integer suffix
   under the parent. Read existing files in `safety/adr/` to determine
   it.

3. **Required fields** (per `safety/adr/schema.yaml`):
     - `id` (e.g., `ADR-3`)
     - `parent` (e.g., `ADR-0`)
     - `type: design-adr`
     - `title` (one line, names the path NOT the verdict)
     - `status: draft` (always; humans promote to `accepted` /
       `rejected` / `superseded`)
     - `description` — reference the prototype branch by full git ref
       and the gating oracle by test name. Bug lives in code, not in
       prose.
     - `fields.locus-of-fix` — meld | wit-bindgen | spec | wasm-tools
                              | hybrid
     - `fields.viability` (1–5, from rank pass)
     - `fields.generalization` — low | medium | high
     - `fields.maintenance-cost` — low | medium | high
     - `fields.fixture-coverage` — list of fixture names the
       prototype demonstrably handles (gating + any others)
     - `fields.upstream-dependency` — text describing what (if
       anything) the path requires from outside this repo

4. **Required links**:
     - `alternative-to` — list of sibling ADR ids under the same
       parent. Even if siblings don't exist YET, leave an empty list;
       later emissions update.
     - `prototype-branch` — full git ref, e.g.
       `feat/explore-D-mini-shim`
     - `oracle` — fully-qualified test name, e.g.
       `meld-core::tests::wit_bindgen_runtime::test_runtime_wit_bindgen_resource_floats`
     - `references` — prior art, RFCs, upstream issues. Include the
       hypothesis-priors paragraph from the prototype's invocation
       so future readers know what the explorer was told to consider.

5. **Status MUST be `draft` on first emission.** The human running
   the synthesis pass promotes one of the siblings to `accepted` and
   the others to `rejected` / `superseded`.

6. **Do not invent verdict text in `description`.** Cite the
   validator's REASON paragraph verbatim. The ADR is not a place to
   re-argue the case the validator already made.

## Output

Emit ONLY the YAML for the new ADR file at `safety/adr/ADR-N.md`,
ready to write to disk. The file body is a YAML front-matter block
followed by a markdown body that quotes the validator reason and
links to the prototype branch.

Example shape (do not copy verbatim — fill from the input):

```yaml
---
id: ADR-3
parent: ADR-0
type: design-adr
title: D — Mini-shim for trivial wit-bindgen wrapper structs
status: draft
fields:
  locus-of-fix: meld
  viability: 4
  generalization: medium
  maintenance-cost: low
  fixture-coverage:
    - resource_floats
  upstream-dependency: independent
links:
  alternative-to:
    - ADR-4
    - ADR-5
  prototype-branch: feat/explore-D-mini-shim
  oracle: meld-core::tests::wit_bindgen_runtime::test_runtime_wit_bindgen_resource_floats
  references:
    - https://github.com/bytecodealliance/wit-bindgen/blob/main/crates/rust/src/interface.rs
---

# ADR-3 — D — Mini-shim for trivial wit-bindgen wrapper structs

## Context

(One paragraph: state the problem from the parent ADR and which
alternative this represents.)

## Decision (DRAFT)

(Cite validator REASON verbatim.)

## Consequences

(From the prototype report's "WHAT THE PROTOTYPE DOES NOT HANDLE",
"GENERALIZATION SCORE", and "MAINTENANCE COST".)

## Prototype

`feat/explore-D-mini-shim` flips the gating oracle. Diff stat: ...
```

Emit ONLY this YAML+markdown file content, nothing else.
