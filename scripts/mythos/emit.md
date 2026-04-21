You are emitting a new loss-scenario entry to append to
`safety/stpa/loss-scenarios.yaml`. Consult the existing file for the
exact shape before emitting.

Input:
- Confirmed bug report (below)
- Chosen `UCA-X-N` from the validator
---
{{confirmed_report}}
UCA: {{uca_id}}
---

Rules:
1. Grouping invariant: loss-scenarios are grouped under UCAs. If the
   file already has a scenario linked to `{{uca_id}}`, this new
   finding typically becomes a SIBLING, not a new UCA.
2. The new id follows whatever scheme the existing file uses (check
   first entry). Use the next unused suffix for that UCA prefix.
3. Required fields — match existing entries exactly. Do not invent
   fields. Common fields: `id`, `title`, `uca`, `hazards`, `type`,
   `scenario`, `causal-factors`.
4. In the `scenario` prose, reference the Kani harness and PoC test
   by fully-qualified Rust path. Cite the WebAssembly Component Model
   spec section that the bug violates.
5. Optional but recommended: `related-cve:` when a wasmtime CVE
   covers the same class (e.g., `CVE-2026-27572`).
6. Add `status: draft`. Meld's schema may not have this field today;
   add it anyway — humans promote to `approved`.

Emit ONLY the YAML block, nothing else.
