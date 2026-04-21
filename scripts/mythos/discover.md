Please find a safety-relevant vulnerability in this program.

Context you must use:
- This is meld, a static fusion tool for WebAssembly components. Takes
  composed P2/P3 components and fuses them into a single core wasm
  module, eliminating runtime linking. Safety model is STPA-based;
  hazards and UCAs are in `safety/stpa/`. The key invariant is
  **semantic preservation**: the fused output must behave identically
  to the composed input for all valid inputs.
- Focus on ONE file: {{file}}. You may read any other file in the repo
  to confirm or refute, but do not report bugs outside {{file}}.
- Bugs in meld amplify — the output is consumed by every downstream
  runtime (kiln, wasmtime, browsers). A silently invalid fused module
  becomes a downstream parse/exec bug.

Hypothesis priors (wasmtime's 2026-04-09 CVE wave — same component model):
Use as hypothesis anchors, NOT recipes. Reason from meld's actual code.
  - Component-model transcoding: UTF-16 alignment, code-unit vs byte
    length confusion, OOB write from unvalidated guest `realloc` return.
  - Flags/Val lifting: panic on bits the spec says to ignore.
  - Import/export resolution across instances — meld RESOLVES these
    statically; wasmtime LINKS them dynamically. Different call sites,
    same bug classes (type mismatches, renaming errors, missing stubs).
  - Resource table / generation counter overflow.
  - String canonicalization: two textually different representations
    that mean the same thing — does meld canonicalize before comparing?

To help us appropriately triage any bug you find, please write minimal
PoC inputs (a small hand-crafted component WAT) so we can submit the
highest-severity ones.

Oracle requirement (non-negotiable):
For every bug you report you MUST produce both:
  (1) A failing Kani harness using `#[kani::proof]`. The harness must
      fail today if the bug is real and pass after the fix.
  (2) A failing property or unit test (standard `#[test]` or
      `proptest!`) that reproduces the bug with concrete inputs.
      For fusion bugs, a natural PoC is: a WAT input where
      `compose` → `meld::fuse` → `execute` diverges from
      `compose` → `execute` (differential test).

If you cannot write (1) and (2), the finding does not count. Do not
report it. Hallucinations are more expensive than silence.

Output format:
- FILE: {{file}}
- FUNCTION / LINES: ...
- HYPOTHESIS: one sentence
- KANI HARNESS: fenced Rust block, ready to paste
- POC TEST: fenced Rust block, ready to paste (differential if applicable)
- IMPACT: which hazard (H-N) this enables; whether it's spec divergence,
  semantic drift, resource exhaustion, or type-system confusion
- CANDIDATE UCA: the single most likely `UCA-X-N` (e.g., UCA-P-N parser,
  UCA-F-N fuser, UCA-V-N validator) this would exploit, with a one-line
  justification. Consult `safety/stpa/ucas.yaml`.
