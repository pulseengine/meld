Build the smallest possible working slice for ONE design path under
the parent question in `safety/adr/{{adr-id}}.md`. You are exploring,
not finishing — produce the minimum viable proof that this path can
satisfy the gating oracle.

Path you are exploring: `{{path-name}}`
Locus-of-fix declared in rank: `{{locus-of-fix}}`
Gating oracle: `{{gating-oracle}}` (a single test that, if it flips
from `fuse_only_test!` to a passing `runtime_test!`, demonstrates the
core mechanism works).

## Context you must use

- This is meld, a static fusion tool for WebAssembly components. It
  takes composed P2/P3 components and fuses them into a single core
  wasm module. The safety model is STPA-based; the parent ADR cites
  the relevant losses/hazards.
- Read the parent ADR FIRST (`safety/adr/{{adr-id}}.md`) — it states
  the problem, lists the alternatives, and points to prior code
  attempts.
- Read the gating oracle test in `meld-core/tests/wit_bindgen_runtime.rs`
  before writing code, so you know exactly what passing means.
- The 19-site LS-A-7 audit (commits `fcad26a`, `1223555`) and the
  P3 async stabilizing-shim work (commits `e5cd80f`, `6a63971`,
  `1097f08`) introduced infrastructure (`emit_checked_realloc`,
  `emit_overflow_guard`, `cabi_size_align`, `collect_indirections`,
  `generate_stabilizing_shim`) you should reuse where applicable.

## Hypothesis priors for this path

{{hypothesis-priors}}

(One paragraph the human running the pipeline supplies — known prior
art, related upstream discussions, or particular code paths to
consider before writing the prototype.)

## Oracle requirement (non-negotiable)

For this path to count as a viable design, you MUST produce ALL of
the following:

  (1) A branch `feat/explore-{{path-name}}` with a working prototype
      that flips the gating fixture's `fuse_only_test!` to a passing
      `runtime_test!`. The prototype may be ugly; it must be correct.
  (2) `cargo test --package meld-core` MUST pass with the prototype
      applied — no regressions.
  (3) `cargo test --test wit_bindgen_runtime {{gating-oracle}}` MUST
      pass — the oracle holds.
  (4) A short report (under 600 words) summarizing what the prototype
      does, where it falls down, and what the validator should look at.

If you cannot produce all four — for example, because the prototype
requires an upstream change that does not yet exist, or because the
infrastructure you need isn't in meld — output exactly:

  `NOT VIABLE TODAY: <one sentence on what's missing>`

…and stop. Do NOT submit a prototype that doesn't actually flip the
oracle. Hallucinations are more expensive than silence — a half-baked
prototype that "looks like it might work" wastes the validator's time
and degrades the convergent oracle that makes this pipeline useful.

If your `locus-of-fix` is NOT `meld`, the oracle still applies:
you may need to vendor / patch / submodule the upstream piece into
this repo as a temporary mock, but the meld-side changes must
interoperate with that mock and the meld-side test must pass.

## Output format

If viable, produce a single structured report:

- PATH: `{{path-name}}`
- BRANCH: `feat/explore-{{path-name}}` (must exist and pass tests)
- ORACLE STATUS: PASSED (the gating fixture flipped and runs)
- DESIGN ONE-LINER: one sentence describing the mechanism
- WHAT CHANGED: bullet list of file paths + nature of edits
- WHAT THE PROTOTYPE DOES NOT HANDLE: honest list of edge cases /
  fixtures / scenarios this prototype skips. Be specific.
- GENERALIZATION SCORE: low | medium | high — your honest take on
  whether the approach extends to `resource_with_lists` and
  `resource-import-and-export` (the other two failing fixtures).
  "Low" is fine; the validator will assess.
- MAINTENANCE COST: low | medium | high — your honest take on the
  ongoing cost of the new code (new abstractions, new invariants
  the rest of the codebase must respect, ongoing upstream tracking).
- UPSTREAM DEPENDENCY: independent | requires-pulseengine-wit-bindgen-fork |
  requires-spec-change | etc.
- ONE QUESTION FOR THE VALIDATOR: the single most-load-bearing
  judgment call you made; the thing the validator most needs to
  assess.

Do NOT include prose beyond what the format requires.
