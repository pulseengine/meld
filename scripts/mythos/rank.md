Rank source files in this repository by likelihood of containing a
safety-relevant bug (spec divergence, fusion-semantics breakage, resource
exhaustion, type-system confusion across component boundaries), on a 1–5
scale. Output JSON: `[{"file": "...", "rank": N, "reason": "..."}]`,
sorted descending.

Scope: `meld-cli/src/**`, `meld-core/src/**`. Exclude tests, examples.

Ranking rubric (meld-specific, component-fusion threat model):

5 (fusion correctness — semantic preservation is the invariant):
  - meld-core/src/parser.rs or parse/**      # component parsing
  - meld-core/src/fuse/** or fusion/**       # core fusion logic
  - meld-core/src/types/** or type_check/**  # cross-component type checks
  - meld-core/src/writer.rs or emit/**       # output WASM emission

4 (resolution + validation):
  - meld-core/src/resolver/** or imports/**  # import/export resolution
  - meld-core/src/validate/**                # post-fusion validation
  - meld-core/src/canonical_abi/**           # component-model canonical ABI

3 (support):
  - meld-core/src/error.rs, metrics.rs
  - meld-cli/** (argv + env; not a heavy attack surface but worth checking)

2 (wiring):
  - glue modules, re-exports

1 (proof artifacts / constants):
  - **/verify/**, **/formal_verification.rs
  - constants files

When ranking:
- If a file straddles two tiers, pick the higher.
- Files with heavy `unwrap_or_else` / silent-default patterns belong one
  tier higher than the rubric suggests.
- Fusion bugs that produce invalid output WASM affect every downstream
  consumer (kiln, wasmtime, browsers). That amplification elevates parser
  and writer tiers.
- Do not guess rank 5 from path alone — open the file.
- Files you haven't seen default to rank 2.
