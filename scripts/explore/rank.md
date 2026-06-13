Rank candidate design paths for the parent question in
`safety/adr/{{adr-id}}.md` by likelihood that a small prototype would
satisfy the oracle (typically: a `fuse_only_test!` flips to a passing
`runtime_test!`).

Output JSON:
`[{"path": "...", "viability": N, "locus": "...", "reason": "..."}]`,
sorted by viability descending then by locus ergonomics (meld first).

## Two-axis rubric

### Axis 1 — viability (1–5)

5 (you can sketch the prototype in 100 lines, no new infrastructure):
  - Mechanism is well-understood; nothing in the code base prevents it
  - Existing helpers cover the primitives (e.g., handle table, shim
    generator, byte-scan tests)
  - Failure modes are obvious and testable

4 (prototype is medium-effort but well-scoped):
  - One new abstraction needed; one or two new helpers
  - Some risk of surfacing a deeper invariant the prototype must respect

3 (real research; prototype is feasible but no one has built one
   before in this repo):
  - Path requires a feasibility report before code, OR
  - Borrows heavily from external tooling (wit-component, wasm-tools)
    we haven't integrated

2 (path needs upstream change to even be built locally):
  - Requires a fork of an external dep + a meld branch consuming the
    fork
  - The prototype isn't testable without the upstream side landing

1 (speculative, no concrete prototype possible today):
  - Spec change required; current tooling doesn't support the pattern

### Axis 2 — locus-of-fix (categorical)

`meld` — the fix is entirely within meld
`wit-bindgen` — the fix belongs in wit-bindgen's resource lowering
                convention; meld can consume the new pattern
`spec` — the fix belongs in the component-model spec
`wasm-tools` — the fix belongs in wasm-tools (validator, encoder, …)
`hybrid` — meld must do part; an upstream change makes the other part
           correct

A path with `locus = wit-bindgen` and viability ≥ 4 should NOT be
discounted just because the upstream change is hard. The honest
verdict in many cases is "the right fix is upstream; meld should
participate in the spec/impl conversation while shipping a workaround."

## Constraints

- Open the parent ADR first (`safety/adr/{{adr-id}}.md`) and the
  fixtures it references. Do not rank from imagination.
- For each candidate path, write at most one sentence in `reason` —
  the ranker is not the prototype agent and should not propose
  solutions, only judge how viable each is.
- Approaches you haven't seen built (no PR / branch / discussion of
  the same approach in this or upstream repos) default to viability 3.
  Do not guess viability 5 from memorability or apparent simplicity.
- The straddle rule: if a path sits between two viability tiers, pick
  the LOWER (be skeptical of yourself).
- Locus-of-fix is binary per path — pick the one that best matches
  where the change PROPERLY belongs, not where it's easiest for us.

## Output

A JSON array sorted by viability descending. Example shape:

```json
[
  {"path": "D-mini-shim",
   "viability": 4,
   "locus": "meld",
   "reason": "Trivial wrapper struct is one i32; existing handle table infra covers most of it."},
  {"path": "I-wit-bindgen-opaque-rep",
   "viability": 3,
   "locus": "wit-bindgen",
   "reason": "Opt-in attribute pattern; downstream consumer needs only a flag, but prototype requires fork."},
  ...
]
```

Return only the JSON. No prose.
