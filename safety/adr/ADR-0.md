---
id: ADR-0
type: design-question
title: Static fusion of re-exporter resource chains
status: open
gating-fixtures:
  - resource_floats
  - resource_with_lists
  - resource-import-and-export
design-paths:
  - D — Mini-shim for trivial wit-bindgen wrapper structs (meld-only)
  - E — Elide trivial pass-through re-exporters (research)
  - F — Layout inference from compiled re-exporter code (research)
  - G — FACT-style trampoline as inner core module (meld-only, larger)
  - H — Outsource the re-exporter boundary to wit-component (heavy dep)
  - I — pulseengine/wit-bindgen opaque-rep pattern (upstream + downstream)
  - J — Hybrid output: emit re-exporter as a sub-instance the host wires
---

# ADR-0 — Static fusion of re-exporter resource chains

## Context

Three wit-bindgen test fixtures (`resource_floats`, `resource_with_lists`,
`resource-import-and-export`) fuse successfully through `meld fuse`
but trap at runtime with a `wasm unreachable instruction executed`
error. They are currently marked as `fuse_only_test!` in
`meld-core/tests/wit_bindgen_runtime.rs` (epic #69 / issue #92).

All three are 3-component re-exporter chains: `A` (caller) → `C`
(re-exporter) → `B` (implementor). The re-exporter `C` is a
wit-bindgen-generated component that wraps an inner type from `B`
in a Rust struct (e.g., `pub struct FloatRep { inner: Float }`),
boxes it, and uses the box pointer as the resource representation.

## Why the runtime trap

Per the investigation memo and the upstream rust-compiler trap on
`& 7`: the re-exporter's user code dereferences the rep pointer it
gets back from `_resource_rep(handle)` and the rust compiler's
debug-mode `assume(ptr.is_aligned())` materializes as a wasm
unreachable when the rep value is not 8-byte aligned (or not in
the right memory).

Meld's existing per-component handle table (commit `30cf088`,
infrastructure on `feat/per-component-handle-tables`) stores whatever
rep value is passed to `[resource-new]`. In a re-exporter chain
that's the CALLER's rep — a pointer in `A`'s memory — but the
re-exporter's user code expects to dereference it as a pointer
in `C`'s memory, to a struct laid out per `C`'s compiler. Both
the address space and the alignment can be wrong.

In other words: the meld-side handle table is correct as a
container, but the **value stored in it is the wrong thing**.
The right value would be a pointer to a properly-constructed
wrapper struct in `C`'s memory — and constructing that wrapper
requires either calling `C`'s own internal helpers (not exposed
as canon imports) or duplicating the layout knowledge in meld.

## Why this needs an ADR

There are at least seven plausible paths. Some are entirely within
meld; some require an upstream change to wit-bindgen; some require
ecosystem-level coordination. The right choice depends on:

1. How many real-world (non-fixture) components exhibit this pattern
2. Whether wit-bindgen will accept an opt-in opaque-rep convention
3. How willing we are to take on `wit-component` as a dependency
4. How much of the work is actually `meld`'s vs. someone else's

This ADR enumerates the design space. Sibling ADRs (`ADR-1` …) under
this parent will document each path's prototype, validation result,
and verdict. The synthesis pass (one final agent reading all
siblings) recommends one as `accepted`; others move to `rejected`
or `superseded`.

## Design space (not the verdict — see siblings)

### D — Mini-shim for trivial wrapper structs

Detect re-exporter resources whose wrapping struct is trivial
(`{ inner: Handle }` with no extra fields). For those, emit a small
function that calls `C`'s `cabi_realloc(0, 0, 4, 4)`, stores the
inner handle, returns the new pointer. Routes `[resource-new]` to
that function. Reuses existing handle-table infrastructure.

Locus: `meld`. Viability ≈ 4. Generalization: medium (covers test
fixtures; fragile for real components with non-trivial wrappers).

### E — Elide trivial pass-through re-exporters

Detect that `C` is a pure WIT-mediation layer and route `A → B`
directly, skipping `C` entirely. Saves output size as a bonus.
Requires "is C trivial?" detection — surprisingly tractable for
wit-bindgen output but fragile against any user-added code.

Locus: `meld`. Viability ≈ 3 (research-y). Risk: brittle detection.

### F — Layout inference from compiled C

Statically analyze `C`'s `[resource-new]` callers to discover the
wrapper struct's layout and field initializations. Use that knowledge
to construct the struct from the adapter side.

Locus: `meld`. Viability ≈ 2 (high effort; reverse-engineering Rust
struct layouts from wasm is brittle).

### G — FACT-style trampoline as inner core module

What wasmtime's FACT does at runtime, done at fuse-time: emit a
separate adapter module that imports `C`'s exports and exports the
canonical interface. The merged P2 wrapper instantiates it as a
sibling core module. Architecturally converges meld with wasmtime's
adapter generation.

Locus: `meld` (with potential future convergence on the
`canonical-abi-emit` crate proposed in
`docs/wasmtime-fact-reusability.md`). Viability ≈ 3.

### H — Outsource to wit-component

`wit-component` is the reference implementation of component
composition. Have meld delegate the re-exporter boundary to
wit-component's logic. Heavy dependency.

Locus: `hybrid` (meld + wit-component). Viability: needs
feasibility report.

### I — pulseengine/wit-bindgen opaque-rep pattern

The rep-as-pointer convention is wit-bindgen's choice, not the
spec's. Add an opt-in `#[wit_bindgen::resource(opaque_rep)]`
attribute that treats the rep as opaque (never dereferenced; just
round-tripped). Components that opt in are statically fusable.
Implementation in `pulseengine/wit-bindgen` (our fork); meld branch
consumes the new pattern; draft RFC for upstream.

Locus: `wit-bindgen`. Viability ≈ 3 (multi-step but each step is
small). Strongest long-term fix.

### J — Hybrid output: re-exporter as sub-instance

Acknowledge meld can't fully fuse re-exporter chains; emit them as
separate component instances inside the output, requiring the host
to do trivial resource-handle translation (which existing wasmtime
/ jco hosts already do).

Locus: `meld`. Viability ≈ 4 (small implementation). Trade-off:
output is no longer a single core module for these cases.

## Pipeline

This ADR is the parent for an `explore` pipeline run (see
`scripts/explore/HOWTO.md`):

1. `rank.md` produces a JSON ranking of the seven paths.
2. For each path with viability ≥ 3: `prototype.md` agent in parallel.
3. For each prototype: `validate.md` fresh agent.
4. For each confirmed: `emit.md` produces `safety/adr/ADR-N.md` as a
   sibling to this parent.
5. Synthesis: one agent reads all siblings, recommends one as
   `accepted`.

## References

- Issue #92 (3-component re-exporter resource chains: implement shim
  module approach)
- Epic #69 (per-component resource handle tables for 3-component chains)
- `feat/per-component-handle-tables` branch (initial infrastructure)
- `docs/wasmtime-fact-reusability.md` (related: shareable canonical-ABI
  emission core)
- `docs/superpowers/plans/2026-03-29-per-component-handle-tables.md`
  (original per-component-handle-table plan, partially landed in main)
