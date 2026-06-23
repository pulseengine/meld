---
title: MultiMemory lowering contract (meld → synth)
status: stable
audience: synth (loom/synth backend), gale (BYO-OS embedder/TCB)
tracks: meld#300, synth#404, synth#369, gale#86
---

# MultiMemory lowering contract

This is the **stable lowering target** for the committed dissolved-library-OS
isolation model — *model 2, multi-memory structural isolation* (meld#300 /
ADR-4). It is the artifact synth builds its differential oracle and frozen
fixtures against: meld guarantees the output shape described here, and any
change to it is a contract change (announced on meld#300, not silent).

> **Scope.** This describes what `meld fuse --memory multi` (and the `auto`
> resolution to multi) emits *structurally*. Native base assignment and MPU/PMP
> region programming are synth's / the embedder's; meld emits the structure,
> never an address map.

Everything below is grounded in code + tests, cited so synth can pin to it.

## C1 — N memories preserved 1:1, no collapse

Under `MemoryStrategy::MultiMemory` each input component/core module keeps its
own linear memory in the fused module; meld never merges or rebases them.

- `meld-core/tests/multi_memory.rs::test_multi_memory_separate_memories` — 2
  core modules → **exactly 2 memories** out.
- `…::test_multi_memory_preserves_isolation` — 2 components → 2 memories.
- `…::test_multi_memory_preserves_isolation_three_components` — N=3 → **exactly
  3 distinct memories**, no collapse, every export callable.

The memory boundary therefore *is* the protection boundary: a component cannot
form a pointer into a neighbour (distinct memidx), as opposed to model 1 where a
miscomputed address lands in a neighbour's sub-range and only the MPU catches it.

## C2 — Deterministic per-memory → component identity (export naming)

This is the relation an embedder uses to map each memory to an MPU/PMP region.

- Component 0's exports keep their bare names (`memory`, `cabi_realloc`, …).
- A name that **collides** with an already-emitted export is suffixed with the
  owning component index: `format!("{}${}", name, comp_idx)` —
  `merger.rs:1992`. So component *k*'s colliding `memory` export becomes
  `memory$k`, its `cabi_realloc` becomes `cabi_realloc$k`, etc.
- The suffix is the component index, stable across runs for a fixed input order.

`meld fuse` input order is the identity order: component *k* on the CLI owns
memory exported as `memory` (k=0) or `memory$k` (k≥1 when it collides).

## C3 — Authoritative index relation

The internal source of truth mapping `(component, module, original-memidx)` to
the fused memory index is `MergedComponent.memory_index_map: HashMap<(usize,
usize, u32), u32>` (`merger.rs:95`), with helper
`component_memory_index(merged, comp_idx)` (`lib.rs:1333`, `merger.rs:2363`).
C2's export naming is the externally-observable projection of this map; synth
does not need the map itself, only the named exports.

## C4 — Cross-memory ops are emitted explicitly with distinct memidx

meld **carries the memory index** on every cross-memory transfer — it never
drops it or assumes memory 0. This is the op shape synth#369 must lower instead
of loud-skipping.

- **General reindexing:** the rewriter remaps both `dst_mem` and `src_mem` of an
  input `memory.copy` through the merge — `rewriter.rs:423`, and
  `rewriter.rs:1224` asserts `src_mem 1→8`, `dst_mem 0→2` (distinct, remapped).
- **Async stream bridge:** `emit_read_shim`/`emit_write_shim` copy between
  `bridge_mem` and `caller_mem` (distinct memidx) — `p3_bridge.rs:639/655/741/
  757`. Same-memory fusion is the identical codegen with caller-memory immediate
  0 (`p3_bridge.rs:25`).
- **Sync result copy:** the returned `(ptr,len)` is copied from callee memory to
  caller memory; exercised by
  `multi_memory.rs::test_multi_memory_result_copy_adapter` (`run()` → 66 proves
  the cross-memory move happened).

The set synth must consume for model 2: `memory.copy` and `memory.fill` with an
explicit `memory_index` ≠ 0 (the synth#369 / bulk-memory class), plus loads/
stores carrying a non-zero `memory_index` in their `MemArg`.

## C5 — Per-memory size in the memory section; base is synth's

Each preserved memory's `min`/`max` pages ride in the fused module's memory
section verbatim (`MemoryType.minimum/maximum`). meld assigns **no** native
base; synth places `memory[k]` at a distinct native base and exposes base/size
so the embedder programs one MPU/PMP region per memory. (Region cap ~8 on
ARMv7-M / PMP bounds practical N either way — not a model differentiator.)

## C6 — MultiMemory + address-rebase is a hard error

`--memory multi` with `--address-rebase` returns
`Error::MemoryStrategyUnsupported` (`lib.rs:2913` pins it). Rebasing is the
shared-memory *collapse* path and is mutually exclusive with structural
isolation. synth never receives a rebased multi-memory module.

## Consuming this as a frozen fixture

`meld fuse --memory multi <components…> -o fused.wasm` is deterministic for a
fixed input set + order. The wasm is multi-memory, so downstream validators need
`--enable-multimemory` (meld#172) — that is expected for model 2 and is not a
defect. synth consumes the fused core module via loom, not via `wasm-opt`; the
`wasm-opt` rejection in meld#172 only applies to the optional optimise step and
is why `--memory shared` remains the documented *secondary* single-domain path.

## Change policy

This shape is frozen as the model-2 lowering target. A change to C1–C6 is a
contract change announced on meld#300 with a synth heads-up; synth files against
meld if it hits a MultiMemory structure it cannot consume (per synth#404).
