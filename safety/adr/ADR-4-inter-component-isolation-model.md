---
id: ADR-4
type: design-question
title: Inter-component memory-isolation model for the dissolved library-OS
status: resolved
gating-fixtures:
  - multi_memory::test_multi_memory_separate_memories
  - multi_memory::test_multi_memory_preserves_isolation
  - multi_memory::test_multi_memory_preserves_isolation_three_components
  - multi_memory::test_multi_memory_result_copy_adapter
design-paths:
  - model-1 — Single shared memory + embedder MPU-carve (rejected as the committed path; retained as a secondary mode)
  - model-2 — Multi-memory; one preserved wasm memory per component = one MPU/PMP region (chosen)
---

# ADR-4 — Inter-component memory-isolation model for the dissolved library-OS

## Context

The cross-repo dissolved-library-OS work (gale#86, gale#404, synth#404,
synth#369, meld#298, meld#299) must choose how fused components are
isolated from one another on the MCU target (Cortex-M / PMP-class). The
fusion-structure half of that choice is meld's, and gale#86's isolation
design forks on it, so meld#300 raised it for an explicit decision.

Two models were on the table (meld#300):

1. **Single shared memory + MPU-carve.** `meld fuse --memory shared`
   produces one linear memory; the embedder / TCB carves MPU
   sub-regions per component by hand. Isolation is *configured*: a
   miscomputed address lands in a neighbour's sub-range and only a
   correct MPU programming catches it. This is what meld#298 / meld#299
   were actively enabling (drop the vestigial canonical-ABI allocator so
   `--memory shared` becomes viable; the lean ~544 B-class core).

2. **Multi-memory → one native region per wasm memory.** meld preserves
   each component's memory as a distinct linear memory; synth places each
   at a distinct native base so the MPU/PMP region boundary *is* the
   semantic boundary. Isolation is *structural*: a component cannot even
   form a pointer into a neighbour's memory — the wasm memory index is
   the capability.

synth (synth#404) lowers whichever structure meld emits and will not be
the blocker for model 2; it scoped the lowering work as: carry `memidx`
through the IR instead of dropping it, place each wasm memory at a
distinct native base, lower cross-memory ops explicitly (synth#369), and
expose per-memory base/size so the embedder programs one MPU/PMP region
per memory. synth is single-memory today, so model 1 is what is
lowerable *now*; model 2 is forward-looking on the synth side.

The MPU/PMP region cap (~8 on ARMv7-M, PMP similar) bounds the component
count N under *either* model, so it is not a differentiator.

## Decision

**model-2 — multi-memory structural isolation is the committed
dissolved-MCU path.** Isolation coincides with the semantic boundary by
construction; this is the stronger story for the ASIL-D context gale
targets (defence-by-construction, not defence-by-correct-MPU-config).
Recorded in meld#300 (the maintainer's call resolves this design
question).

meld is **already on this side of the fork** and is not the blocker.
`MemoryStrategy::MultiMemory` preserves each component's memory as a
distinct region and emits the explicit cross-memory data movement that
fusion across distinct memories requires — verified today by the gating
fixtures:

- `test_multi_memory_separate_memories` — a two-module component fuses to
  **two** memories, one per original core module.
- `test_multi_memory_preserves_isolation` — two separate components fuse
  to **two distinct** memories, both exports callable.
- `test_multi_memory_preserves_isolation_three_components` — the
  invariant **scales** to the realistic dissolved-OS shape (≥3
  components, e.g. relay + kernel + app): three distinct memories survive
  with no collapse/merge of address spaces.
- `test_multi_memory_result_copy_adapter` — cross-memory `(ptr, len)`
  result data is copied callee→caller correctly.

So the meld half of model 2 — emit N distinct memories + correct
cross-memory ops, no rebasing/merging, per-memory sizes carried in the
fused memory section — exists and is tested. The committed path's
remaining work is **synth-side** (synth#369 cross-memory op lowering,
synth#404 carry `memidx` + distinct native bases + per-memory base/size
for MPU). meld keeps `MultiMemory` output stable as the lowering target
and adjusts only if synth hits a structure it cannot consume.

### Why not model-1 (kept as a secondary mode)

model 1 is lean and lowerable on synth *today*, but its isolation is
only as good as the embedder's MPU-carve — a miscomputed address is
caught by hardware config rather than being unrepresentable. For the
committed safety-critical path, structural isolation wins. model 1 is
**retained as a secondary, optional mode** for targets that accept
embedder-MPU-carve isolation in exchange for the smallest core.

### Status of the secondary `--memory shared` path

meld#298 / meld#299 are **reclassified secondary** (commented on both).
The work already landed on branch `fix/298-dead-allocator-dce` is sound
and stays for that secondary mode:

- in-repo kill-criterion + real-artifact blocker oracles
  (`merger::tests::test_298_vestigial_grow_blocks_shared_rebase_fusion`,
  `rebasing_end_to_end::test_298_real_wit_bindgen_component_blocks_shared_rebase`);
- proven compatibility with the fork's arena-backed no-grow
  `cabi_realloc`
  (`merger::tests::test_298_fork_arena_realloc_fuses_under_shared_rebase_today`);
- the inert fail-safe vestigial-allocator verdict
  (`Fuser::cabi_realloc_drop_provably_safe`, 4 gate oracles) and the
  inert tolerant-rewriter flag (`IndexMaps::defer_grow_under_rebase`).

The **corruption-critical drop wiring is paused** — it is no longer on
the priority path. Resume only if a specific target needs the secondary
shared mode.

## Open knob (not settled by this ADR)

The `Auto` strategy (#172) currently prefers `SharedMemory` + rebasing
when provably sound, else `MultiMemory`. With model 1 now *secondary*,
whether `Auto` should keep that bias or whether structural-isolation
targets should explicitly select `--memory multi` is a separate policy
decision, still open.

## Rivet artifacts

The committed model-2 path relies on the existing multi-memory
correctness requirements rather than a new one: SR-9/SR-10 (memory and
data/element index reindexing), SR-12 (multi-memory adapter generation
for pointer-bearing types), SR-14 (correct source/destination memory
indices in adapters), SR-16 (inner-pointer rewrite into the destination
memory), SR-21/SR-23 (correct per-memory `canon lower` indices and
import slots in multi-memory mode). These collectively pin "distinct
memories preserved + cross-memory ops correct," which is exactly the
structural-isolation guarantee.

## References

- meld#300 (the decision), meld#298, meld#299 (now secondary).
- gale#86, gale#404 (isolation design that forked on this).
- synth#404, synth#369 (the lowering work this commits synth to).
