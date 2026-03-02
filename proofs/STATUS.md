# Proof Coverage Status

Implementation vs formal verification coverage for the Meld fusion pipeline.

## Numbers at a Glance

| Metric | Count |
|--------|-------|
| Rocq `.v` files | 23 |
| Rocq lines (total) | 13,330 |
| Closed proofs (Qed) | 286 |
| Admitted proofs | 0 |
| Rust lines (`meld-core/src`) | 8,218 |
| Proof-to-code ratio | 1.62x |

## Pipeline Coverage Matrix

| Stage | Rust source | Rust lines | Proof files | Proof lines | Status | What's proved |
|-------|-------------|------------|-------------|-------------|--------|---------------|
| Parser | `parser.rs` | 974 | `parser/parser.v` | 7 | Placeholder | — |
| Resolver | `resolver.rs` | 546 | `resolver/resolver.v`, `resolve/resolve_spec.v` | 1,447 | Covered | Topo sort correctness, dependency resolution soundness, adapter site identification |
| Merger | `merger.rs` | 2,189 | `merge/*.v` (6 files), `rust_verified/merger_core_proofs.v` | 4,364 | Covered | Index remap injectivity/completeness/boundedness, memory layout disjointness, type/func/table/mem/global/elem/data merge correctness, import resolution refinement |
| Rewriter | `rewriter.rs` | 979 | `rewriter/rewriter.v` | 7 | Placeholder | — |
| Adapters | `adapter/*.rs` | 1,638 | `adapter/adapter.v`, `adapter/adapter_spec.v` | 806 | Covered | Canonical ABI specification, string encoding, adapter type correctness, crossing adapter semantics preservation, lift/lower roundtrip |
| Segments | `segments.rs` | 624 | `segments/segments.v` | 25 | Placeholder | Offset map injectivity only |
| Orchestration | `lib.rs` | 773 | — | — | None | — |
| Attestation | `attestation.rs` | 411 | `attestation/attestation.v` | 7 | Placeholder | — |
| **Spec layer** | — | — | `spec/*.v` (6 files) | 4,392 | Covered | Wasm core types, component model, fusion types, instruction semantics, forward simulation (fully proved), trap simulation (forward direction) |

Proof file paths are relative to `proofs/` (e.g. `merge/*.v` means `proofs/transformations/merge/*.v`).

## What the Proofs Establish

### Merge transformation

The merge proofs (`merge_remap.v`, `merge_correctness.v`, `merge_layout.v`, `merge_bridge.v`, `merge_defs.v`) establish that index remapping is complete, injective, and bounded for all six Wasm index spaces (functions, tables, memories, globals, element segments, data segments). Space counts are preserved through merging. Memory layout is sequential and disjoint across components. Import resolution is proved as a refinement of flat import concatenation, bridged in `merge_resolution.v`.

### Resolver

The resolver proofs (`resolve_spec.v`, `resolver.v`) prove that topological sort produces a valid processing order, dependency resolution is sound and complete, and cycle detection terminates. Adapter call sites are correctly identified at component boundaries.

### Specification layer

The spec files (`fusion_spec.v`, `fusion_types.v`, `wasm_semantics.v`, `wasm_core.v`, `wasm_core_generated.v`, `component_model.v`) define a forward simulation relation between composed and fused execution. Instruction-level correspondence is established for index-sensitive operations: `call`, `global.get`/`global.set`, `table.get`/`table.set`, `memory.load`/`memory.store`, `elem.drop`, and `data.drop`. Twenty-one rewrite rules are specified in `fusion_types.v` and connected to implementation-level index maps via bridge lemmas in `merge_bridge.v`.

### Rust-verified (rocq-of-rust)

Offset computation monotonicity and summation correctness are proved over Rust code translated to Rocq via `rocq-of-rust`. Memory layout disjointness follows from these properties. Coverage is limited to `compute_offsets` and `compute_memory_layout`.

## Proof Completion

All theorems are fully proved (Qed) with zero Admitted proofs. Key resolutions:

### `lift_lower_roundtrip_primitive` — `adapter_spec.v`

Resolved by replacing axiomatized `Parameter lower_value` and `Parameter lift_values` with concrete `Definition`s that handle all 20 component value types. Compound types return `None` (making the roundtrip implication vacuously true), while primitive types (bool, integers, floats, char, handles) have explicit encoding/decoding with verified roundtrip via case analysis and `Nat2Z.id`.

### `fusion_trap_simulation` — `fusion_spec.v`

The unprovable backward direction of trap equivalence was dropped. The theorem was weakened to forward-only `trap_simulation` (composed traps → fused traps). The SharedMemory forward case was closed by strengthening `memory_corresponds` to include data-length equality.

### `fusion_forward_simulation` — `fusion_spec.v`

Fully proved for both CS_Instr and CS_CrossModuleCall cases:
- **CS_CrossModuleCall**: Constrained `ms_src'` to `set_stack ms_src new_src_stack` (preserving all index spaces) and added `ms_locals ms_tgt = ms_locals ms_src` hypothesis. Full 3-way case split proof for state correspondence.
- **CS_Instr surjectivity** (`sc_memory_surj`, `sc_table_surj`): Proved via `eval_instr_mems_length`/`eval_instr_tables_length` (list length preservation), old surjectivity recovery, and case split on source = active module using remap injectivity and frame conditions.

## Known Model Gaps

- The proof model uses flat import concatenation; the Rust implementation resolves imports with priority ordering. `merge_resolution.v` bridges these but the connection is not end-to-end through the full pipeline.

- `rocq-of-rust` translation covers `compute_offsets` and `compute_memory_layout` only. The larger merger functions (`merge_functions`, `build_index_maps_for_module`) are not yet translated.

- Instruction rewriting (`rewriter.rs`, 979 lines) has specification-level support in `fusion_types.v` (21 rewrite rules defined) and bridge lemmas in `merge_bridge.v`, but no direct implementation proof.

- Adapter generation (1,497 lines of Rust in `fact.rs`) has spec-level coverage but no connection to the FACT implementation.

- Parser (`parser.rs`, 974 lines) and attestation (`attestation.rs`, 411 lines) have placeholder proof files only.

## Next Targets

- Expand `rocq-of-rust` coverage to import resolution logic.
- Connect adapter spec to FACT implementation.
- Add rewriter implementation proofs linking `fusion_types.v` rewrite rules to `rewriter.rs`.
- Add parser and attestation proofs (currently placeholders).
- Add Kani bounded model checking harnesses for the merger.
