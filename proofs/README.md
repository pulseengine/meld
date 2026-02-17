# Meld Proofs

This directory contains formal proofs for meld. Proofs are kept separate from
source code, but the layout mirrors `meld-core/src` so each proof area maps to a
specific implementation module.

See `proofs/DECISIONS.md` for the specification baselines and other proof
infrastructure decisions.

## Layout

| Proofs path | Source path | Focus |
| --- | --- | --- |
| `proofs/parser/` | `meld-core/src/parser.rs` | Parsing and decoding correctness |
| `proofs/resolver/` | `meld-core/src/resolver.rs` | Import/export graph resolution |
| `proofs/merger/` | `meld-core/src/merger.rs` | Index-space merging and type preservation |
| `proofs/adapter/` | `meld-core/src/adapter/` | Canonical ABI adapter generation |
| `proofs/rewriter/` | `meld-core/src/rewriter.rs` | Rewrite passes and invariants |
| `proofs/segments/` | `meld-core/src/segments.rs` | Segment layout and bounds |
| `proofs/attestation/` | `meld-core/src/attestation.rs` | Attestation integrity invariants |
| `proofs/rust_verified/` | (special) | Rust-to-Rocq translated proofs |
| `proofs/spec/` | (specifications) | Core spec definitions and fusion semantics |
| `proofs/transformations/` | (specs for transforms) | Transform correctness specs |

## Memory Strategy in Proofs

The proof model supports both memory strategies via `memory_strategy` in
`fusion_types.v`:

- **`SeparateMemory`**: Each component's memory indices are remapped via
  `gen_remaps_for_space` (normal offsetting). Memory instructions carry a
  `memidx` parameter. State correspondence uses `lookup_remap` for `MemIdx`,
  the same as `FuncIdx`/`GlobalIdx`/`TableIdx`. Memory index remapping is
  injective — each component's memory maps to a distinct fused index.

- **`SharedMemory`**: All memory indices remap to 0 via
  `gen_remaps_for_space_zero`. State correspondence uses
  `memory_corresponds` with a `memory_layout` that maps each component's
  address range into a region of the single shared memory.

## Build

Bazel targets are defined in `proofs/BUILD.bazel`.

Build proofs: `bazel build //proofs:all_proofs`
Run a specific proof test (manual tag): `bazel test //proofs:parser_proofs_test`

Note: proof builds require Nix for the Rocq toolchain.
