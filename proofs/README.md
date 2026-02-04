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

## Build

Bazel targets are defined in `proofs/BUILD.bazel`.

Build proofs: `bazel build //proofs:all_proofs`
Run a specific proof test (manual tag): `bazel test //proofs:parser_proofs_test`

Note: proof builds require Nix for the Rocq toolchain.
