# Proof Decisions and Spec Baselines

Last updated: 2026-02-04

This file records the normative baselines and structural decisions that guide
proofs and specification-based tests for meld.

## Specification baselines

- Core spec baseline: WebAssembly Core Specification, Release 3.0 (released
  2025-09-17).
- Component Model baseline: WebAssembly Component Model specification pinned to
  commit `deb0b0a` (2025-05-19).
- WIT/WASI baseline: WASI v0.2.3 WIT definitions (2024-12-17).

## Test-suite baselines

- Core spec tests: `wasm-3.0` branch, commit
  `9aa45e862ad616a1d93a115fe3ffd6c7cc2f7c2e`.
- Component Model tests: same commit as the Component Model baseline
  (`deb0b0a`).
- WASI WIT definitions: same tag as the WASI baseline (`v0.2.3`).
- wit-bindgen e2e tests: `v0.52.0` tag - composed runtime test components.

These are exposed via Bazel filegroups under `//tests/spec:*`.

## Memory strategy

- The default memory strategy is `MultiMemory` (`SeparateMemory` in proofs).
  Each component keeps its own linear memory in the fused module.
- Multi-memory relies on WebAssembly Core Specification 3.0 (the same spec
  baseline used for all other features).
- `SharedMemory` is retained as a legacy option but is known to be broken
  when any component uses `memory.grow`.

## Proof organization

- Proofs live under `proofs/` and mirror `meld-core/src`.
- Each proof directory targets semantic preservation or safety invariants for
  its matching module.
- Rust-to-Rocq translation proofs live under `proofs/rust_verified`.

## Tooling decisions

- Proofs use `rules_rocq_rust` for Rocq/Coq builds.
- The Rocq toolchain is managed via Nix and is required to build proofs.
- Proof tests are tagged `manual` to avoid running in default `bazel test //...`.
