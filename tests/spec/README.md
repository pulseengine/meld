# Specification Test Inputs

This directory exposes upstream specification test suites and WIT definitions
as Bazel filegroups, so they can be consumed by meld's tests and proofs.

## Available targets

- `//tests/spec:wasm_core_tests` - WebAssembly Core Spec tests (Release 3.0)
- `//tests/spec:wasm_proposals_tests` - Proposal tests (optional)
- `//tests/spec:component_model_tests` - Component Model tests
- `//tests/spec:component_model_wit` - WIT files from component-model repo
- `//tests/spec:wasi_wit` - WASI 0.2.x WIT definitions

See `proofs/DECISIONS.md` for the exact pinned commits and tags.
