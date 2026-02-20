<div align="center">

# Meld

<sup>Static WebAssembly component fusion</sup>

&nbsp;

![Rust](https://img.shields.io/badge/Rust-CE422B?style=flat-square&logo=rust&logoColor=white&labelColor=1a1b27)
![WebAssembly](https://img.shields.io/badge/WebAssembly-654FF0?style=flat-square&logo=webassembly&logoColor=white&labelColor=1a1b27)
![Component Model](https://img.shields.io/badge/Component_Model-654FF0?style=flat-square&logoColor=white&labelColor=1a1b27)
![Formally Verified](https://img.shields.io/badge/Formally_Verified-00C853?style=flat-square&logoColor=white&labelColor=1a1b27)
![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue?style=flat-square&labelColor=1a1b27)

&nbsp;

<h6>
  <a href="https://github.com/pulseengine/meld">Meld</a>
  &middot;
  <a href="https://github.com/pulseengine/loom">Loom</a>
  &middot;
  <a href="https://github.com/pulseengine/synth">Synth</a>
  &middot;
  <a href="https://github.com/pulseengine/kiln">Kiln</a>
  &middot;
  <a href="https://github.com/pulseengine/sigil">Sigil</a>
</h6>

</div>

&nbsp;

Meld fuses. Loom weaves. Synth transpiles. Kiln fires. Sigil seals.

Meld statically fuses multiple WebAssembly P2/P3 components into a single core module, eliminating the need for runtime linking. Import resolution, index-space merging, and canonical ABI adapter generation happen at build time. Every transformation carries mechanized proofs covering parsing, resolution, merging, and adapter correctness.

Unlike composition tools that produce linked-but-separate component graphs, Meld produces a single monolithic module suitable for whole-program optimization by Loom and native transpilation by Synth.

## Quick Start

```bash
# From source (Cargo)
cargo install --path meld-cli

# From source (Bazel)
bazel build //meld-cli:meld

# Fuse two components
meld fuse component_a.wasm component_b.wasm -o fused.wasm
```

### Full Pipeline

```bash
# 1. Build components
cargo component build --release

# 2. Fuse into single module
meld fuse composed.wasm -o fused.wasm

# 3. Optimize with Loom
loom optimize fused.wasm -o optimized.wasm

# 4. Run
wasmtime run optimized.wasm
```

### Bazel Integration

```starlark
load("@meld//rules:meld.bzl", "meld_fuse")

meld_fuse(
    name = "my_app",
    components = [
        ":component_a",
        ":component_b",
    ],
)
```

## How It Works

1. **Parse** — Extract core modules and type information from components
2. **Resolve** — Build import/export graph, identify cross-component calls
3. **Merge** — Combine function/memory/table/global index spaces
4. **Adapt** — Generate Canonical ABI trampolines for cross-component calls
5. **Encode** — Output single core WebAssembly module

### Adapter Generation

Cross-component calls may require adapters that handle string transcoding (UTF-8, UTF-16, Latin-1), memory copying between component memories, list/array serialization, and resource handle transfer. Meld generates these adapters using techniques inspired by Wasmtime's FACT (Fused Adapter Compiler of Trampolines).

## Memory Strategies

### Multi-Memory (Default)

Each component retains its own linear memory. Cross-component calls use adapters that allocate in the callee's memory via `cabi_realloc` and copy data with `memory.copy`. Requires multi-memory support (WebAssembly Core Spec 3.0).

```bash
meld fuse a.wasm b.wasm -o fused.wasm
```

### Shared Memory (Legacy)

All components share a single linear memory. Simpler but one component's `memory.grow` corrupts every other component's address space.

```bash
meld fuse --memory shared a.wasm b.wasm -o fused.wasm
```

## Supply Chain Security

Meld integrates with [Sigil](https://github.com/pulseengine/sigil) for supply chain attestation. Each fusion operation records input component hashes, tool version and configuration, and transformation metadata. The attestation is embedded in the output module's custom section.

## Formal Verification

Meld's core transformations are formally verified using Rocq 9.0 (formerly Coq). The proofs establish that fusion preserves program semantics — the fused module behaves identically to the original composed components.

Key verified properties:
- **Merge correctness** — Index remapping preserves function/memory/table references
- **Resolve correctness** — Topological sort produces valid instantiation order; cycle detection terminates
- **Adapter correctness** — Generated trampolines preserve call semantics
- **Forward simulation** — Fused module simulates the original component graph step-by-step

Proofs are built via Bazel using [`rules_rocq_rust`](https://github.com/pulseengine/rules_rocq_rust):

```bash
bazel build //proofs/transformations/merge:merge_spec
bazel build //proofs/spec:fusion_spec
```

See [`proofs/`](proofs/) for the full proof tree and [`PROOF_GUIDE.md`](proofs/PROOF_GUIDE.md) for an introduction.

> [!NOTE]
> **Cross-cutting verification** &mdash; Rocq mechanized proofs, Kani bounded model checking, Z3 SMT verification, and Verus Rust verification are used across the PulseEngine toolchain. Sigil attestation chains bind it all together.

## Limitations

- **Resources** — Resource handle transfer across components is limited
- **Async** — Async component functions not yet supported
- **String transcoding** — UTF-8/UTF-16 and Latin-1/UTF-8 are implemented; UTF-8/Latin-1 is not yet supported

## Development

```bash
cargo build                # Build
cargo test                 # Test
bazel build //...          # Bazel build
RUST_LOG=debug cargo run -- fuse a.wasm b.wasm -o out.wasm
```

## License

Apache-2.0

---

<div align="center">

<sub>Part of <a href="https://github.com/pulseengine">PulseEngine</a> &mdash; formally verified WebAssembly toolchain for safety-critical systems</sub>

</div>
