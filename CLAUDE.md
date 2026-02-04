# Meld - Static Component Fusion

## Project Overview

Meld is a static component fusion tool for WebAssembly. It takes composed P2/P3
components and fuses them into a single core wasm module, eliminating the need
for runtime linking.

Part of the **pulseengine toolchain**:
- **loom** - WebAssembly optimizer (formally verified)
- **meld** - Static component fuser (this tool)

## Build Commands

### Cargo (Development)

```bash
# Build all crates
cargo build

# Build release
cargo build --release

# Run tests
cargo test

# Run specific test
cargo test --package meld-core test_name

# Run CLI
cargo run --bin meld -- fuse input.wasm -o output.wasm

# Build for WASM target
cargo build --target wasm32-wasip2 --profile release-wasm
```

### Bazel (Production/CI)

```bash
# Build all targets
bazel build //...

# Build specific target
bazel build //meld-cli:meld

# Run tests
bazel test //...

# Build with release config
bazel build --config=release //meld-cli:meld
```

## Architecture

```
meld/
├── meld-core/          # Core fusion library
│   ├── src/
│   │   ├── lib.rs          # Public API
│   │   ├── parser.rs       # Component parsing (wasmparser)
│   │   ├── resolver.rs     # Dependency resolution
│   │   ├── merger.rs       # Module merging
│   │   ├── adapter/        # Adapter generation
│   │   │   ├── mod.rs      # Trait interface
│   │   │   ├── fact.rs     # FACT-style implementation
│   │   │   └── native.rs   # Future: standalone impl
│   │   └── attestation.rs  # wsc-attestation integration
│   └── Cargo.toml
├── meld-cli/           # CLI binary
│   ├── src/main.rs
│   └── Cargo.toml
└── rules/              # Bazel rules (for rules_wasm_component)
    ├── meld.bzl        # meld_fuse() rule
    └── providers.bzl
```

## Key Concepts

### Component Fusion Pipeline

```
P2/P3 Components → Parser → Resolver → Merger → Adapter Gen → Single Module
```

1. **Parser**: Extracts core modules and type info from components
2. **Resolver**: Builds import/export graph, topological sort
3. **Merger**: Combines function/memory/table/global spaces
4. **Adapter Gen**: Creates Canonical ABI trampolines for cross-component calls

### Multi-Memory Support

- Phase 1 (current): Single shared memory
- Phase 2 (future): Multi-memory (each component keeps own memory)

## Development Guidelines

1. **Error Handling**: Use `anyhow` for CLI, `thiserror` for library errors
2. **Testing**: Property-based tests with `proptest` for core logic
3. **Documentation**: Doc comments on all public APIs
4. **Logging**: Use `log` crate, configure via `RUST_LOG` env var

## Key Files

- `meld-core/src/parser.rs` - Component binary parsing
- `meld-core/src/resolver.rs` - Import/export resolution
- `meld-core/src/merger.rs` - Module merging logic
- `meld-core/src/adapter/mod.rs` - Adapter trait definition
- `meld-cli/src/main.rs` - CLI entry point

## Integration Points

### wsc-attestation
Track transformation provenance through fusion. Add attestation to output
module's custom section.

### LOOM
Output is optimizable by LOOM. Use LOOM after meld for whole-program optimization:
```bash
meld fuse a.wasm b.wasm -o fused.wasm
loom optimize fused.wasm -o optimized.wasm
```

### rules_wasm_component
Bazel rule integration via `meld_fuse()`:
```starlark
load("@meld//rules:meld.bzl", "meld_fuse")

meld_fuse(
    name = "fused",
    components = [":component_a", ":component_b"],
)
```

## Testing

```bash
# Unit tests
cargo test

# Integration tests (requires test fixtures)
cargo test --test integration

# Property-based tests
cargo test --features proptest
```

## Verification

```bash
# Validate output
wasm-tools validate fused.wasm

# Print structure
wasm-tools print fused.wasm | head -50

# Component info
wasm-tools component wit input.wasm
```
