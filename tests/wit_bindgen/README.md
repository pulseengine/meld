# wit-bindgen End-to-End Tests

End-to-end tests validating meld's component fusion using composed components
from the [wit-bindgen](https://github.com/bytecodealliance/wit-bindgen) test suite.

## Setup

### Generate Fixtures

The tests require pre-built composed components from wit-bindgen:

```bash
# Clone and checkout wit-bindgen
git clone https://github.com/bytecodealliance/wit-bindgen /tmp/wit-bindgen
cd /tmp/wit-bindgen
git checkout v0.52.0

# Install wit-bindgen CLI if needed
cargo install wit-bindgen-cli

# Generate test artifacts
wit-bindgen test --languages rust --artifacts artifacts tests/runtime

# Copy all fixtures to meld
for dir in artifacts/*/; do
  test=$(basename "$dir")
  src=$(find "$dir" -name 'composed-*.wasm' -print -quit)
  [ -n "$src" ] && cp "$src" "/path/to/meld/tests/wit_bindgen/fixtures/${test}.wasm"
done
```

### Run Tests

```bash
# Run all e2e tests (requires fixtures)
bazel test //tests/wit_bindgen:wit_bindgen_e2e

# Run individual test
bazel test //tests/wit_bindgen:numbers_e2e_test

# Just build fused output without testing
bazel build //tests/wit_bindgen:numbers_fused
```

## Pipeline

```
fixtures/{test}.wasm  (composed component)
        │
        ▼
    meld fuse (genrule)
        │
        ▼
    {test}_fused.wasm
        │
        ▼
    wasm_test --invoke run
```

## Test Cases

45 fixtures from the wit-bindgen test suite. 21 pass full runtime execution,
12 pass core fusion only (graceful degradation), and tests skip gracefully
when `.wasm` files are absent.

See `meld-core/tests/wit_bindgen_runtime.rs` for the full test list and
per-fixture status notes.

## Notes

- Tests are tagged `manual` - they only run when explicitly requested
- Phase 2 (TODO): Build from source once `rules_wasm_component` exports `@crates`
- Baseline: wit-bindgen `v0.52.0` (see `proofs/DECISIONS.md`)

## Opaque-rep variant (resource_floats_opaque.wasm)

Built from the **pulseengine/wit-bindgen fork**, branch
`feat/opaque-rep-attribute` (commit `236ef4bb` or later). This branch adds
an opt-in `--opaque-export-resources` flag for the Rust generator that
emits a stripped-down wrapper for re-exporter resources, sidestepping the
`Box::into_raw` + `assume(ptr.is_aligned())` debug-assert chain that
trips the `& 7` alignment trap in the standard `resource_floats` fixture.

```bash
git clone https://github.com/pulseengine/wit-bindgen /tmp/wit-bindgen-fork
cd /tmp/wit-bindgen-fork
git checkout feat/opaque-rep-attribute
cargo run --release --bin wit-bindgen -- test \
  --artifacts /tmp/witbg-artifacts \
  --languages rust \
  tests/runtime/resource_floats_opaque
cp /tmp/witbg-artifacts/resource_floats_opaque/composed-runner.rs-intermediate.rs-leaf.rs.wasm \
   tests/wit_bindgen/fixtures/resource_floats_opaque.wasm
```

Status: meld fuses cleanly, validates, construct-only path works, but
construct+drop traps with a memory fault during drop teardown. The fuse
oracle is the load-bearing test today; the runtime drop bug needs
explicit inner-handle forwarding in the opaque-rep dtor (wit-bindgen
generator side) plus per-resource handle table discrimination in meld
(`merger.rs:739`, `fact.rs:582`).
