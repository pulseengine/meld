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

## Opaque-rep variant (`resource_floats_opaque.wasm`) — #305

A 3-component re-exporter chain whose intermediate exports a `Float` resource
opted into **opaque-rep**, built from the **pulseengine/wit-bindgen fork**,
branch `feat/opaque-rep-attribute` (commit `51eca6b6` or later — the
"user-supplied dtor for opaque-rep export resources"). Opaque-rep returns the
leaf's inner handle as the rep verbatim, skipping the `Box::into_raw` +
`assume(ptr.is_aligned())` chain.

The `.wasm` is **gitignored** (~11 MB build artifact); regenerate it:

```bash
git clone https://github.com/pulseengine/wit-bindgen /tmp/wit-bindgen-fork
cd /tmp/wit-bindgen-fork && git checkout feat/opaque-rep-attribute
cargo run --release --bin wit-bindgen -- test \
  --artifacts /tmp/witbg-artifacts --languages rust \
  tests/runtime/resource_floats_opaque
cp /tmp/witbg-artifacts/resource_floats_opaque/composed-runner.rs-intermediate.rs-leaf.rs.wasm \
   tests/wit_bindgen/fixtures/resource_floats_opaque.wasm
```

**#305 status: resolved.** The original drop-teardown trap was the
wit-bindgen-side opaque-rep destructor (no inner-handle forwarding); the
fork's user-supplied dtor fixes it. With that fixture, meld fuses the chain
**and `construct+drop` runs cleanly** (`test_runtime_wit_bindgen_resource_floats_opaque`)
— no meld handle-table change was needed. The runtime test pins it; it skips
in CI when the fixture is absent (the 11 MB artifact is not committed).
