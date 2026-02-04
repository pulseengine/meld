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

# Copy fixtures to meld
for test in numbers strings lists records; do
  cp "artifacts/${test}/composed-runner.rs-test.rs.wasm" \
     "/path/to/meld/tests/wit_bindgen/fixtures/${test}.wasm"
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

| Test | Description |
|------|-------------|
| `numbers` | Integer and float type conversions |
| `strings` | String passing across component boundaries |
| `lists` | List/array handling |
| `records` | Struct-like composite types |

## Notes

- Tests are tagged `manual` - they only run when explicitly requested
- Phase 2 (TODO): Build from source once `rules_wasm_component` exports `@crates`
- Baseline: wit-bindgen `v0.52.0` (see `proofs/DECISIONS.md`)
