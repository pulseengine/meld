# meld fuzz targets

Coverage-guided fuzz targets for the meld component-fusion pipeline,
addressing dynamic-V&V gap [#104](https://github.com/pulseengine/meld/issues/104).

meld parses untrusted WebAssembly component binaries and feeds them through
parser → resolver → merger → adapter generator. Any panic or unbounded
allocation along that pipeline is a crash bug or DoS vector. The Rocq proofs
under `proofs/` cover semantic correctness on **well-formed** inputs; these
fuzz targets cover robustness on **malformed and adversarial** inputs.

## Targets

| Target | Stage | Property |
|---|---|---|
| `fuzz_parse_component`   | `parser.rs`             | `ComponentParser::parse(bytes)` never panics on arbitrary bytes; returns `Ok` or `Err`. |
| `fuzz_resolver_terminates` | `resolver.rs`         | `Resolver::resolve(...)` always terminates and never panics. Pathological import graphs fail gracefully. |
| `fuzz_merger_idempotent` | `merger.rs`             | Two `Merger::merge(...)` runs on identical input produce structurally identical output (determinism). |
| `fuzz_fusion_roundtrip`  | full pipeline (`Fuser`) | If `Fuser::fuse()` returns `Ok(bytes)`, those bytes pass `wasmparser::Validator::validate_all`. |

## Prerequisites

Cargo-fuzz requires the **nightly** Rust toolchain (libfuzzer-sys uses
unstable sanitizer flags). Install:

```sh
rustup toolchain install nightly
cargo install cargo-fuzz
```

The fuzz crate is excluded from the main workspace
(see `[workspace.exclude]` in the root `Cargo.toml`). It builds independently
from `fuzz/`.

## Running locally

From the repository root:

```sh
# 60-second smoke (matches CI)
cargo +nightly fuzz run fuzz_parse_component -- -max_total_time=60

# Full overnight campaign
cargo +nightly fuzz run fuzz_parse_component

# Specific target — substitute any of the four
cargo +nightly fuzz run fuzz_merger_idempotent
cargo +nightly fuzz run fuzz_resolver_terminates
cargo +nightly fuzz run fuzz_fusion_roundtrip
```

Crashes land in `fuzz/artifacts/<target>/`. Reproduce with:

```sh
cargo +nightly fuzz run fuzz_parse_component fuzz/artifacts/fuzz_parse_component/crash-<hex>
```

## Compile-only check

If you do not have nightly available, you can at least confirm the targets
compile by pointing `cargo-fuzz` at `--dev`:

```sh
cargo +nightly fuzz build
```

## Corpus

Seed inputs live under `fuzz/corpus/<target>/`. Each target has at least one
hand-crafted seed — typically the 8-byte component magic header — to give
libfuzzer a starting point. The wit_bindgen test fixtures under
`tests/wit_bindgen/fixtures/` are intentionally **not** committed as seeds:
they are 7–8 MB each and would balloon the repository. Copy them in locally
when running long campaigns:

```sh
cp tests/wit_bindgen/fixtures/numbers.wasm fuzz/corpus/fuzz_parse_component/
```

After a productive run you may wish to minimize the corpus and commit new
inputs that revealed coverage:

```sh
cargo +nightly fuzz cmin fuzz_parse_component
```

## CI

`.github/workflows/fuzz.yml` runs each target for 60 s on every PR. The
job is informational (continue-on-error) until nightly Rust is wired into
the standard CI matrix, but a regression that crashes within 60 s of
fuzzing will surface as a failed step in the PR checks.

## When to add new targets

When a `confirmed` Mythos finding lands in `safety/stpa/loss-scenarios.yaml`
that names a parser/resolver/merger code path not currently fuzzed, add a
new target here covering that code path. The acceptance criterion in
`scripts/mythos/discover.md` (failing PoC test as oracle) usually doubles
as a corpus seed.
