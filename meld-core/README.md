# meld-core

Core library for static WebAssembly component fusion.

See [`ARCHITECTURE.md`](ARCHITECTURE.md) for the 5-stage pipeline overview
(Parse → Resolve → Merge → Adapt → Encode) and a tour of each stage.

## Verification & validation

meld combines three layers of static checks:

| Layer | What it proves | Where it runs |
|-------|----------------|---------------|
| Rocq proofs (`proofs/`) | Semantic preservation of fusion at the IR level (28 theorems covering `fusion_spec.v`, `merger_core_proofs.v`, `resolver_core_proofs.v`). | `make -C proofs` (separate Rocq toolchain) |
| Kani harnesses (`tests/kani_*.rs` + `src/merger.rs::kani_proofs`) | Bounded model checking on the Rust impl edges (no panics, index arithmetic, termination). | `cargo kani --package meld-core` |
| proptest harnesses (`tests/proptest_*.rs`) | Random well-formed input round-trips for the parser/merger pipeline. | `cargo test --release` (gated under regular CI) |

The Rocq layer covers the mathematical model; the Kani and proptest layers
cover "the Rust impl actually implements that model" on bounded inputs.
See issue [#102](https://github.com/pulseengine/meld/issues/102) for the
V&V coverage rationale.

### Running proptest

proptest harnesses run as ordinary Rust tests:

```bash
cargo test --release --test proptest_fusion
```

They run as part of the normal `cargo test --release` suite — no extra
toolchain required.

### Running Kani

Kani is a bounded model checker for Rust that requires its own toolchain.
It is **not** enabled in CI yet because the toolchain install is heavy
and the proofs run for tens of seconds each.

One-time setup:

```bash
cargo install --locked kani-verifier
cargo kani-setup
```

Run all Kani harnesses in `meld-core`:

```bash
cargo kani --package meld-core
```

Run a single harness (faster while iterating):

```bash
cargo kani --package meld-core --harness kani_parser_does_not_panic_on_short_buffer
cargo kani --package meld-core --harness kani_merger_self_loop_is_cycle
cargo kani --package meld-core --harness kani_resolver_terminates_within_bound
```

### Bounded scope

Kani harnesses are bounded (≤ 4 components, ≤ 4 imports per component, ≤ 16
bytes for parser inputs) so each proof finishes in seconds.  Issue #102's
upper limit is "≤ 8 functions, ≤ 16 imports"; harnesses stay well under
that.  The intent is *not* exhaustive search of real-world inputs — that
is what the proptest layer covers — but a bounded existence/absence
guarantee on small adversarial inputs (e.g. malformed component
binaries, contrived import cycles).
