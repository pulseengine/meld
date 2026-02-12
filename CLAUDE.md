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

## Rocq Formal Verification

This project uses Rocq 9.0 (formerly Coq) for formal verification of the fusion
pipeline. Proofs are built via Bazel using `rules_rocq_rust`, which provides
both the Rocq toolchain and `rocq-of-rust` for Rust-to-Rocq translation.

### Rocq 9.0 Migration from Coq 8.x

Rocq 9.0 introduced significant naming changes. The codebase uses the new
conventions:

#### Import Changes
```coq
(* OLD Coq 8.x style - DO NOT USE *)
From Coq Require Import List ZArith.

(* NEW Rocq 9.0 style - USE THIS *)
From Stdlib Require Import List ZArith Lia Arith.
```

#### Deprecated Lemma Names
Many lemmas were renamed to follow a consistent `property_type` pattern:

| Old Name (8.x)     | New Name (9.0)      |
|--------------------|---------------------|
| `app_length`       | `length_app`        |
| `map_length`       | `length_map`        |
| `app_nil_r`        | `app_nil_r` (same)  |
| `app_assoc`        | `app_assoc` (same)  |
| `fold_left_app`    | `fold_left_app`     |
| `nth_error_None`   | `nth_error_None`    |
| `nth_error_Some`   | `nth_error_Some`    |
| `in_map_iff`       | `in_map_iff`        |
| `in_seq`           | `in_seq`            |

### Build Commands

```bash
# Build all proofs
bazel build //proofs:all_proofs

# Run a specific proof test (note: tagged 'manual')
bazel test //proofs:parser_proofs_test

# Build Rust-translated proofs
bazel build //proofs/rust_verified:merger_core_proofs
```

Note: Proof builds require Nix for the hermetic Rocq toolchain.

### Powerful Tactics and Automation

#### Arithmetic Solvers

- **`lia`** (Linear Integer Arithmetic): Solves goals involving linear
  arithmetic over integers/naturals. Use for bounds, inequalities, and
  simple arithmetic.
  ```coq
  Proof. intros. lia. Qed.
  ```

- **`nia`** (Nonlinear Integer Arithmetic): Extends `lia` with limited
  nonlinear support. More powerful but slower.

- **`omega`**: Deprecated in Rocq 9.0. Use `lia` instead.

#### Automated Proof Search

- **`auto`**: Basic proof search using hint databases. Fast but limited.
  ```coq
  auto with arith.  (* Use arithmetic hints *)
  ```

- **`eauto`**: Like `auto` but handles existentials. Use `eauto with *`
  for aggressive search.

- **`intuition`**: Propositional logic solver. Combines `auto` with
  logical decomposition.
  ```coq
  intuition lia.  (* Decompose then solve arithmetic *)
  ```

- **`tauto`**: Pure propositional tautology checker. Fast and complete
  for propositional goals.

- **`firstorder`**: First-order logic prover. Powerful but can be slow.
  ```coq
  firstorder auto.  (* First-order with auto fallback *)
  ```

#### Extensions in This Codebase

From `MODULE.bazel`, the following Rocq extensions are available:

- **rocq_stdlib**: Standard library (Lists, Arith, ZArith, etc.)
- **rocq_coqutil**: Utility library with tactics and definitions
- **rocq_hammer**: Automated theorem prover integration (for hard goals)
- **rocq_smpl**: Simplification tactics

### Proof Engineering Patterns

#### Structuring Complex Proofs

1. **Use sections for local assumptions**:
   ```coq
   Section MergeCorrectness.
     Variable input : merge_input.
     Hypothesis Hwf : well_formed input.

     Lemma helper1 : ... .
     Lemma helper2 : ... .
     Theorem main : ... .
   End MergeCorrectness.
   ```

2. **Break into helper lemmas**: Each file in `proofs/` contains multiple
   lemmas building toward main theorems.

#### Assertion Tactics: `assert` vs `enough` vs `cut`

- **`assert (H: P)`**: Prove `P` first, then use `H` in the main goal.
  Most common pattern.
  ```coq
  assert (Hbound: x < length l).
  { (* prove bound *) lia. }
  (* now use Hbound *)
  ```

- **`enough (H: P)`**: Assume `H`, prove main goal, then prove `H`.
  Use when `H` makes the main goal obvious.
  ```coq
  enough (Heq: x = y).
  { subst. reflexivity. }
  (* now prove x = y *)
  ```

- **`cut P`**: Like `assert` but leaves goals in reverse order.
  Rarely needed; prefer `assert`.

#### Generalizing Induction Hypotheses with `revert`

When induction needs a stronger hypothesis, use `revert` to generalize:

```coq
(* BAD: IH is too weak *)
Lemma fold_monotonic : forall l base,
    base <= fold_left f l base.
Proof.
  induction l.  (* IH only works for specific base *)
  ...

(* GOOD: revert makes IH general *)
Lemma fold_monotonic : forall l base,
    base <= fold_left f l base.
Proof.
  induction l; intro base.  (* IH works for all base values *)
  - simpl. lia.
  - simpl. apply IH.  (* Can apply to any base *)
Qed.
```

See `proofs/transformations/merge/merge_spec.v` for examples of this pattern
in `fold_left_add_nonneg_ge` and related lemmas.

#### Using `set` and `remember` for Abstraction

- **`set (x := expr)`**: Name a subexpression without generating equality.
  Good for readability.
  ```coq
  set (offset := compute_offset input space mod_idx).
  ```

- **`remember expr as x eqn:Heq`**: Name subexpression AND generate
  equality hypothesis. Use when you need to unfold later.
  ```coq
  remember (j - i) as diff eqn:Hdiff.
  ```

### rocq-of-rust Translation

Rust code is translated to Rocq via `coq_of_rust_library` rules. See
`proofs/rust_verified/BUILD.bazel`:

```starlark
coq_of_rust_library(
    name = "merger_core_translated",
    rust_sources = ["merger_core.rs"],
    edition = "2021",
)

rocq_library(
    name = "merger_core",
    srcs = [":merger_core_translated"],
    deps = [":rocq_of_rust_lib"],
    include_path = "meld",
    extra_flags = ["-impredicative-set"],
)
```

The translated code uses the rocq-of-rust runtime library. Proofs then
bridge between the translated Rust and pure-model specifications.

### Common Pitfalls and Solutions

#### 1. `lia` Failing on `fold_left`

`lia` cannot reason about `fold_left` directly. Abstract the term first:

```coq
(* BAD: lia fails *)
Lemma bad : forall l, 0 <= fold_left (fun a x => a + x) l 0.
Proof. intros. lia. (* FAILS *) Abort.

(* GOOD: use a helper lemma *)
Lemma fold_left_nonneg : forall l base,
    base <= fold_left (fun a x => a + x) l base.
Proof.
  induction l; intro base; simpl.
  - lia.
  - specialize (IHl (base + a)). lia.
Qed.

Lemma good : forall l, 0 <= fold_left (fun a x => a + x) l 0.
Proof. intros. apply fold_left_nonneg. Qed.
```

See `proofs/transformations/merge/merge_spec.v:fold_left_add_nonneg_ge`.

#### 2. Pattern Matching Issues (Boolean Associativity)

Boolean `&&` is left-associative. When matching on complex conditions:

```coq
(* The expression ((A && B) && C) && D *)
apply Bool.andb_true_iff in H.
destruct H as [H123 H4].      (* Split off D *)
apply Bool.andb_true_iff in H123.
destruct H123 as [H12 H3].    (* Split off C *)
apply Bool.andb_true_iff in H12.
destruct H12 as [H1 H2].      (* Split A and B *)
```

#### 3. Induction Needing Generalization

If induction gives a weak hypothesis, generalize more variables:

```coq
(* Weak: IH only for fixed values *)
induction l.

(* Strong: generalize auxiliary variables *)
generalize dependent aux_var.
induction l; intros aux_var.

(* Or use revert before induction *)
revert aux_var.
induction l.
```

#### 4. nth_error vs In

Converting between `In` and `nth_error`:

```coq
(* In -> nth_error *)
apply In_nth_error in Hin.
destruct Hin as [i Hi].

(* nth_error -> In *)
apply nth_error_In in Hnth.

(* Checking bounds *)
apply nth_error_Some. rewrite H. discriminate.
apply nth_error_None in H. (* H : i >= length l *)
```

#### 5. Admitted Proofs

Some complex proofs are `Admitted` pending further development. Search for
`Admitted` to find incomplete proofs that need attention. Priorities:

1. `merge_spec.v`: Core merge correctness theorems
2. `fusion_spec.v`: Semantic preservation (placeholder)
3. `resolve_spec.v`: Topological sort correctness

### Proof Directory Layout

| Proofs path              | Source path                | Focus                          |
|--------------------------|----------------------------|--------------------------------|
| `proofs/parser/`         | `meld-core/src/parser.rs`  | Parsing and decoding           |
| `proofs/resolver/`       | `meld-core/src/resolver.rs`| Import/export resolution       |
| `proofs/merger/`         | `meld-core/src/merger.rs`  | Index-space merging            |
| `proofs/adapter/`        | `meld-core/src/adapter/`   | Canonical ABI adapters         |
| `proofs/rewriter/`       | `meld-core/src/rewriter.rs`| Rewrite passes                 |
| `proofs/segments/`       | `meld-core/src/segments.rs`| Segment layout                 |
| `proofs/attestation/`    | `meld-core/src/attestation.rs`| Attestation integrity       |
| `proofs/rust_verified/`  | (special)                  | Rust-to-Rocq translated proofs |
| `proofs/spec/`           | (specifications)           | Core spec definitions          |
| `proofs/transformations/`| (specs for transforms)     | Transform correctness specs    |

### Specification Baselines

From `proofs/DECISIONS.md`:

- **Core spec**: WebAssembly Core Specification, Release 3.0
- **Component Model**: Commit `deb0b0a`
- **WASI**: v0.2.3 WIT definitions

### Tips for Writing New Proofs

1. **Start with the spec**: Define what correctness means in
   `proofs/spec/` or `proofs/transformations/` before proving.

2. **Use pure-model definitions**: Mirror Rust implementation in a
   simpler form (see `merger_core_proofs.v` for examples).

3. **Build incrementally**: Small lemmas compose into theorems.

4. **Leverage automation**: Try `auto`, `eauto`, `lia` early. Use
   `intuition` for propositional goals.

5. **Document admitted proofs**: Explain why and what's needed to complete.

6. **Human readability**: All lemmas, theorems, and proof structures must
   be human readable and understandable. Proofs should be written so that
   a developer can follow the logical reasoning without needing to step
   through tactics interactively. Prefer explicit structure over tactic
   magic:
   - Use meaningful names for hypotheses (`Hbound`, `Hvalid`, not `H1`, `H2`)
   - Add comments for non-obvious proof steps
   - Break complex proofs into named helper lemmas
   - Avoid deeply nested bullet structures (max 3-4 levels)
   - When using `admit`, document what remains to be proven
