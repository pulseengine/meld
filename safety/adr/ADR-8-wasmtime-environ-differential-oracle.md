---
id: ADR-8
type: design-question
title: wasmtime-environ's component translator as a pinned, dev-only differential oracle for meld's component resolution
status: proposed
gating-fixtures:
  # Run with `cargo test -p meld-core --features oracle --test oracle_wasmtime_environ`
  # (also run by every `--all-features` test run, e.g. the CI coverage job).
  - oracle_wasmtime_environ::oracle_lift_memory_481_both_module_orders
  - oracle_wasmtime_environ::oracle_lower_memory_484_every_module_order
  - oracle_wasmtime_environ::oracle_lower_encoding_484_utf16
  - oracle_wasmtime_environ::oracle_lower_realloc_484
  - oracle_wasmtime_environ::oracle_wit_bindgen_single_components
  - oracle_wasmtime_environ::oracle_wit_bindgen_composed
  - oracle_wasmtime_environ::oracle_wit_bindgen_record_provider_resolver
  - oracle_wasmtime_environ::oracle_issue_461_falcon_cascade_resolver
  - oracle_wasmtime_environ::oracle_lower_alias_chain_490
  - oracle_wasmtime_environ::oracle_export_binding_485_resolver
  # Ignored until the meld bug they expose is fixed (they fail today, by design):
  - oracle_wasmtime_environ::oracle_wit_bindgen_record_provider_output  # meld#486
  - oracle_wasmtime_environ::oracle_export_binding_485_output           # meld#485
  - oracle_wasmtime_environ::oracle_issue_461_falcon_cascade_output     # #476 class, unconfirmed
design-paths:
  - path-K — status quo — hand-rolled resolution checked only by per-bug regression tests and runtime differential tests (rejected — each bug class is found once, by hand, after it ships)
  - path-L — depend on it — use wasmtime-environ's translator as meld's resolver at runtime (rejected — couples meld's output to wasmtime's internal, unstable API and makes meld a wasmtime build)
  - path-M — port it — transcribe wasmtime's inliner into meld (rejected — a second copy of the same reasoning loses the independence that makes a cross-check worth anything)
  - path-N — differential oracle — keep meld's own resolution; pin wasmtime-environ as a dev-only second implementation and cross-test (proposed)
---

# ADR-8 — wasmtime-environ as a differential oracle for component resolution

## Context

meld resolves components with its own implementation: the parser
(`parser.rs`), the resolver (`resolver.rs`), the canonical-option resolution
in the P2 wrapper (`component_wrap.rs`), and the merger (`merger/`). That
implementation decides, for every `canon lift` and `canon lower`, which core
function is lifted and which memory, `realloc`, post-return, callback and
string encoding it uses. It also decides how the core and component index
spaces are numbered, how aliases trace back to their definitions, and which
exports bind to which implementation.

Almost all of the silent wrong-result bugs from the week of 2026-10-14 were in
that resolution. In each one the fused component validated, ran, and returned
the wrong answer at exit 0:

- #481 and #484: the memory, realloc and encoding a lift or lower names.
  `--component` lifted every export from fused memory 0 (#481). It lowered
  host imports with whichever memory a `HashMap` scan returned first, so the
  output varied from run to run (#484).
- #485 and #489: index spaces. A replayed func alias shifted every export
  index (#485). Component core-function indices were decomposed as offsets
  into module function counts (#489).
- Alias tracing. PR #490 (the first #484 fix) had to trace a lower through
  any number of core-instance alias hops; the `chain_fixture` shape in
  `lower_memory_484.rs` pins it.
- #499: export binding. A world export ran an internal component's
  implementation.

Each was found by hand, often during a Mythos delta-pass on an unrelated PR.
Each was then pinned by a regression test for that one shape. Nothing checks
the resolution as a whole.

There is already a second, independent, production-grade implementation of
exactly this resolution in the dependency graph. meld dev-depends on
`wasmtime = "41.0.1"` for its runtime tests, and that pulls in
`wasmtime-environ 41.0.4`. Its component translator inlines a component into
a flat list of `GlobalInitializer`s and records the `CanonicalOptions` it
resolved for every lift and lower. meld already mirrors wasmtime on the
adapter side: the FACT adapter generator follows wasmtime's `fact` module.
This ADR applies the same idea to resolution, as a cross-check rather than a
mirror.

## Decision (proposed)

meld keeps its own implementation of component resolution: the parser, the
resolver, the canonical-option resolution in `component_wrap.rs`, and the
merger.

`wasmtime-environ`'s component translator becomes a pinned, dev-only
differential oracle. It is a second, independent implementation that meld is
cross-tested against. A disagreement means one of two things, and both are
worth knowing:

- a meld bug; or
- a semantic change in wasmtime, which the deliberate upgrade (below) is
  there to surface.

It is never a runtime dependency.

### Feasibility (spike, 2026-10-21)

Everything the comparison needs is public in `wasmtime-environ 41.0.4`, under
the `compile` and `component-model` features. `wasmtime` already enables
both, so the dev-dependency adds no crate and no feature to the graph (checked
with `cargo tree -e features -i wasmtime-environ`; `Cargo.lock` gains one
dependency edge and no package).

- **Entry point:** `component::Translator::new(&Tunables, &mut Validator, &mut ComponentTypesBuilder, &ScopeVec<u8>).translate(bytes)`.
  It returns `(ComponentTranslation, PrimaryMap<StaticModuleIndex, ModuleTranslation>)`.
  - `Tunables::default_host()` is enough. No compiler, `Engine` or `Config`
    is needed.
  - `Validator` and `WasmFeatures` must come from the crate's re-export,
    `wasmtime_environ::wasmparser`, not from meld's `wasmparser`.
- **Per lift:** `Component::exports` (a `NameMap`), then
  `Component::export_items[i]`, then
  `Export::LiftedFunction { func: CoreDef, options: OptionsIndex }`.
  - `Component::options[options]` is a `CanonicalOptions`. It carries
    `string_encoding`, `async_`, `callback` and `post_return`; `memory()`;
    and `realloc`, which sits inside `CanonicalOptionsDataModel::LinearMemory`.
- **Per lower:** `ComponentTranslation::trampolines` holds
  `Trampoline::LowerImport { index, options }`.
  - `GlobalInitializer::LowerImport { index, import }` connects it to
    `Component::imports[import]` and `import_types`, which give the import
    path.
- **Resolving to a definition:**
  - `GlobalInitializer::Extract{Memory,Realloc,PostReturn,Callback}` give a
    `CoreDef` / `CoreExport { instance, item }`.
  - The Nth `InstantiateModule` is `RuntimeInstanceIndex` N, which gives a
    `StaticModuleIndex` and its argument list.
  - `Module::exports` and `Module::initializers` let an imported entity be
    chased through the instantiation arguments to the module that defines it.
- **Joining to meld:** `ModuleTranslation::wasm` holds each static module's
  bytes, and those join to meld's `CoreModule::bytes`. Nested components and
  wasmtime's own adapter modules shift positional numbering, so the join is
  never positional.
- **Not reachable without forking:** the pre-`finish` dataflow graph.
  `component::dfg` is public, but `inline::run` and `dfg::Adapter` (the
  per-adapter `lift_options` / `lower_options`) are private to `translate`.
  - After `finish`, a component-to-component adapter survives only as an
    instantiated FACT module plus the core definitions passed to it.
  - So the per-option resolution of INTERNAL (component-to-component) calls
    is not directly readable. It could be reconstructed from the adapter
    module's imports and its instantiation arguments, but that is more work
    and is left for later.
  - The component's own boundary is fully readable: exported lifts and
    lowered host imports.

### What is compared now

The harness is `meld-core/tests/oracle_wasmtime_environ.rs`, behind the cargo
feature `oracle`.

- **Why a feature and not `#[ignore]`:**
  - the same feature also gates meld-core's one read-only hook;
  - `--all-features` runs (CI coverage) compile and run it, so it cannot go
    dark, as the #405 tests did;
  - the default suite never compiles it.

It runs two comparisons per fixture.

1. **Output side.** wasmtime-environ translates the SOURCE and meld's
   `--memory multi --component` OUTPUT.
   - Per exported lift, it compares the lifted core function, `memory`,
     `realloc`, `post-return`, `callback`, `string-encoding` and `async`.
   - Per lowered host import, it compares the same option set.
   - Source definitions are mapped to fused indices through the merger's own
     `memory_index_map` / `function_index_map`. These are snapshotted by the
     feature-gated `Fuser::oracle_index_maps()`, which changes no behaviour.
   - An output memory supplied by meld's memory-provider module is read back
     as the fused module's import of it.
   - An option the output supplies and the source omits counts as inert, not
     as a disagreement. Validation requires every option a type needs, so an
     omitted option is one the Canonical ABI never consults for that type.
   - An output the oracle rejects as invalid is reported as a disagreement.
2. **Resolver side.** This compares meld's own resolver's reading of every
   source `canon lift` with the oracle's reading of the same source.
   - meld's reading comes from `resolver::core_func_sources` and
     `core_memory_sources`, the functions the wrapper and the #400 signature
     manifest resolve options with.
   - It needs only a core-module fuse, so it also covers inputs the wrapper
     cannot yet wrap (the falcon trio below).

**Results on `main` (8060df3):**

| Fixture | Output side | Resolver side |
|---|---|---|
| #481 WAT, both module orders ×10 fuses | 7 facts agree | 7 agree |
| #484 WAT memory, 6 orders ×10 | 12 agree, 1 inert | — |
| #484 WAT utf16, 2 orders ×10 | 12 agree, 1 inert | — |
| #484 WAT realloc, 3 orders ×10 | 13 agree | — |
| PR #490 alias chain (utf16 lower through 1 / 3 / 256 hops) | 12 agree, 1 inert each | — |
| #485 WAT (func alias before the first core module) | **meld output rejected (meld#485)** | 7 agree |
| wit-bindgen strings / lists / records / flavorful / resource_aggregates | 119 agree, 26 inert each | 7 agree each |
| wit-bindgen `compose/composed` | 14 agree | 14 agree |
| wit-bindgen `compose_record/composed_record` | 7 agree | 7 agree |
| wit-bindgen `compose_record/provider` | **meld output invalid (meld#486)** | 7 agree |
| #461 falcon estimator / control / split | **meld cannot wrap** (`cannot find source type definition at index 1`; nested-component inputs, same error class as #476, root cause not confirmed) | 14 / 14 / 21 agree |
| #461 falcon, all three fused | — | 49 agree |

The five wit-bindgen runtime fixtures have the same top-level shape: they
export `run` and import 23 WASI functions, with two memory-owning modules.
That is why their counts are identical.

The oracle flagged two open bugs on `main`. In both, meld exits 0.

- **`compose_record/provider.wasm`**, a tracked fixture.
  - `--component` emits `(canon lift (core func 0))` with no options, where
    the source lift names `(memory $memory)`.
  - wasmtime-environ rejects the result: "canonical option `memory` is
    required".
  - The root cause is the same as meld#486: export lifts drop the source's
    `memory` / `realloc` unless a post-return or async forces them. Here it is
    reached by a record result rather than a string parameter.
- **#485's reproduction.**
  - The output's `run` export names the imported `log` instead of the lift.
  - wasmtime-environ rejects it: "component export `run` is a reexport of an
    imported function which is not implemented".

Both are `#[ignore = "meld#NNN"]` until fixed.

**Potency.**

- *Output side, against the real bug.* The hook, the feature and the test
  were applied with `patch` onto an export of `9926d47` (7eaeccc^, before
  the #481 fix). They applied cleanly. The oracle flagged:
  - #481: `lift run memory: source names Index(1), meld's output names Index(0)`;
  - #484 memory: source memory 0, output memory 1;
  - #484 encoding: source utf16, output utf8;
  - #484 realloc: source (memory 1, realloc 2), output (memory 0, realloc 1);
  - PR #490 alias chain: source (memory 1, utf16), output (memory 0, utf8).

  The output side would have caught both bugs. The re-run used the committed
  patch, applied to a fresh export.

  For #484 memory and realloc, the FIRST fuse of the failing order agreed and
  a later one disagreed. That is #484's hash-order nondeterminism, and it is
  why each WAT fixture is fused 10 times.
- *Resolver side, injected.* An off-by-one shift was injected into
  `resolver::core_func_sources`, of the kind the #485 index-space miscount
  produces. Both resolver-side tests that were run went red: the falcon test
  and the record-provider test ("wasmtime lifts fused func #N; meld's
  resolver traces no lift to it"). The injection was reverted.

**What the join does NOT detect.** The output-side comparison trusts meld's
index maps. If `memory_index_map` itself sent a source memory to the wrong
fused memory, the expected value and the output would agree with each other
and both be wrong. Runtime differential tests (unfused against fused under
wasmtime) remain the check for that.

### What is compared later (in priority order)

1. **Internal (component-to-component) call options.** This is the #489 shape.
   - For each FACT adapter module in the oracle's output, read the memories,
     reallocs and post-returns passed as its instantiation arguments, and the
     lift/lower pairing implied by which core import each adapter satisfies.
   - Compare them with meld's adapter-site resolution
     (`DependencyGraph::adapter_sites`, or a similar snapshot).
   - This is the comparison that covers the wit-bindgen corpus's real string,
     list and record traffic, which today crosses only internal boundaries.
2. **Export binding in core-module output.** This is the #499 shape.
   - #499 is about the fused core module's export names: the unsuffixed world
     name binds an internal component's function.
   - The harness compares lifts only in `--component` output today. On #499's
     `middleware.wasm`, from the unmerged `feat/463-exports-world` branch, the
     resolver side agrees and `--component` refuses the input ("fused module
     has no memory section"). So #499 is NOT covered yet.
   - Next step: compare each world export name's lifted core function in the
     source with the fused core module's export of the same name.
3. **Lower identity.** Join each source lower to the fused import slot it
   becomes, instead of comparing sets by import path.
4. **P3 (component-model async), the north star.**
   - The options carry `async_`, `callback` and `cancellable`.
   - wasmtime-environ 41's trampolines cover most of the P3 builtins meld's
     parser recognises (`parser::CanonicalEntry`), each tagged with its
     component instance:
     - `TaskReturn { results, options }` and `TaskCancel`;
     - `StreamRead` and `StreamWrite`, and `FutureRead` and `FutureWrite`,
       each with `options`, plus the stream and future new / cancel / drop
       operations;
     - `WaitableSet*` and `WaitableJoin`;
     - `SubtaskDrop` and `SubtaskCancel`;
     - `ContextGet` and `ContextSet`;
     - `BackpressureInc` and `BackpressureDec`;
     - `ErrorContext*` and `ThreadYield`.
   - Not checked one-for-one: meld's `ThreadSpawn`, `ThreadHwConcurrency` and
     `ResourceDropAsync` have no trampoline of the same name in 41.x. The
     closest wasmtime entries are `ThreadNewIndirect` and `ResourceDrop`.
   - For every builtin both sides know, the oracle can state its instance, its
     stream/future table type and its options.
   - meld's P3 support can then be measured as "constructs whose resolution
     agrees with the oracle / constructs present". That is a number that
     moves, rather than a feature list.

### Pinning and upgrade policy

- **Pin exactly.** The dev-dependency is
  `wasmtime-environ = { version = "=41.0.4", features = ["compile", "component-model"] }`,
  the same version `wasmtime` resolves.
  - wasmtime pins its internal crates with `=`, so any other spec would pull
    a second copy.
  - `cargo tree -d` must not list `wasmtime-environ` twice.
- **Upgrade deliberately, together with `wasmtime`.** An upgrade is its own PR.
  - It changes no meld code.
  - It records each new disagreement as an issue, classified as either a
    meld bug or a wasmtime semantic change.
  - Expected churn in the harness (renamed fields, moved options) is fixed in
    the harness, not in meld.
- **Never "fix" meld by copying wasmtime's output into it.** A disagreement is
  resolved by reasoning from the spec, then fixing whichever side is wrong.
  If that is meld, the fix is in meld's own resolution, with its own
  regression test.

### Breaking a disagreement

The oracle is not the authority. When meld and wasmtime-environ disagree, two
things decide:

1. the Component Model specification (`Explainer.md` and
   `CanonicalABI.md`); and
2. the wasmtime runtime behaviour of the UNFUSED component, which is the same
   unfused-against-fused differential the runtime tests already use.

If the spec and the unfused run side with meld, the disagreement is an oracle
bug or a wasmtime semantic change. It is reported upstream, recorded in the
harness as a pinned expected disagreement with the issue link, and re-checked
at the next upgrade.

### What the oracle must NOT do

- It must not become a runtime, build or CLI dependency of meld. It stays a
  `[dev-dependencies]` entry, and its code stays behind `cfg(feature = "oracle")`.
- It must not be used to produce meld output. No resolution result flows from
  wasmtime-environ into meld's code paths, not even as a fallback.
- It must not weaken a comparison to get green. A fixture that disagrees on
  `main` is `#[ignore = "meld#NNN"]` with the issue cited, never loosened.
- It must not be counted as proof. Agreement between two implementations is
  evidence, not verification. The Rocq proofs and the runtime differential
  tests keep their roles.

## Alternatives considered

- **path-K: status quo.** Per-bug regression tests plus runtime differential
  tests.
  - They catch a shape only after someone has found it.
  - The runtime tests only see what a given fixture executes. #484's
    nondeterminism passed some runs.
- **path-L: depend on it.** Call wasmtime-environ's translator from meld to do
  the resolution.
  - The internal API changes every release.
  - It would make meld's correctness wasmtime's.
  - It would add wasmtime-environ and its dependencies to every meld build,
    including the Bazel build.
  - It would remove the independent check.
- **path-M: port it.** Transcribe the inliner into meld.
  - This produces the same reasoning twice, so the two cannot disagree in the
    cases where the shared reasoning is wrong.
  - It also leaves a port to maintain against an upstream that changes every
    release.
- **path-N: differential oracle.** Chosen.
  - meld keeps its own implementation and its proofs.
  - The second implementation costs nothing at runtime and has no build
    dependency.
  - A disagreement is a signal in both directions.

## Risks

- **Internal API churn.** `wasmtime-environ` is not a stable public API, and
  the translator's types change between releases.
  - For example, in 41.x `realloc` is not a field of `CanonicalOptions` but
    sits inside `CanonicalOptionsDataModel::LinearMemory`, which is the kind
    of detail that moves.
  - Mitigation: an exact pin, an upgrade only alongside `wasmtime`, and churn
    absorbed in one test file. If an upgrade makes the harness uneconomic,
    the oracle can stay pinned at the last workable version for longer than
    `wasmtime` itself. That is acceptable for a dev-only cross-check, at the
    cost of the "semantic change" signal.
- **Oracle bugs.** wasmtime-environ can be wrong, or can be ahead of or behind
  the spec, as with P3 constructs still settling. The tie-break above applies,
  and an oracle disagreement is never auto-applied to meld.
- **Join trust.** The output-side comparison trusts meld's index maps (see
  "What the join does NOT detect"). The resolver side shares that trust for
  the final fused index, but not for the source-side tracing it checks.
- **Coverage illusion.** "N facts agree" covers only the boundary the oracle
  can read today: exported lifts and host lowers. The wit-bindgen corpus's
  rich types cross internal boundaries, which the harness does not compare
  yet. The per-fixture fact counts are printed and asserted to be above a
  floor so that a comparison which silently stops looking fails.
- **Feature unification.** `--all-features` enables `oracle`. The hook is a
  `Mutex<Option<_>>` snapshot that the pipeline writes and never reads, so it
  cannot change output. The gate runs `--workspace` with and without
  `--all-features`.

## References

- Issues:
  - #481 and #484: fixed; the oracle catches both at 9926d47.
  - #485 and #486: open; flagged by this oracle on `main`.
  - #489 and #499: open; not covered yet (see "What is compared later").
  - #476: open; the falcon failure is of the same error class.
- PR #490: the first #484 fix (alias-chain tracing).
- `meld-core/tests/oracle_wasmtime_environ.rs`: the harness.
- `meld-core/src/lib.rs`: `OracleIndexMaps`, `Fuser::oracle_index_maps`
  (feature `oracle`).
- `wasmtime-environ 41.0.4`: `src/component/translate.rs` (`Translator`),
  `src/component/info.rs` (`Component`, `GlobalInitializer`,
  `CanonicalOptions`, `Trampoline`), `src/component/translate/adapt.rs`
  (adapter partitioning; the private `dfg::Adapter`).
- ADR-1 and ADR-2 (P3 async lowering and error conventions): the constructs
  the later comparison measures.
