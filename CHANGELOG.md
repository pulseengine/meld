# Changelog

All notable changes to this project will be documented in this file.

## [0.6.0] — Unreleased

### Added

- **P3 async lowering pass — full data plane** (#120 / #129).
  Canonical built-ins `(canon stream.{new,read,write,cancel-read,
  cancel-write,drop-readable,drop-writable})` and the same seven verbs
  for `future` are now rewritten into core-module imports against the
  `pulseengine:async` ABI documented in `meld_core::p3_async`. The
  rewrite reuses every existing function-index reference so already-
  encoded `call N` instructions pick up the new defined-function
  positions. End-to-end tests for `stream<u8>` and `future<i32>`
  symmetric cases pass; the 73-test suite stays green when no P3
  async features are present (the pass is a no-op).
- **Closed `AbiError` enum + typed result decoders for `pulseengine:async`**
  (#121 / #127). Stable numeric error codes (`Closed=-1`,
  `InvalidHandle=-2`, `Oom=-3`, `Cancelled=-4`, `Pending=-5`,
  `Runtime=-6`) plus `StreamWriteResult` / `StreamReadResult` /
  `FutureReadResult` decoders. Per-variant rustdoc on every
  `HostIntrinsic::Stream*` / `Future*` documents partial-write
  semantics (producer is retry authority — runtime does NOT queue),
  EOF vs Pending distinguishability, and the `[waitable-set-wait]`
  interaction. ADR-2 documents the conventions.
- **Async-export callback trampoline alignment** (#122 / #128). Stable
  numeric event-type codes (`event::NONE`, `SUBTASK`, `STREAM_READ`,
  `STREAM_WRITE`, `FUTURE_READ`, `FUTURE_WRITE`, `CANCELLED`) and
  callback-return-code constants (`callback::EXIT`, `YIELD`, `WAIT`,
  `POLL` + `CODE_MASK` / `PAYLOAD_SHIFT`) exposed in
  `meld_core::p3_async`. ADR-1 addendum pins the canonical trampoline
  shape (`generate_async_callback_adapter` emits one shape regardless
  of which P3 built-ins the guest happens to use). Tests
  `async_callback_trampoline_shape_canonical`,
  `async_callback_event_codes_pinned`,
  `async_callback_return_codes_pinned` pin the contract.

### Fixed

- **`callback::POLL` dispatched as YIELD (LS-A-9 / pre-release Mythos
  finding).** The trampoline's
  `if code == WAIT { dispatch [waitable-set-poll] } else { send EVENT_NONE }`
  silently treated POLL (3) as YIELD (1), dropping any event the host
  had ready. Discovered by the v0.6 pre-release Mythos pass on
  `adapter/fact.rs`. Fix: branch on `code == WAIT || code == POLL`.
  Approved as **LS-A-9**.

### Safety / STPA

- New approved loss scenario: **LS-A-9** (UCA-F-3): async callback
  POLL fall-through; fixed in `adapter/fact.rs`.
- New ADR: **ADR-2** (`safety/adr/ADR-2-p3-async-error-conventions.md`)
  — `pulseengine:async` error / backpressure conventions.
- Updated ADR-1 — P3 async lowering pass marked shipped; trampoline
  addendum from #122 included; ADR-2 cross-reference added.

### Internal

- `meld-core/src/p3_async.rs` — +1019 LOC: lowering pass
  (`lower_p3_async_intrinsics`, `LoweringPlan`), `AbiError` enum,
  result decoders, event/callback constant tables, partial-write +
  EOF + waitable-set-wait rustdoc.
- `meld-core/src/adapter/fact.rs` — async-callback trampoline now
  references named `event::*` / `callback::*` constants (no more
  magic numbers); POLL dispatch fix.
- `meld-core/tests/p3_async_lowering.rs` — +399 LOC: lowering
  end-to-end tests for stream/future, callback shape pins.
- `meld-core/tests/p3_async_abi.rs` (new) — 22 encoding-pin tests for
  the `AbiError` numeric values and result decoders.
- `safety/adr/ADR-2-p3-async-error-conventions.md` (new).

### Pre-release Mythos pass

Tier-5 + tier-4 files changed since v0.5.0: `adapter/fact.rs` only
(+62 LOC, async-callback constant references). Scanned per
`scripts/mythos/discover.md`; **1 confirmed finding** (LS-A-9 above).
Fix shipped in this release; the discovery → fix → approved-LS pattern
parallels v0.3.0 and v0.4.0's Mythos cycle.

## [0.5.0] — Unreleased

### Added

- **P3 async lowering — foundation layer (#94 / #124, partial).** New
  `meld-core::p3_async` module documents the `pulseengine:async`
  host-intrinsic ABI (14 verbs covering `stream<T>` and `future<T>`), with
  `HostIntrinsic` enum and per-canonical-built-in mapping. New
  `Fuser::p3_async_summary()` exposes per-component P3 async usage. ADR-1
  (`safety/adr/ADR-1-p3-async-lowering.md`) records the design and the
  scope boundary. The actual rewrite pass remains deferred to follow-ups
  #120 (lowering pass), #121 (error/backpressure), #122 (async-export
  callback alignment); the v0.5.0 ABI is the stable contract those land
  against.
- **Criterion benchmarks for the fusion pipeline (#103 / #123).**
  `meld-core/benches/fusion_benchmarks.rs` ships four groups (parser,
  merger, resolver, end-to-end) running against the wit-bindgen test
  fixtures. CI `Bench compile-only` job verifies they compile on every
  PR. `safety/requirements/benchmarks.yaml` adds `TEST-BENCH-*` rivet
  artifacts. README badge + run instructions included.

### Fixed

- **Parser slice OOB on truncated component-section input (#118 / #125).**
  `meld-core/src/parser.rs` previously did
  `&full_bytes[unchecked_range.start..unchecked_range.end]` on
  `Payload::ModuleSection.unchecked_range` (and three sibling section
  payloads) — a libFuzzer-discovered crash on truncated component-model
  input. Fix: new `checked_section_slice` helper validates
  `range.start <= range.end <= full.len()` and returns
  `Error::ParseError("<section> range out of bounds (start=…, end=…,
  input_len=…)")` on mismatch. Applied at all four sites. Regression test
  + libFuzzer corpus seed shipped. cargo-fuzz `fuzz_parse_component`
  smoke now passes.

### Safety / STPA

- New approved loss scenario:
  - **LS-P-5** (UCA-P-3): truncated component-section input panic; fixed
    via `checked_section_slice` (PR #125).

### Internal

- `meld-core/src/lib.rs` — added `Fuser::p3_async_summary()`,
  `Fuser::components()`, and `Fuser::wiring_hints()` accessors (the
  latter two for benchmark / external-tool drive-the-pipeline parity).
- `meld-core/src/p3_async.rs` (new, ~470 LOC) — host-intrinsic ABI +
  detection.
- `meld-core/tests/p3_async_lowering.rs` (new) — 5 integration tests
  including a hand-built `stream<u8>` component.
- `meld-core/benches/fusion_benchmarks.rs` (new) — criterion harness.
- `.github/workflows/bench.yml` — bench compile-only PR smoke.
- `safety/adr/ADR-1-p3-async-lowering.md` — P3 async design ADR.
- `safety/requirements/benchmarks.yaml` — TEST-BENCH-* artifacts.

### Pre-release Mythos pass

Tier-5 + tier-4 files changed since v0.4.0: `meld-core/src/parser.rs`
only. Scanned per `scripts/mythos/discover.md`; **no confirmed findings**.
The v0.5 LS-P-5 fix is itself the result of v0.4's cargo-fuzz finding,
so additional discovery on that surface largely re-confirms the fix.

One unverified hypothesis flagged for the v0.5.1 / v0.6 follow-up Mythos
pass: there are three additional `reader.range()` / `range` storage
sites in `parse_core_module` (`parser.rs:1268`, `:1272`, `:1276`) whose
downstream consumers raw-index `&module.bytes[start..end]`. They share
LS-P-5's bug class but the outer module slice is already bounds-checked
at `parser.rs:820`, narrowing the surface. The 2026-05-20 verification
routine includes a deeper Mythos sweep that will revisit this.

## [0.4.0] — Unreleased

### Added

- **Kani + proptest harnesses for parser/merger/resolver (#102 / #116).**
  Three Kani harnesses (parser no-panic on bounded inputs, model topological
  sort, model resolver loop) plus a proptest suite for fusion round-trips.
  Kani is documented but not gated in CI yet; proptest runs as part of
  `cargo test --release`.
- **cargo-fuzz scaffolding (#104 / #114).** Four targets exercising the
  parser, merger, resolver, and end-to-end fusion. Seed corpus committed
  under `fuzz/corpus/`. CI smoke runs each target for 60 s on every PR
  (informational; nightly Rust required). The first run already surfaced
  a real parser panic — tracked as #118.

### Fixed

- **`compare_version` handles pre-release suffixes (#98 / #113).** The
  previous `filter_map(parse::<u32>)` silently dropped non-numeric segments,
  so `"0.2.99-rc1"` sorted *less* than `"0.2.0"`. Replaced with an inline
  subset of semver 2.0.0 precedence rules. Build metadata is stripped per
  spec. ~70 LOC, no new dependencies.
- **Resource-import fallback keyed by name, sentinel eliminated (#99 /
  #115).** `build_resource_type_to_import` previously collapsed all
  `[resource-rep]` / `[resource-new]` imports onto a single `(0u32, prefix)`
  sentinel slot when a component imported resources without canonical
  entries. Replaced with `ResourceImportMap { by_type_id, by_name }` —
  per-resource keying so multi-resource components don't silently overwrite
  one another's imports.
- **Mythos v0.4 follow-up — items 4, 5, 6 (#112 / #117).** Three confirmed
  determinism / routing fixes:
  - **Item 4 (LS-CP-3 / SR-19):** `graph.adapter_sites` is now sorted via
    `sort_adapter_sites_for_determinism` after both cross- and
    intra-component adapter passes. HashMap iteration was previously the
    only order, propagating into adapter-offset → merged-function-index and
    `merger.rs:1500` first-match.
  - **Item 5 (LS-R-10 / UCA-R-3):** `identify_intra_component_adapter_sites`
    now preserves `from_import_module` when promoting a `ModuleResolution`
    to an `AdapterSite`; the previous code copied `import_name` and the
    merger's disjunctive match accepted the wrong import for two same-name
    functions from different modules.
  - **Item 6 (LS-CP-3, second class):** three `caller_lower_map.iter().next()`
    encoding fallbacks now use `iter().min_by_key(|(k, _)| **k)` so the
    chosen `string_encoding` is stable across builds.
  - Items 1–3 (HT_CAPACITY enforcement, u32 truncation, silent
    `memory.maximum` raise) closed as still-uncertain — each requires
    fixtures meld doesn't currently accept; tracked for future passes.

### Safety / STPA

- New approved loss scenarios documenting the v0.4 fixes:
  - **LS-R-10** (UCA-R-3): intra-adapter-site promotion preserves
    `from_import_module`.
  - **LS-CP-3** (SR-19): adapter_sites sorting + caller-encoding fallback
    determinism.

### Internal

- `meld-core/src/merger.rs` — semver-correct `compare_version` + new
  `compare_prerelease` helper; 8 new unit tests.
- `meld-core/src/resolver.rs` — `ResourceImportMap` struct;
  `sort_adapter_sites_for_determinism`; `identify_intra_component_adapter_sites`
  promotion fix; three `iter().next()` → `iter().min_by_key()` sites.
- `meld-core/tests/kani_*.rs` and `meld-core/tests/proptest_fusion.rs` —
  bounded V&V harnesses.
- `fuzz/` — cargo-fuzz workspace with 4 targets and seed corpora.

### Pre-release Mythos pass

Tier-5 + tier-4 files changed since v0.3.0: `merger.rs`, `resolver.rs`.
Both scanned per `scripts/mythos/discover.md`; **no confirmed findings**.
The v0.4 fixes (LS-R-10, LS-CP-3) are themselves the result of the v0.3.0
deferred follow-ups.

## [0.3.0] — Unreleased

### Added

- **Per-component handle tables for resource definers (#108, #109).** Each
  component that defines a resource now gets its own handle table, so
  cross-component handle hand-offs go through bridging trampolines that
  translate `(caller_handle → caller.ht_rep → rep → callee.ht_new →
  callee_handle)`. This unblocks fixtures where the same canonical resource
  type is referenced through multiple interfaces (e.g. `import test` and
  `export test` on the same iface, or `use test.{T}` aliases).
- **Trio runtime fixtures pass.** `resource_floats`, `resource_with_lists`,
  and `resource-import-and-export` are now `runtime_test!` fixtures (closes
  #75). The 73-test wit-bindgen suite remains green.
- **`--opaque-rep` CLI flag** (in #108) for resources whose representation
  should be treated as a `u32` rather than a boxed pointer, skipping the
  per-resource handle-table layer entirely.

### Fixed

- **Borrow lower for method-like exports (#109).** `[method]/[static]/
  [constructor]` exports on a locally-defined resource expect the **rep**
  as `arg0` (wit-bindgen's `_export_*_cabi` calls `ThingBorrow::lift(arg0)`
  which derefs as `*mut _ThingRep<T>`). The previous bridge appended a
  `callee.ht_new(rep)` step that minted a fresh slot whose address was
  passed as the rep — the deref read 4 bytes at the slot (the just-stored
  rep) and `Option`'s discriminant byte was the low byte of that rep
  (0 for typical aligned box pointers) → `Option::unwrap on None`. Now
  emits only `caller.ht_rep` for method-like calls.
- **`ht_drop` dtor recursion in re-exporters (#109).** Phase 1's
  per-component HTs for definers store *foreign* reps placed by own
  bridges. The dtor (`<iface>#[dtor]<rn>`) blindly cast every stored value
  as `*mut _ThingRep<LocalT>`, so for foreign reps `Box::from_raw` would
  misinterpret memory and trigger re-entrant drops via the wit-bindgen
  `Resource::drop` impl, producing unbounded recursion. The dtor is now
  suppressed for re-exporter components.
- **Determinism in the wrapper alias-fallback (#109).**
  `reexporter_components` and `reexporter_resources` are now sorted before
  storage on the dependency graph. Previously they were collected from
  `HashSet` (non-deterministic iteration), so HT-allocation order varied
  build-to-build and the wrapper alias-fallback would sometimes wire
  `[resource-drop]` for the runner to leaf's `ht_drop` and sometimes
  intermediate's — the "passes manually, fails in cargo test" flakiness.
- **Canonical-ABI size overflow on nested fixed-length-list (LS-P-4 / #109).**
  `canonical_abi_size_unpadded`, `canonical_abi_element_size`,
  `flat_count`, and `flat_byte_size` did `element_size * len` on raw
  `u32` with no overflow check. Nested `fixed-length-list` types whose
  per-level lengths each pass wasmparser validation but whose product
  exceeds `u32::MAX` would either panic in debug builds (DoS in
  `meld fuse`) or silently wrap to `0` in release — the wrapped tiny
  size propagated to adapter realloc/copy, causing OOB writes in the
  receiver. Saturating arithmetic everywhere (`saturating_mul`,
  `saturating_add`, hardened `align_up`) keeps the size at `u32::MAX`
  instead of wrapping; downstream allocation then fails safely.
- **Inner-list rep_func selection (LS-A-8 / #109).** For
  `list<record { x: borrow<A>, ... }>`, the adapter's inner-resource
  fixup loops in `compute_adapter_options` and the params-ptr emission
  selected the `[resource-rep]` import via
  `resource_rep_imports.values().next()` (HashMap iteration order),
  routing handle A through resource B's rep_func when the callee
  imported more than one resource — silent rep-vs-handle confusion at
  the cross-component boundary. `resolver::InnerResource` now carries a
  pre-resolved `rep_import` filled at site-requirements time via the
  callee's resource_type_to_import map; `fact.rs` looks up rep_func per
  type rather than via the iteration-order arbitrary first match.

### Internal

- `meld-core/src/adapter/fact.rs` — borrow-rep discriminator in both the
  2-component (callee_defines=true) and 3-component branches; per-type
  `rep_func` selection for inner-list resources.
- `meld-core/src/merger.rs` — `ht_drop` dtor invocation gated on
  `!graph.reexporter_components.contains(&comp_idx)`.
- `meld-core/src/parser.rs` — saturating arithmetic across canonical-ABI
  size math; regression tests for fixed-length-list overflow boundary.
- `meld-core/src/resolver.rs` — `sort_unstable()` on `reexporter_components`
  and `reexporter_resources` before storing on `DependencyGraph`;
  `InnerResource` carries pre-resolved `(import_module, import_field)`
  for inner-list `borrow<T>` fixups.

### Safety / STPA

- New approved loss scenarios: **LS-P-4** (canonical-ABI size overflow,
  UCA-P-3) and **LS-A-8** (inner-list rep_func selection, UCA-A-7).
  Both fixed in this release; documented in
  `safety/stpa/loss-scenarios.yaml`.

## [0.2.0]

Initial tagged release.
