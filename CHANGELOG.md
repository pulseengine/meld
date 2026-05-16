# Changelog

All notable changes to this project will be documented in this file.

## [Unreleased]

## [0.8.1] — 2026-05-16

### Fixed

- **Extended-const initializer / offset truncation** (LS-A-11, UCA-M-6,
  H-1 / H-2 / H-3.3). Two const-expression parsers in meld-core read
  only the first operator and discarded the rest, silently truncating
  any wasm 2.0 `extended-const` expression. A data / element segment
  with offset `(i32.const 5)(i32.const 10) i32.add` landed at offset 5
  instead of 15; a global initialized to `(i32.const 100)(i32.const 23)
  i32.add` (intended 123) was emitted as 100. Affected
  `segments.rs::parse_const_expr_with_value` (data + element offsets)
  and `merger.rs::convert_init_expr` (global initializers). Fix
  introduces shared `fold_extended_const_i32` /
  `fold_extended_const_i64` helpers that walk all operators with a
  small stack-machine interpreter (i32/i64 add/sub/mul with wrapping
  semantics) and return the folded scalar. Regression pinned by 6
  tests covering all three arithmetic ops and the single-const
  passthrough. Surfaced by the post-v0.8.0 Mythos delta-pass sweep on
  the remaining 8 Tier-5 files (the protocol introduced in #151).

- **Resource graph + merger key-matching bugs** (LS-A-17, LS-A-18, LS-A-19;
  UCA-F-2 / UCA-M-9). Four sites in `meld-core` either dropped the
  interface dimension of `(component, interface, resource_name)` tuples
  or used substring/suffix matching where exact match was required:
  - `resource_graph.rs` definer purge ignored the iface when removing
    defines_cache entries, purging legitimate definers when an
    unrelated component imported a resource sharing the name.
  - `resource_graph.rs` terminal-exporter pass used over-broad
    `to_also_imports_resource` check that classified a component as a
    re-exporter if any of its imports carried any resource interface.
  - `resource_graph.rs` only registered resource nodes for
    `[resource-drop]X` imports on pure-consumer components; re-exporters
    that dropped a foreign resource had their drop calls invisible to
    the graph.
  - `merger.rs::add_unresolved_imports` dedup-skip path matched
    `imp.name.ends_with(rn)`, so two resources sharing a suffix (e.g.
    `float` / `bigfloat`) collided into the same tracking entry.
  All four led to silent cross-resource confusion or wrong-handle-table
  routing with no host trap. Fixes scope each comparison to the full
  `(comp, iface, rn)` tuple or use exact-match against the full
  `[resource-{rep,new,drop}]<name>` import string.

- **HashMap iteration non-determinism in resource / realloc fallbacks**
  (LS-A-15, UCA-M-10, H-7 / H-3 / H-4.3). Three sites resolved
  cross-component routing via `HashMap::iter().find(...)`, which picks
  an arbitrary entry per hash-seed-randomised iteration order. When
  multiple entries matched, the chosen entry varied per run —
  producing non-reproducible fused output bytes and, in some cases,
  routing a call to the wrong target. Affected:
  - `merger.rs::component_realloc_index` fallback when a component
    has multiple modules each with `cabi_realloc` — could pick a
    realloc bound to a different memory than the calling site.
  - `merger.rs` handle-table fallbacks at two sites — ties between
    candidate handle tables broken by iteration order.
  - `resolver.rs::resolve_resource_positions` last-resort fallback
    on `[resource-rep]` / `[resource-new]` prefix collisions.
  Fix: collect candidate keys, sort, pick `.first()`. Deterministic
  tie-breaking by lowest module index / smallest type-id /
  lexicographic key. Picks may still be semantically wrong if
  multiple distinct resources share a prefix (Step 6 alias propagation
  is the right structural mitigation), but the output is now
  reproducible across runs.

- **`flags<N>` canonical ABI silently modeled as `Record<N × Bool>`**
  (LS-A-20, UCA-P-10, H-4 / H-4.1). `parser.rs::convert_wp_defined_type`
  mapped a Component-Model `flags<N>` to `Record(N × Bool)`, so the
  downstream canonical-ABI helpers (`flat_count`,
  `canonical_abi_size_unpadded`, `canonical_abi_align`, etc.) computed
  flat=N, size=N bytes, align=1. The spec requires flat=ceil(N/32) i32
  words, size=ceil(N/8) padded to power-of-2 storage class, align ∈
  {1, 2, 4}. A function taking `flags<17>` crossed meld's params-ptr
  threshold (`total_flat_params > 16`) while the producer kept on the
  flat path — silent calling-convention mismatch between fused and
  composed paths. Bug shipped since March 2026 (~2 months, multiple
  releases). Fix adds `ComponentValType::Flags(Vec<String>)` variant,
  has the parser produce it directly, and adds explicit Flags arms to
  every canonical-ABI function that walks ComponentValType. Regression
  pinned by `ls_a_20_flags_canonical_abi_matches_spec` (covers
  N=1/8/9/17/32/33) and `ls_a_20_flags_parser_produces_flags_variant`.

- **P3 async detection: mixed-mode stackful, substring type classification,
  stream-write over-count** (LS-A-12, LS-A-13, LS-A-14). Three independent
  defects in `meld-core/src/p3_async.rs` surfaced by the post-v0.8.0 Mythos
  delta-pass.
  - `P3AsyncFeatures::uses_stackful_lift()` was derived as `uses_async_lift
    && !uses_callback_lift`, mis-classifying mixed-mode components (one
    callback-mode lift + one stackful-mode lift) as callback-only.
    Now tracks the stackful presence via a new independent
    `uses_stackful_lift_internal: bool` set per-lift in `detect_features`.
  - `StreamWriteResult::decode(ret, requested)` folded any
    `written >= requested` into `Complete { written }`, including the
    out-of-contract `written > requested` case. A buggy / hostile runtime
    returning `n > data_len` could drive callers to advance their cursor
    past the source buffer. Now classifies as `Unknown(ret)` so callers
    see a clear contract violation instead of silent corruption.
  - `detect_features` classified P3Async types via `desc.contains("stream")`
    / `desc.contains("future")`, so `future<stream<u8>>` matched "stream"
    first and landed in `stream_types`. Now classifies on the **root
    constructor** of the type description.

- **Wrapper drops source canonical options for lifts** (LS-A-16, UCA-W-2,
  H-1 / H-4). `component_wrap.rs::find_lift_type_for_interface_func`
  built a `{iface}#{func}` target export name but never compared it
  against anything, returning the first lift entry for every (iface,
  func) request. For multi-export components, every export silently
  received the first lift's type and canonical options (including
  `string_encoding`). A guest compiled with `--string-encoding=utf16`
  had every export's encoding downgraded to whatever the first lift
  declared. Same family as the wasmtime 2026-04-09 CM-transcoding CVE
  wave; silent mojibake / truncated strings, no trap. Fix routes lift
  lookup via export-name match (wit-bindgen `{iface}#{func}`
  convention) and propagates the source `CanonStringEncoding` through
  a new `source_string_encoding_option` helper. Lower-side encoding
  propagation and lift-side `Memory(0)` hardcoding in multi-memory
  mode remain deferred — they need additional source-memory-index
  threading and land in a follow-up under the same UCA.

### Added

- **Mythos delta-pass CI gate** (`.github/workflows/mythos-gate.yml`,
  `scripts/mythos/HOWTO-gate.md`). Blocks merge of PRs that modify
  Tier-5 source files (parser, merger, resolver, rewriter,
  component_wrap, p3_async, adapter/, resource_graph, segments) until
  the author records a Mythos delta-pass on the touched files —
  evidence as a PR comment plus the `mythos-pass-done` label.
  Motivated by LS-A-10 (CABI alignment padding in async-lift retptr
  writeback), which the v0.8.0 pre-release pass found but which had
  silently lived in the callback emitter since #128. A PR-time gate
  would have caught it at review time rather than at the release
  boundary. The gate does not automate the LLM-driven pass itself;
  that's tracked separately and requires API-key / cost design.

- **Stackful async-lift cross-memory `(ptr, len)` return** (SR-32 follow-up,
  sub-#94). The stackful trampoline emitter now handles the case where a
  stackful async lift returns a `string` or `list<T>` and the caller and
  callee live in different linear memories. v0.8.0 errored out on this
  path; v0.8.1 routes it through the same `emit_ptr_pair_result_writeback`
  helper the callback emitter uses — `cabi_realloc` in caller memory,
  cross-memory `memory.copy`, nested-indirection patch if the list
  element carries indirections, then `(new_ptr, len)` written to retptr.
  Both emitters now share the writeback contract single source of truth.
  Regression pinned by
  `stackful_ptr_pair_return_emits_realloc_memcopy_retptr_writes`.

## [0.8.0] — 2026-05-14

### Fixed

- **CABI alignment padding in async-lift retptr writeback** (LS-A-10,
  UCA-A-13, H-4 / H-4.5). Both `generate_async_callback_adapter` and
  `generate_async_stackful_adapter` advanced the retptr byte offset by
  only the flat size of each result global (4 or 8 bytes) and never
  aligned up to the next field's natural alignment. For any P3 async
  lift returning an aggregate whose flat lowering mixes 4- and 8-byte
  values (record `{u32, u64}`, tuple `(s32, s64)`, `result<u64, u32>`,
  etc.), the i64 / f64 field was stored at the wrong canonical-ABI
  offset and the caller's canon.lower read stale/zero bytes. Silent
  data corruption — wasm engines treat `MemArg.align` as a hint and
  do not trap. Fix extracts the writeback into a shared
  `emit_globals_to_retptr_cabi` helper that pads via `align_up` before
  each store. Surfaced by the v0.8.0 pre-release Mythos delta-pass on
  `adapter/fact.rs`; regression pinned by
  `cabi_alignment_stackful_retptr_writes_i64_at_offset_8`.

### Added

- **P3 stackful lifting — ABI foundation** (#140 / SR-32, sub-#94).
  Adds four new host-intrinsic imports under `pulseengine:async` —
  `thread_new`, `thread_switch_to`, `thread_yield`, `thread_exit` —
  exposed as `HostIntrinsic::Thread*` variants with pinned signatures
  and a new `thread` constants module. `P3AsyncFeatures::uses_stackful_lift()`
  returns true when a component declares `(canon lift ... async ...)`
  without a `(callback ...)` option. ADR-1 addendum (2026-05-13)
  documents the two-mode lifting policy and emission contract.
  Verified by `stackful_intrinsic_signatures_pinned` and
  `stackful_lift_is_async_without_callback`.

- **P3 stackful lifting — trampoline emitter** (#140 / SR-32, sub-#94).
  `FactStyleGenerator::generate_async_stackful_adapter` emits the
  adapter trampoline for async-lift exports that declare no
  `(callback ...)` option. The dispatcher routes async-lift sites
  based on the presence of a `[callback]<export>` companion in the
  merged module; absence routes to the stackful path. Shipped design
  is a direct call to the lift function — the runtime treats the call
  as a transparent fiber boundary, suspending on `task.wait` and
  resuming on awaited events. The Phase 1 `thread_*` ABI surface
  remains valid for component-internal concurrency but is not consumed
  by this trampoline. ADR-1 addendum 2026-05-13 (b) records why this
  design replaced the originally sketched `thread_new` + drive-loop
  approach (avoids per-export wrapper functions and per-export
  `$fiber_done` globals injected late in the adapter pass). Cross-
  memory `(ptr, len)` result returns from stackful mode are deferred
  to a follow-up under the same #140 and produce an explicit error
  for now. The step 0.5 cross-memory param copy was extracted into
  a shared `emit_param_copy_step` helper used by both callback and
  stackful paths (SR-12 / SR-17 contract single source of truth).
  Verified by `sr32_has_callback_export_detects_companion`,
  `sr32_stackful_emitter_handles_no_shim_with_default_results`, and
  `sr32_stackful_emitter_shape_pins_call_drop_globalget` (byte-scan
  pin on the emitted wasm shape).

## [0.7.0] — 2026-05-11

### Added

- **Explicit DWARF policy** (`DwarfHandling::{Strip, PassThrough}` on
  `FuserConfig`, default `Strip`). Phase 1.5 of issue #130
  (witness-mapping epic). Until Phase 2 ships an address-remap pass,
  passing input `.debug_*` sections through verbatim produces source-
  line attribution that points at wrong instructions in the merged code
  section — strictly worse than no DWARF for downstream MC/DC tooling
  (`pulseengine/witness`). The new default drops `.debug_*` sections;
  `PassThrough` is opt-in for the rare case a caller wants the lossy
  prior behaviour. Recorded in attestation `tool_parameters` as
  `dwarf_handling = "strip" | "passthrough"`. Verified by
  `meld-core/tests/dwarf_strip.rs`. Lands #135.

### Safety / STPA

- New approved loss scenario: **LS-CP-4** (DWARF passthrough emits
  address-incorrect debug info on fused output, [H-7]).

### Breaking

- Default DWARF handling changed: `.debug_*` sections are now dropped
  from fused output by default. Callers that previously relied on
  passed-through DWARF must opt in with
  `FuserConfig { dwarf_handling: DwarfHandling::PassThrough, .. }`,
  understanding that the addresses inside those sections do not match
  the merged code section.

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
