# Changelog

All notable changes to this project will be documented in this file.

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
