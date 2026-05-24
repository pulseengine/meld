# Changelog

All notable changes to this project will be documented in this file.

## [Unreleased]

### Changed

- **`list<option-with-pointer>` / `list<result<…,…>>` /
  `list<variant{…(string)…}>` now generate correct cross-component
  adapters** (LS-P-12 + LS-P-18 structural upgrade,
  `meld-core/src/resolver.rs`, `meld-core/src/parser.rs`,
  `meld-core/src/adapter/fact.rs`). v0.10 mitigated by panicking at
  adapter generation when these shapes appeared; v0.11 ships the
  proper per-element conditional pointer fixup. New `InnerPointer`
  descriptor on `CopyLayout::Elements.inner_pointers` (replaces the
  bare `(u32, CopyLayout)` tuple) carries a `Vec<DiscriminantGuard>`
  chain per inner pointer; `element_inner_pointers` in the parser
  now has `Option` / `Result` / `Variant` arms that recurse into the
  payload at the post-disc/aligned offset and append the enclosing
  discriminant to the chain; the FACT adapter's
  `emit_inner_pointer_fixup` per-element loop loads each guard's
  discriminant byte at element-relative offset, AND-evaluates the
  chain, and wraps the existing realloc + memory.copy + ptr-rewrite
  in an `If` so the fixup only fires when every enclosing arm
  holds. The LS-P-12 panic and the `has_pointer_bearing_conditional`
  helper are removed; the LS-P-12 / LS-P-18 regression tests are
  upgraded from `#[should_panic]` to structural assertions that pin
  the guarded `InnerPointer` shape. Mixed records (LS-P-18:
  `record { items: list<u8>, maybe: option<string> }`) now emit
  TWO inner pointers — one unconditional (the bare list field) and
  one guarded (the option payload). Fused adapters can now safely
  cross-memory-copy these common WIT types instead of refusing to
  generate.

- **UTF transcoders now emit U+FFFD instead of trapping on truncated input**
  (LS-P-16 + LS-P-19 upgrade, `meld-core/src/adapter/fact.rs`). v0.10
  closed two cross-memory leaks by trapping (`unreachable`) when
  `emit_utf16_to_utf8_transcode` encountered a lone high surrogate at
  end-of-input (LS-P-16) and when `emit_utf8_to_utf16_transcode`
  encountered a truncated multi-byte lead (LS-P-19, three sites for
  the 2/3/4-byte branches). The Canonical ABI's correct behaviour for
  malformed UTF input is **lossy replacement**, not abort. Both
  emitters now set `cp_local = 0xFFFD` and consume only the lead /
  lone code unit; the existing UTF-8 / UTF-16 encoders handle
  `0xFFFD` directly (3-byte UTF-8 `EF BF BD` / single UTF-16 BMP
  code unit). Fused adapters are now spec-compliant on malformed
  input rather than refusing to run. LS-P-16 and LS-P-19 regression
  tests updated to pin the new `I32Const(0xFFFD)` emission at all
  four sites.

## [0.10.0] - 2026-05-24

### Fixed

- **UTF-8→UTF-16 transcoding read 1–3 bytes past the input buffer for
  truncated multi-byte UTF-8 sequences — silent cross-memory leak,
  mirror of LS-P-16** (LS-P-19, UCA-P-3, H-2 / H-4 / H-4.4,
  `meld-core/src/adapter/fact.rs`). `emit_utf8_to_utf16_transcode`'s
  outer loop bounds-checked only the lead byte; each multi-byte
  branch then unconditionally read its continuation bytes at
  `src_idx + 1`/`+2`/`+3`. A UTF-8 string ending on a truncated
  multi-byte lead (e.g. a bare `0xE2` at the buffer tail) caused the
  adapter to load up to 3 bytes of attacker-adjacent caller memory,
  fold them into a synthesized code point, and emit the result as
  UTF-16 into the callee output. Conservative mitigation prepends a
  `src_idx + N >= input_len` `unreachable` trap to each multi-byte
  branch (N = 1/2/3). Promoted to approved loss scenario
  **LS-P-19** (priority high). Regression pinned by
  `ls_p_19_utf8_to_utf16_continuation_byte_oob_guard_emitted`.

- **LS-P-12 bypassed when a record mixed a covered pointer with a
  hidden conditional one — silent cross-memory dangling pointers in
  callee elements** (LS-P-18, UCA-P-3, H-4 / H-4.2,
  `meld-core/src/parser.rs`). The original LS-P-12 guard in
  `copy_layout(List(inner))` fired only when
  `element_inner_pointers(inner, 0)` was empty AND `inner` contained
  pointers. A record/tuple that mixed a covered field (bare
  `string`/`list`) with a hidden conditional pointer field (e.g.
  `option<string>`) made `element_inner_pointers` return a non-empty
  Vec from the covered field — the LS-P-12 panic didn't fire, and
  `copy_layout` produced `CopyLayout::Elements` whose
  `inner_pointers` omitted the option-payload pointer. The FACT
  adapter then never fixed up the conditional payload across
  memories, leaving callee elements with stale string pointers per
  `Some(_)`. Fix replaces the emptiness-based guard with a deep
  recursive `has_pointer_bearing_conditional(inner)` check (new
  helper) that walks Option / Result / Variant arms reachable
  through Records, Tuples, FixedSizeLists, and `Type` aliases. If
  any pointer-bearing conditional exists, `copy_layout(List(inner))`
  panics with the LS-P-18 marker. Promoted to approved loss scenario
  **LS-P-18** (priority high). Regression pinned by
  `ls_p_18_mixed_record_with_option_string_bypasses_p12_then_refuses`
  + positive sanity test
  `ls_p_18_pure_bare_pointer_record_still_works`.

- **Caller-encoding name match filtered on `ComponentTypeRef::Func`
  only, miscalibrated `string_transcoding` for mixed-encoding
  callers — defensive warn-before-heuristic** (LS-P-17, UCA-R-3,
  H-4 / H-4.4, `meld-core/src/resolver.rs`). Two structurally-
  identical lookup loops (primary around lines 2877–2910, fallback
  around 3175–3225) filtered `from_component.imports` on
  `ComponentTypeRef::Func(_)` to find a caller's `Lower` options
  for the resolved interface. WIT interface imports lower to
  `ComponentTypeRef::Instance(_)`, so the loops **never matched**
  for typical wit-component / wasm-tools output and fell through to
  a heuristic `caller_lower_map.iter().min_by_key(|(k, _)| **k)`
  that picked the lowest-indexed Lower's encoding for **every**
  interface. For single-encoding callers (the common case) this
  happens to be correct; for mixed-encoding callers (UTF-16 for one
  interface, UTF-8 for another — e.g. JS/.NET host components) the
  heuristic miscalibrated `string_transcoding` across the board,
  silently scrambling strings at one or more call boundaries.
  **Mitigation only**: detect mixed-encoding callers (`values()`
  not all identical) before the heuristic and emit a `log::warn!`
  with the LS-P-17 marker and the interface name. The full
  structural per-interface attribution (Instance-aliased func
  indices or per-interface lookup) is tracked as follow-up. **A
  confirmed Mythos finding** — surfaced by the mythos-auto
  delta-pass on PR #179, clean-room verified. Promoted to approved
  loss scenario **LS-P-17** (priority low — bug is latent for
  single-encoding callers). Regression pinned by
  `ls_p_17_mixed_caller_encoding_warns_before_heuristic_fallback`.

- **UTF-16→UTF-8 transcoding read 2 bytes past the input buffer on a
  lone high surrogate at the end of a UTF-16 string — silent
  cross-memory leak of adjacent caller bytes into the callee's UTF-8
  output** (LS-P-16, UCA-P-3, H-2 / H-4 / H-4.4,
  `meld-core/src/adapter/fact.rs`).
  `emit_utf16_to_utf8_transcode`'s only bounds check was
  `src_idx >= input_len` against the *first* code unit per iteration.
  When that code unit was a high surrogate (`[0xD800, 0xDC00)`), the
  surrogate-pair `If` arm unconditionally emitted a second
  `I32Load16U` at `mem16[ptr + (src_idx + 1) * 2]`. For input whose
  last code unit was a lone high surrogate, that load read 2 bytes
  past the caller-supplied UTF-16 buffer; those 2 attacker-adjacent
  bytes were treated as the "low surrogate" without validating
  `0xDC00 <= cu2 < 0xE000` and packed into a 4-byte UTF-8 sequence
  written to callee memory — silent cross-memory leak per
  transcoded string. `src_idx += 2` advanced past `input_len`, so
  the outer break check cleanly terminated the loop, no trap,
  silent corruption. **Conservative mitigation only**: inject an
  inline `src_idx + 1 >= input_len` check inside the surrogate-pair
  `If` arm and `unreachable`-trap on failure. The Canonical-ABI-
  correct behaviour replaces the lone surrogate with U+FFFD
  (3-byte UTF-8 `EF BF BD`) and continues; that upgrade is tracked
  as a separate structural follow-up. **A confirmed Mythos
  finding** — surfaced by the mythos-auto delta-pass on PR #179,
  independently clean-room verified. Promoted to approved loss
  scenario **LS-P-16** (priority high). Regression pinned by
  `ls_p_16_utf16_lone_high_surrogate_oob_guard_emitted`, a
  structural test that requires the LS-P-16 marker AND an
  `Unreachable` + `I32GeU` opcode pair to live inside the
  surrogate-pair `If` arm before the second `I32Load16U`.

- **Out-of-bounds `resource_type_id` silently misclassified as
  callee-defined — `[resource-rep]` / `[resource-new]` swap on the
  fused adapter** (LS-P-15, UCA-R-3, H-5 / H-1,
  `meld-core/src/resolver.rs`). `resolve_resource_positions` decided
  callee-vs-caller resource ownership via
  `.get(pos.resource_type_id as usize).map(|def| !matches!(def,
  ComponentTypeDef::Import(_))).unwrap_or(true)`. When the id
  exceeded `component_type_defs.len()` (stale id, alias remap past
  the local table, malformed input), `.get(...) → None` and
  `.unwrap_or(true)` silently classified the resource as
  *callee-defined* with no warning — the adapter emitted a
  `[resource-rep]` call where `[resource-new]` was correct (or vice
  versa), swapping the two resource-handle conversion sides on every
  fused cross-component call passing that handle. The handle
  type-checks on both sides, so the validator doesn't catch it.
  Reachability is bounded — the instance-graph path keys
  `resource_type_id` through validated parser-produced indices —
  making this **defensive hardening**, not a memory-safety
  emergency. Replaces the `unwrap_or(true)` with an explicit `match`:
  on `None`, emit `log::warn!` and `continue` so the position is
  dropped instead of silently misclassified; the downstream adapter
  will surface a loud missing-fixup error at adapter generation
  rather than silently swap. **A confirmed Mythos finding** —
  surfaced by the mythos-auto delta-pass on PR #179. Promoted to
  approved loss scenario **LS-P-15** (priority low). Regression
  pinned by
  `ls_p_15_out_of_bounds_resource_type_id_is_dropped_not_misclassified`.

- **Nested-list inner copy `buf_len = len * sub_elem_size` missed the
  overflow guard** (LS-P-14, UCA-P-3, H-2 / H-4 / H-4.1,
  `meld-core/src/adapter/fact.rs`).
  `emit_patch_nested_indirections` — the per-element fixup loop for a
  list-of-records (or tuples) — computed the byte count for each inner
  list's `cabi_realloc` + `memory.copy` by loading the callee's
  `len` field and multiplying by `sub_elem_size` with a bare
  `i32.mul`. `i32.mul` is modulo 2³², so a callee-supplied `len` near
  `u32::MAX / sub_elem_size` wrapped `buf_len` to a small value;
  the subsequent `old_ptr + buf_len > mem_bytes` bounds check used
  `i32.add` (also wrapping) and was bypassed. The adapter then
  allocated/copied only the wrapped byte count while the caller-side
  bulk copy of the outer element kept the original large `len` —
  silent inner-list truncation, plus OOB read/write into adjacent
  caller-allocated memory on every dereference past the truncated
  edge. The `emit_overflow_guard` helper (added as the LS-A-7 leg
  (a) fix for the outer copy paths) was never retrofitted to the
  inner copy. Fix stashes the loaded `len` into the existing
  `l_buf_len` scratch local, calls `emit_overflow_guard(body,
  l_buf_len, sub_elem_size as u32)` to trap via `unreachable` on
  wrapping, then re-fetches the local for the multiplication.
  **A confirmed Mythos finding** — surfaced by the mythos-auto
  delta-pass on PR #179. Promoted to approved loss scenario
  **LS-P-14** (priority high). Regression pinned by
  `ls_p_14_nested_list_inner_copy_emits_overflow_guard`, which
  emits a synthetic patch loop for `record { items: list<u32> }`
  (`sub_elem_size = 4`) and asserts the encoded function body
  contains an `Unreachable` opcode (the only place that opcode
  appears along this path is inside `emit_overflow_guard`).

- **Async adapter param-copy treated every consecutive `(i32, i32)`
  pair as a pointer pair, corrupting plain integer args** (LS-P-13,
  UCA-P-3, H-2 / H-4 / H-4.1,
  `meld-core/src/adapter/fact.rs`). The P3-async lift adapter
  (`emit_param_copy_step`, called from
  `generate_async_callback_adapter` /
  `generate_async_stackful_adapter`) walked `caller_type.params`
  looking for adjacent `(i32, i32)` slots and gated each match on
  `pointer_pair_positions.iter().any(|_| true)` — semantically
  `!is_empty()`. Every adjacent integer-pair argument was rewritten
  via `cabi_realloc` + cross-memory `memory.copy` as if it were a
  `(ptr, len)` string/list, using one integer as the source pointer
  and the other as the byte count. For `fn f(a, s: string, b, c)`
  the buggy code copied `(a, ptr_s)` and `(len_s, b)` as
  pointer-pair slots and missed the real string at flat index 1 —
  callee saw corrupted integer args, the real string was never
  copied, and `memory.copy` read from caller-memory addresses
  influenced by the caller. The resolver's
  `pointer_pair_param_positions` already returns the correct *flat*
  indices (computed via `flat_count`), and canonical lowering
  preserves param order between caller and callee component types —
  the heuristic walk's claim of a caller/callee mismatch was
  misleading. Replaces the whole walk with
  `site.requirements.pointer_pair_positions.clone()`. **A confirmed
  Mythos finding** — surfaced by the mythos-auto delta-pass on PR
  #179, clean-room verified. Promoted to approved loss scenario
  **LS-P-13** (priority high); regression pinned by
  `ls_p_13_pointer_pair_param_positions_is_flat_indices_not_just_nonempty`.

- **`list<option<string>>` / `list<result<string, _>>` / `list<variant
  with string payload>` silently produced stale cross-memory pointers
  in callee elements — defensive refusal (partial mitigation)** (LS-P-12,
  UCA-P-3, H-4 / H-4.2, `meld-core/src/parser.rs`).
  `element_inner_pointers` (the helper that builds the per-element
  inner-pointer descriptor consumed by `CopyLayout::Elements`) has no
  arms for `Option` / `Result` / `Variant` — its match falls through
  to `_ => {}`. So `copy_layout(list<option<string>>)` (and the
  Result/Variant analogues) classified as `CopyLayout::Bulk {
  byte_multiplier }` with no per-element pointer walk — even though
  `type_contains_pointers(option<string>) == true`. The FACT adapter's
  Bulk path is a flat `memory.copy(dst, src, len * byte_mult)` with
  no per-element fixup, so every option's `(ptr, len)` pair was copied
  verbatim into the callee — `ptr` still referencing the *source*
  component's memory. The callee then dereferenced a wild pointer for
  each `Some(...)` element. **Mitigation only**: `copy_layout` now
  detects the smoking gun (`element_inner_pointers` empty AND
  `type_contains_pointers(inner)`) and panics with a clearly-labelled
  `LS-P-12: …` message at adapter-generation time, converting silent
  cross-memory dangling-reference into a loud refusal. The full
  structural fix — Option/Result/Variant arms on `element_inner_pointers`,
  per-element `DiscriminantGuard` chains on the inner-pointer
  descriptor, and adapter-side per-element guard evaluation
  (structurally analogous to LS-P-10 on the list-element axis) — is
  tracked as follow-up. **A confirmed Mythos finding** — surfaced by
  the mythos-auto delta-pass on PR #179, clean-room verified.
  Promoted to approved loss scenario **LS-P-12** (priority high).
  Regression pinned by
  `ls_p_12_list_of_option_string_refuses_rather_than_silently_corrupts`,
  `ls_p_12_list_of_result_string_refuses`, and a positive sanity test
  `ls_p_12_pure_scalar_option_list_is_still_bulk` that pins the check
  is gated on `type_contains_pointers(inner)`.

- **Flat-name resolver silently overwrote duplicate module exports**
  (LS-P-11, UCA-R-3, H-5 / H-1, `meld-core/src/resolver.rs`,
  `meld-core/src/error.rs`). `resolve_via_flat_names` built its export
  index with a blind `HashMap::insert(key, …)` where `key` is the flat
  export name. When two core modules within one component both
  exported the same name, the second silently overwrote the first
  (last-writer wins), routing any importer of that name to the wrong
  module with no error or warning. The instance-graph resolver
  (taken whenever the component has an `InstanceSection`, which
  `wit-component` / `wasm-tools` always emit for multi-module
  components) is immune; the vulnerable path is practically
  unreachable for production components, **defensive hardening** for
  the synthetic-fixture and legacy single-module fallback shapes.
  Replaces the blind insert with an explicit collision check that
  returns a new `Error::DuplicateModuleExport { component_idx,
  export_name, first_module_idx, second_module_idx }`, mirroring the
  existing `DuplicateModuleInstantiation` pattern. **A confirmed
  Mythos finding** — clean-room verified, promoted to approved loss
  scenario **LS-P-11** (priority `low`); regression pinned by
  `ls_p_11_duplicate_flat_name_export_is_rejected`.

- **Nested conditional pointer pair omitted outer-discriminant guard —
  arbitrary cross-component read with attacker-controlled `(ptr, len)`**
  (LS-P-10, UCA-P-3, H-2 / H-4 / H-4.2, `meld-core/src/parser.rs`,
  `meld-core/src/resolver.rs`, `meld-core/src/adapter/fact.rs`). For a
  pointer-containing type nested inside an option/result/variant arm
  — `result<option<string>, u32>`,
  `variant { a(option<string>), b(u32) }`, `option<option<string>>`,
  etc. — `collect_conditional_pointers` /
  `collect_conditional_result_pointers` emitted a
  `ConditionalPointerPair` guarded **only** on the innermost
  discriminant. The four FACT adapter consumer loops processed each
  pair independently: load disc → compare to value → fire copy. When
  the runtime value was `Err(v: u32)` (or any sibling arm whose payload
  type is something else), the byte at the option's discriminant slot
  was actually the `u32` payload; if those bytes happened to read as
  `1`, the adapter sampled the adjacent slots as a `(ptr, len)` string
  pair and ran `cabi_realloc` + `memory.copy` with attacker-controlled
  source pointer and length — **an arbitrary cross-component memory
  read** that also hands the callee a forged string pointer pointing
  into the freshly allocated buffer. New `DiscriminantGuard` struct +
  `outer_guards: Vec<DiscriminantGuard>` field on
  `ConditionalPointerPair`; both collectors thread the enclosing
  discriminant chain through their recursion and stamp it onto each
  emitted pair. Two new fact-adapter helpers
  (`emit_conditional_guard_chain_flat` /
  `emit_conditional_guard_chain_byte`) emit each guard's `(load disc,
  I32Const value, I32Eq)` and `I32And` them before the existing `If` /
  copy block. The innermost guard stays in the existing
  `discriminant_*` fields, so single-level conditionals (empty
  `outer_guards`) behave identically. **A confirmed Mythos finding** —
  surfaced by the mythos-auto delta-pass on PR #179, independently
  clean-room-verified as a real memory-safety hazard, promoted to
  approved loss scenario **LS-P-10**; regression pinned by
  `ls_p_10_nested_conditional_pointer_carries_outer_guard_chain`.

- **`total_flat_params` used `Iterator::sum::<u32>()` instead of a
  saturating fold** (LS-P-9, UCA-P-3, H-2 / H-4,
  `meld-core/src/parser.rs`). The Component Model canonical ABI picks
  the calling convention from `total_flat_params`: `<=
  MAX_FLAT_PARAMS` (16) → flat; `>` → params-ptr. `flat_count` for a
  `FixedSizeList` is `flat_count(elem).saturating_mul(len)`
  (LS-P-4), so a nested `FixedSizeList` can produce a per-param
  `flat_count` of `u32::MAX`. A bare `.sum()` over `u32` then panics
  in debug on `u32::MAX + 1` and **wraps to a small value** in
  release; the wrapped total compares `<= 16` and the adapter selects
  the flat convention for a function that genuinely needs params-ptr
  — call-site lowering and callee-side lifting disagree on the ABI
  slot. The sibling area-size accumulators inside
  `params_area_byte_size` / `return_area_byte_size` already use
  `saturating_add` (LS-P-6); this calling-convention picker was
  missed. Replaces `.sum()` with `.fold(0u32, u32::saturating_add)`.
  **A confirmed Mythos finding** — surfaced by the mythos-auto
  delta-pass on PR #179, promoted to approved loss scenario
  **LS-P-9**; regression pinned by
  `ls_p_9_total_flat_params_saturates_across_params`.

- **Record/tuple field-walk added the unpadded child size, undercounting
  every offset and size built on it** (LS-P-8, UCA-P-3,
  H-4 / H-4.1 / H-4.2, `meld-core/src/parser.rs`). The Component Model
  canonical ABI lays out a record/tuple as `s = 0; for each field f:
  s = align_to(s, alignment(f)); s += size(f)`, where `size(f)` for an
  aggregate field is its *full padded* size. In this codebase the full
  padded size is `canonical_abi_element_size`; `canonical_abi_size_unpadded`
  is the outer type *without* its own trailing align-up. Roughly 25
  field-walk sites — the `Record` / `Tuple` arms of
  `canonical_abi_size_unpadded`, `collect_pointer_byte_offsets`,
  `collect_pointer_byte_offsets_with_layout` (the LS-P-7 helper),
  `collect_conditional_result_pointers`, `collect_return_area_type_slots`,
  `collect_resource_byte_positions`, `element_inner_pointers`,
  `element_inner_resources`, plus the top-level params/results walks in
  `params_area_byte_size`, `return_area_byte_size`,
  `pointer_pair_params_byte_offsets`, `pointer_pair_result_offsets`,
  `params_area_slots`, `return_area_slots`,
  `resource_params_area_positions`, `resource_result_positions`, and
  `conditional_pointer_pair_result_positions` — advanced the running
  offset by `canonical_abi_size_unpadded(field)` instead of
  `canonical_abi_element_size(field)`. The per-field `align_up` on the
  next field does NOT re-absorb the preceding field's omitted trailing
  pad when the next field has *smaller* alignment, so a
  `tuple<record { u32, u8 }, u8>` came out with `_unpadded` 6 and
  `element_size` 8 instead of the spec's 9 / 12, and a `list<u32>`
  following `record { u32, u8 }` was located at offset 5 instead of 8.
  Wrong field offsets flow into the FACT adapter's pointer-pair load,
  list-copy byte length, and inner pointer-fixup walk; the area-size
  callers under-size the `cabi_realloc` buffer (LS-P-6 hazard class
  reached via the per-field primitive rather than the cross-field `+=`).
  Fix replaces `canonical_abi_size_unpadded(field)` with
  `canonical_abi_element_size(field)` at the 25 field-walk sites;
  `canonical_abi_size_unpadded` itself still returns the outer size
  minus its own trailing pad (its contract is unchanged —
  `canonical_abi_element_size` recovers the pad). **A confirmed Mythos
  finding** — surfaced by the mythos-auto delta-pass on PR #179, with
  the auto-runner mis-locating the bug as the option/variant/result
  payload contribution (which is actually spec-correct); independent
  clean-room verification corrected the location to the Record/Tuple
  field accumulation. Promoted to approved loss scenario **LS-P-8**;
  regression pinned by
  `ls_p_8_record_tuple_field_accumulation_uses_padded_field_size`.

- **Conditional-pointer `CopyLayout` computed for the composite payload,
  not the pointer leaf** (LS-P-7, UCA-P-3, H-4 / H-4.1 / H-4.2,
  `meld-core/src/parser.rs`). `collect_conditional_pointers` (flat-param
  path) and `collect_conditional_result_pointers` (retptr byte-offset
  path) emit one `ConditionalPointerPair` per pointer leaf inside an
  `option` / `result` / `variant` payload. They enumerated each leaf's
  position correctly but computed the `CopyLayout` once by calling
  `copy_layout` on the *whole payload type* and reusing it for every
  position. `copy_layout` only special-cases a bare `string` / `list`;
  any composite payload (`record`, `tuple`, `fixed-length-list`) fell
  to its `_ => Bulk { byte_multiplier: 1 }` fallback. So a `list<u64>`
  leaf inside `option<tuple<u32, list<u64>>>` or
  `result<record { items: list<u64> }, E>` was tagged `Bulk { 1 }`
  instead of `Bulk { 8 }` — the adapter copies `len * 1` bytes, a 7/8
  silent under-copy — and a pointer-containing `list<string>` leaf,
  whose correct layout is `Elements` with recursive inner-pointer
  fixup, collapsed to flat `Bulk`, dropping the fixup so the callee
  dereferences pointers still addressing the source memory (the LS-R-2
  misclassification class, on the conditional path). New
  `collect_pointer_positions_with_layout` /
  `collect_pointer_byte_offsets_with_layout` helpers carry each
  String/List leaf's own `CopyLayout` alongside its position; the now
  dead `copy_layout_for_string_or_list_at` shim is removed. **A
  confirmed Mythos finding** — surfaced by the mythos-auto delta-pass
  on PR #179, promoted to approved loss scenario **LS-P-7**; regression
  pinned by
  `ls_p_7_conditional_pointer_layout_is_per_leaf_not_per_composite`.

- **Area-size accumulators wrapped, undoing `canonical_abi_size_unpadded`
  saturation** (LS-P-6, UCA-P-3, H-2 / H-4 / H-4.1,
  `meld-core/src/parser.rs`). `params_area_byte_size` and
  `return_area_byte_size` accumulated each field with a bare
  `size += canonical_abi_size_unpadded(ty)`. `canonical_abi_size_unpadded`
  saturates to `u32::MAX` for a pathological `fixed-length-list`
  (LS-P-4), but the LS-P-4 fix did not reach these two cross-field
  accumulators: once a first field saturated `size`, the next field's
  `+=` overflowed — a debug build panics, a release build wraps
  `u32::MAX` down to a small value. The resolver stores that wrapped
  value as `params_area_byte_size`; the FACT adapter passes it to
  `cabi_realloc`, under-allocating the params buffer and then writing
  every parameter into it — an OOB write into callee memory. The
  sibling Record/Tuple accumulators inside `canonical_abi_size_unpadded`
  already used `saturating_add`; these two were missed. Both `+=`
  sites are now `size.saturating_add(...)`. **A confirmed Mythos
  finding** — surfaced by the mythos-auto delta-pass on PR #179,
  validated with a panicking PoC, promoted to approved loss scenario
  **LS-P-6**; regression pinned by
  `ls_p_6_area_byte_size_saturates_across_fields`.

- **`flat_byte_size` underestimated `result`/`variant` flat width**
  (`meld-core/src/parser.rs`). Surfaced by the mythos-auto delta-pass
  on PR #178: `flat_byte_size` computed the payload of `result<T,E>`
  and `variant` as `max(flat_byte_size(arm))` rather than the
  Component Model's element-wise `flatten_variant` JOIN. When two
  arms flatten to a different *number* of core values, `max` of byte
  totals underestimates — `result<u64, string>` returned 12 where
  the joined sequence `[i32, i64, i32]` is 16. Rewrites
  `flat_byte_size` over a new `flat_width_list` helper that
  materialises each type's flat core-value width list and JOINs
  variant arms element-wise; non-variant types are unchanged. The
  helper caps its list length (`FLAT_WIDTH_CAP`) so a pathological
  nested `fixed-length-list` still saturates to `u32::MAX` rather
  than allocating an unbounded `Vec` (preserves the LS-P-4
  saturation contract). This is correctness hygiene on a `pub fn`:
  the mythos-auto finding's claimed OOB-write impact was rejected on
  validation — `flat_byte_size` has no in-tree consumers, so there
  is no reachable hazard and no LS-N entry; a future consumer would
  nonetheless have inherited the wrong value.

### Added

- **Regression guard for the `parse_core_module` section-range
  invariant** (issue #174 Step 5, `meld-core/src/parser.rs`). The
  v0.5 post-ship Mythos sweep flagged an unverified LS-P-5-sibling
  hypothesis: `parse_core_module` stores `reader.range()` for the
  element/data sections and `parse_element_segments` /
  `parse_data_segments` slice `module.bytes[start..end]` from it
  without an explicit bounds check. Mythos delta-pass verdict:
  **NO FINDINGS**. Unlike `ModuleSection::unchecked_range` (the
  LS-P-5 site), a core-module element/data section is only framed
  once `wasmparser` has its declared bytes — a truncated section
  makes `parse_all` yield an `Err`, propagated by
  `parse_core_module`'s `payload?`, so no out-of-bounds range is
  ever stored. Adds `truncated_core_section_errors_rather_than_yielding_oob_range`
  to pin that `wasmparser` framing guarantee: if a future bump
  changes it, the test fails and the hypothesis reopens.

### Changed

- **`meld fuse` warns when the `multi` memory default is used**
  (issue #172, `meld-cli`). The default `--memory multi` produces a
  multi-memory core module that `wasm-opt` rejects without
  `--enable-multimemory` and that has no single-address-space (MCU)
  lowering for `synth`. A user on the happy path
  (`meld fuse a b -o fused.wasm`) previously hit that wall silently
  at the next tool. `meld fuse` now prints a warning naming the
  downstream implication and pointing at
  `--memory shared --address-rebase`, and the `--memory` help text
  documents it. The *default itself* is intentionally left at
  `multi` — flipping it is a high-blast-radius change, and `shared`
  carries its own caveat (broken under `memory.grow`, currently
  labelled "legacy mode"), so the default flip is deferred as a
  separate decision (#172 option 1) rather than made here.

## [0.9.0] — 2026-05-20

### Fixed

- **mythos-auto aggregate job: `gh` → `curl`**
  (`.github/workflows/mythos-auto.yml`). The `aggregate` job composed
  the sticky PR comment and applied the `mythos-pass-done` label via
  `gh api` / `gh pr edit`, but the GitHub CLI is not installed on the
  `light` runner — the step exited 127 (`gh: command not found`),
  blocking the label even when the Mythos scan returned NO_FINDINGS.
  Rewrites both the comment upsert and the label apply with `curl`
  against the REST API (`curl` + `jq` are universally present). The
  markdown body is JSON-encoded with `jq -Rs '{body: .}'` so nothing
  in the model-authored hypothesis text can break the request. Also
  registers `meld-core/src/p3_stream.rs` in the Mythos Tier-5 path
  lists (`mythos-gate.yml`, `mythos-auto.yml`) — deferred from #173,
  which could not modify `mythos-auto.yml` and still be scanned by
  it (claude-code-action self-validates the invoking workflow against
  `main`). This PR touches only the workflow files, so its own
  auto-runner detect job finds no Tier-5 source and skips the scan.

### Added

- **Cross-component `stream<T>` pairing detection** (issue #141,
  ADR-3, `meld-core/src/p3_stream.rs`). Foundation for the in-module
  stream adapter: when meld fuses two components that share a
  `stream<T>` endpoint, today both sides still route every chunk
  through host `pulseengine:async` imports. This PR adds the
  detection half — a `StreamPairGraph` built at resolve time that
  inventories which fused components form producer → consumer stream
  pairings. The graph is attached to `DependencyGraph` next to the
  resource graph. A `StreamPair` is a conservative *candidate*: it is
  recorded only when two fusion-connected components have
  complementary roles (one `StreamWrite`, one `StreamRead`) on a
  stream of the **same element type** — pairing on matching element
  type is the line between an honest candidate and a hallucinated
  one. The ring-buffer (same-memory) and copy-chain (cross-memory)
  adapter *emitter* is a runtime-verified follow-up (ADR-3 Path N);
  cross-component stream codegen is only correct once executed on a
  real runtime, so it is deliberately not in this PR. ADR-3 records
  the design; SR-33's detection half is satisfied here, the codegen
  half by the follow-up. 9 unit tests including the 4 ADR-3 gating
  fixtures. Registering `p3_stream.rs` in the Mythos Tier-5 path
  lists is a separate follow-up — claude-code-action self-validates
  that the invoking workflow matches `main`, so a PR cannot both
  modify `mythos-auto.yml` and be scanned by it.

### Changed

- **CI workflows now skip on docs/safety-only changes**
  (`.github/workflows/{bench,fuzz,ci}.yml`). Adds conservative
  `paths-ignore` filters to bench, fuzz, and ci workflows: PRs that
  only edit Markdown, `safety/`, `scripts/mythos/`, or
  `tools/*.py` skip the rust-cpu-hungry jobs (~9 jobs saved per
  docs-only PR). The LS-N gate, mythos-gate, and mythos-auto
  workflows are untouched — they need to keep firing on those very
  paths (`safety/stpa/loss-scenarios.yaml` is what the LS-N gate
  reads). Substantive code PRs are unaffected. Pulls meld's
  footprint on the shared smithy fleet down without losing
  regression signal on real changes.

### Fixed

- **LS-A-8 regression coverage** (`meld-core/src/adapter/fact.rs`).
  PR f0e981b fixed the `resource_rep_imports.values().next()`
  HashMap-iteration-order bug in `analyze_call_site` (inner-list
  borrow rep_func selection) by threading a pre-resolved
  `rep_import: Option<(String, String)>` through `InnerResource` and
  looking up per-type. The fix landed without a dedicated
  regression test; the LS-N verification gate surfaced this as the
  **last** missing-bucket entry. Adds two tests:
  `ls_a_8_inner_list_rep_func_selected_by_type_not_iteration_order`
  (adversarial 2-resource list, asserts per-byte-offset fixups map
  to the correct rep_func — sampled 32× to make any residual
  HashMap-order leak observable) and
  `ls_a_8_no_rep_import_skips_fixup_rather_than_picking_arbitrary`
  (pins the `rep_import=None` skip-with-warning path against the
  pre-fix arbitrary-fallback regression). Gate verdict moves from
  18/19 verified to **19/19 — full coverage**. The advisory
  missing-bucket is now empty.

- **Fuzz smoke `sanitizer is incompatible with statically linked
  libc` recurrence** (`.github/workflows/fuzz.yml`, #168). The
  toolchain install was requesting `x86_64-unknown-linux-musl` as
  an extra target. cargo-fuzz's `--release` reuse path can pick up
  that musl target on cache restore, and musl statically links libc
  which is incompatible with the AddressSanitizer cargo-fuzz
  injects. The fuzz_parse_component / fuzz_resolver_terminates
  failures attributed to runner config-drift (#139 §3) were
  actually workflow-side: same failure on the "good" runner-7 once
  the musl cache hit. Drops the `targets: x86_64-unknown-linux-musl`
  line and version-bumps the `actions/cache` key to `v2-` to
  invalidate any contaminated snapshots. Root-cause analysis
  contributed by smithy team on the #168 thread.

- **mythos-auto.yml missing `id-token: write` permission**
  (`.github/workflows/mythos-auto.yml`). After the unzip block on
  rust-cpu runners cleared (#167), the next mythos-auto run
  surfaced a third plumbing issue: claude-code-action calls
  `core.getIDToken()` early in `setupGitHubToken`, which requires
  the OIDC token issuer URL. Without `id-token: write` in
  `permissions:`, the action gets "Unable to get
  ACTIONS_ID_TOKEN_REQUEST_URL env variable" and aborts before
  running its prompt. Adds the permission with an inline comment
  explaining the requirement. Discovered by PR #169's matrix scan
  on the now-unzip-fixed runner image.

- **LS-A-9 regression coverage** (`meld-core/src/adapter/fact.rs`).
  PR fixed the callback-mode `if code == WAIT` branch that silently
  treated `POLL (3)` as a YIELD fall-through (dropping host-ready
  events on the callback handshake), but landed without a dedicated
  test. The LS-N verification gate surfaced this gap. Adds
  `ls_a_9_callback_adapter_dispatches_both_wait_and_poll`, which
  drives `generate_async_callback_adapter` end-to-end against a
  minimal merged-module fixture (lift func + `[callback]` companion
  + `[waitable-set-poll]` import) and asserts the emitted body
  contains the canonical `i32.const 2 / i32.eq / local.get … /
  i32.const 3 / i32.eq / i32.or` byte sequence in order. Gate
  verdict moves from 17/19 verified to **18/19** — only LS-A-8 left
  in the missing bucket. **First PR to touch a Tier-5 file** since
  `mythos-auto.yml`'s plumbing fixes (#164), so this also serves as
  the auto-runner's first true end-to-end matrix-scan smoke test.

- **LS-CP-4 regression coverage + LS-N gate integration-test scan**
  (`tools/run_ls_verification.py`,
  `meld-core/tests/dwarf_strip.rs`). The LS-N verification gate was
  previously invoking `cargo test --lib`, which filtered out
  integration tests under `<package>/tests/`. Three pre-existing
  tests in `dwarf_strip.rs` (`default_strips_dwarf`,
  `passthrough_preserves_dwarf`, `default_is_strip`) already pin
  LS-CP-4 ("DWARF passthrough emits address-incorrect debug info on
  fused output") via Phase 1.5's Strip-default policy, but the gate
  reported the entry as missing because the test names didn't match
  the `ls_cp_4_*` convention AND the integration-test binary
  wasn't being scanned. Adds three convention aliases delegating to
  the existing test bodies, and drops `--lib` from the gate runner
  so both lib and integration tests participate. Gate verdict moves
  from 16/19 verified to **17/19 verified**; remaining
  missing-bucket entries are LS-A-8 and LS-A-9 (both need
  net-new tests, not aliases).

- **LS-A-19 regression coverage** (`meld-core/src/merger.rs`). PR #156
  fixed the `imp.name.ends_with(rn)` suffix-collision bug
  (`float` / `bigfloat` cross-resource confusion) but landed without
  a regression test. The LS-N verification gate (#161) surfaced this
  gap as the "missing test" advisory bucket. Extracts the
  exact-match lookup into a private helper
  `find_exact_resource_import_idx` and adds three regression tests:
  `ls_a_19_exact_match_picks_float_not_bigfloat`,
  `ls_a_19_no_match_returns_none_even_with_suffix_collision`, and
  `ls_a_19_resource_new_lookup_is_also_exact`. Gate result moves
  from 15/19 verified to 16/19; remaining missing-bucket entries are
  LS-CP-4 (likely subsumed by #130 Phase 2), LS-A-8, LS-A-9.

### Added

- **Mythos delta-pass auto-runner** (`.github/workflows/mythos-auto.yml`).
  Automates the human-driven discover protocol that
  `mythos-gate.yml` enforces by label. On every PR that touches a
  Tier-5 file, runs `anthropics/claude-code-action` (SHA-pinned)
  against each touched file with `scripts/mythos/discover.md` as
  the prompt, captures a structured `{verdict: NO_FINDINGS | FINDING}`
  JSON via `--json-schema`, and posts a sticky `<!-- mythos-auto-gate -->`
  PR comment with per-file results. Applies `mythos-pass-done` when
  every file is `NO_FINDINGS`; fails the job (without applying the
  label) when any file is `FINDING`. Single-actor scoped — runs only
  when both `github.actor == 'avrabe'` and the immutable
  `github.actor_id == '10056645'` match, and only on
  `pull_request` (not `pull_request_target`) so fork PRs never see
  the OAuth token. Auth flow uses `CLAUDE_CODE_OAUTH_TOKEN` from the
  maintainer's Max-plan subscription (no separate API billing). The
  detect job path-shape-validates every Tier-5 file
  (`^[a-zA-Z0-9/_.-]+$`) before piping into the matrix so a hostile
  path cannot inject through `${{ matrix.file }}` interpolation
  downstream. The label-only `mythos-gate.yml` remains the source of
  truth; the auto-runner is *one way* the label gets applied.

- **LS-N verification gate**
  (`.github/workflows/verification-gate.yml`,
  `tools/run_ls_verification.py`, `tools/post_verification_comment.py`).
  PR-time gate that enforces the test-naming contract: each
  `status: approved` entry in `safety/stpa/loss-scenarios.yaml` must
  have at least one `#[test] fn ls_<letter>_<num>_*` in `meld-core`
  (e.g. `LS-A-11` → `ls_a_11_*`). Runs the matching tests via cargo,
  buckets results as passed / failed / missing, and upserts a single
  sticky PR comment (marker `<!-- meld-ls-verification-gate -->`).
  Failed tests hard-fail the gate; missing tests are advisory so the
  10 older approved entries with ad-hoc test names (e.g. PR #114's
  `test_canonical_abi_size_fixed_size_list_saturates_on_overflow`
  for LS-P-4) can migrate incrementally rather than blocking every
  PR. Adapted from spar's rivet-driven verification gate
  (pulseengine/spar@ba329f3d); meld substitutes its STPA loss-
  scenario artifacts for rivet's executable artifacts, resolving
  test linkage via naming convention. The same script runs locally
  via `python3 tools/run_ls_verification.py`.

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
