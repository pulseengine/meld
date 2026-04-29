---
id: ADR-1
type: design-question
title: P3 async lowering — host-intrinsic ABI for stream<T>/future<T>/async exports
status: open
gating-fixtures:
  - p3_async_lowering::stream_u8_component_detected_end_to_end
  - p3_async_lowering::all_intrinsics_emit_pulseengine_async_imports
design-paths:
  - A — Host-intrinsic ABI under module `pulseengine:async` (chosen, foundation in this PR)
  - B — Inline P3 async natively in fused output (rejected — temporal data flow can't be resolved at build time)
  - C — Reject P3 async at the parser (current main behaviour pre-#94 — to be replaced)
---

# ADR-1 — P3 async lowering

## Context

WASM Component Model 0.3 (P3) introduces `stream<T>`, `future<T>`, and
async-lifted/lowered exports. Meld is a static fusion tool (RFC #46): it
resolves component-model constructs at build time and emits a single
core module. P3 async constructs CANNOT be resolved at build time —
they represent temporal data flow (data arriving over time) — so meld
must lower them to import calls against a stable ABI that the runtime
(kiln, wasmtime, …) implements.

Issue #94 proposes: lower P3 async to a documented host-intrinsic ABI.

## Decision

**Path A — Host-intrinsic ABI under module `pulseengine:async`.**

The ABI surface is the smallest set of imports that covers the
canonical built-ins meld already parses (`stream.{new,read,write,
cancel-read,cancel-write,drop-readable,drop-writable}` and the same
seven for `future`). Element-width information is **not** part of the
intrinsic signature — it is encoded in the canonical-ABI glue meld
emits around each call. This keeps the intrinsic count constant at
**14** regardless of how many `stream<T>` / `future<T>` types appear in
fused components.

The ABI is fully documented in `meld-core/src/p3_async.rs` (rustdoc
table) and surfaced as constants in two sub-modules:

* `meld_core::p3_async::stream::*` — `NEW`, `READ`, `WRITE`,
  `CANCEL_READ`, `CANCEL_WRITE`, `DROP_READABLE`, `DROP_WRITABLE`.
* `meld_core::p3_async::future::*` — same seven verbs.

The qualified import name is always
`(meld_core::p3_async::HOST_INTRINSIC_MODULE, NAME)` =
`("pulseengine:async", "<verb>")`.

## What this PR ships (foundation layer)

This PR establishes the **detection and ABI-documentation layer** —
i.e., everything below the actual rewrite of fused-output imports.

In scope:

1. `meld_core::p3_async` module:
   * Documented host-intrinsic ABI surface.
   * `HostIntrinsic` enum with `from_canonical_entry` and `import()`.
   * `P3AsyncFeatures` summary struct.
   * `detect_features(&ParsedComponent) -> P3AsyncFeatures` inspector.
2. Public API on `Fuser`:
   * `Fuser::p3_async_summary()` returns per-component features.
3. Detection in the parser side already existed (`p3_async_features`
   on `ParsedComponent`); this PR makes it queryable structurally
   instead of stringly-typed.
4. End-to-end fixture:
   * `meld-core/tests/p3_async_lowering.rs::stream_u8_component_detected_end_to_end`
     parses a synthetic component with `stream<u8>` + the five core
     stream canonical built-ins and verifies detection produces the
     expected `HostIntrinsic` set.
5. Regression guard:
   * `pure_p2_component_has_no_p3_features` ensures detection has no
     false positives on non-async components.
   * Existing 73-test `wit_bindgen_runtime` suite stays green.

Out of scope (deferred to follow-up sub-issues under #94):

- **Lowering pass (rewrite phase)** — actually rewriting
  `(canon stream.new $T)` → `(import "pulseengine:async" "stream_new")`
  in the fused core module. The detection layer this PR ships gives the
  lowering pass everything it needs (entry → intrinsic mapping, import
  module name) but the rewrite itself in `component_wrap.rs` /
  `merger.rs` is a larger change and is split out.
- **`future<T>` end-to-end** — the ABI is defined and the
  `HostIntrinsic::Future*` enum variants exist, but no integration
  fixture exercises them. The deferred lowering pass should land
  `future<T>` and `stream<T>` together for symmetry.
- **Async export callback variants** — async lift with `(callback ...)`
  is *detected* (`P3AsyncFeatures::uses_callback_lift`) but the
  callback-trampoline emission is partially implemented in
  `component_wrap.rs::generate_callback_driving_adapter`. Aligning the
  trampoline with this PR's `pulseengine:async` ABI is deferred.
- **Stackful (task.wait/yield) async lifting mode** — issue #94
  identifies callback mode as preferred for embedded; the stackful
  mode (`thread_new`/`thread_switch_to`) is fully out of scope.
- **Cross-component stream adapter** — when two fused components share
  a `stream<T>`, meld should generate a same-memory ring buffer or a
  multi-memory copy adapter. Neither is implemented.
- **Error and backpressure conventions** — the ABI doc spec
  (`stream_write` returns bytes accepted < requested = backpressure;
  negative = error) is fixed in rustdoc, but the runtime contract
  needs companion docs in kiln + a wasmtime reference impl.
  *Update (issue #121):* the closed-enum convention is now formalised
  in [`ADR-2`](ADR-2-p3-async-error-conventions.md) and pinned by
  `meld-core/tests/p3_async_abi.rs`. Companion docs in kiln and the
  wasmtime reference impl remain out of scope (separable tracking
  issues).
- **Static validation** — type-compat and circular-dependency checks
  for cross-component streams (issue #94 §4).

## Why these defer

Issue #94 is "major-version-class" scope. Landing the entire async
lowering in one PR would (a) be a 5k+ LOC change touching merger,
component_wrap, adapter, and resolver; (b) require cross-repo runtime
work in kiln to test e2e; (c) couple unrelated decisions (callback
trampoline shape, stream adapter ring-buffer layout, error encoding)
into one review.

The foundation layer in this PR is the **stable API contract** the
rest of the work builds on. Once the ABI module names + intrinsic
enum + detection API are merged, the lowering pass and runtime
implementation can land independently — and crucially, in parallel,
since they share only this contract.

## Backward compatibility

* No existing test regresses (73/73 wit_bindgen_runtime green).
* Components that don't use P3 async features see zero behaviour
  change. `Fuser::p3_async_summary()` returns empty features for them.
* Components that DO use P3 async features now parse successfully (no
  longer rejected by `Error::P3AsyncNotSupported`) and surface the
  detection summary, but fusion still cannot lower them — the
  resulting fused output will validate but contain unresolved
  `(canon stream.*)` constructs that downstream tooling will reject.
  This is a documented intermediate state.

## References

* GitHub issue #94 — original proposal.
* GitHub issue #121 — error/backpressure conventions follow-up
  (resolved by ADR-2).
* RFC #46 — meld toolchain architecture.
* WASM Component Model P3 spec —
  https://github.com/WebAssembly/component-model
* WASI 0.3 roadmap — https://wasi.dev/roadmap
* `meld-core/src/p3_async.rs` — canonical ABI documentation.
* [ADR-2](ADR-2-p3-async-error-conventions.md) — error/backpressure
  conventions for the same `pulseengine:async` ABI.
