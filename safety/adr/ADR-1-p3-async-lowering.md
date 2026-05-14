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

### Lowering pass — landed in issue #120

The rewrite half of the pipeline is now implemented as
`p3_async::lower_p3_async_intrinsics`. After `Merger::merge` produces a
`MergedModule`, the pass:

1. Walks `canonical_functions` across all components to collect the
   `BTreeSet<HostIntrinsic>` of intrinsics actually used.
2. Allocates (or reuses) one core function type per intrinsic per its
   declared `signature()` (`stream_new: () -> i64`, `stream_read:
   (i32,i32,i32,i32) -> i32`, …).
3. Inserts one function import per intrinsic into `merged.imports`
   under module `pulseengine:async`.
4. Shifts every reference to a *defined* function (in
   `function_index_map`, `realloc_map`, `resource_*_by_component`,
   `handle_tables.{new,rep,drop}_func`, `task_return_shims`, function
   exports, the start function, element-segment function refs) up by
   `K = number of new imports`. Existing function imports keep their
   indices.
5. Re-extracts function bodies from their origin core modules with the
   updated `function_index_map` so already-encoded `call N`
   instructions pick up the new defined-function indices.
6. Returns a `LoweringPlan` reporting `(intrinsic, merged_func_index)`
   for each emitted import — useful for downstream tooling that wants
   to wire `call N` instructions to specific intrinsics without
   re-parsing the output.

Coverage: `stream<T>` and `future<T>` symmetric (see
`p3_async_lowering::stream_u8_lowering_emits_pulseengine_async_imports`
and `…::future_s32_lowering_emits_pulseengine_async_imports`). The
73-test `wit_bindgen_runtime` suite stays green because the pass is a
no-op when `required_intrinsics` is empty.

Out of scope (deferred to follow-up sub-issues under #94):

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
* GitHub issue #122 — async-export callback trampoline alignment
  (sub-issue of #94).
* RFC #46 — meld toolchain architecture.
* WASM Component Model P3 spec —
  https://github.com/WebAssembly/component-model
* WASI 0.3 roadmap — https://wasi.dev/roadmap
* `meld-core/src/p3_async.rs` — canonical ABI documentation.
* [ADR-2](ADR-2-p3-async-error-conventions.md) — error/backpressure
  conventions for the same `pulseengine:async` ABI.

---

## Addendum (2026-04-26) — issue #122

The "Out of scope" item *Async export callback variants* is partially
addressed by this addendum: the **trampoline shape and event-code
contract** are now pinned, even though the lowering pass that rewrites
`(canon stream.*)` to `pulseengine:async/*` imports remains deferred.

### What this addendum pins

1. **Event-type codes** (`event::NONE`, `SUBTASK`, `STREAM_READ`,
   `STREAM_WRITE`, `FUTURE_READ`, `FUTURE_WRITE`, `CANCELLED`) are
   exposed as `pub const i32` in `meld_core::p3_async::event`. Numeric
   values match the Component Model "Async Explainer" `EventCode` enum
   and are now part of the cross-tool ABI: any runtime implementing
   `pulseengine:async/stream_read` etc. **must** enqueue events with
   these exact codes against the waitable set the trampoline polls.

2. **Callback return codes** (`callback::EXIT`, `YIELD`, `WAIT`, `POLL`)
   plus the unpack scheme (`CODE_MASK = 0xF`, `PAYLOAD_SHIFT = 4`) are
   exposed in `meld_core::p3_async::callback`. The trampoline reads
   these directly; the constants are referenced from
   `adapter/fact.rs::generate_async_callback_adapter` in place of the
   prior magic numbers.

3. **Trampoline ↔ runtime interaction** (no host upcall) is documented
   in `p3_async.rs` §"Trampoline ↔ `pulseengine:async/stream_read`
   interaction": the runtime *enqueues* events; the trampoline *polls*
   them via `[waitable-set-poll]`. This matches the Component Model's
   no-host-reentrancy rule and is what lets meld emit a deterministic
   core-wasm-only trampoline.

4. **Single canonical trampoline shape**. The existing
   `generate_async_callback_adapter` already emits one shape regardless
   of which P3 built-ins the guest happens to use, because it speaks to
   the callee through `[async-lift]` / `[callback]` and to the host
   through `[waitable-set-poll]` only. This addendum adds tests
   (`async_callback_trampoline_shape_canonical`,
   `async_callback_event_codes_pinned`,
   `async_callback_return_codes_pinned`) that pin the shape so a future
   refactor can't accidentally diverge it.

### What remains deferred

* **Lowering pass for `stream<T>` / `future<T>`** (rewriting
  `(canon stream.new $T)` → `(import "pulseengine:async" "stream_new")`)
  — still tracked under #94. The trampoline is now wired against the
  ABI; the data-plane rewrite is what's left to land for full e2e P3
  async on a real runtime.
* **Runtime stub for the e2e fixture**. Issue #122's acceptance allows
  a fuse-only structural test (which this addendum ships); a kiln /
  wasmtime stub for the `stream<u8>`-in / `stream<u8>`-out scenario is
  cross-repo work and stays deferred.
* **`POLL` (callback code 3) dispatch** is documented but currently
  walks the same path as `WAIT` in the trampoline — non-blocking vs
  blocking is the runtime's responsibility against `[waitable-set-poll]`
  semantics. If the spec ever splits poll into a distinct host
  intrinsic, the trampoline will need a third arm.

---

## Addendum 2026-05-13 — Two-mode lifting policy (SR-32 / #140)

P3 async exports come in two lifting modes per the Component Model:

| Mode | Component opt-in | Trampoline cost | Use case |
|---|---|---|---|
| **Callback** (shipped) | `(canon lift ... async ... (callback $cb))` | One shared stack per component | Embedded / `cFS`-style "one message at a time" guests |
| **Stackful** (foundation in this PR, emitter follow-up) | `(canon lift ... async ...)` with **no** `(callback ...)` | One stack per in-flight async call | Languages with native async/await (Rust, Go, Java) |

**Detection.** `P3AsyncFeatures::uses_stackful_lift()` returns true iff
the component has any `(canon lift ... async ...)` *without* a
`(callback ...)` option. Mutually exclusive with the callback case on
a per-lift basis; a single component may declare both kinds of lifts,
in which case meld will emit both trampolines.

**ABI surface.** Four new host-intrinsic imports under the existing
`pulseengine:async` module:

```wasm
(import "pulseengine:async" "thread_new"        (func (param i32 i32) (result i32)))
(import "pulseengine:async" "thread_switch_to"  (func (param i32)))
(import "pulseengine:async" "thread_yield"      (func))
(import "pulseengine:async" "thread_exit"       (func))
```

`thread_new(start_fn, arg) -> i32` returns a non-negative thread handle
on success or a negative [`AbiError`] (typically [`AbiError::Oom`]) on
failure. `thread_switch_to` traps if the target thread is exited or
unknown. `thread_yield` lets the runtime scheduler pick another fiber.
`thread_exit` permanently releases the current fiber.

These names and signatures are pinned by
`p3_async::tests::stackful_intrinsic_signatures_pinned`. Changing them
is a breaking change to `pulseengine:async` and requires a version bump.

**Emission policy.** Until the stackful trampoline emitter ships in a
follow-up PR within the v0.8.0 milestone, meld surfaces a clear error
for components that need stackful lifting rather than silently
generating a callback trampoline (which would corrupt the suspended-
stack semantics the guest expects).

**Why not unify with `task.wait` / `task.yield` parsing.** Those
component-model canon builtins are *what the guest emits inside its own
body* to suspend; they go through the existing `P3BuiltinOp` lowering
path in `component_wrap.rs`. The new `thread_*` intrinsics are *what
meld synthesises* around the lifted function so the host can save and
restore the wasm stack. The two are connected (the stackful trampoline
turns `task.wait` body invocations into `thread_yield` / waitable
registration sequences) but live at different abstraction layers.

### What this addendum leaves deferred

* **Stackful trampoline emitter** — separate follow-up PR under v0.8.0
  / #140. The emitter generates: (a) a host-visible export function
  that creates a fresh fiber on each async invocation, and (b)
  in-body rewrites of `task.wait` to `thread_yield` + waitable
  registration. ABI-level shape pins exist; structural test for the
  generated trampoline will land with the emitter.
* **Stackful + callback in the same component.** Permitted by the
  Component Model. The emitter will produce both trampolines without
  cross-talk; the test for that case ships with the emitter.

---

## Addendum 2026-05-13 (b) — Stackful trampoline emitter shipped (#140 phase 2)

The emitter described as "deferred" above has shipped. This addendum
records the implementation decision and the gap between the originally
sketched approach (a) and what actually landed.

**What shipped.** `FactStyleGenerator::generate_async_stackful_adapter`
emits a trampoline of the form:

```wat
(func $async_stackful_adapter_<from>_to_<to>
  ;; step 0.5 — cross-memory param copy (shared with callback path)
  ;; step 1   — call [async-lift]<export> with caller's params
  ;; step 1.5 — drop the lift's runtime-owned packed return
  ;; step 3   — read task.return result globals (push-on-stack or
  ;;            write-to-retptr) and return
)
```

The dispatcher in `<impl AdapterGenerator>::generate` routes any
`is_async_lift` site to this emitter when the merged module has no
`[callback]<export>` companion.

**What the originally sketched design got wrong, and why.** The
original sketch above ("creates a fresh fiber on each async
invocation") proposed an adapter-driven scheduling loop using
`thread_new` + `thread_switch_to` + `thread_yield`. Implementing it
literally requires:

1. A per-export wrapper function whose `(i32 arg) -> ()` signature
   matches `thread_new`, with the wrapper unpacking the canonical-
   flattened params from scratch memory and invoking the lift.
2. A per-export `$fiber_done` sentinel global, written by the wrapper
   after the lift returns, read by the trampoline drive loop.
3. Both (1) and (2) injected into the merged module's function and
   global index spaces *from the adapter pass*, which runs after the
   merger has finalised those spaces.

That trio is implementable but adds roughly 350 lines of emitter code
and a non-trivial late-stage modification of merged-module state. The
shipped design replaces all of it with a direct call to the lift
function: the wasm runtime sees `(canon lift ... async ...)` with no
callback option and runs the call on a fresh fiber transparently,
suspending on `task.wait` and resuming on the awaited event. From the
adapter's perspective the call looks synchronous; the fiber lifecycle
is the runtime's concern.

**Status of the Phase 1 `thread::*` ABI.** Unchanged. The four
host-intrinsic imports remain part of the `pulseengine:async` surface
and are pinned by `p3_async::tests::stackful_intrinsic_signatures_pinned`.
They are reserved for component-internal concurrency primitives (a
guest spawning parallel tasks via `wasi:thread` or similar) but are
**not consumed** by the stackful trampoline. A runtime that supports
stackful lift need not yet implement them; a runtime that wants to
expose userspace threading to guests must.

**Part (b) — in-body `task.wait` rewrites.** Still deferred. The shipped
trampoline relies on the runtime's transparent suspension contract,
not on rewriting the lift body. If a future runtime requires explicit
`task.wait` → `thread_yield` rewrites at the wasm level, those land
as a separate follow-up; the stackful trampoline contract above does
not change.

**Deferred from this phase.** Stackful lifts that return a cross-
memory `(ptr, len)` result (i.e., `string` or `list<T>` returns where
caller and callee live in different linear memories) currently produce
an explicit "deferred to follow-up" error rather than emit wrong wasm.
Components hitting this can use callback-mode lifting or fuse same-
memory components in the interim. Tracked under #140; structural test
in `sr32_stackful_emitter_shape_pins_call_drop_globalget` excludes
the cross-memory ptr-pair path by construction.
