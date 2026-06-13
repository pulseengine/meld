---
id: ADR-2
type: design-question
title: P3 async error and backpressure conventions for the `pulseengine:async` ABI
status: open
gating-fixtures:
  - p3_async_abi::abi_error_numeric_values_are_pinned
  - p3_async_abi::stream_read_pending_is_distinct_from_eof
  - p3_async_abi::stream_write_zero_accepted_is_partial_not_error
  - p3_async_abi::error_codes_are_consistent_across_decoders
design-paths:
  - K — Closed `AbiError` enum with stable negative-i32 codes (chosen, this PR)
  - L — Per-intrinsic ad-hoc error codes (rejected — diverges across runtimes)
  - M — Component-model `result<T, E>` lift around every intrinsic (rejected — too heavyweight for the data plane)
---

# ADR-2 — P3 async error and backpressure conventions

## Context

ADR-1 fixed the **shape** of the host-intrinsic ABI under module
`pulseengine:async` (14 imports, signatures, element-width hidden in the
handle). It deferred the **semantic conventions** the intrinsics' return
values follow:

> *Out of scope (deferred to follow-up sub-issues under #94):*
> *— Error and backpressure conventions — the ABI doc spec
> (`stream_write` returns bytes accepted < requested = backpressure;
> negative = error) is fixed in rustdoc, but the runtime contract
> needs companion docs in kiln + a wasmtime reference impl.*

Issue #121 tracks the formalisation. Without a closed enum of error
codes, runtimes (kiln, wasmtime reference impl, ad-hoc embedders) would
each invent their own negative-`i32` mapping and fused components would
behave subtly differently across hosts. Worse, two of the intrinsic
return contracts have ambiguous corners that issue #121 explicitly
calls out:

1. **`stream_write` partial-write semantics.** "Accepted fewer bytes
   than requested" is documented as backpressure. Two questions: (a) is
   `0 bytes accepted` *also* backpressure or a special "no progress"
   error? (b) does the runtime queue the un-accepted tail, or must the
   producer always retry?

2. **`stream_read` EOF distinguishability.** "Returns 0 = EOF" leaves
   no way to express "the stream is still open but no bytes are
   available right now" — the reader cannot tell whether to drop the
   handle or register a waitable. The same ambiguity affects
   `future_read` (`0` = pending vs `0` = closed?).

This ADR formalises the conventions and pins them with unit tests so
runtimes can be conformance-checked against meld's expectations.

## Decision

**Path K — closed `AbiError` enum, negative-`i32` codes, partial-count
backpressure with the producer as retry authority, EOF distinguishable
from pending via a dedicated `Pending` code.**

### The closed `AbiError` enum

`meld_core::p3_async::AbiError` is `#[repr(i32)]` with these stable
discriminants:

| Variant | Value | Meaning |
|---------|-------|---------|
| `Closed` | `-1` | Peer end of the stream/future was dropped. |
| `InvalidHandle` | `-2` | Handle is not live, not owned by this caller, or is the wrong end. |
| `Oom` | `-3` | Runtime could not allocate buffer space to make any progress. |
| `Cancelled` | `-4` | Concurrent `*_cancel_*` aborted the operation. |
| `Pending` | `-5` | Operation would block; register in waitable-set and retry. |
| `Runtime` | `-6` | Catch-all runtime-internal failure. Forward-compat escape hatch; specific codes preferred. |

The numeric values are pinned by `meld-core/tests/p3_async_abi.rs` and
referenced in `AbiError::ALL` for exhaustive coverage. Adding a new
variant is non-breaking only if it takes the next free negative
discriminant (`-7`); removing or renumbering a variant is a breaking
ABI change.

### Partial-write semantics (`stream_write`)

* `written == requested` — full success.
* `0 <= written < requested` — **partial write / backpressure**. The
  reader cannot keep up. The runtime DOES NOT queue the un-accepted
  tail; the **producer is the retry authority**. `written == 0` is
  treated identically to a positive partial — it is **not** an error,
  not EOF, just "no progress this round".
* `written < 0` — error from `AbiError`. Notably, `Closed` means the
  readable end was dropped (further writes will fail the same way) and
  `Oom` is distinct from backpressure (hard error, propagate).

The "producer retries" rule is what allows the runtime to remain a
*reactive* implementation — no internal buffer beyond what's pending in
flight. Hosts that want to absorb more data can wrap the intrinsic in
component-model glue, but the ABI-level contract is no buffering.

### EOF vs Pending (`stream_read`)

* `n > 0` — `n` bytes copied. May be less than requested; stream is
  **not** at EOF.
* `n == 0` — **EOF, sticky.** The writable end was dropped AND no
  buffered bytes remain. Subsequent reads also return `0`.
* `n == AbiError::Pending` (`-5`) — stream is still open, no bytes
  available *right now*. Reader registers in a waitable-set and retries
  after `[waitable-set-wait]` fires.
* Other negative — `AbiError` per the table above.

Runtimes MAY conflate `Closed` with `0`-EOF on `stream_read`: if the
writable end was dropped *before* the read started AND no bytes were
buffered, returning `0` is observably equivalent to returning `Closed`.
Most runtimes return `0` (the simpler case) but `Closed` is permitted
for runtimes that distinguish "drained the buffer naturally" from
"drained it because the writer disappeared".

### Resolved vs Pending vs Closed (`future_read`)

* `1` — resolved; `T`'s canonical layout has been written to the
  buffer.
* `0` — **pending**. The future is unresolved AND the write end is
  still alive. Reader registers in waitable-set and retries.
* `AbiError::Closed` (`-1`) — write end was dropped without resolving;
  no value will ever arrive. **Distinguishable** from pending.
* Other negative — `AbiError` per the table above.

Unlike `stream_write`, `future_write` is all-or-nothing: there is no
partial-write case for futures.

### Interaction with `[waitable-set-wait]`

The data-plane intrinsics are non-blocking. Each `stream_read`,
`stream_write`, and `future_read` may report a "would block" condition
(`AbiError::Pending`, partial count, or `0` for `future_read`). The
caller's recovery is uniform:

1. The handle (readable for read, writable for write) is **the
   waitable**. No separate waitable object.
2. Caller obtains a waitable-set via `[waitable-set-new]`.
3. Caller joins the handle into the set via `[waitable-join]`.
4. Caller blocks (or spins, depending on the lift mode) on
   `[waitable-set-wait]`. The set fires when:
   * `stream_read` waitable: bytes become available OR the writable
     end is dropped.
   * `stream_write` waitable: buffer space frees up OR the readable
     end is dropped.
   * `future_read` waitable: the future resolves OR the write end is
     dropped.
5. The waitable's payload identifies *which* handle is ready. The
   actual byte count / resolved flag / error code is delivered by
   re-invoking the relevant data-plane intrinsic — **not** by the
   `[waitable-set-wait]` return value.

This decoupling is intentional: it means waitable-sets only carry
identity-of-readiness, while the data-plane intrinsics retain full
control over their return contract. A runtime that wants to deliver
bulk readiness without blocking can poll via `[waitable-set-poll]`
identically.

## What this PR ships

* `meld_core::p3_async::AbiError` enum with `repr(i32)`, `as_i32`,
  `from_i32`, `ALL` array.
* `StreamWriteResult`, `StreamReadResult`, `FutureReadResult` decoder
  enums for typed handling of return values in tests and in adapter
  glue meld emits in the deferred lowering pass.
* Per-variant rustdoc on `HostIntrinsic::Stream*` and
  `HostIntrinsic::Future*` documenting partial-write semantics, EOF
  distinguishability, and the waitable-set interaction.
* `meld-core/tests/p3_async_abi.rs` pinning the numeric values and the
  decoder behaviour (encoding-only — no runtime interaction).

## Out of scope

* **Companion docs in kiln** — referenced from this ADR; tracked as a
  follow-up issue in `pulseengine/kiln`.
* **Reference implementation in wasmtime** — referenced; tracked as a
  separable follow-up.
* **Lowering pass that uses these decoders in adapter glue** — the
  decoders are public API in this PR, but the rewrite phase that
  emits adapter code calling them is deferred per ADR-1.
* **Component-model `result<T, E>` lift around every intrinsic
  (path L)** — rejected because every data-plane call would pay the
  canonical-ABI lift/lower cost of a `result`, and the
  zero-copy contract for `stream_read` / `stream_write` would be lost.
  The closed-enum-on-`i32` convention is the lowest-overhead option
  that still gives runtimes a stable wire format.
* **Per-intrinsic ad-hoc error codes (path M)** — rejected because it
  fragments the conformance surface. With the closed enum, kiln and
  the wasmtime reference can share a single error-mapping table.

## Backward compatibility

This PR adds new public API (`AbiError`, the three decoder enums) and
does not modify the existing `HostIntrinsic` enum variants (per the
v0.5.0 stability contract). Components fused before this PR continue
to validate; the decoders are opt-in for new adapter glue and tests.

## References

* GitHub issue #121 — original task list.
* GitHub issue #94 — parent epic.
* ADR-1 (`safety/adr/ADR-1-p3-async-lowering.md`) — host-intrinsic ABI
  shape, declared error/backpressure conventions out of scope for #94.
* WASI 0.3 stream semantics — https://wasi.dev/roadmap
* WASM Component Model P3 spec —
  https://github.com/WebAssembly/component-model
* `meld-core/src/p3_async.rs` — canonical ABI documentation.
* `meld-core/tests/p3_async_abi.rs` — pin tests for the conventions.
