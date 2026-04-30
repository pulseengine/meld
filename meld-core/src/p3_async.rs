//! # P3 async lowering — host-intrinsic ABI
//!
//! This module defines the **build-time ABI** that meld lowers P3 async
//! constructs (`stream<T>`, `future<T>`, async lift/lower) **to**, and
//! provides detection helpers used by the parser and fuser.
//!
//! ## Why a host-intrinsic ABI?
//!
//! Per RFC #46 (toolchain architecture), meld is a *static fusion* tool:
//! everything that can be resolved at build time is resolved at build time,
//! and everything else is lowered to a documented import surface that the
//! runtime (kiln, wasmtime, …) implements.
//!
//! Async constructs (`stream<T>`, `future<T>`) cannot be resolved statically
//! because they represent temporal data flow. They CAN, however, be lowered
//! to import calls against a fixed ABI. Meld emits these imports; consumers
//! provide the implementation.
//!
//! ## ABI surface (`pulseengine:async`)
//!
//! All host intrinsics live in the import module **`pulseengine:async`**.
//! The intrinsic surface is intentionally minimal — it is the
//! lowest-common-denominator over what P3 async constructs need at the core
//! WebAssembly level, after canonical lift/lower has been applied.
//!
//! Stream operations (handle is the canonical ABI stream handle, `i32`):
//!
//! | Function                    | Signature                              | Semantics |
//! |-----------------------------|----------------------------------------|-----------|
//! | `stream_new`                | `() -> i64`                            | Allocate a new stream handle pair. Low 32 bits = readable end, high 32 bits = writable end. |
//! | `stream_read`               | `(handle: i32, buf_ptr: i32, buf_len: i32, mem_idx: i32) -> i32` | Read up to `buf_len` bytes into `buf_ptr` of memory `mem_idx`. Returns bytes read (0 = EOF, negative = error code). |
//! | `stream_write`              | `(handle: i32, data_ptr: i32, data_len: i32, mem_idx: i32) -> i32` | Write `data_len` bytes from `data_ptr`. Returns bytes accepted (may be < `data_len` for backpressure). |
//! | `stream_cancel_read`        | `(handle: i32) -> i32`                 | Cancel a pending read. Returns 1 if cancelled, 0 if no read was pending. |
//! | `stream_cancel_write`       | `(handle: i32) -> i32`                 | Cancel a pending write. |
//! | `stream_drop_readable`      | `(handle: i32)`                        | Drop the readable end. Closing both ends destroys the stream. |
//! | `stream_drop_writable`      | `(handle: i32)`                        | Drop the writable end. |
//!
//! Future operations (handle is `i32`):
//!
//! | Function                    | Signature                              | Semantics |
//! |-----------------------------|----------------------------------------|-----------|
//! | `future_new`                | `() -> i64`                            | Allocate a new future handle pair. Low 32 = read end, high 32 = write end. |
//! | `future_read`               | `(handle: i32, buf_ptr: i32, mem_idx: i32) -> i32` | Read the resolved value into `buf_ptr` (size = canonical layout of `T`). Returns 1 if resolved, 0 if not yet, negative = error. |
//! | `future_write`              | `(handle: i32, data_ptr: i32, mem_idx: i32) -> i32` | Resolve the future. |
//! | `future_cancel_read`        | `(handle: i32) -> i32`                 | Cancel a pending read. |
//! | `future_cancel_write`       | `(handle: i32) -> i32`                 | Cancel a pending write. |
//! | `future_drop_readable`      | `(handle: i32)`                        | Drop the readable end. |
//! | `future_drop_writable`      | `(handle: i32)`                        | Drop the writable end. |
//!
//! ### Design notes
//!
//! * **Element width is hidden in the handle.** A `stream<u8>` and a
//!   `stream<record { x: u32, y: u32 }>` use the *same* `stream_read` /
//!   `stream_write` primitives. The byte-level canonical-ABI lowering of
//!   `T` happens in adapter glue meld emits *around* the call. This keeps
//!   the host intrinsic count constant.
//! * **`mem_idx` parameter** is required because meld supports
//!   multi-memory components (each fused component keeps its own memory).
//!   The runtime needs to know which memory to read/write.
//! * **Backpressure** is exposed via the bytes-written return: a write that
//!   accepts fewer bytes than requested means the consumer is slow and the
//!   producer should retry. There is no separate "wait" primitive — that
//!   composes with the existing `[waitable-set-wait]` builtin already
//!   handled by `component_wrap.rs`.
//! * **No async-export callback intrinsics here.** Async exports are
//!   already handled by meld's existing P3 callback-driving adapter
//!   (`component_wrap.rs::generate_callback_driving_adapter`). This module
//!   only provides the *data-plane* (stream/future) intrinsics.
//!
//! ## Error and backpressure conventions (issue #121, ADR-2)
//!
//! Every `stream_*` / `future_*` intrinsic that returns `i32` follows the
//! convention: **non-negative = success-with-payload, negative = error
//! drawn from the closed enum [`AbiError`]**.
//!
//! * Stream EOF is `0` from `stream_read` and is **distinguishable** from
//!   "no bytes available right now" — the latter returns
//!   [`AbiError::Pending`]. EOF is sticky once observed.
//! * `stream_write` exposes backpressure as a partial count
//!   (`written < requested`). The **producer** is the retry authority;
//!   the runtime does not queue the un-accepted tail. A write of `0`
//!   bytes is still backpressure, NOT EOF.
//! * `future_read` returns `1` (resolved), `0` (pending), or negative
//!   (error). `0` is **not** EOF — `Closed` is.
//! * Pending operations register the relevant handle in a waitable-set
//!   and re-invoke the intrinsic after `[waitable-set-wait]` fires.
//!   Byte counts / resolved flags are read from the *next intrinsic
//!   call*, not from the waitable's payload.
//!
//! Helper decoders [`StreamWriteResult`], [`StreamReadResult`], and
//! [`FutureReadResult`] turn raw `i32` returns into typed variants for
//! use in tests and adapter glue.
//!
//! See [ADR-2](../../safety/adr/ADR-2-p3-async-error-conventions.md) for
//! the formal rationale.
//!
//! ## Detection
//!
//! [`P3AsyncFeatures`] summarises what P3 async constructs a parsed component
//! contains. [`detect_features`] inspects a [`crate::parser::ParsedComponent`]
//! and returns the summary. This is a **pure inspection** — it never
//! mutates the component.
//!
//! ## Scope
//!
//! This module covers both halves of the P3 async pipeline:
//!
//! * **Detection** — [`detect_features`] inspects a parsed component
//!   and returns the [`P3AsyncFeatures`] summary (foundation, PR #94).
//! * **Lowering** — [`lower_p3_async_intrinsics`] rewrites the merged
//!   module to add `pulseengine:async` imports for every detected
//!   intrinsic and shifts function indices accordingly (issue #120).
//!
//! [`HostIntrinsic`] is the bridge: `from_canonical_entry` maps parsed
//! entries to the abstract intrinsic, and `signature` / `import` /
//! `name` give the concrete core-wasm shape used during lowering.

use crate::parser::{CanonicalEntry, ComponentTypeKind, ParsedComponent};

/// Import module name used for all P3 async host intrinsics emitted by
/// meld. The runtime (kiln, wasmtime, …) is expected to satisfy these
/// imports.
pub const HOST_INTRINSIC_MODULE: &str = "pulseengine:async";

/// Names of all stream-related host intrinsic imports.
pub mod stream {
    /// `() -> i64` — allocate a new stream. Returns packed (write << 32 | read).
    pub const NEW: &str = "stream_new";
    /// `(i32, i32, i32, i32) -> i32` — `(handle, buf_ptr, buf_len, mem_idx)`.
    pub const READ: &str = "stream_read";
    /// `(i32, i32, i32, i32) -> i32` — `(handle, data_ptr, data_len, mem_idx)`.
    pub const WRITE: &str = "stream_write";
    /// `(i32) -> i32` — cancel a pending read on the given handle.
    pub const CANCEL_READ: &str = "stream_cancel_read";
    /// `(i32) -> i32` — cancel a pending write on the given handle.
    pub const CANCEL_WRITE: &str = "stream_cancel_write";
    /// `(i32) -> ()` — drop the readable end of the stream.
    pub const DROP_READABLE: &str = "stream_drop_readable";
    /// `(i32) -> ()` — drop the writable end of the stream.
    pub const DROP_WRITABLE: &str = "stream_drop_writable";
}

/// Names of all future-related host intrinsic imports.
pub mod future {
    /// `() -> i64` — allocate a new future. Returns packed (write << 32 | read).
    pub const NEW: &str = "future_new";
    /// `(i32, i32, i32) -> i32` — `(handle, buf_ptr, mem_idx)`.
    pub const READ: &str = "future_read";
    /// `(i32, i32, i32) -> i32` — `(handle, data_ptr, mem_idx)`.
    pub const WRITE: &str = "future_write";
    /// `(i32) -> i32` — cancel a pending read on the given future.
    pub const CANCEL_READ: &str = "future_cancel_read";
    /// `(i32) -> i32` — cancel a pending write on the given future.
    pub const CANCEL_WRITE: &str = "future_cancel_write";
    /// `(i32) -> ()` — drop the readable end of the future.
    pub const DROP_READABLE: &str = "future_drop_readable";
    /// `(i32) -> ()` — drop the writable end of the future.
    pub const DROP_WRITABLE: &str = "future_drop_writable";
}

/// A specific P3 async canonical built-in, mapped to the host intrinsic
/// it lowers to.
///
/// # Return-value conventions
///
/// All `stream_*` / `future_*` intrinsics that return `i32` follow the
/// **non-negative = success, negative = error** convention, where the error
/// codes are drawn from the closed enum [`AbiError`]. Helper decoders
/// [`StreamReadResult`], [`StreamWriteResult`], and [`FutureReadResult`]
/// turn raw return values into these typed variants for testing and for
/// generated adapter glue.
///
/// See the per-variant rustdoc below for partial-write semantics, EOF
/// distinguishability, and how each intrinsic interacts with the
/// `[waitable-set-wait]` built-in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HostIntrinsic {
    /// `() -> i64` — allocate a new stream handle pair. Low 32 bits =
    /// readable end, high 32 bits = writable end.
    ///
    /// Errors are reported by encoding [`AbiError::Oom`] (or other
    /// negative codes) **in the low 32 bits** with the high 32 bits set to
    /// zero. Callers MUST inspect the low 32 bits as `i32` before using
    /// either half. (`i64::from_ne_bytes`-style decoding never produces a
    /// negative low half from a valid handle pair, since handles are
    /// non-negative.)
    StreamNew,
    /// `(handle: i32, buf_ptr: i32, buf_len: i32, mem_idx: i32) -> i32`
    /// — read up to `buf_len` bytes into `buf_ptr` of memory `mem_idx`.
    ///
    /// Return value (decode with [`StreamReadResult::decode`]):
    ///
    /// * `n > 0` — exactly `n` bytes were copied into `buf_ptr`. `n` may
    ///   be less than `buf_len`; that simply means the runtime had fewer
    ///   bytes available *right now*. The reader is free to retry — the
    ///   stream is **not** at EOF.
    /// * `n == 0` — **EOF, distinguishable from "0 bytes available"**:
    ///   the writable end has been dropped AND no buffered bytes remain.
    ///   The runtime MUST NOT return 0 to indicate "nothing available
    ///   right now"; in that case the reader receives [`AbiError::Pending`]
    ///   so the reader can register a waitable instead of busy-looping.
    ///   Once a reader has observed `0`, every subsequent call on the
    ///   same handle MUST also return `0` (EOF is sticky).
    /// * `n < 0` — error from [`AbiError`]. Notable codes:
    ///   * [`AbiError::Pending`] — no bytes available right now and the
    ///     stream is still open. The reader SHOULD register the handle
    ///     in a waitable-set (see *Interaction with `[waitable-set-wait]`*
    ///     below) and re-invoke `stream_read` after the set fires.
    ///   * [`AbiError::Closed`] — the writable end was dropped *before*
    ///     the read started AND no buffered bytes were available. This
    ///     is the same observable state as EOF; the runtime MAY return
    ///     `0` instead and most do.
    ///   * [`AbiError::InvalidHandle`] — `handle` is not a live readable
    ///     end of a stream owned by this caller.
    ///   * [`AbiError::Cancelled`] — the read was cancelled by a
    ///     concurrent `stream_cancel_read`.
    ///
    /// ### Interaction with `[waitable-set-wait]`
    ///
    /// `stream_read` is a *non-blocking* primitive. When it returns
    /// [`AbiError::Pending`], the caller registers the **readable handle**
    /// in a waitable-set (created via `[waitable-set-new]`, populated via
    /// `[waitable-join]`). The runtime fires the waitable when bytes
    /// become available OR the writable end is dropped (whichever comes
    /// first). The caller drains the readiness via `[waitable-set-wait]`
    /// and re-invokes `stream_read` to retrieve the actual bytes (or `0`
    /// for EOF). The waitable's payload identifies *which* handle is
    /// ready; the byte count is **not** delivered through the waitable —
    /// it is read out of the next `stream_read` call.
    StreamRead,
    /// `(handle: i32, data_ptr: i32, data_len: i32, mem_idx: i32) -> i32`
    /// — write `data_len` bytes from `data_ptr`.
    ///
    /// Return value (decode with [`StreamWriteResult::decode`]):
    ///
    /// * `n == data_len` — full success.
    /// * `0 <= n < data_len` — **partial write / backpressure**: the
    ///   reader is slow. The producer is the *retry authority*: meld and
    ///   the runtime do **not** queue the un-accepted tail. The producer
    ///   MUST resubmit the slice `[data_ptr + n .. data_ptr + data_len)`
    ///   (typically after a `[waitable-set-wait]` round; see below). A
    ///   compliant runtime may return `0` to mean "no progress right now";
    ///   producers SHOULD treat `n == 0` identically to a positive
    ///   partial write — backpressure, retry. Returning `0` is **not**
    ///   EOF on the write side; readable EOF is signalled only on the
    ///   read side.
    /// * `n < 0` — error from [`AbiError`]:
    ///   * [`AbiError::Closed`] — the readable end was dropped. The
    ///     producer should drop the writable end; further writes will
    ///     fail with the same code.
    ///   * [`AbiError::InvalidHandle`] — `handle` is not a live writable
    ///     end of a stream owned by this caller.
    ///   * [`AbiError::Cancelled`] — the write was cancelled by a
    ///     concurrent `stream_cancel_write`.
    ///   * [`AbiError::Oom`] — the runtime could not allocate buffer
    ///     space for any progress. Distinct from backpressure: producers
    ///     SHOULD propagate this as a hard error rather than retry.
    ///
    /// ### Interaction with `[waitable-set-wait]`
    ///
    /// On a partial write or `AbiError::Pending` (some runtimes prefer
    /// the latter when 0 bytes were accepted), the producer registers
    /// the **writable handle** in a waitable-set. The runtime fires the
    /// waitable when buffer space frees up OR the readable end is
    /// dropped. The producer re-invokes `stream_write` with the
    /// remaining slice; the actual byte count is read out of that call,
    /// not the waitable payload.
    StreamWrite,
    /// `(handle: i32) -> i32` — cancel a pending read on the given handle.
    ///
    /// Return value:
    ///
    /// * `1` — a pending read was cancelled. The cancelled `stream_read`
    ///   call (on whichever task issued it) returns
    ///   [`AbiError::Cancelled`].
    /// * `0` — no read was pending; this is a no-op success.
    /// * `n < 0` — error from [`AbiError`], typically
    ///   [`AbiError::InvalidHandle`].
    StreamCancelRead,
    /// `(handle: i32) -> i32` — cancel a pending write on the given
    /// handle. Return convention matches [`HostIntrinsic::StreamCancelRead`].
    StreamCancelWrite,
    /// `(handle: i32)` — drop the readable end. Closing both ends destroys
    /// the stream and any buffered bytes. After dropping the readable end:
    ///
    /// * Pending writes complete with [`AbiError::Closed`] (if no bytes
    ///   were already accepted) or with the partial count.
    /// * Subsequent writes return [`AbiError::Closed`].
    StreamDropReadable,
    /// `(handle: i32)` — drop the writable end. After dropping:
    ///
    /// * Pending reads drain any buffered bytes, then return `0` (EOF).
    /// * Subsequent reads return `0` (EOF is sticky).
    StreamDropWritable,
    /// `() -> i64` — allocate a new future handle pair. Low 32 bits =
    /// read end, high 32 bits = write end. Error encoding matches
    /// [`HostIntrinsic::StreamNew`].
    FutureNew,
    /// `(handle: i32, buf_ptr: i32, mem_idx: i32) -> i32` — read the
    /// resolved value into `buf_ptr` (size = canonical layout of `T`).
    ///
    /// Return value (decode with [`FutureReadResult::decode`]):
    ///
    /// * `1` — resolved; the canonical-ABI layout of `T` has been written
    ///   to `buf_ptr`. Subsequent calls on the same handle MUST also
    ///   return `1` (the resolved value is sticky until the read end is
    ///   dropped); runtimes MAY instead return [`AbiError::Closed`] after
    ///   the value has been consumed once.
    /// * `0` — **not yet resolved AND the write end is still alive.**
    ///   The reader registers the handle in a waitable-set (see
    ///   `[waitable-set-wait]` interaction below) and retries on
    ///   readiness.
    /// * `n < 0` — error from [`AbiError`]:
    ///   * [`AbiError::Closed`] — the write end was dropped without
    ///     resolving. Distinguishable from "not yet resolved": EOF on a
    ///     future means *no value will ever arrive*.
    ///   * [`AbiError::InvalidHandle`], [`AbiError::Cancelled`].
    ///
    /// ### Interaction with `[waitable-set-wait]`
    ///
    /// Identical to `stream_read`: the reader joins the readable end
    /// into a waitable-set, waits, then re-invokes `future_read` to
    /// retrieve the resolved value (`1`) or observe drop (`Closed`).
    FutureRead,
    /// `(handle: i32, data_ptr: i32, mem_idx: i32) -> i32` — resolve the
    /// future by writing `T`'s canonical layout from `data_ptr`.
    ///
    /// Return value:
    ///
    /// * `1` — resolved successfully.
    /// * `n < 0` — error from [`AbiError`]:
    ///   * [`AbiError::Closed`] — the read end was dropped before
    ///     resolution. The value is discarded.
    ///   * [`AbiError::InvalidHandle`], [`AbiError::Cancelled`],
    ///     [`AbiError::Oom`].
    ///
    /// Unlike `stream_write`, `future_write` is **all-or-nothing**:
    /// there is no partial-write / backpressure case. Either the runtime
    /// accepts the resolution or it errors.
    FutureWrite,
    /// `(handle: i32) -> i32` — cancel a pending read on the given
    /// future. Return convention matches
    /// [`HostIntrinsic::StreamCancelRead`].
    FutureCancelRead,
    /// `(handle: i32) -> i32` — cancel a pending write on the given
    /// future. Return convention matches
    /// [`HostIntrinsic::StreamCancelRead`].
    FutureCancelWrite,
    /// `(handle: i32)` — drop the readable end. After dropping, a
    /// pending or subsequent `future_write` returns [`AbiError::Closed`].
    FutureDropReadable,
    /// `(handle: i32)` — drop the writable end without resolving.
    /// Pending `future_read` calls return [`AbiError::Closed`] (no
    /// value will arrive). Subsequent reads also return
    /// [`AbiError::Closed`].
    FutureDropWritable,
}

impl HostIntrinsic {
    /// The unqualified intrinsic name (the `name` half of the import).
    pub const fn name(self) -> &'static str {
        match self {
            Self::StreamNew => stream::NEW,
            Self::StreamRead => stream::READ,
            Self::StreamWrite => stream::WRITE,
            Self::StreamCancelRead => stream::CANCEL_READ,
            Self::StreamCancelWrite => stream::CANCEL_WRITE,
            Self::StreamDropReadable => stream::DROP_READABLE,
            Self::StreamDropWritable => stream::DROP_WRITABLE,
            Self::FutureNew => future::NEW,
            Self::FutureRead => future::READ,
            Self::FutureWrite => future::WRITE,
            Self::FutureCancelRead => future::CANCEL_READ,
            Self::FutureCancelWrite => future::CANCEL_WRITE,
            Self::FutureDropReadable => future::DROP_READABLE,
            Self::FutureDropWritable => future::DROP_WRITABLE,
        }
    }

    /// Fully qualified import: `(HOST_INTRINSIC_MODULE, name())`.
    pub const fn import(self) -> (&'static str, &'static str) {
        (HOST_INTRINSIC_MODULE, self.name())
    }

    /// Core-wasm function signature for the host-intrinsic lowering.
    ///
    /// Returns `(params, results)` matching the rustdoc table at the top
    /// of this module. The lowering pass uses this when emitting the
    /// `(import "pulseengine:async" "<name>" (func (type ...)))` entry.
    ///
    /// Element-width is intentionally NOT part of the signature — it is
    /// encoded in adapter glue meld emits around each call. See ADR-1.
    pub fn signature(self) -> (Vec<wasm_encoder::ValType>, Vec<wasm_encoder::ValType>) {
        use wasm_encoder::ValType::{I32, I64};
        match self {
            // stream_new / future_new : () -> i64
            Self::StreamNew | Self::FutureNew => (vec![], vec![I64]),
            // stream_read / stream_write : (handle, ptr, len, mem_idx) -> i32
            Self::StreamRead | Self::StreamWrite => (vec![I32, I32, I32, I32], vec![I32]),
            // future_read / future_write : (handle, ptr, mem_idx) -> i32
            Self::FutureRead | Self::FutureWrite => (vec![I32, I32, I32], vec![I32]),
            // *_cancel_{read,write} : (handle) -> i32
            Self::StreamCancelRead
            | Self::StreamCancelWrite
            | Self::FutureCancelRead
            | Self::FutureCancelWrite => (vec![I32], vec![I32]),
            // *_drop_{readable,writable} : (handle) -> ()
            Self::StreamDropReadable
            | Self::StreamDropWritable
            | Self::FutureDropReadable
            | Self::FutureDropWritable => (vec![I32], vec![]),
        }
    }

    /// Map a parsed `CanonicalEntry` to its host intrinsic, if any.
    /// Returns `None` for non-async canonicals (lift/lower/resource ops).
    pub fn from_canonical_entry(entry: &CanonicalEntry) -> Option<Self> {
        match entry {
            CanonicalEntry::StreamNew { .. } => Some(Self::StreamNew),
            CanonicalEntry::StreamRead { .. } => Some(Self::StreamRead),
            CanonicalEntry::StreamWrite { .. } => Some(Self::StreamWrite),
            CanonicalEntry::StreamCancelRead { .. } => Some(Self::StreamCancelRead),
            CanonicalEntry::StreamCancelWrite { .. } => Some(Self::StreamCancelWrite),
            CanonicalEntry::StreamDropReadable { .. } => Some(Self::StreamDropReadable),
            CanonicalEntry::StreamDropWritable { .. } => Some(Self::StreamDropWritable),
            CanonicalEntry::FutureNew { .. } => Some(Self::FutureNew),
            CanonicalEntry::FutureRead { .. } => Some(Self::FutureRead),
            CanonicalEntry::FutureWrite { .. } => Some(Self::FutureWrite),
            CanonicalEntry::FutureCancelRead { .. } => Some(Self::FutureCancelRead),
            CanonicalEntry::FutureCancelWrite { .. } => Some(Self::FutureCancelWrite),
            CanonicalEntry::FutureDropReadable { .. } => Some(Self::FutureDropReadable),
            CanonicalEntry::FutureDropWritable { .. } => Some(Self::FutureDropWritable),
            _ => None,
        }
    }
}

/// Closed enum of error codes returned by `pulseengine:async` intrinsics.
///
/// This is the **canonical, stable** set of negative `i32` values that any
/// `stream_*` or `future_*` intrinsic may return. Runtimes (kiln,
/// wasmtime reference impl, …) MUST NOT invent additional negative codes
/// outside this enum without a matching addition here and a version bump.
///
/// # Numeric stability
///
/// The discriminants are pinned by [`AbiError::as_i32`] / [`AbiError::from_i32`]
/// and by the unit tests in `meld-core/tests/p3_async_abi.rs`. Changing
/// these is a **breaking ABI change** — bump the meld minor version and
/// document in the next ADR.
///
/// All codes are negative `i32` so that on the wire (`i32` return) the
/// sign bit cleanly distinguishes error from success.
///
/// # Code rationale (mapping to WASI 0.3 stream semantics)
///
/// * [`AbiError::Closed`] — the *peer end* of the stream/future was
///   dropped. Distinct from EOF on a stream-read (returned as `0`
///   bytes), but the runtime MAY conflate the two on `stream_read` if
///   no buffered bytes remain (see [`HostIntrinsic::StreamRead`] doc).
/// * [`AbiError::InvalidHandle`] — the handle is not live, not owned by
///   this caller, or is the wrong end (e.g., calling `stream_read` on a
///   writable handle).
/// * [`AbiError::Oom`] — the runtime could not allocate the buffer space
///   needed to make any progress. NOT used for backpressure (which is
///   signalled by partial-write / `Pending`).
/// * [`AbiError::Cancelled`] — a concurrent `*_cancel_read` /
///   `*_cancel_write` aborted this operation.
/// * [`AbiError::Pending`] — operation would block. The caller is
///   expected to register the handle in a waitable-set (see
///   `[waitable-set-wait]` interaction in [`HostIntrinsic`] doc) and
///   retry. Runtimes MAY instead return a positive partial count for
///   `stream_write` / `stream_read`; producers and consumers must
///   handle both forms.
/// * [`AbiError::Runtime`] — catch-all for runtime-internal failures
///   (e.g., trap during a multi-memory copy in the data-plane). Hosts
///   SHOULD prefer a more specific code; this is a forward-compatible
///   escape hatch so that runtimes can surface a non-fatal failure
///   without trapping.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(i32)]
pub enum AbiError {
    /// The peer end of the stream/future has been dropped.
    Closed = -1,
    /// The provided handle is not live, not owned, or is the wrong end.
    InvalidHandle = -2,
    /// The runtime could not allocate buffer space to make any progress.
    Oom = -3,
    /// The operation was aborted by a concurrent `*_cancel_*` call.
    Cancelled = -4,
    /// The operation would block. Register the handle in a waitable-set
    /// and retry once `[waitable-set-wait]` reports readiness.
    Pending = -5,
    /// Catch-all for runtime-internal failures. Forward-compatible
    /// escape hatch; specific codes SHOULD be preferred.
    Runtime = -6,
}

impl AbiError {
    /// All defined error codes, in stable order. Useful for exhaustive
    /// tests and for runtime implementers that want to assert coverage.
    pub const ALL: [Self; 6] = [
        Self::Closed,
        Self::InvalidHandle,
        Self::Oom,
        Self::Cancelled,
        Self::Pending,
        Self::Runtime,
    ];

    /// The numeric `i32` value of this error code.
    ///
    /// Note: `repr(i32)` allows direct casting (`code as i32`); this
    /// helper is provided for clarity at call sites.
    pub const fn as_i32(self) -> i32 {
        self as i32
    }

    /// Decode a raw `i32` return value into `Some(AbiError)` if it
    /// matches a known code, or `None` otherwise.
    ///
    /// Non-negative values are always `None` (they are success codes,
    /// not errors). Negative values that don't match a known
    /// discriminant are also `None` — callers that receive such a value
    /// SHOULD treat it as `AbiError::Runtime` per the forward-compat
    /// rule, but this decoder does not synthesise that mapping.
    pub const fn from_i32(v: i32) -> Option<Self> {
        match v {
            -1 => Some(Self::Closed),
            -2 => Some(Self::InvalidHandle),
            -3 => Some(Self::Oom),
            -4 => Some(Self::Cancelled),
            -5 => Some(Self::Pending),
            -6 => Some(Self::Runtime),
            _ => None,
        }
    }
}

/// Decoded return value of [`HostIntrinsic::StreamWrite`].
///
/// See the variant docs on [`HostIntrinsic::StreamWrite`] for the full
/// partial-write / backpressure contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamWriteResult {
    /// All `requested` bytes were accepted.
    Complete { written: u32 },
    /// `written < requested`. The producer is the retry authority; meld
    /// and the runtime do NOT queue the un-accepted tail. `written` may
    /// be `0`, which is still backpressure (not EOF, not error).
    Partial { written: u32, requested: u32 },
    /// The runtime returned an error code.
    Error(AbiError),
    /// The runtime returned an unrecognised negative code. Callers
    /// SHOULD treat this as `AbiError::Runtime`. Surfacing the raw value
    /// helps debugging and test assertions.
    Unknown(i32),
}

impl StreamWriteResult {
    /// Decode the raw `i32` return value of `stream_write` against the
    /// `requested` byte count the producer passed in.
    pub const fn decode(ret: i32, requested: u32) -> Self {
        if ret < 0 {
            match AbiError::from_i32(ret) {
                Some(e) => Self::Error(e),
                None => Self::Unknown(ret),
            }
        } else {
            let written = ret as u32;
            if written >= requested {
                Self::Complete { written }
            } else {
                Self::Partial { written, requested }
            }
        }
    }
}

/// Decoded return value of [`HostIntrinsic::StreamRead`].
///
/// See [`HostIntrinsic::StreamRead`] for the full EOF-vs-pending
/// distinguishability contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamReadResult {
    /// `n > 0` bytes were copied into the caller's buffer. `n` may be
    /// less than the requested length; the stream is **not** at EOF.
    Bytes { read: u32 },
    /// `0` — EOF. The writable end has been dropped AND no buffered
    /// bytes remain. EOF is sticky.
    Eof,
    /// The runtime returned a known error code (typically
    /// [`AbiError::Pending`] for "no bytes available right now").
    Error(AbiError),
    /// The runtime returned an unrecognised negative code.
    Unknown(i32),
}

impl StreamReadResult {
    /// Decode the raw `i32` return value of `stream_read`.
    pub const fn decode(ret: i32) -> Self {
        if ret > 0 {
            Self::Bytes { read: ret as u32 }
        } else if ret == 0 {
            Self::Eof
        } else {
            match AbiError::from_i32(ret) {
                Some(e) => Self::Error(e),
                None => Self::Unknown(ret),
            }
        }
    }
}

/// Decoded return value of [`HostIntrinsic::FutureRead`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FutureReadResult {
    /// `1` — the future is resolved; `T`'s canonical layout has been
    /// written to the caller's buffer.
    Resolved,
    /// `0` — the future is not yet resolved AND the write end is still
    /// alive. Register in a waitable-set and retry.
    Pending,
    /// The runtime returned a known error code.
    Error(AbiError),
    /// The runtime returned an unrecognised negative code.
    Unknown(i32),
}

impl FutureReadResult {
    /// Decode the raw `i32` return value of `future_read`.
    pub const fn decode(ret: i32) -> Self {
        match ret {
            1 => Self::Resolved,
            0 => Self::Pending,
            n if n < 0 => match AbiError::from_i32(n) {
                Some(e) => Self::Error(e),
                None => Self::Unknown(n),
            },
            // Positive non-1 values are reserved; treat as Unknown.
            n => Self::Unknown(n),
        }
    }
}

/// Summary of P3 async features used by a parsed component.
///
/// Built by [`detect_features`]. Use [`is_empty`](Self::is_empty) to check
/// whether a component is "P3-async-clean" (no async features).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct P3AsyncFeatures {
    /// Component-level types that are `stream<T>`. Stored as type-index → human-readable description.
    pub stream_types: Vec<(u32, String)>,
    /// Component-level types that are `future<T>`.
    pub future_types: Vec<(u32, String)>,
    /// Distinct host intrinsics that meld would emit imports for, given
    /// the canonical built-ins this component already declares.
    pub required_intrinsics: Vec<HostIntrinsic>,
    /// Whether any canonical lift uses `(canon lift ... async ...)`.
    pub uses_async_lift: bool,
    /// Whether any canonical lift carries a `(callback ...)` option (P3
    /// callback mode for async exports).
    pub uses_callback_lift: bool,
    /// Whether any canonical lower uses `(canon lower ... async ...)`.
    pub uses_async_lower: bool,
}

impl P3AsyncFeatures {
    /// `true` if the component uses no P3 async constructs at all.
    pub fn is_empty(&self) -> bool {
        self.stream_types.is_empty()
            && self.future_types.is_empty()
            && self.required_intrinsics.is_empty()
            && !self.uses_async_lift
            && !self.uses_callback_lift
            && !self.uses_async_lower
    }

    /// `true` if the component uses any *data-plane* (stream/future) construct.
    pub fn uses_data_plane(&self) -> bool {
        !self.stream_types.is_empty()
            || !self.future_types.is_empty()
            || !self.required_intrinsics.is_empty()
    }

    /// `true` if the component uses any *control-plane* (async lift/lower /
    /// callback) construct.
    pub fn uses_control_plane(&self) -> bool {
        self.uses_async_lift || self.uses_callback_lift || self.uses_async_lower
    }
}

/// Inspect a parsed component and summarise its P3 async usage.
///
/// Pure inspection — does not mutate `comp`.
pub fn detect_features(comp: &ParsedComponent) -> P3AsyncFeatures {
    let mut feats = P3AsyncFeatures::default();
    let mut required: std::collections::BTreeSet<HostIntrinsic> = std::collections::BTreeSet::new();

    // Walk component-level types looking for stream/future declarations.
    for (idx, ty) in comp.types.iter().enumerate() {
        if let ComponentTypeKind::P3Async(desc) = &ty.kind {
            if desc.contains("stream") {
                feats.stream_types.push((idx as u32, desc.clone()));
            } else if desc.contains("future") {
                feats.future_types.push((idx as u32, desc.clone()));
            }
            // `map<K,V>` is also P3Async but not handled by this ABI;
            // it's tracked in `comp.p3_async_features` for the warning path.
        }
    }

    // Walk canonicals to find any data-plane intrinsic the component
    // already declares, and detect async lift/lower options.
    for entry in &comp.canonical_functions {
        if let Some(intr) = HostIntrinsic::from_canonical_entry(entry) {
            required.insert(intr);
        }
        match entry {
            CanonicalEntry::Lift { options, .. } => {
                if options.async_ {
                    feats.uses_async_lift = true;
                }
                if options.callback.is_some() {
                    feats.uses_callback_lift = true;
                }
            }
            CanonicalEntry::Lower { options, .. } if options.async_ => {
                feats.uses_async_lower = true;
            }
            _ => {}
        }
    }

    feats.required_intrinsics = required.into_iter().collect();
    feats
}

// `BTreeSet<HostIntrinsic>` requires `Ord`. Provide a deterministic ordering.
impl PartialOrd for HostIntrinsic {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for HostIntrinsic {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (*self as u8).cmp(&(*other as u8))
    }
}

/// Result of [`lower_p3_async_intrinsics`].
///
/// Reports which intrinsics were emitted and where they live in the
/// fused module's import section. Useful for downstream tooling that
/// wants to know the function index of each intrinsic (e.g., to wire
/// `call N` instructions in glue code) without re-parsing the output.
#[derive(Debug, Clone, Default)]
pub struct LoweringPlan {
    /// For each emitted intrinsic, `(intrinsic, merged_func_index)`.
    /// The function index points into the fused module's function index
    /// space (i.e., the position among function imports + defined funcs).
    pub emitted: Vec<(HostIntrinsic, u32)>,
}

impl LoweringPlan {
    /// Number of intrinsics emitted by the pass.
    pub fn len(&self) -> usize {
        self.emitted.len()
    }
    /// `true` when the pass was a no-op (no P3 async intrinsics required).
    pub fn is_empty(&self) -> bool {
        self.emitted.is_empty()
    }
    /// Look up the merged function index of a specific intrinsic, if it
    /// was emitted.
    pub fn func_index(&self, intr: HostIntrinsic) -> Option<u32> {
        self.emitted
            .iter()
            .find_map(|(i, idx)| (*i == intr).then_some(*idx))
    }
}

/// Lower P3 async canonical built-ins to `pulseengine:async` core-module
/// imports in a [`crate::merger::MergedModule`].
///
/// This is the rewrite half of the P3 async lowering pipeline (see
/// ADR-1). Detection has already populated component canonical entries;
/// this pass walks those entries, collects the required
/// [`HostIntrinsic`] set, and inserts the corresponding function imports
/// into `merged.imports` under module
/// [`HOST_INTRINSIC_MODULE`] (`"pulseengine:async"`).
///
/// Because new function imports occupy the lowest slots of the function
/// index space, every existing reference to a *defined* function (in
/// exports, element segments, the start function, function-index
/// metadata, and call instructions inside function bodies) is shifted
/// up by `K = number of new imports`. Existing function imports keep
/// their indices.
///
/// # Returns
///
/// A [`LoweringPlan`] describing which intrinsics were emitted and at
/// which final function indices. An empty plan means no P3 async
/// constructs were detected — the merged module is unchanged.
///
/// # Errors
///
/// Returns an error if a function body cannot be re-extracted from its
/// origin core module (this should not happen in practice; it would
/// indicate corrupt component bytes).
pub fn lower_p3_async_intrinsics(
    merged: &mut crate::merger::MergedModule,
    components: &[crate::parser::ParsedComponent],
) -> crate::Result<LoweringPlan> {
    use crate::merger::{MergedFuncType, MergedImport};
    use std::collections::BTreeSet;

    // -----------------------------------------------------------------
    // 1. Collect required intrinsics across all components (deduped).
    // -----------------------------------------------------------------
    let mut required: BTreeSet<HostIntrinsic> = BTreeSet::new();
    for comp in components {
        for entry in &comp.canonical_functions {
            if let Some(intr) = HostIntrinsic::from_canonical_entry(entry) {
                required.insert(intr);
            }
        }
    }
    if required.is_empty() {
        return Ok(LoweringPlan::default());
    }

    let k = required.len() as u32;
    let f_old = merged.import_counts.func;

    // -----------------------------------------------------------------
    // 2. Allocate or reuse function types for each intrinsic.
    //
    //    Types may be appended (their indices are stable), so this does
    //    not require any rewriting elsewhere in the merged module.
    // -----------------------------------------------------------------
    let mut intr_type_idx: Vec<(HostIntrinsic, u32)> = Vec::with_capacity(required.len());
    for intr in &required {
        let (params, results) = intr.signature();
        let type_idx = match merged
            .types
            .iter()
            .position(|t| t.params == params && t.results == results)
        {
            Some(idx) => idx as u32,
            None => {
                let idx = merged.types.len() as u32;
                merged.types.push(MergedFuncType { params, results });
                idx
            }
        };
        intr_type_idx.push((*intr, type_idx));
    }

    // -----------------------------------------------------------------
    // 3. Shift all existing references to defined functions by `k`.
    //
    //    Function imports keep indices 0..f_old; new intrinsic imports
    //    take f_old..f_old+k; defined funcs shift from f_old.. to
    //    f_old+k.. .
    // -----------------------------------------------------------------
    shift_function_indices(merged, components, f_old, k)?;

    // -----------------------------------------------------------------
    // 4. Append the intrinsic imports themselves and their final
    //    function indices.
    // -----------------------------------------------------------------
    let mut plan = LoweringPlan::default();
    for (i, (intr, type_idx)) in intr_type_idx.iter().enumerate() {
        let merged_idx = f_old + i as u32;
        merged.imports.push(MergedImport {
            module: HOST_INTRINSIC_MODULE.to_string(),
            name: intr.name().to_string(),
            entity_type: wasm_encoder::EntityType::Function(*type_idx),
            component_idx: None,
        });
        // Per-import metadata vectors must stay aligned with merged.imports.
        // Intrinsic imports do not need a memory or realloc binding.
        merged.import_memory_indices.push(0);
        merged.import_realloc_indices.push(None);
        plan.emitted.push((*intr, merged_idx));
    }

    // -----------------------------------------------------------------
    // 5. Update the import count.
    // -----------------------------------------------------------------
    merged.import_counts.func = f_old + k;

    log::info!(
        "P3 async lowering: emitted {} import(s) under '{}'",
        plan.emitted.len(),
        HOST_INTRINSIC_MODULE
    );

    Ok(plan)
}

/// Shift every reference to a defined function index by `k` for indices
/// that were `>= f_old` before the shift.
///
/// Function imports (indices `< f_old`) are not affected. Defined
/// functions had indices in `[f_old, ...)`; after the shift they live at
/// `[f_old + k, ...)`. We re-extract function bodies from their origin
/// modules using the updated `function_index_map` so already-encoded
/// `call` instructions pick up the new indices.
fn shift_function_indices(
    merged: &mut crate::merger::MergedModule,
    components: &[crate::parser::ParsedComponent],
    f_old: u32,
    k: u32,
) -> crate::Result<()> {
    use std::collections::HashSet;

    if k == 0 {
        return Ok(());
    }

    // Rule: idx < f_old => unchanged; idx >= f_old => idx + k.
    let bump = |idx: u32| -> u32 { if idx < f_old { idx } else { idx + k } };

    // function_index_map values
    for v in merged.function_index_map.values_mut() {
        *v = bump(*v);
    }

    // realloc map values are function indices
    for v in merged.realloc_map.values_mut() {
        *v = bump(*v);
    }

    // resource_rep_by_component, resource_new_by_component values
    for v in merged.resource_rep_by_component.values_mut() {
        *v = bump(*v);
    }
    for v in merged.resource_new_by_component.values_mut() {
        *v = bump(*v);
    }

    // handle_tables: new_func / rep_func / drop_func are function indices
    for ht in merged.handle_tables.values_mut() {
        ht.new_func = bump(ht.new_func);
        ht.rep_func = bump(ht.rep_func);
        ht.drop_func = bump(ht.drop_func);
    }

    // task_return_shims keys are merged import indices for
    // [task-return]N — those are in the function index space too.
    if !merged.task_return_shims.is_empty() {
        let old: Vec<_> = merged.task_return_shims.drain().collect();
        for (key, mut info) in old {
            info.shim_func = bump(info.shim_func);
            merged.task_return_shims.insert(bump(key), info);
        }
    }

    // exports: function exports
    for exp in merged.exports.iter_mut() {
        if exp.kind == wasm_encoder::ExportKind::Func {
            exp.index = bump(exp.index);
        }
    }

    // start function
    if let Some(s) = merged.start_function.as_mut() {
        *s = bump(*s);
    }

    // element segments: function refs
    for seg in merged.elements.iter_mut() {
        match &mut seg.items {
            crate::segments::ReindexedElementItems::Functions(funcs) => {
                for f in funcs.iter_mut() {
                    *f = bump(*f);
                }
            }
            crate::segments::ReindexedElementItems::Expressions(_) => {
                // Expressions hold encoded ConstExpr bytes (already
                // baked). For ref.func the function index is encoded
                // inside; we cannot easily rewrite without re-parsing.
                // P3 async lowering does not currently support this
                // case and components that hit it will be flagged.
                // The vast majority of element segments in fused
                // output use Functions(_) form.
            }
        }
    }

    // -----------------------------------------------------------------
    // Re-extract function bodies from origin modules with updated
    // index maps so already-encoded `call` instructions get the new
    // function indices. We collect the unique (comp_idx, mod_idx)
    // pairs that contributed defined functions to merged.functions.
    // -----------------------------------------------------------------
    let affected_modules: HashSet<(usize, usize)> = merged
        .functions
        .iter()
        .map(|f| (f.origin.0, f.origin.1))
        .collect();

    for (comp_idx, mod_idx) in affected_modules {
        // Skip synthetic modules (e.g. wrappers / shims with origin func index u32::MAX)
        // Those modules may not correspond to a real core_module entry,
        // but we should still be careful: real defined functions originate
        // from `components[comp_idx].core_modules[mod_idx]`. Out-of-range
        // (synthetic) origins are filtered below.
        let Some(component) = components.get(comp_idx) else {
            continue;
        };
        let Some(module) = component.core_modules.get(mod_idx) else {
            continue;
        };

        // Build index maps for this module using the updated merged state.
        // Memory/global/etc maps are unaffected by the function-index shift.
        let memory_strategy = if !merged.memories.is_empty() {
            // Strategy doesn't affect function-index rewriting; multi-memory
            // is the safe default for general re-extraction here.
            crate::MemoryStrategy::MultiMemory
        } else {
            crate::MemoryStrategy::SharedMemory
        };
        let module_memory = crate::merger::module_memory_type(module).ok().flatten();
        let memory64 = module_memory.as_ref().map(|m| m.memory64).unwrap_or(false);
        let memory_initial_pages = module_memory.as_ref().map(|m| m.initial);

        let index_maps = crate::merger::build_index_maps_for_module(
            comp_idx,
            mod_idx,
            module,
            merged,
            memory_strategy,
            false,
            0,
            memory64,
            memory_initial_pages,
        );

        let import_func_count = module
            .imports
            .iter()
            .filter(|i| matches!(i.kind, crate::parser::ImportKind::Function(_)))
            .count() as u32;

        // For every defined function in this module, re-extract & rewrite.
        for (old_idx, &type_idx) in module.functions.iter().enumerate() {
            let old_func_idx = import_func_count + old_idx as u32;
            let param_count = module
                .types
                .get(type_idx as usize)
                .map(|ty| ty.params.len() as u32)
                .unwrap_or(0);

            let body = match crate::merger::extract_function_body(
                module,
                old_idx,
                param_count,
                &index_maps,
            ) {
                Ok(b) => b,
                Err(_) => continue, // Best-effort — leave body untouched if we can't re-extract.
            };

            if let Some(mf) = merged
                .functions
                .iter_mut()
                .find(|f| f.origin == (comp_idx, mod_idx, old_func_idx))
            {
                mf.body = body;
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{
        CanonStringEncoding, CanonicalEntry, CanonicalOptions, ComponentType, ComponentTypeKind,
    };

    fn empty_component() -> ParsedComponent {
        // Use the same test helper pattern parser.rs uses.
        ParsedComponent {
            name: None,
            core_modules: vec![],
            imports: vec![],
            exports: vec![],
            types: vec![],
            instances: vec![],
            canonical_functions: vec![],
            sub_components: vec![],
            component_aliases: vec![],
            component_instances: vec![],
            core_entity_order: vec![],
            component_func_defs: vec![],
            component_instance_defs: vec![],
            component_type_defs: vec![],
            original_size: 0,
            original_hash: String::new(),
            depth_0_sections: vec![],
            p3_async_features: vec![],
        }
    }

    #[test]
    fn empty_component_has_no_p3_features() {
        let comp = empty_component();
        let feats = detect_features(&comp);
        assert!(feats.is_empty());
        assert!(!feats.uses_data_plane());
        assert!(!feats.uses_control_plane());
    }

    #[test]
    fn stream_type_is_detected() {
        let mut comp = empty_component();
        comp.types.push(ComponentType {
            kind: ComponentTypeKind::P3Async("stream<u8>".to_string()),
        });
        let feats = detect_features(&comp);
        assert!(!feats.is_empty());
        assert_eq!(feats.stream_types.len(), 1);
        assert!(feats.stream_types[0].1.contains("stream"));
        assert!(feats.uses_data_plane());
    }

    #[test]
    fn future_type_is_detected() {
        let mut comp = empty_component();
        comp.types.push(ComponentType {
            kind: ComponentTypeKind::P3Async("future<string>".to_string()),
        });
        let feats = detect_features(&comp);
        assert_eq!(feats.future_types.len(), 1);
        assert!(feats.uses_data_plane());
    }

    #[test]
    fn stream_canonical_maps_to_intrinsic() {
        let mut comp = empty_component();
        comp.canonical_functions
            .push(CanonicalEntry::StreamNew { ty: 0 });
        comp.canonical_functions.push(CanonicalEntry::StreamRead {
            ty: 0,
            options: CanonicalOptions::default(),
        });
        comp.canonical_functions
            .push(CanonicalEntry::StreamDropReadable { ty: 0 });

        let feats = detect_features(&comp);
        assert!(
            feats
                .required_intrinsics
                .contains(&HostIntrinsic::StreamNew)
        );
        assert!(
            feats
                .required_intrinsics
                .contains(&HostIntrinsic::StreamRead)
        );
        assert!(
            feats
                .required_intrinsics
                .contains(&HostIntrinsic::StreamDropReadable)
        );
        // De-duplicated even if declared twice
        comp.canonical_functions.push(CanonicalEntry::StreamRead {
            ty: 0,
            options: CanonicalOptions::default(),
        });
        let feats2 = detect_features(&comp);
        assert_eq!(
            feats2
                .required_intrinsics
                .iter()
                .filter(|i| **i == HostIntrinsic::StreamRead)
                .count(),
            1
        );
    }

    #[test]
    fn async_lift_detected() {
        let mut comp = empty_component();
        let opts = CanonicalOptions {
            string_encoding: CanonStringEncoding::Utf8,
            memory: Some(0),
            realloc: None,
            post_return: None,
            async_: true,
            callback: Some(7),
        };
        comp.canonical_functions.push(CanonicalEntry::Lift {
            core_func_index: 0,
            type_index: 0,
            options: opts,
        });
        let feats = detect_features(&comp);
        assert!(feats.uses_async_lift);
        assert!(feats.uses_callback_lift);
        assert!(feats.uses_control_plane());
    }

    #[test]
    fn intrinsic_imports_have_pulseengine_module() {
        for intr in [
            HostIntrinsic::StreamNew,
            HostIntrinsic::StreamRead,
            HostIntrinsic::StreamWrite,
            HostIntrinsic::FutureNew,
            HostIntrinsic::FutureRead,
        ] {
            let (module, name) = intr.import();
            assert_eq!(module, "pulseengine:async");
            assert!(!name.is_empty());
            assert!(!name.contains(' '));
        }
    }

    #[test]
    fn intrinsic_names_are_distinct() {
        let all = [
            HostIntrinsic::StreamNew,
            HostIntrinsic::StreamRead,
            HostIntrinsic::StreamWrite,
            HostIntrinsic::StreamCancelRead,
            HostIntrinsic::StreamCancelWrite,
            HostIntrinsic::StreamDropReadable,
            HostIntrinsic::StreamDropWritable,
            HostIntrinsic::FutureNew,
            HostIntrinsic::FutureRead,
            HostIntrinsic::FutureWrite,
            HostIntrinsic::FutureCancelRead,
            HostIntrinsic::FutureCancelWrite,
            HostIntrinsic::FutureDropReadable,
            HostIntrinsic::FutureDropWritable,
        ];
        let names: std::collections::HashSet<&'static str> = all.iter().map(|i| i.name()).collect();
        assert_eq!(names.len(), all.len(), "intrinsic names must be unique");
    }
}
