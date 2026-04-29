//! Pin tests for the `pulseengine:async` error-and-backpressure ABI
//! (issue #121, ADR-2).
//!
//! These tests are **encoding-only**. Meld is a build-time tool and does
//! not run a P3 runtime; nothing here exercises real stream / future
//! intrinsics. What they DO exercise is the wire-level convention any
//! conforming runtime (kiln, the wasmtime reference impl, …) MUST
//! reproduce:
//!
//! 1. Closed enum `AbiError` has stable, non-overlapping `i32`
//!    discriminants in the negative half-plane.
//! 2. `StreamWriteResult::decode` distinguishes complete writes,
//!    partial-write backpressure (including the `written == 0` corner),
//!    and errors. The producer is the retry authority — the runtime does
//!    NOT queue the tail; the decoder simply surfaces the count.
//! 3. `StreamReadResult::decode` distinguishes `Bytes`, `Eof` (`0`), and
//!    `Pending` (`-5`). EOF and "no bytes available right now" map to
//!    different variants — this is what issue #121 asks us to pin.
//! 4. `FutureReadResult::decode` separates `Resolved` (`1`), `Pending`
//!    (`0`), and `Closed` (`-1`).
//!
//! Changing any numeric value in `AbiError` is a **breaking ABI change**
//! and must update both this test and ADR-2.

use meld_core::p3_async::{AbiError, FutureReadResult, StreamReadResult, StreamWriteResult};

// ---------------------------------------------------------------------------
// AbiError — closed enum with pinned numeric values
// ---------------------------------------------------------------------------

/// Pin the numeric value of every `AbiError` variant. Any change here is
/// a breaking ABI change and must be coordinated with ADR-2 and runtime
/// implementers.
#[test]
fn abi_error_numeric_values_are_pinned() {
    assert_eq!(AbiError::Closed.as_i32(), -1);
    assert_eq!(AbiError::InvalidHandle.as_i32(), -2);
    assert_eq!(AbiError::Oom.as_i32(), -3);
    assert_eq!(AbiError::Cancelled.as_i32(), -4);
    assert_eq!(AbiError::Pending.as_i32(), -5);
    assert_eq!(AbiError::Runtime.as_i32(), -6);
}

/// `AbiError` discriminants must all be negative (the sign bit is the
/// success/error discriminator on the wire).
#[test]
fn all_abi_errors_are_negative() {
    for e in AbiError::ALL {
        assert!(
            e.as_i32() < 0,
            "AbiError variant {e:?} has non-negative wire value {}",
            e.as_i32()
        );
    }
}

/// `AbiError::ALL` is in stable order (matches numeric order, descending
/// magnitude / ascending negativity).
#[test]
fn abi_error_all_is_in_stable_order() {
    let codes: Vec<i32> = AbiError::ALL.iter().map(|e| e.as_i32()).collect();
    assert_eq!(codes, vec![-1, -2, -3, -4, -5, -6]);
}

/// All variants in `AbiError::ALL` must have distinct numeric values.
/// Belt-and-braces guard against accidental discriminant collisions if
/// someone reorders the enum.
#[test]
fn abi_error_values_are_distinct() {
    let mut codes: Vec<i32> = AbiError::ALL.iter().map(|e| e.as_i32()).collect();
    codes.sort();
    let len_before = codes.len();
    codes.dedup();
    assert_eq!(
        codes.len(),
        len_before,
        "AbiError discriminants must be distinct"
    );
}

/// `from_i32` is the inverse of `as_i32` for every defined variant, and
/// returns `None` for non-negative values and unknown negative codes.
#[test]
fn abi_error_from_i32_round_trips() {
    for e in AbiError::ALL {
        assert_eq!(AbiError::from_i32(e.as_i32()), Some(e));
    }
    // Success codes are not errors.
    assert_eq!(AbiError::from_i32(0), None);
    assert_eq!(AbiError::from_i32(1), None);
    assert_eq!(AbiError::from_i32(i32::MAX), None);
    // Unknown negative codes return None — caller is expected to map to
    // AbiError::Runtime per the forward-compat rule (documented).
    assert_eq!(AbiError::from_i32(-7), None);
    assert_eq!(AbiError::from_i32(i32::MIN), None);
}

// ---------------------------------------------------------------------------
// StreamWriteResult — partial-write / backpressure semantics
// ---------------------------------------------------------------------------

/// A write that accepts every byte requested is `Complete`.
#[test]
fn stream_write_complete_when_all_bytes_accepted() {
    match StreamWriteResult::decode(64, 64) {
        StreamWriteResult::Complete { written } => assert_eq!(written, 64),
        other => panic!("expected Complete, got {other:?}"),
    }
}

/// `written < requested` is **partial / backpressure** — NOT EOF, NOT
/// error. The producer is responsible for retrying with the un-accepted
/// tail.
#[test]
fn stream_write_partial_is_backpressure_not_eof() {
    match StreamWriteResult::decode(20, 64) {
        StreamWriteResult::Partial { written, requested } => {
            assert_eq!(written, 20);
            assert_eq!(requested, 64);
        }
        other => panic!("expected Partial, got {other:?}"),
    }
}

/// `written == 0` with a positive `requested` is **still backpressure**,
/// not EOF or error. This is the corner case issue #121 calls out:
/// `stream_write` returning `0` bytes accepted means "no progress right
/// now"; producers retry like any other partial.
#[test]
fn stream_write_zero_accepted_is_partial_not_error() {
    match StreamWriteResult::decode(0, 64) {
        StreamWriteResult::Partial { written, requested } => {
            assert_eq!(written, 0);
            assert_eq!(requested, 64);
        }
        other => panic!("expected Partial(0, 64), got {other:?}"),
    }
}

/// A `requested == 0` empty write that returns `0` is `Complete` —
/// vacuously, all zero requested bytes were accepted.
#[test]
fn stream_write_zero_requested_zero_written_is_complete() {
    match StreamWriteResult::decode(0, 0) {
        StreamWriteResult::Complete { written } => assert_eq!(written, 0),
        other => panic!("expected Complete, got {other:?}"),
    }
}

/// Negative return values decode to the matching `AbiError`.
#[test]
fn stream_write_error_codes_decode_to_abi_error() {
    let cases = [
        (-1, AbiError::Closed),
        (-2, AbiError::InvalidHandle),
        (-3, AbiError::Oom),
        (-4, AbiError::Cancelled),
        (-5, AbiError::Pending),
        (-6, AbiError::Runtime),
    ];
    for (raw, expected) in cases {
        match StreamWriteResult::decode(raw, 32) {
            StreamWriteResult::Error(e) => assert_eq!(e, expected, "raw {raw}"),
            other => panic!("raw {raw}: expected Error({expected:?}), got {other:?}"),
        }
    }
}

/// Unknown negative codes surface as `Unknown`, preserving the raw value
/// for diagnostics. Forward-compat: callers SHOULD map these to
/// `AbiError::Runtime`, but the decoder doesn't synthesise the mapping.
#[test]
fn stream_write_unknown_negative_is_preserved() {
    match StreamWriteResult::decode(-99, 32) {
        StreamWriteResult::Unknown(v) => assert_eq!(v, -99),
        other => panic!("expected Unknown(-99), got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// StreamReadResult — EOF distinguishability from "0 bytes available"
// ---------------------------------------------------------------------------

/// Positive return is `Bytes` (read N bytes, may be < buffer length).
#[test]
fn stream_read_positive_is_bytes() {
    match StreamReadResult::decode(7) {
        StreamReadResult::Bytes { read } => assert_eq!(read, 7),
        other => panic!("expected Bytes, got {other:?}"),
    }
}

/// `0` from `stream_read` is **EOF**, not "no bytes right now". Issue
/// #121 explicitly calls for this distinguishability.
#[test]
fn stream_read_zero_is_eof() {
    assert_eq!(StreamReadResult::decode(0), StreamReadResult::Eof);
}

/// "No bytes right now (still open)" is `AbiError::Pending`, distinct
/// from EOF. This is the core issue-#121 contract.
#[test]
fn stream_read_pending_is_distinct_from_eof() {
    let pending = StreamReadResult::decode(AbiError::Pending.as_i32());
    let eof = StreamReadResult::decode(0);
    assert_ne!(pending, eof);
    assert_eq!(pending, StreamReadResult::Error(AbiError::Pending));
    assert_eq!(eof, StreamReadResult::Eof);
}

/// All `AbiError` codes round-trip through `StreamReadResult::decode`.
#[test]
fn stream_read_error_codes_decode_to_abi_error() {
    for e in AbiError::ALL {
        match StreamReadResult::decode(e.as_i32()) {
            StreamReadResult::Error(decoded) => assert_eq!(decoded, e),
            other => panic!("decoding {e:?} produced {other:?}"),
        }
    }
}

/// Unknown negative codes surface as `Unknown`.
#[test]
fn stream_read_unknown_negative_is_preserved() {
    match StreamReadResult::decode(-42) {
        StreamReadResult::Unknown(v) => assert_eq!(v, -42),
        other => panic!("expected Unknown(-42), got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// FutureReadResult — Resolved (1) vs Pending (0) vs Closed (-1)
// ---------------------------------------------------------------------------

#[test]
fn future_read_one_is_resolved() {
    assert_eq!(FutureReadResult::decode(1), FutureReadResult::Resolved);
}

/// `0` from `future_read` is **Pending**, not "future EOF". A future
/// with a dropped write end returns `Closed` instead.
#[test]
fn future_read_zero_is_pending_not_closed() {
    let pending = FutureReadResult::decode(0);
    let closed = FutureReadResult::decode(AbiError::Closed.as_i32());
    assert_ne!(pending, closed);
    assert_eq!(pending, FutureReadResult::Pending);
    assert_eq!(closed, FutureReadResult::Error(AbiError::Closed));
}

#[test]
fn future_read_error_codes_decode_to_abi_error() {
    for e in AbiError::ALL {
        match FutureReadResult::decode(e.as_i32()) {
            FutureReadResult::Error(decoded) => assert_eq!(decoded, e),
            other => panic!("decoding {e:?} produced {other:?}"),
        }
    }
}

/// Positive non-1 values are reserved; treated as `Unknown` so future
/// extensions (e.g., `2 = "resolved with multi-value"`) can be added
/// without retagging the existing variants.
#[test]
fn future_read_positive_non_one_is_unknown() {
    match FutureReadResult::decode(2) {
        FutureReadResult::Unknown(v) => assert_eq!(v, 2),
        other => panic!("expected Unknown(2), got {other:?}"),
    }
}

#[test]
fn future_read_unknown_negative_is_preserved() {
    match FutureReadResult::decode(-77) {
        FutureReadResult::Unknown(v) => assert_eq!(v, -77),
        other => panic!("expected Unknown(-77), got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Cross-cutting: AbiError numeric values must agree across decoders
// ---------------------------------------------------------------------------

/// The same negative `i32` must decode to the same `AbiError` across
/// `StreamReadResult`, `StreamWriteResult`, and `FutureReadResult`.
/// Catches divergent decoding tables if the convention drifts.
#[test]
fn error_codes_are_consistent_across_decoders() {
    for e in AbiError::ALL {
        let raw = e.as_i32();

        let r = StreamReadResult::decode(raw);
        let w = StreamWriteResult::decode(raw, 16);
        let f = FutureReadResult::decode(raw);

        match (r, w, f) {
            (
                StreamReadResult::Error(a),
                StreamWriteResult::Error(b),
                FutureReadResult::Error(c),
            ) => {
                assert_eq!(a, e);
                assert_eq!(b, e);
                assert_eq!(c, e);
            }
            other => {
                panic!("code {raw} ({e:?}) decoded inconsistently across result types: {other:?}")
            }
        }
    }
}
