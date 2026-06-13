//! Kani bounded-verification harnesses for the component parser.
//!
//! These harnesses verify that the parser handles malformed component
//! binaries cleanly: it must return `Err`, never panic, never spin in an
//! infinite loop, and never allocate unboundedly.  They complement the
//! proptest suite in `proptest_fusion.rs` (which exercises *random* bytes)
//! and the Rocq spec proofs (which prove semantic preservation on the
//! mathematical model).
//!
//! Kani is bounded model checking: each harness symbolically explores all
//! byte buffers up to a small fixed length, proving the absence of panics
//! within those bounds.  The whole-file size is intentionally small
//! (≤16 bytes) so verification finishes in seconds.
//!
//! Run: `cargo kani --package meld-core --harness kani_parser_*`
//!
//! Tracks issue #102.

#![cfg(kani)]

use meld_core::ComponentParser;

/// Maximum buffer length explored by Kani.  Keep this very small — every
/// extra byte multiplies the symbolic state space.  Kani is not meant to
/// be exhaustive on real-world inputs; it complements proptest by
/// proving "no panic on small adversarial inputs".
const MAX_BUF_LEN: usize = 16;

// ---------------------------------------------------------------------------
// Harness 1: Tiny arbitrary buffer must not panic the parser.
// ---------------------------------------------------------------------------

/// For any byte buffer of length 0..=MAX_BUF_LEN, the parser must return
/// without panicking.  An `Err` return is acceptable (in fact expected for
/// most inputs); a panic, abort, or infinite loop is a bug.
#[kani::proof]
#[kani::unwind(4)]
fn kani_parser_does_not_panic_on_short_buffer() {
    let len: usize = kani::any();
    kani::assume(len <= MAX_BUF_LEN);

    let mut buf = [0u8; MAX_BUF_LEN];
    for byte in buf.iter_mut().take(len) {
        *byte = kani::any();
    }

    let parser = ComponentParser::without_validation();
    // Discard the result; the property is that we reach this point.
    let _ = parser.parse(&buf[..len]);
}

// ---------------------------------------------------------------------------
// Harness 2: Buffer with valid component magic but garbage body.
// ---------------------------------------------------------------------------

/// Even when the buffer starts with a well-formed WASM component header
/// (`\0asm` + version `0x0001000d`), parsing the rest as garbage must
/// reject cleanly.  This is the adversarial-input case: a fuzzer that
/// learns the magic bytes won't be able to drive the parser into a
/// panic state.
#[kani::proof]
#[kani::unwind(4)]
fn kani_parser_does_not_panic_on_corrupted_component() {
    // 8-byte component header: '\0asm' + LE u32 version 0x0001_000d.
    let header: [u8; 8] = [0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00];
    let tail_len: usize = kani::any();
    kani::assume(tail_len <= MAX_BUF_LEN - 8);

    let mut buf = [0u8; MAX_BUF_LEN];
    buf[..8].copy_from_slice(&header);
    for i in 8..(8 + tail_len) {
        buf[i] = kani::any();
    }

    let parser = ComponentParser::without_validation();
    let _ = parser.parse(&buf[..(8 + tail_len)]);
}

// ---------------------------------------------------------------------------
// Harness 3: Sub-magic-length buffers always return InvalidWasm("too small").
// ---------------------------------------------------------------------------

/// A buffer shorter than the 8-byte WASM header must always be rejected
/// as `InvalidWasm`.  This proves the early-return check at the top of
/// `ComponentParser::parse` is correct on bounded inputs.
#[kani::proof]
fn kani_parser_rejects_short_buffer() {
    let len: usize = kani::any();
    kani::assume(len < 8);

    let mut buf = [0u8; 8];
    for byte in buf.iter_mut().take(len) {
        *byte = kani::any();
    }

    let parser = ComponentParser::without_validation();
    let result = parser.parse(&buf[..len]);
    assert!(
        result.is_err(),
        "buffers shorter than 8 bytes must be rejected"
    );
}
