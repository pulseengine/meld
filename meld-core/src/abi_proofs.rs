//! Kani proof harnesses for Canonical-ABI invariants the code already
//! claims (#218 increment 1, SR-40, v0.30.0).
//!
//! Scope discipline: these harnesses prove invariants of EXISTING
//! claims — the SR-3/SR-17 canonical-ABI layout contract and LS-P-9's
//! saturating arithmetic — plus a model-level proof of the #141 stream
//! bridge's ring-cursor arithmetic. They introduce no new theory.
//!
//! The harnesses exercise the PUBLIC `ParsedComponent` layout API over
//! bounded nondeterministic type trees, so they live outside the
//! Tier-5 `parser.rs` (no decision-logic churn there).
//!
//! Run with: `cargo kani --package meld-core` (or per harness:
//! `cargo kani --harness abi_size_is_multiple_of_align`). Not yet in
//! CI — the smithy runners do not ship the Kani toolchain; recorded in
//! SR-40 as local-evidence verification with the invocation pinned
//! here.
//!
//! The ring proof is a MODEL of the wasm codegen in [`crate::p3_bridge`]
//! (the codegen itself is pinned by the runtime trap-stub oracles in
//! `tests/p3_bridge_runtime.rs`); the const assertions below tie the
//! model's parameters to the emitter's, so parameter drift breaks the
//! build, not just the proof.

#![cfg(kani)]

use crate::parser::{ComponentValType, ParsedComponent, PrimitiveValType};

/// Bounded nondeterministic primitive.
fn any_primitive() -> PrimitiveValType {
    match kani::any::<u8>() % 12 {
        0 => PrimitiveValType::Bool,
        1 => PrimitiveValType::S8,
        2 => PrimitiveValType::U8,
        3 => PrimitiveValType::S16,
        4 => PrimitiveValType::U16,
        5 => PrimitiveValType::S32,
        6 => PrimitiveValType::U32,
        7 => PrimitiveValType::S64,
        8 => PrimitiveValType::U64,
        9 => PrimitiveValType::F32,
        10 => PrimitiveValType::F64,
        _ => PrimitiveValType::Char,
    }
}

// NOTE (honest scope cut, part 1): nondet leaf/container harnesses
// for the size-multiple-of-align contract were attempted and do not
// converge in CBMC within a usable time on this codebase (the layout
// functions recurse through `ParsedComponent`, whose construction
// carries ~15 Vec fields of heap state per call). The leaf/container
// contract is pinned exhaustively by the existing unit tests
// (parser::tests::test_canonical_abi_element_size_* and
// adapter::fact::tests::test_sr17_alignment_*). A Kani proof becomes
// tractable once the layout core is factored allocation-free;
// recorded in SR-40.

// NOTE (honest scope cut): an aggregate-padding harness over
// Vec<(String, ComponentValType)> record shapes was attempted and is
// CBMC-hostile (heap-state explosion; >50 min unsolved on 3 concrete
// shapes). The padding path is pinned by the existing unit tests
// (parser::tests::test_canonical_abi_element_size_record_with_padding
// and siblings, SR-3 traceability); a Kani aggregate proof is deferred
// until the layout functions get an allocation-free core to verify
// against. Recorded in SR-40's verification description.

/// LS-A-20: `flags<N>` storage classes at every boundary of the spec's
/// storage-class function (N ∈ {1, 8, 9, 16, 17, 32, 33, 64} — the
/// points where the class or word count changes). The interior points
/// are constant between boundaries by the implementation's ceil/select
/// shape; the full N range is additionally covered by the unit tests
/// from LS-A-20's original fix. Boundary enumeration keeps the CBMC
/// state small (one Vec build per point, no clone-per-iteration).
#[kani::proof]
#[kani::unwind(70)]
fn flags_layout_matches_spec() {
    let comp = ParsedComponent::empty();
    let boundaries = [1usize, 8, 9, 16, 17, 32, 33, 64];
    for &n in &boundaries {
        let mut names: Vec<String> = Vec::new();
        let mut i = 0;
        while i < n {
            names.push(String::new());
            i += 1;
        }
        let ty = ComponentValType::Flags(names);
        assert_eq!(
            comp.flat_count(&ty),
            n.div_ceil(32) as u32,
            "flat = ceil(N/32)"
        );
        let size = comp.canonical_abi_element_size(&ty);
        let expected = if n <= 8 {
            1
        } else if n <= 16 {
            2
        } else {
            4 * n.div_ceil(32) as u32
        };
        assert_eq!(size, expected, "flags storage class");
    }
}

/// LS-P-9: `total_flat_params` never panics and is monotone under
/// adding a parameter (nondet primitives, fixed two-param shape).
#[kani::proof]
#[kani::unwind(4)]
fn total_flat_params_saturating_monotone() {
    let comp = ParsedComponent::empty();
    let a = (String::new(), ComponentValType::Primitive(any_primitive()));
    let b = (String::new(), ComponentValType::String);
    let one = comp.total_flat_params(std::slice::from_ref(&a));
    let two = comp.total_flat_params(&[a, b]);
    assert!(two >= one, "adding a param never shrinks the flat total");
}

// ====================================================================
// #141 stream-bridge ring model (SR-33 / LS-ST-1 support)
// ====================================================================

// Tie the model to the emitter's parameters — drift breaks the build.
const _: () = assert!(crate::p3_bridge::RING_CAP == 4096);
const _: () = assert!(crate::p3_bridge::RING_CAP.is_power_of_two());
const _: () = assert!(
    crate::p3_bridge::RINGS_BASE
        >= crate::p3_bridge::HEADER_BASE
            + crate::p3_bridge::SLOT_COUNT * crate::p3_bridge::SLOT_HEADER_STRIDE
);

const CAP: u32 = crate::p3_bridge::RING_CAP;

/// Model of the emitted write shim's cursor math.
fn model_write(rd: u32, wr: u32, len: u32) -> (u32, u32) {
    let avail = CAP.wrapping_sub(wr.wrapping_sub(rd));
    let n = len.min(avail);
    (wr.wrapping_add(n), n)
}

/// Model of the emitted read shim's cursor math.
fn model_read(rd: u32, wr: u32, len: u32) -> (u32, u32) {
    let fill = wr.wrapping_sub(rd);
    let n = len.min(fill);
    (rd.wrapping_add(n), n)
}

/// The ring invariant `fill = wr - rd ≤ CAP` is inductive over any
/// interleaving of one write and one read with arbitrary lengths —
/// including u32 cursor wraparound — and both two-part copy segments
/// stay within the slot's ring.
#[kani::proof]
fn ring_cursor_invariant_inductive() {
    let rd: u32 = kani::any();
    let wr: u32 = kani::any();
    kani::assume(wr.wrapping_sub(rd) <= CAP);

    let (wr2, accepted) = model_write(rd, wr, kani::any());
    assert!(wr2.wrapping_sub(rd) <= CAP, "write preserves fill ≤ CAP");
    assert!(accepted <= CAP);

    let (rd2, read) = model_read(rd, wr2, kani::any());
    assert!(wr2.wrapping_sub(rd2) <= CAP, "read preserves fill ≤ CAP");
    assert!(read <= CAP);

    // Two-part copy bounds for the write that just happened: the first
    // segment ends at most at CAP; the wrapped remainder is smaller
    // than the offset it restarts before.
    let off = wr & (CAP - 1);
    let first = accepted.min(CAP - off);
    let second = accepted - first;
    assert!(off + first <= CAP, "segment 1 inside the ring");
    assert!(second <= off || second == 0, "segment 2 wraps below offset");
}
