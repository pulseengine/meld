//! Rustc-built MC/DC gate fixture (meld#302 Track C2, SR-62 follow-up).
//!
//! Decision under test:
//!     `(year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)`
//!
//! The textbook ISO leap-year rule — three short-circuit conditions in
//! mixed AND/OR shape. Modular arithmetic blocks the constant-fold +
//! bitwise-collapse rustc would otherwise apply to a plain
//! `(a && b) || c` over bools, so the predicate stays a real branch
//! chain in the emitted Wasm.
//!
//! Unlike the hand-written WAT seam (tests/gate/consumer_core.wat, a
//! single `result > 40` guard where MC/DC collapses to branch coverage),
//! rustc lowers this to a short-circuit `br_if` chain with DWARF line
//! info, so witness reconstructs ONE decision with TWO independent
//! conditions (rustc fuses the `% 400 == 0` check into the same chain)
//! and proves each under masking / unique-cause MC/DC. That is the rich
//! multi-condition decision this gate exists to hold.
//!
//! This crate mirrors witness's own `witness new` scaffold so the
//! lowering is one witness already reconstructs end-to-end; the point of
//! THIS copy is to prove the decision + DWARF survive a `meld fuse`.
//!
//! Build knobs (see Cargo.toml): `no_std` (wasm32-unknown-unknown has no
//! libc/unwinder), `panic = "abort"`, `opt-level = 1`, `lto = false`,
//! `codegen-units = 1`, `debug = true`, `strip = false` — keep the
//! lowering close to source and preserve the DWARF witness reads.

#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

/// The decision under test. `#[inline(never)]` keeps the predicate a
/// distinct function (not inlined into each caller) so witness
/// reconstructs the decision against a single stable source attribution
/// (a `lib.rs:<line>` entry — the gate asserts the attribution is
/// present, not which line, since the line moves as this file is edited).
#[inline(never)]
fn is_leap_year(year: u32) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

/// Single typed-arg export. `#[unsafe(export_name = ...)]` gives it the
/// canonical Component-Model ABI name for the `gate:leap/rule@0.1.0`
/// interface's `is-leap` func, so `wasm-tools component embed --world
/// leap` finds it and `meld fuse` carries it through to the fused core
/// module's export table. witness drives it with
/// `--invoke-with-args 'gate:leap/rule@0.1.0#is-leap=<year>'`.
#[unsafe(export_name = "gate:leap/rule@0.1.0#is-leap")]
pub extern "C" fn is_leap(year: i32) -> i32 {
    is_leap_year(year as u32) as i32
}
