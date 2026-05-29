//! DWARF address remapping for fused output — issue #143 Phase 2.
//!
//! When meld fuses N components into one core module, each function
//! body moves to a new offset in the merged code section AND its
//! internal byte layout shifts (the rewriter changes operand index
//! values whose LEB128 encodings change length — see
//! [`crate::rewriter::InstrOffsetMap`]). WebAssembly DWARF encodes
//! code addresses as offsets relative to the start of the code
//! section's contents, so every `DW_AT_low_pc`, line-number-program
//! address, and range entry in the input DWARF is wrong for the
//! fused output unless remapped.
//!
//! This module composes the two anchors built in increments 1 and 2:
//!
//! - **Per-function base** (increment 1): where each function's body
//!   lands in the *merged* code section, from the component-provenance
//!   v2 `code_range` ([`crate::provenance::CodeRange`]).
//! - **Intra-function instruction offsets** (increment 2): how byte
//!   offsets shift *within* a rewritten function body, from
//!   [`crate::rewriter::InstrOffsetMap`].
//!
//! into an [`AddressRemap`]: a function from an input code-section-
//! relative address to its fused-output code-section-relative
//! address. Increment 3 (the gimli section rewrite) uses this as the
//! `convert_address` closure for `gimli::write::Dwarf::from`.
//!
//! ## Offset-convention reconciliation
//!
//! Three byte-offset spaces meet here, and getting their bases
//! aligned is the whole game:
//!
//! 1. **Input DWARF address** `A`: code-section-relative offset in the
//!    *source* component. Points at an instruction. To locate which
//!    function `A` is in, we need each input function body's
//!    code-section-relative span (`FunctionSpan::input`).
//! 2. **Instruction-stream offset**: relative to the first instruction
//!    of a function body (after the locals-declaration vector). The
//!    [`InstrOffsetMap`](crate::rewriter::InstrOffsetMap) keys on this.
//!    Converting `A` to this space means subtracting the input
//!    function body's start AND the locals-prefix length.
//! 3. **Output DWARF address** `A'`: code-section-relative offset in
//!    the *merged* module = merged function body start
//!    (`FunctionSpan::output_body_start`) + output locals-prefix
//!    length + new instruction-stream offset.
//!
//! Because meld preserves a function's locals declarations verbatim
//! (the rewriter only converts val-types, never adds/removes locals
//! except the address-rebasing scratch locals, which are off in the
//! DWARF-remap path), the locals-prefix length is identical on input
//! and output. So the prefix cancels when both are equal, and the
//! [`FunctionSpan`] records it once as `locals_prefix_len`.

use crate::rewriter::InstrOffsetMap;
use std::collections::BTreeMap;

/// One fused function's mapping data: where it was in the input code
/// section, where it landed in the output, the shared locals-prefix
/// length, and the per-instruction offset shift.
#[derive(Debug, Clone)]
pub struct FunctionSpan {
    /// `[start, end)` of this function body in the **input** code
    /// section (code-section-relative), including the locals prefix.
    pub input_start: u32,
    pub input_end: u32,
    /// Start of this function body in the **output** (merged) code
    /// section (code-section-relative), including the locals prefix.
    /// This is the v2 provenance `code_range.start`.
    pub output_body_start: u32,
    /// Byte length of the locals-declaration vector at the head of the
    /// body — identical on input and output (locals are preserved).
    /// The instruction stream begins `locals_prefix_len` bytes past
    /// each body start.
    pub locals_prefix_len: u32,
    /// Per-instruction old→new offset map (instruction-stream-relative).
    pub instr_offsets: InstrOffsetMap,
}

impl FunctionSpan {
    /// `true` if the input code address `addr` falls within this
    /// function body's input span.
    fn contains_input(&self, addr: u32) -> bool {
        addr >= self.input_start && addr < self.input_end
    }
}

/// Composed input→output code-address remapper for fused DWARF.
///
/// Built from the per-function [`FunctionSpan`]s collected during
/// fusion. Lookups are by input code-section-relative address; the
/// result is the output code-section-relative address, or `None` when
/// the address can't be mapped (outside any known function, or not on
/// a recorded instruction boundary — DWARF code addresses always sit
/// at instruction starts, so a miss is a genuine "don't emit this
/// address" signal for the gimli converter).
#[derive(Debug, Clone, Default)]
pub struct AddressRemap {
    /// Indexed by input_start for an O(log n) containing-function
    /// lookup. Spans are non-overlapping (function bodies are laid
    /// out sequentially), so the greatest key ≤ addr is the candidate.
    by_input_start: BTreeMap<u32, FunctionSpan>,
}

impl AddressRemap {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a function's span. Panics in debug builds if two
    /// spans share an input_start (would indicate a merger bug —
    /// function bodies are distinct).
    pub fn insert(&mut self, span: FunctionSpan) {
        debug_assert!(
            !self.by_input_start.contains_key(&span.input_start),
            "duplicate input_start {} in AddressRemap",
            span.input_start
        );
        self.by_input_start.insert(span.input_start, span);
    }

    /// Translate an input code-section-relative address to the fused
    /// output code-section-relative address.
    ///
    /// Returns `None` if `addr` is not inside any registered function
    /// or does not land on a recorded instruction boundary.
    pub fn translate(&self, addr: u32) -> Option<u32> {
        // Greatest span whose input_start ≤ addr.
        let (_, span) = self.by_input_start.range(..=addr).next_back()?;
        if !span.contains_input(addr) {
            return None;
        }
        // Convert the input address to an instruction-stream offset:
        // subtract the body start and the locals prefix.
        let body_rel = addr - span.input_start;
        let instr_stream_old = body_rel.checked_sub(span.locals_prefix_len)?;
        // Map through the rewriter's instruction offset map.
        let instr_stream_new = span.instr_offsets.translate(instr_stream_old)?;
        // Reassemble the output address: merged body start + locals
        // prefix (unchanged) + new instruction-stream offset.
        Some(span.output_body_start + span.locals_prefix_len + instr_stream_new)
    }

    /// Number of registered function spans.
    pub fn len(&self) -> usize {
        self.by_input_start.len()
    }

    pub fn is_empty(&self) -> bool {
        self.by_input_start.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rewriter::{InstrOffset, InstrOffsetMap};

    fn span(
        input_start: u32,
        input_end: u32,
        output_body_start: u32,
        locals_prefix_len: u32,
        offsets: &[(u32, u32)],
    ) -> FunctionSpan {
        FunctionSpan {
            input_start,
            input_end,
            output_body_start,
            locals_prefix_len,
            instr_offsets: InstrOffsetMap {
                entries: offsets
                    .iter()
                    .map(|&(old, new)| InstrOffset { old, new })
                    .collect(),
            },
        }
    }

    /// Single function, no locals prefix, identity instruction map:
    /// an input address maps to output_body_start + same offset.
    #[test]
    fn translate_single_function_identity_offsets() {
        let mut remap = AddressRemap::new();
        // Input body [10, 20), output body starts at 100, no locals,
        // instructions at stream offsets 0,2,3.
        remap.insert(span(10, 20, 100, 0, &[(0, 0), (2, 2), (3, 3)]));

        // Input addr 10 = body start = instr-stream 0 → output 100.
        assert_eq!(remap.translate(10), Some(100));
        // Input addr 12 = instr-stream 2 → output 100 + 2 = 102.
        assert_eq!(remap.translate(12), Some(102));
        assert_eq!(remap.translate(13), Some(103));
    }

    /// LEB-growth case: the instruction map shifts offsets, and the
    /// output base differs. Input body [10,20), output body at 200,
    /// instr map shows divergence (drop moved +1 after a remapped call).
    #[test]
    fn translate_applies_instruction_offset_shift() {
        let mut remap = AddressRemap::new();
        // instr stream: call@0→0, drop@2→3 (call grew 1 byte).
        remap.insert(span(10, 20, 200, 0, &[(0, 0), (2, 3)]));

        // call at input 10 → output 200.
        assert_eq!(remap.translate(10), Some(200));
        // drop at input 12 (stream offset 2) → output 200 + 3 = 203.
        assert_eq!(remap.translate(12), Some(203));
    }

    /// Locals prefix is subtracted on the way in and re-added on the
    /// way out (it's preserved verbatim), so a function whose body
    /// starts with a 3-byte locals vector still maps instructions
    /// correctly.
    #[test]
    fn translate_accounts_for_locals_prefix() {
        let mut remap = AddressRemap::new();
        // Input body [10, 30), 3-byte locals prefix, output body at 50.
        // First instruction is at body_rel 3 = instr-stream 0.
        remap.insert(span(10, 30, 50, 3, &[(0, 0), (4, 5)]));

        // Input addr 13 = body_rel 3 = instr-stream 0 → 50 + 3 + 0 = 53.
        assert_eq!(remap.translate(13), Some(53));
        // Input addr 17 = body_rel 7 = instr-stream 4 → 50 + 3 + 5 = 58.
        assert_eq!(remap.translate(17), Some(58));
    }

    /// Multiple functions: the BTreeMap range lookup picks the right
    /// containing span.
    #[test]
    fn translate_selects_correct_function_among_many() {
        let mut remap = AddressRemap::new();
        remap.insert(span(0, 10, 1000, 0, &[(0, 0), (5, 5)]));
        remap.insert(span(10, 25, 2000, 0, &[(0, 0), (8, 9)]));
        remap.insert(span(25, 40, 3000, 0, &[(0, 0), (3, 3)]));

        assert_eq!(remap.translate(5), Some(1005)); // func 0
        assert_eq!(remap.translate(18), Some(2009)); // func 1, shifted
        assert_eq!(remap.translate(28), Some(3003)); // func 2
    }

    /// Addresses outside any function, or not on an instruction
    /// boundary, return None — gimli will then drop them rather than
    /// emit a wrong address.
    #[test]
    fn translate_misses_return_none() {
        let mut remap = AddressRemap::new();
        remap.insert(span(10, 20, 100, 0, &[(0, 0), (2, 2)]));

        assert_eq!(remap.translate(5), None, "before any function");
        assert_eq!(remap.translate(20), None, "at end (exclusive)");
        assert_eq!(remap.translate(50), None, "past all functions");
        assert_eq!(remap.translate(1), None, "below first function");
        // Inside the function but not on a recorded instruction start.
        assert_eq!(remap.translate(11), None, "mid-instruction offset");
    }

    /// An address whose body-relative offset is *less than* the locals
    /// prefix (i.e. pointing into the locals declarations, not the
    /// instruction stream) returns None rather than underflowing.
    #[test]
    fn translate_address_inside_locals_prefix_is_none() {
        let mut remap = AddressRemap::new();
        remap.insert(span(10, 30, 50, 5, &[(0, 0)]));
        // Input addr 12 = body_rel 2 < locals_prefix_len 5 → None.
        assert_eq!(remap.translate(12), None);
    }
}
