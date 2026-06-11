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

use crate::rewriter::{InstrOffset, InstrOffsetMap};
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
    /// Exclusive end of this function body in the **output** code
    /// section. Used to map an exclusive-end DWARF address
    /// (`DW_AT_high_pc` as address, range-list end, line-program
    /// `end_sequence`) — which points one byte past the last
    /// instruction — to the corresponding output end.
    pub output_body_end: u32,
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
    /// Exclusive end of the **input** module's code section (the size of
    /// its code-section contents), covering *every* input function —
    /// including ones meld dropped that have no registered span. This is
    /// the code/data boundary: an address below it is a code offset
    /// (mapped or tombstoned), at/above it is a linear-memory address.
    /// Distinct from the registered spans' max `input_end`, which would
    /// wrongly classify a dropped *trailing* function's code address as
    /// data (Mythos #209).
    input_code_extent: u32,
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
    /// WebAssembly DWARF measures code addresses from the **function
    /// body start** (the locals-declaration byte), so three regions of
    /// a body must be handled:
    ///
    /// 1. **Locals/prefix** `[input_start, input_start+locals_prefix)`
    ///    — includes `DW_AT_low_pc`, which points at the body start.
    ///    Locals are preserved verbatim during fusion, so this maps
    ///    linearly: `output_body_start + body_rel`.
    /// 2. **Instruction stream** — mapped through the rewriter's
    ///    [`InstrOffsetMap`] (operand LEB widths shift offsets).
    /// 3. **Exclusive end** `addr == input_end` — an end address
    ///    (`high_pc`, range end, line `end_sequence`) one byte past the
    ///    last instruction; maps to `output_body_end`.
    ///
    /// Returns `None` if `addr` is not inside any registered function
    /// or does not land on a recorded instruction boundary.
    pub fn translate(&self, addr: u32) -> Option<u32> {
        // Greatest span whose input_start ≤ addr.
        let (_, span) = self.by_input_start.range(..=addr).next_back()?;

        // Aliased boundary: input function bodies are contiguous, so
        // `addr` can be BOTH the previous function A's exclusive end
        // (A.input_end) and this span B's start (B.input_start). The
        // range lookup picks B, but a `high_pc`/range-end/`end_sequence`
        // query means A's end while a `low_pc`/first-instruction query
        // means B's start — and `convert_address` cannot tell them
        // apart. The two output offsets coincide ONLY when A and B stay
        // adjacent in the fused output (input order preserved — the
        // single-source case). If they diverge (functions interleaved
        // or reordered), the address is genuinely ambiguous: return None
        // so the caller tombstones it rather than emit a plausible but
        // wrong offset for one of the two meanings (Mythos #209).
        if addr == span.input_start
            && let Some((_, prev)) = self.by_input_start.range(..addr).next_back()
            && prev.input_end == addr
            && prev.output_body_end != span.output_body_start
        {
            return None;
        }

        // Exclusive-end address: maps to the output body end. Reached
        // for the span whose input_end equals addr (the last body, or a
        // boundary where the next body's start was not selected above).
        if addr == span.input_end {
            return Some(span.output_body_end);
        }
        if !span.contains_input(addr) {
            return None;
        }
        let body_rel = addr - span.input_start;
        // Region 1: locals/prefix — preserved verbatim, maps linearly.
        if body_rel < span.locals_prefix_len {
            return Some(span.output_body_start + body_rel);
        }
        // Region 2: instruction stream. Map to the *containing*
        // operator's new offset. Exact on instruction boundaries; for
        // an address inside an operator's operand bytes — which happens
        // because LLVM emits fixed-width (zero-padded) LEBs for
        // relocatable indices while meld re-encodes them canonically —
        // it resolves to that operator's start, attributing the address
        // to the instruction it is actually inside (correct source-line
        // attribution for debuggers / witness).
        let instr_stream_old = body_rel - span.locals_prefix_len;
        let entries = &span.instr_offsets.entries;
        // Greatest entry whose `old` <= instr_stream_old (entries are in
        // ascending operator order).
        let idx = entries.partition_point(|e| e.old <= instr_stream_old);
        let entry = entries.get(idx.checked_sub(1)?)?;
        Some(span.output_body_start + span.locals_prefix_len + entry.new)
    }

    /// Number of registered function spans.
    pub fn len(&self) -> usize {
        self.by_input_start.len()
    }

    pub fn is_empty(&self) -> bool {
        self.by_input_start.is_empty()
    }

    /// Record the input module's full code-section extent (covering all
    /// input functions, including dropped ones). Set once at build time.
    pub fn set_input_code_extent(&mut self, extent: u32) {
        self.input_code_extent = extent;
    }

    /// Exclusive upper bound of the input code section — the code/data
    /// classification boundary. Prefers the explicitly-recorded full
    /// input extent ([`Self::set_input_code_extent`]); falls back to the
    /// greatest registered span end when unset (synthetic test remaps).
    /// Addresses `< code_extent` are code offsets (mapped or tombstoned);
    /// `>= code_extent` are linear-memory data addresses.
    pub fn code_extent(&self) -> u32 {
        let registered_max = self
            .by_input_start
            .values()
            .map(|s| s.input_end)
            .max()
            .unwrap_or(0);
        self.input_code_extent.max(registered_max)
    }
}

// ---------------------------------------------------------------------------
// Increment 3b: build the remap from a real fusion and rewrite `.debug_*`.
// ---------------------------------------------------------------------------

/// Per-defined-function byte layout of one core module's code section,
/// recovered by parsing. Used on both the input and the fused output so
/// the two can be walked in lockstep to recover the instruction offset
/// map without threading state through the merge hot path.
struct FnLayout {
    /// Function body start, code-section-relative (points at the
    /// locals-count LEB — the same convention as
    /// [`crate::provenance::CodeRange`]).
    body_start: u32,
    /// Function body end, code-section-relative (exclusive).
    body_end: u32,
    /// Bytes from `body_start` to the first operator (locals vector).
    locals_prefix_len: u32,
    /// Instruction-stream offset (0 at the first operator) of every
    /// operator, in code order.
    op_offsets: Vec<u32>,
}

/// Parse `module_bytes` and return the [`FnLayout`] of every *defined*
/// function, in code-section order. Returns `None` on any parse error
/// or if there is no code section — the caller then falls back to
/// stripping DWARF rather than emitting a guessed address.
fn module_function_layouts(module_bytes: &[u8]) -> Option<Vec<FnLayout>> {
    use wasmparser::{Parser, Payload};
    let mut content_start: Option<usize> = None;
    let mut layouts = Vec::new();
    for payload in Parser::new(0).parse_all(module_bytes) {
        match payload.ok()? {
            Payload::CodeSectionStart { range, .. } => content_start = Some(range.start),
            Payload::CodeSectionEntry(body) => {
                let base = content_start?;
                let r = body.range();
                let ops_reader = body.get_operators_reader().ok()?;
                let first_op_pos = ops_reader.original_position();
                let locals_prefix_len = (first_op_pos - r.start) as u32;
                let mut op_offsets = Vec::new();
                for item in ops_reader.into_iter_with_offsets() {
                    let (_op, pos) = item.ok()?;
                    op_offsets.push((pos - first_op_pos) as u32);
                }
                layouts.push(FnLayout {
                    body_start: (r.start - base) as u32,
                    body_end: (r.end - base) as u32,
                    locals_prefix_len,
                    op_offsets,
                });
            }
            _ => {}
        }
    }
    // No code section → cannot remap; signal the caller to strip.
    content_start?;
    Some(layouts)
}

/// Number of imported functions in a core module — the offset between a
/// module-level function index and its defined-function index.
fn import_func_count(module: &crate::parser::CoreModule) -> u32 {
    module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, crate::parser::ImportKind::Function(_)))
        .count() as u32
}

/// Build an [`AddressRemap`] for the single source core module
/// `(comp_idx, mod_idx)`, pairing each of its defined functions with
/// the corresponding fused-output function and zipping their
/// instruction streams.
///
/// Returns `None` if any function's input/output layouts are
/// inconsistent (different operator count or locals prefix — which
/// happens when the rewriter inserted instructions, e.g. memory
/// address-rebasing) or if parsing fails. A `None` is a hard "do not
/// remap" signal: better to strip DWARF than emit a wrong address.
fn build_remap_for_module(
    module: &crate::parser::CoreModule,
    merged: &crate::merger::MergedModule,
    comp_idx: usize,
    mod_idx: usize,
    output_bytes: &[u8],
) -> Option<AddressRemap> {
    let imports = import_func_count(module);
    // (output defined-function index, input module-level function index)
    // for every fused function originating from this source module.
    let pairs: Vec<(usize, u32)> = merged
        .functions
        .iter()
        .enumerate()
        .filter(|(_, mf)| mf.origin.0 == comp_idx && mf.origin.1 == mod_idx)
        .map(|(out_idx, mf)| (out_idx, mf.origin.2))
        .collect();
    build_remap_from_parts(&module.bytes, imports, output_bytes, &pairs)
}

/// Testable core of [`build_remap_for_module`]: pair input and output
/// function layouts and assemble the [`AddressRemap`]. `pairs` lists
/// `(output_defined_idx, input_module_level_func_idx)` for the source
/// module. Returns `None` on any layout inconsistency (operator-count
/// or locals-prefix mismatch — meaning the rewriter inserted
/// instructions, so addresses cannot be mapped 1:1) or if no function
/// mapped.
fn build_remap_from_parts(
    input_bytes: &[u8],
    imports: u32,
    output_bytes: &[u8],
    pairs: &[(usize, u32)],
) -> Option<AddressRemap> {
    let input_layouts = module_function_layouts(input_bytes)?;
    let output_layouts = module_function_layouts(output_bytes)?;

    let mut remap = AddressRemap::new();
    // Code/data boundary = the full input code-section extent (every
    // input function, including any meld dropped), so a dropped
    // function's code address is tombstoned rather than mistaken for a
    // linear-memory data address (Mythos #209).
    let input_code_extent = input_layouts.iter().map(|l| l.body_end).max().unwrap_or(0);
    remap.set_input_code_extent(input_code_extent);
    for &(defined_out_idx, old_func_idx) in pairs {
        // Module-level function index → input defined-function index.
        let in_idx = old_func_idx.checked_sub(imports)? as usize;
        let input = input_layouts.get(in_idx)?;
        let output = output_layouts.get(defined_out_idx)?;

        // Locals are preserved verbatim in the DWARF-remap path, so the
        // prefix must be identical; an operator was inserted otherwise.
        if input.locals_prefix_len != output.locals_prefix_len {
            log::debug!(
                "dwarf remap abort: func in_idx={in_idx} locals_prefix mismatch \
                 (in={} out={})",
                input.locals_prefix_len,
                output.locals_prefix_len
            );
            return None;
        }
        if input.op_offsets.len() != output.op_offsets.len() {
            log::debug!(
                "dwarf remap abort: func in_idx={in_idx} out_idx={defined_out_idx} \
                 operator-count mismatch (in={} out={})",
                input.op_offsets.len(),
                output.op_offsets.len()
            );
            return None;
        }

        let entries = input
            .op_offsets
            .iter()
            .zip(output.op_offsets.iter())
            .map(|(&old, &new)| InstrOffset { old, new })
            .collect();

        remap.insert(FunctionSpan {
            input_start: input.body_start,
            input_end: input.body_end,
            output_body_start: output.body_start,
            output_body_end: output.body_end,
            locals_prefix_len: input.locals_prefix_len,
            instr_offsets: InstrOffsetMap { entries },
        });
    }

    if remap.is_empty() {
        return None;
    }
    Some(remap)
}

/// Read the `.debug_*` sections in `debug` (a single source module's
/// DWARF), remap every code address through `remap`, and re-serialize.
/// Returns the rewritten `(section_name, bytes)` pairs, or `None` if
/// gimli could not round-trip the DWARF (caller falls back to strip).
///
/// Wasm DWARF is little-endian and uses code-section-relative
/// addresses, which is exactly what [`AddressRemap::translate`]
/// consumes and produces.
///
/// **Fidelity note:** `DW_AT_high_pc` encoded as a *length*
/// (`DW_FORM_data*`, the common Rust/LLVM encoding) is copied verbatim
/// — gimli treats it as a constant, not an address, so it is not routed
/// through `convert_address`. The function's start address (`low_pc`)
/// and the line-number program — what debuggers use for breakpoints and
/// backtraces — are remapped correctly; the high_pc *length* may be off
/// by the intra-function LEB drift. This is tracked as LS-D-1.
fn rewrite_debug_sections(
    debug: &[(String, Vec<u8>)],
    remap: &AddressRemap,
    adapter_spans: &[AdapterSpan],
) -> Option<Vec<(String, Vec<u8>)>> {
    use gimli::write::{Address, Dwarf as WriteDwarf, EndianVec, Sections};
    use gimli::{EndianSlice, LittleEndian, SectionId};

    let endian = LittleEndian;
    let section_data = |name: &str| -> &[u8] {
        debug
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, d)| d.as_slice())
            .unwrap_or(&[])
    };

    let load = |id: SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        Ok(EndianSlice::new(section_data(id.name()), endian))
    };
    let read_dwarf = gimli::Dwarf::load(load).ok()?;

    // gimli's `Dwarf::from` is all-or-nothing: if `convert_address`
    // returns `None` for *any* address it queries, the whole conversion
    // fails. We exploit that as a correct-or-strip gate — a real
    // instruction address that we cannot map aborts the conversion and
    // the caller strips the DWARF rather than emit a wrong address.
    //
    // The one address that is *structurally invariant* and not a mapped
    // instruction is `0`: wasm DWARF code addresses are relative to the
    // start of the code-section contents, and the compilation unit's
    // base (`DW_AT_low_pc` = 0) denotes that start, which is offset 0 in
    // both the input and the fused output. Map it to itself; everything
    // else must go through the instruction-accurate remap.
    // DWARF tombstone: the conventional "this address is invalid / dead
    // code" marker (max address). Consumers (debuggers, gimli, witness)
    // skip DIEs and line rows whose address is the tombstone. wasm-ld
    // itself tombstones discarded code this way.
    const TOMBSTONE: u64 = 0xFFFF_FFFF;

    let code_extent = remap.code_extent() as u64;
    // `convert_address` is **total** — it never returns `None`, because
    // `gimli::write::Dwarf::from` aborts the *entire* conversion on a
    // single `None`. On real compiler output (hundreds of functions,
    // dead-code gaps, padded LEBs, data addresses) some address always
    // fails to map; all-or-nothing would then strip every byte of
    // DWARF. Instead each address is independently resolved to either
    // its correct fused offset or a tombstone — never a plausible but
    // wrong address. This keeps the LS-D-1 guarantee per-address while
    // emitting correct debug info for everything that does map.
    let convert_address = |addr: u64| -> Option<Address> {
        if addr == 0 {
            return Some(Address::Constant(0));
        }
        if let Some(new) = remap.translate(addr as u32) {
            return Some(Address::Constant(new as u64));
        }
        // Not a mapped code offset. At/beyond the code extent it is a
        // linear-memory / data address (e.g. `DW_OP_addr` in a variable
        // location) or an existing wasm-ld tombstone — unchanged under
        // multi-memory fusion, pass through. Within the code section it
        // is a genuine code miss (a function meld dropped, a dead-code
        // range): tombstone it rather than emit a stale offset.
        if addr >= code_extent {
            return Some(Address::Constant(addr));
        }
        log::debug!("dwarf remap: tombstoning unmapped code address {addr:#x}");
        Some(Address::Constant(TOMBSTONE))
    };

    let mut write_dwarf = match WriteDwarf::from(&read_dwarf, &convert_address) {
        Ok(d) => d,
        Err(e) => {
            log::debug!("dwarf remap abort: gimli convert failed: {e:?}");
            return None;
        }
    };
    // #144 inc 3: the synthetic `<meld-adapter>` unit rides the SAME
    // write as the remapped original units, so every cross-section
    // offset is computed in one shared offset space (appending
    // independently-serialised `.debug_*` bytes would collide).
    append_adapter_unit(&mut write_dwarf, adapter_spans);
    let mut sections = Sections::new(EndianVec::new(endian));
    write_dwarf.write(&mut sections).ok()?;

    let mut out = Vec::new();
    sections
        .for_each(|id, data| {
            let bytes = data.slice();
            if !bytes.is_empty() {
                out.push((id.name().to_string(), bytes.to_vec()));
            }
            Ok::<(), gimli::Error>(())
        })
        .ok()?;
    Some(out)
}

/// Top-level entry point for [`crate::DwarfHandling::Remap`].
///
/// Inspects the input components for `.debug_*` sections and, when
/// exactly one source core module carries DWARF, builds its
/// [`AddressRemap`] and returns the rewritten debug sections to embed in
/// the fused output. meld-GENERATED code ranges additionally get a
/// synthetic `<meld-adapter>` unit in the same write (#144 inc 3) —
/// including when NO source DWARF exists at all, so adapter attribution
/// never depends on the inputs being built with debug info. Returns
/// `None` (caller strips/omits DWARF) when:
///
/// - no input module carries DWARF AND the fusion generated no adapter
///   code, or
/// - **more than one** module carries DWARF (merging independent DWARF
///   unit sets into one consistent `.debug_info` is a separate problem,
///   #208 — emitting either source's addresses against the merged code
///   section would be wrong for the other). The synthetic adapter unit
///   IS still emitted in this case: it references only meld-generated
///   ranges, so no wrong source addresses are involved, or
/// - the remap or gimli round-trip fails any consistency check.
///
/// `output_bytes` must be the fused module encoded *without* the
/// remapped DWARF (its code-section offsets are what the remap targets;
/// trailing custom sections do not shift code offsets, so the same
/// offsets hold in the final output).
pub fn remap_for_output(
    components: &[crate::parser::ParsedComponent],
    merged: &crate::merger::MergedModule,
    adapter_classes: &[crate::adapter::AdapterClass],
    output_bytes: &[u8],
) -> Option<Vec<(String, Vec<u8>)>> {
    // Find every (comp_idx, mod_idx) whose module carries DWARF.
    let mut dwarf_sources: Vec<(usize, usize)> = Vec::new();
    for (ci, comp) in components.iter().enumerate() {
        for (mi, module) in comp.core_modules.iter().enumerate() {
            if module
                .custom_sections
                .iter()
                .any(|(name, _)| name.starts_with(".debug_"))
            {
                dwarf_sources.push((ci, mi));
            }
        }
    }

    // #144: which fused-output ranges are meld-generated. Computed once;
    // attributed to `<meld-adapter>` in every branch below.
    let spans = adapter_spans(merged, adapter_classes, output_bytes);

    match dwarf_sources.as_slice() {
        [] => {
            if spans.is_empty() {
                return None;
            }
            log::debug!(
                "dwarf remap: no source DWARF; emitting synthetic \
                 <meld-adapter> unit for {} generated ranges (#144)",
                spans.len()
            );
            build_adapter_dwarf(&spans)
        }
        [(ci, mi)] => {
            let module = &components[*ci].core_modules[*mi];
            log::debug!("dwarf remap: single DWARF source at component {ci} module {mi}");
            let remap = build_remap_for_module(module, merged, *ci, *mi, output_bytes)?;
            log::debug!(
                "dwarf remap: built remap with {} function spans",
                remap.len()
            );
            let debug: Vec<(String, Vec<u8>)> = module
                .custom_sections
                .iter()
                .filter(|(name, _)| name.starts_with(".debug_"))
                .cloned()
                .collect();
            rewrite_debug_sections(&debug, &remap, &spans)
        }
        many => {
            // #208 inc 1: per-source convert+remap into independent
            // section sets, then merge via the bounded relocator. The
            // synthetic adapter unit rides the FIRST successful set's
            // write (single shared offset space within that set); the
            // relocator then makes the sets coexist.
            log::debug!(
                "dwarf remap: {} source modules carry DWARF; merging (#208)",
                many.len()
            );
            let mut sets: Vec<Vec<(String, Vec<u8>)>> = Vec::new();
            let mut spans_pending = spans.as_slice();
            for (ci, mi) in many {
                let module = &components[*ci].core_modules[*mi];
                let Some(remap) = build_remap_for_module(module, merged, *ci, *mi, output_bytes)
                else {
                    log::warn!(
                        "dwarf remap: source ({ci},{mi}) failed remap; dropping \
                         its DWARF (others proceed)"
                    );
                    continue;
                };
                let debug: Vec<(String, Vec<u8>)> = module
                    .custom_sections
                    .iter()
                    .filter(|(name, _)| name.starts_with(".debug_"))
                    .cloned()
                    .collect();
                let Some(set) = rewrite_debug_sections(&debug, &remap, spans_pending) else {
                    log::warn!(
                        "dwarf remap: source ({ci},{mi}) failed conversion; \
                         dropping its DWARF (others proceed)"
                    );
                    continue;
                };
                spans_pending = &[]; // adapter unit emitted exactly once
                sets.push(set);
            }
            if sets.is_empty() {
                // Every source failed — fall back to synthetic-only,
                // exactly the pre-#208 behaviour.
                if spans.is_empty() {
                    return None;
                }
                return build_adapter_dwarf(&spans);
            }
            match concat_dwarf_section_sets(&sets) {
                Some(merged_sections) => Some(merged_sections),
                None => {
                    // Outside the bounded repertoire: never guess.
                    log::warn!(
                        "dwarf remap: multi-source merge outside the bounded \
                         relocation repertoire; falling back to synthetic-only"
                    );
                    if spans.is_empty() {
                        None
                    } else {
                        build_adapter_dwarf(&spans)
                    }
                }
            }
        }
    }
}

// ====================================================================
// #208 increment 1: multi-source DWARF merge (bounded relocator)
// ====================================================================
//
// gimli's `write::UnitTable`s cannot be merged (private fields, per-table
// `BaseId`s), so multi-source merge works at the SECTION level: each
// DWARF-bearing source module is converted+remapped into its own
// independently written section set (the proven single-source path), and
// the sets are then concatenated with raw offset fixups applied to every
// set after the first. This is sound ONLY because we control the
// producer: the sets are gimli-written DWARF32 v4 with gimli's fixed
// form repertoire, so the complete list of cross-section references is
// known and bounded:
//
//   1. CU header `debug_abbrev_offset` (fixed position: unit offset + 6)
//   2. `DW_FORM_strp`        → `.debug_str`    (+ str prefix len)
//   3. `DW_FORM_sec_offset`  → by attribute:
//        `DW_AT_stmt_list`   → `.debug_line`   (+ line prefix len)
//        `DW_AT_ranges`      → `.debug_ranges` (+ ranges prefix len)
//        `DW_AT_location` &c → `.debug_loc`    (+ loc prefix len)
//   4. `DW_FORM_ref_addr`    → `.debug_info`   (+ info prefix len)
//
// `.debug_abbrev` / `.debug_str` / `.debug_line` / `.debug_ranges` /
// `.debug_loc` contents are offset-free internally (addresses, not
// section offsets), so they concatenate verbatim. Anything outside this
// repertoire (DWARF64, version ≠ 4, an unexpected `sec_offset`
// attribute) aborts the merge — the caller falls back to synthetic-only
// emission rather than risk a wrong offset.

/// Cumulative lengths of already-merged sections, used as relocation
/// bases for the next set.
#[derive(Debug, Default, Clone, Copy)]
struct SectionBases {
    info: u32,
    abbrev: u32,
    line: u32,
    ranges: u32,
    loc: u32,
}

fn section_of<'a>(set: &'a [(String, Vec<u8>)], name: &str) -> &'a [u8] {
    set.iter()
        .find(|(n, _)| n == name)
        .map(|(_, d)| d.as_slice())
        .unwrap_or(&[])
}

/// Apply the bounded relocations to one section set's `.debug_info`,
/// returning the patched bytes. `None` aborts the whole merge.
///
/// `strp_map` maps this set's `.debug_str` offsets to offsets in the
/// DEDUPED merged string pool (#208 inc 2) — identity for set 0, a real
/// remapping for later sets whose strings collapsed into earlier ones.
fn relocate_debug_info(
    set: &[(String, Vec<u8>)],
    bases: SectionBases,
    strp_map: &std::collections::HashMap<u32, u32>,
) -> Option<Vec<u8>> {
    use gimli::{EndianSlice, LittleEndian, constants};

    let mut info = section_of(set, ".debug_info").to_vec();
    if info.is_empty() {
        return Some(info);
    }

    let load = |id: gimli::SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        Ok(EndianSlice::new(section_of(set, id.name()), LittleEndian))
    };
    let dwarf = gimli::Dwarf::load(load).ok()?;

    let patch = |info: &mut [u8], pos: usize, delta: u32| -> Option<()> {
        let bytes: &mut [u8] = info.get_mut(pos..pos + 4)?;
        let old = u32::from_le_bytes(bytes.try_into().ok()?);
        bytes.copy_from_slice(&old.checked_add(delta)?.to_le_bytes());
        Some(())
    };

    let mut units = dwarf.units();
    while let Some(header) = units.next().ok()? {
        // DWARF32 v4 only: initial length must not be the DWARF64
        // escape, version must be 4. (We produced these sections, so
        // anything else means the producer changed — abort, never
        // guess.)
        if header.version() != 4 || header.format() != gimli::Format::Dwarf32 {
            log::warn!(
                "multi-DWARF merge: unit not DWARF32 v4 (version {}, {:?}); aborting merge",
                header.version(),
                header.format()
            );
            return None;
        }
        let unit_base = header.offset().as_debug_info_offset()?.0;
        // CU header: length(4) version(2) abbrev_offset(4) addr_size(1)
        patch(&mut info, unit_base + 6, bases.abbrev)?;

        let unit = dwarf.unit(header).ok()?;
        let mut entries = unit.entries_raw(None).ok()?;
        while !entries.is_empty() {
            let Some(abbrev) = entries.read_abbreviation().ok()? else {
                continue; // null entry
            };
            for spec in abbrev.attributes() {
                let value_pos = unit_base + entries.next_offset().0;
                let attr = entries.read_attribute(*spec).ok()?;
                match spec.form() {
                    constants::DW_FORM_strp => {
                        let bytes: &[u8] = info.get(value_pos..value_pos + 4)?;
                        let old_off = u32::from_le_bytes(bytes.try_into().ok()?);
                        let new_off = *strp_map.get(&old_off)?;
                        info.get_mut(value_pos..value_pos + 4)?
                            .copy_from_slice(&new_off.to_le_bytes());
                    }
                    constants::DW_FORM_ref_addr => {
                        patch(&mut info, value_pos, bases.info)?;
                    }
                    constants::DW_FORM_sec_offset => {
                        let delta = match attr.name() {
                            constants::DW_AT_stmt_list => bases.line,
                            constants::DW_AT_ranges => bases.ranges,
                            constants::DW_AT_location
                            | constants::DW_AT_data_member_location
                            | constants::DW_AT_frame_base
                            | constants::DW_AT_vtable_elem_location
                            | constants::DW_AT_use_location => bases.loc,
                            other => {
                                log::warn!(
                                    "multi-DWARF merge: unexpected sec_offset \
                                     attribute {other}; aborting merge"
                                );
                                return None;
                            }
                        };
                        patch(&mut info, value_pos, delta)?;
                    }
                    _ => {}
                }
            }
        }
    }
    Some(info)
}

/// Merge independently written DWARF section sets into one coherent set
/// (#208 inc 1). Set 0 is taken verbatim; each later set's `.debug_info`
/// is relocated against the cumulative bases, then all sections are
/// concatenated. Returns `None` (caller falls back) if any set is
/// outside the bounded repertoire.
fn concat_dwarf_section_sets(sets: &[Vec<(String, Vec<u8>)>]) -> Option<Vec<(String, Vec<u8>)>> {
    const NAMES: &[&str] = &[
        ".debug_info",
        ".debug_abbrev",
        ".debug_str",
        ".debug_line",
        ".debug_ranges",
        ".debug_loc",
    ];
    // Any section outside the known list means a producer change —
    // abort rather than silently drop it.
    for set in sets {
        for (name, _) in set {
            if !NAMES.contains(&name.as_str()) {
                log::warn!("multi-DWARF merge: unexpected section {name}; aborting merge");
                return None;
            }
        }
    }

    let mut out: Vec<(String, Vec<u8>)> =
        NAMES.iter().map(|n| (n.to_string(), Vec::new())).collect();
    let mut bases = SectionBases::default();
    // #208 inc 2: dedup state. The merged string pool maps string
    // CONTENT to its pool offset; identical `.debug_abbrev` tables
    // (gimli emits byte-identical tables for same-shaped sources) are
    // reused instead of appended.
    let mut string_pool: Vec<u8> = Vec::new();
    let mut pool_index: std::collections::HashMap<Vec<u8>, u32> = Default::default();
    let mut abbrev_seen: Vec<(u32, Vec<u8>)> = Vec::new();
    let mut abbrev_out: Vec<u8> = Vec::new();

    for set in sets {
        // Intern this set's strings into the pool, recording the
        // old-offset → pool-offset map for the strp relocation.
        let mut strp_map: std::collections::HashMap<u32, u32> = Default::default();
        let strs = section_of(set, ".debug_str");
        let mut off = 0usize;
        while off < strs.len() {
            let end = off + strs[off..].iter().position(|b| *b == 0)?;
            let content = strs[off..=end].to_vec(); // include NUL
            let pool_off = *pool_index.entry(content.clone()).or_insert_with(|| {
                let at = string_pool.len() as u32;
                string_pool.extend_from_slice(&content);
                at
            });
            strp_map.insert(u32::try_from(off).ok()?, pool_off);
            off = end + 1;
        }

        // Byte-equal abbrev reuse.
        let abbrev = section_of(set, ".debug_abbrev");
        let abbrev_base = match abbrev_seen.iter().find(|(_, b)| *b == abbrev) {
            Some((at, _)) => *at,
            None => {
                let at = u32::try_from(abbrev_out.len()).ok()?;
                abbrev_out.extend_from_slice(abbrev);
                abbrev_seen.push((at, abbrev.to_vec()));
                at
            }
        };
        bases.abbrev = abbrev_base;

        let info = relocate_debug_info(set, bases, &strp_map)?;
        for (name, acc) in out.iter_mut() {
            match name.as_str() {
                ".debug_info" => acc.extend_from_slice(&info),
                ".debug_str" | ".debug_abbrev" => {} // pooled below
                other => acc.extend_from_slice(section_of(set, other)),
            }
        }
        bases.info = bases.info.checked_add(u32::try_from(info.len()).ok()?)?;
        let grow = |base: &mut u32, name: &str| -> Option<()> {
            *base = base.checked_add(u32::try_from(section_of(set, name).len()).ok()?)?;
            Some(())
        };
        grow(&mut bases.line, ".debug_line")?;
        grow(&mut bases.ranges, ".debug_ranges")?;
        grow(&mut bases.loc, ".debug_loc")?;
    }
    for (name, acc) in out.iter_mut() {
        match name.as_str() {
            ".debug_str" => *acc = string_pool.clone(),
            ".debug_abbrev" => *acc = abbrev_out.clone(),
            _ => {}
        }
    }
    out.retain(|(_, d)| !d.is_empty());
    Some(out)
}

// ====================================================================
// Phase 3 (#144): synthetic source attribution for meld-generated code
// ====================================================================
//
// The fused output contains functions meld emits *itself* — cross-
// component adapters, canonical-ABI lift/lower glue, `cabi_realloc`
// trampolines — that have no original source and so no input DWARF.
// Phase 2 (above) remaps the DWARF of *original* code; Phase 3 attributes
// the *generated* code to a placeholder `<meld-adapter>` source so
// witness's MC/DC truth-table view surfaces these as **adapter branches**
// rather than unattributed `unknown` gaps (see #130 §"Phase 3").
//
// Increment 1 (this code): the enumeration seam. [`adapter_spans`] reports
// which fused-output code ranges are meld-generated, the data witness
// consumes to classify adapter branches and the input the synthetic-DIE
// emitter will iterate. Embedding synthetic DWARF DIEs for stock debuggers,
// and per-class [`AdapterRole`] line numbers, land in a follow-up increment.

/// Role of a meld-generated function, for synthetic source attribution.
///
/// Per #130 §"Phase 3 — adapters and inlined code", each role maps to a
/// line in the placeholder `<meld-adapter>` file. Increment 1 records only
/// [`AdapterRole::Generated`] (line 0): it answers "which ranges are
/// meld-generated" completely. Per-class lines (1 = canonical-ABI
/// transcode loop, 2 = `cabi_realloc` trampoline, 3 = lift, 4 = lower)
/// require the merger to tag each synthetic function's class at generation
/// time and land in a follow-up increment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdapterRole {
    /// meld-generated, class not determinable (fallback).
    Generated,
    /// FACT direct call shim — same memory, no transcoding.
    Direct,
    /// FACT cross-memory `(ptr, len)` copy chain (lower → callee
    /// `cabi_realloc` → `memory.copy` → lift, fused in one body).
    MemoryCopy,
    /// FACT cross-memory + string-encoding transcode loop.
    Transcode,
    /// P3 async adapter (callback-driving or stackful trampoline).
    Async,
    /// Merger handle-table helper (`ht_new` / `ht_rep` / `ht_drop`).
    HandleTable,
    /// Merger multi-`start` wrapper.
    StartWrapper,
    /// Type-coercion shim wrapping a FACT adapter call (i32/i64 glue).
    AdapterShim,
    /// P3 async `task.return` result-global shim.
    TaskReturnShim,
}

impl AdapterRole {
    /// Line number in the synthetic `<meld-adapter>` file encoding this
    /// role (#144 inc 4). Line 0 means "no source line" in DWARF, so the
    /// mapping starts at 1; the assignment is a stable contract consumed
    /// by witness's adapter-branch classification.
    ///
    /// Note on granularity vs #130's sketch ("transcode / cabi_realloc /
    /// lift / lower"): meld emits ONE fused trampoline per call site —
    /// lowering, allocation (a call to the callee's own `cabi_realloc`),
    /// copying and lifting live inline in a single body — so the honest
    /// class unit is the trampoline kind, not sub-function stages.
    pub fn adapter_line(self) -> u32 {
        match self {
            AdapterRole::Generated => 1,
            AdapterRole::Direct => 2,
            AdapterRole::MemoryCopy => 3,
            AdapterRole::Transcode => 4,
            AdapterRole::Async => 5,
            AdapterRole::HandleTable => 6,
            AdapterRole::StartWrapper => 7,
            AdapterRole::AdapterShim => 8,
            AdapterRole::TaskReturnShim => 9,
        }
    }
}

impl From<crate::adapter::AdapterClass> for AdapterRole {
    fn from(class: crate::adapter::AdapterClass) -> Self {
        match class {
            crate::adapter::AdapterClass::Direct => AdapterRole::Direct,
            crate::adapter::AdapterClass::MemoryCopy => AdapterRole::MemoryCopy,
            crate::adapter::AdapterClass::Transcode => AdapterRole::Transcode,
            crate::adapter::AdapterClass::Async => AdapterRole::Async,
        }
    }
}

impl From<crate::merger::SyntheticKind> for AdapterRole {
    fn from(kind: crate::merger::SyntheticKind) -> Self {
        match kind {
            crate::merger::SyntheticKind::HandleTable => AdapterRole::HandleTable,
            crate::merger::SyntheticKind::StartWrapper => AdapterRole::StartWrapper,
            crate::merger::SyntheticKind::AdapterShim => AdapterRole::AdapterShim,
            crate::merger::SyntheticKind::TaskReturnShim => AdapterRole::TaskReturnShim,
        }
    }
}

/// The synthetic placeholder "source file" name meld-generated functions
/// are attributed to. witness recognises this sentinel and treats lines in
/// it as adapter branches exempt from source-level MC/DC.
pub const ADAPTER_SOURCE_NAME: &str = "<meld-adapter>";

/// One meld-generated function's location in the fused output code
/// section — the unit of Phase 3 synthetic attribution (#144).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdapterSpan {
    /// Defined-function index in the fused output (0-based among defined
    /// functions, i.e. excluding imports). Equals the function's position
    /// in [`crate::merger::MergedModule::functions`].
    pub output_defined_idx: usize,
    /// `[start, end)` of the function body in the fused output code
    /// section (code-section-relative), including the locals prefix —
    /// the same convention as [`FunctionSpan::output_body_start`] and
    /// [`crate::provenance::CodeRange`].
    pub output_body_start: u32,
    pub output_body_end: u32,
    /// Best-effort adapter role (see [`AdapterRole`]).
    pub role: AdapterRole,
}

/// `true` if `origin` is one of the merger's synthetic-function sentinels
/// — a function meld generated rather than carried over from an input
/// module. The merger marks these as `(comp_idx, 0, u32::MAX)`
/// (component-attributed synthetics: resource destructors, callback /
/// stream adapters) or `(usize::MAX, usize::MAX, 0)` (fully synthetic). A
/// real defined-function index is never `u32::MAX` and a real component
/// index is never `usize::MAX`, so either sentinel is unambiguous.
fn is_generated_origin(origin: (usize, usize, u32)) -> bool {
    origin.0 == usize::MAX || origin.2 == u32::MAX
}

/// Enumerate the meld-generated (adapter / synthetic) functions in the
/// fused output, with their output code-section ranges — the foundation
/// for Phase 3 synthetic attribution (#144).
///
/// `output_bytes` is the fused core module; its defined-function layout
/// aligns index-for-index with [`crate::merger::MergedModule::functions`]
/// (both exclude imports, same order), exactly as
/// [`build_remap_for_module`] relies on. Returns an empty vector if the
/// output code section can't be parsed or there are no generated
/// functions.
pub fn adapter_spans(
    merged: &crate::merger::MergedModule,
    adapter_classes: &[crate::adapter::AdapterClass],
    output_bytes: &[u8],
) -> Vec<AdapterSpan> {
    // Roles for merged.functions (None = real source function), followed
    // by the FACT adapters the encoder appends AFTER merged.functions in
    // the output code section — previously un-enumerated (#144 inc 4),
    // which left every FACT trampoline unattributed.
    let mut roles: Vec<Option<AdapterRole>> = merged
        .functions
        .iter()
        .map(|f| {
            f.synthetic_kind.map(AdapterRole::from).or_else(|| {
                // Sentinel origin without a kind tag (future generator
                // paths): still attribute, as the unclassified fallback.
                is_generated_origin(f.origin).then_some(AdapterRole::Generated)
            })
        })
        .collect();
    roles.extend(adapter_classes.iter().map(|c| Some(AdapterRole::from(*c))));
    adapter_spans_from_parts(&roles, output_bytes)
}

/// Testable core of [`adapter_spans`]: `roles[i]` is `Some(role)` when
/// fused-output defined-function `i` is meld-generated.
fn adapter_spans_from_parts(
    roles: &[Option<AdapterRole>],
    output_bytes: &[u8],
) -> Vec<AdapterSpan> {
    let Some(layouts) = module_function_layouts(output_bytes) else {
        return Vec::new();
    };
    roles
        .iter()
        .enumerate()
        .filter_map(|(out_idx, role)| {
            let role = (*role)?;
            let l = layouts.get(out_idx)?;
            Some(AdapterSpan {
                output_defined_idx: out_idx,
                output_body_start: l.body_start,
                output_body_end: l.body_end,
                role,
            })
        })
        .collect()
}

/// The `<meld-adapter>` line attributed to a span, as actually emitted in
/// the synthetic line-number program.
///
/// DWARF line `0` conventionally means "no source line", so it would read
/// back as `unknown` — defeating the attribution. Increment 2 therefore
/// emits every meld-generated range at line **1** ("meld-generated,
/// class unspecified"). Increment 3 assigns distinct per-class lines
/// (transcode / `cabi_realloc` / lift / lower) once the merger tags each
/// synthetic function's class at generation time; the [`AdapterRole`]
/// enum and [`AdapterRole::adapter_line`] are the seam that refinement
/// will populate.
fn emitted_adapter_line(role: AdapterRole) -> u64 {
    u64::from(role.adapter_line())
}

/// Build a fresh, synthetic DWARF unit attributing each adapter span's
/// fused-output code range to the placeholder `<meld-adapter>` source via
/// a line-number program, so a DWARF consumer (witness's MC/DC view,
/// debuggers) resolves those addresses to `<meld-adapter>:N` instead of
/// `unknown` (#144 / #130 §Phase 3). Returns the `.debug_*`
/// `(section_name, bytes)` pairs, or `None` when there are no spans or
/// gimli fails to serialise.
///
/// Addresses are output code-section-relative `Address::Constant`, the
/// same convention [`rewrite_debug_sections`] emits for remapped original
/// DWARF, so the synthetic unit and any remapped original units share one
/// address space and can coexist in the fused module's `.debug_*`.
///
/// Each span becomes a one-row line-table sequence: a row at the body
/// start attributing the whole body to `<meld-adapter>:1`
/// ([`emitted_adapter_line`]), closed by `end_sequence` at the exclusive
/// body end.
pub fn build_adapter_dwarf(spans: &[AdapterSpan]) -> Option<Vec<(String, Vec<u8>)>> {
    use gimli::LittleEndian;
    use gimli::write::{Dwarf, EndianVec, Sections};

    let mut dwarf = Dwarf::new();
    if !append_adapter_unit(&mut dwarf, spans) {
        return None;
    }

    let mut sections = Sections::new(EndianVec::new(LittleEndian));
    dwarf.write(&mut sections).ok()?;

    let mut out = Vec::new();
    sections
        .for_each(|id, data| {
            let bytes = data.slice();
            if !bytes.is_empty() {
                out.push((id.name().to_string(), bytes.to_vec()));
            }
            Ok::<(), gimli::Error>(())
        })
        .ok()?;
    Some(out)
}

/// Add the synthetic `<meld-adapter>` compilation unit into an existing
/// `gimli::write::Dwarf` (#144 increment 3).
///
/// This is the single-write integration point: the remapped original
/// units (Phase 2) and the synthetic unit must go through ONE
/// `dwarf.write()` so all `.debug_*` cross-section offsets are computed
/// in one shared offset space. Serialising the synthetic unit separately
/// and concatenating section bytes would produce two unit sets whose
/// abbrev/str/line offsets collide. Returns `false` (Dwarf untouched)
/// when there are no non-empty spans.
fn append_adapter_unit(dwarf: &mut gimli::write::Dwarf, spans: &[AdapterSpan]) -> bool {
    use gimli::write::{Address, AttributeValue, LineProgram, LineString, Unit};
    use gimli::{Encoding, Format, LineEncoding, constants};

    if spans
        .iter()
        .all(|s| s.output_body_end <= s.output_body_start)
    {
        return false;
    }

    let encoding = Encoding {
        format: Format::Dwarf32,
        version: 4,
        address_size: 4,
    };
    let line_encoding = LineEncoding::default();

    let comp_dir = b"<meld>".to_vec();
    let mut line_program = LineProgram::new(
        encoding,
        line_encoding,
        LineString::String(comp_dir.clone()),
        LineString::String(ADAPTER_SOURCE_NAME.as_bytes().to_vec()),
        None,
    );
    let dir_id = line_program.default_directory();
    let file_id = line_program.add_file(
        LineString::String(ADAPTER_SOURCE_NAME.as_bytes().to_vec()),
        dir_id,
        None,
    );

    for span in spans {
        if span.output_body_end <= span.output_body_start {
            continue;
        }
        line_program.begin_sequence(Some(Address::Constant(span.output_body_start as u64)));
        {
            let row = line_program.row();
            row.address_offset = 0;
            row.file = file_id;
            row.line = emitted_adapter_line(span.role);
            row.is_statement = true;
        }
        line_program.generate_row();
        let body_len = (span.output_body_end - span.output_body_start) as u64;
        line_program.end_sequence(body_len);
    }

    let unit_id = dwarf.units.add(Unit::new(encoding, line_program));
    let unit = dwarf.units.get_mut(unit_id);
    let root = unit.root();
    unit.get_mut(root).set(
        constants::DW_AT_name,
        AttributeValue::String(ADAPTER_SOURCE_NAME.as_bytes().to_vec()),
    );
    unit.get_mut(root)
        .set(constants::DW_AT_comp_dir, AttributeValue::String(comp_dir));
    true
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
            // Tests that don't exercise the end-address path set a
            // plausible end; the dedicated end-address test overrides it.
            output_body_end: output_body_start + (input_end - input_start),
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

    /// Addresses outside any registered function return None — the
    /// caller then tombstones or passes them through.
    #[test]
    fn translate_outside_functions_return_none() {
        let mut remap = AddressRemap::new();
        // span(10,20,...) → output_body_end = 100 + (20-10) = 110.
        remap.insert(span(10, 20, 100, 0, &[(0, 0), (2, 2)]));

        assert_eq!(remap.translate(5), None, "before any function");
        assert_eq!(remap.translate(50), None, "past all functions");
        assert_eq!(remap.translate(1), None, "below first function");
    }

    /// An exclusive-end address (`high_pc` as address, range end, line
    /// `end_sequence`) maps to the output body end, not the next
    /// function's start.
    #[test]
    fn translate_exclusive_end_maps_to_output_body_end() {
        let mut remap = AddressRemap::new();
        remap.insert(span(10, 20, 100, 0, &[(0, 0), (2, 2)]));
        // addr == input_end (20) → output_body_end (110).
        assert_eq!(remap.translate(20), Some(110));
    }

    /// An address inside an operator's operand bytes (not on a recorded
    /// boundary — e.g. inside a padded LEB) resolves to the *containing*
    /// operator's new offset, attributing it to the right instruction.
    #[test]
    fn translate_mid_operator_maps_to_containing_operator() {
        let mut remap = AddressRemap::new();
        // Operators at stream offsets 0 and 2; output shifts 2→3.
        remap.insert(span(10, 20, 100, 0, &[(0, 0), (2, 3)]));
        // Input 11 = stream 1, inside the first operator → maps to op 0.
        assert_eq!(remap.translate(11), Some(100));
        // Input 13 = stream 3, inside the second operator → maps to op@2.
        assert_eq!(remap.translate(13), Some(103));
    }

    /// Mythos #209: when two adjacent input functions (A.input_end ==
    /// B.input_start) are NOT adjacent in the fused output, the shared
    /// boundary address is ambiguous (A's exclusive end vs B's start)
    /// and must tombstone (None) rather than emit B's start as A's end.
    /// When they ARE adjacent in the output (input order preserved), the
    /// two interpretations coincide and the address resolves cleanly.
    #[test]
    fn translate_ambiguous_boundary_tombstones_when_reordered() {
        // A = [10,20) → output [200,210); B = [20,30) → output [500,510).
        // A and B are contiguous in input but far apart in output.
        let mut remap = AddressRemap::new();
        remap.insert(span(10, 20, 200, 0, &[(0, 0)]));
        remap.insert(span(20, 30, 500, 0, &[(0, 0)]));
        // addr 20 is A.input_end AND B.input_start; outputs diverge
        // (A end = 210, B start = 500) → ambiguous → None.
        assert_eq!(remap.translate(20), None);

        // Order-preserved layout: A end (210) == B start (210) → the
        // boundary is unambiguous and resolves.
        let mut ordered = AddressRemap::new();
        ordered.insert(span(10, 20, 200, 0, &[(0, 0)]));
        ordered.insert(span(20, 30, 210, 0, &[(0, 0)]));
        assert_eq!(ordered.translate(20), Some(210));
    }

    /// An address in the locals/prefix region (`DW_AT_low_pc` points at
    /// the body start) maps linearly — the locals are preserved verbatim
    /// during fusion.
    #[test]
    fn translate_locals_prefix_maps_linearly() {
        let mut remap = AddressRemap::new();
        remap.insert(span(10, 30, 50, 5, &[(0, 0)]));
        // low_pc at body start (body_rel 0) → output_body_start.
        assert_eq!(remap.translate(10), Some(50));
        // body_rel 2 (still in the 5-byte locals prefix) → 50 + 2.
        assert_eq!(remap.translate(12), Some(52));
    }

    /// Oracle for inc 3b: build real input DWARF with gimli, remap a
    /// subprogram's `low_pc` from 0x10 → 0x200 through
    /// [`rewrite_debug_sections`], then re-parse the *output* DWARF and
    /// assert the address was actually translated. This exercises the
    /// full gimli read → `convert_address` → write → read round-trip —
    /// the genuinely new, fidelity-risky code path.
    #[test]
    fn ls_d_1_remap_translates_low_pc() {
        use gimli::write::{
            Address, AttributeValue, Dwarf, EndianVec, LineProgram, Sections, Unit,
        };
        use gimli::{Encoding, Format, LittleEndian, constants};

        // --- Build input DWARF: one unit, one subprogram @ low_pc 0x10.
        let encoding = Encoding {
            format: Format::Dwarf32,
            version: 4,
            address_size: 4,
        };
        let mut in_dwarf = Dwarf::new();
        let unit_id = in_dwarf.units.add(Unit::new(encoding, LineProgram::none()));
        let unit = in_dwarf.units.get_mut(unit_id);
        let root = unit.root();
        let sp = unit.add(root, constants::DW_TAG_subprogram);
        unit.get_mut(sp).set(
            constants::DW_AT_low_pc,
            AttributeValue::Address(Address::Constant(0x10)),
        );
        unit.get_mut(sp)
            .set(constants::DW_AT_high_pc, AttributeValue::Udata(0x20));

        let mut sections = Sections::new(EndianVec::new(LittleEndian));
        in_dwarf.write(&mut sections).expect("write input dwarf");
        let mut input: Vec<(String, Vec<u8>)> = Vec::new();
        sections
            .for_each(|id, data| {
                input.push((id.name().to_string(), data.slice().to_vec()));
                Ok::<(), gimli::Error>(())
            })
            .expect("collect input sections");

        // --- Remap input 0x10 → output 0x200 (single instruction).
        let mut remap = AddressRemap::new();
        remap.insert(FunctionSpan {
            input_start: 0x10,
            input_end: 0x40,
            output_body_start: 0x200,
            output_body_end: 0x230,
            locals_prefix_len: 0,
            instr_offsets: InstrOffsetMap {
                entries: vec![InstrOffset { old: 0, new: 0 }],
            },
        });

        let out = rewrite_debug_sections(&input, &remap, &[]).expect("rewrite debug sections");

        // --- Re-parse output DWARF and read the subprogram's low_pc.
        let section_data = |name: &str| -> &[u8] {
            out.iter()
                .find(|(n, _)| n == name)
                .map(|(_, d)| d.as_slice())
                .unwrap_or(&[])
        };
        let load =
            |id: gimli::SectionId| -> Result<gimli::EndianSlice<'_, LittleEndian>, gimli::Error> {
                Ok(gimli::EndianSlice::new(
                    section_data(id.name()),
                    LittleEndian,
                ))
            };
        let dwarf = gimli::Dwarf::load(load).expect("load output dwarf");
        let mut units = dwarf.units();
        let header = units.next().expect("units iter").expect("exactly one unit");
        let unit = dwarf.unit(header).expect("parse unit");
        let mut entries = unit.entries();
        let mut low_pc = None;
        while let Some((_, entry)) = entries.next_dfs().expect("dfs walk") {
            if entry.tag() == constants::DW_TAG_subprogram
                && let Some(gimli::AttributeValue::Addr(a)) = entry
                    .attr_value(constants::DW_AT_low_pc)
                    .expect("read low_pc attr")
            {
                low_pc = Some(a);
            }
        }
        assert_eq!(
            low_pc,
            Some(0x200),
            "low_pc must be remapped from input 0x10 to output 0x200"
        );
    }

    /// The parallel-walk core: with an identity rewrite (output bytes ==
    /// input bytes) the recovered remap must be an identity on the first
    /// instruction of every function — proving the layout parsing and
    /// instruction-stream zipping line up.
    #[test]
    fn build_remap_from_parts_identity_walk() {
        let wat = r#"(module
            (func (param i32) (result i32) local.get 0 i32.const 1 i32.add)
            (func (result i32) i32.const 42))"#;
        let bytes = wat::parse_str(wat).expect("assemble wat");

        // No imports; merged order matches input defined order.
        let pairs = [(0usize, 0u32), (1usize, 1u32)];
        let remap =
            build_remap_from_parts(&bytes, 0, &bytes, &pairs).expect("build identity remap");
        assert_eq!(remap.len(), 2);

        let layouts = module_function_layouts(&bytes).expect("layouts");
        assert_eq!(layouts.len(), 2);
        for l in &layouts {
            let first_instr = l.body_start + l.locals_prefix_len;
            assert_eq!(
                remap.translate(first_instr),
                Some(first_instr),
                "identity rewrite must map an address to itself"
            );
        }
    }

    /// Mythos #209 (2nd finding): `code_extent` must cover the input
    /// module's *full* code section — including functions meld dropped —
    /// so a dropped function's code address is classified as code
    /// (tombstoned) rather than as a linear-memory data address (passed
    /// through stale). Using only the surviving spans' max end would
    /// misclassify a dropped trailing function.
    #[test]
    fn code_extent_covers_dropped_trailing_function() {
        let wat = r#"(module
            (func (result i32) i32.const 1)
            (func (result i32) i32.const 2)
            (func (result i32) i32.const 3))"#;
        let bytes = wat::parse_str(wat).expect("assemble wat");
        let layouts = module_function_layouts(&bytes).expect("layouts");
        let full_extent = layouts.iter().map(|l| l.body_end).max().unwrap();
        let surviving_max = layouts[1].body_end;
        assert!(
            full_extent > surviving_max,
            "the dropped trailing function must extend past the survivors"
        );

        // meld keeps func 0 and func 1; func 2 is dropped (no pair).
        let pairs = [(0usize, 0u32), (1usize, 1u32)];
        let remap = build_remap_from_parts(&bytes, 0, &bytes, &pairs).expect("build remap");

        // The code/data boundary is the full input extent, so func 2's
        // address range stays classified as code (→ tombstone in
        // convert_address), not data (→ stale pass-through).
        assert_eq!(remap.code_extent(), full_extent);
    }

    /// A layout mismatch (output has more operators than input — what a
    /// rewriter that inserted instructions would produce) must abort the
    /// remap rather than emit a misaligned address.
    #[test]
    fn build_remap_from_parts_aborts_on_operator_count_mismatch() {
        let input = wat::parse_str("(module (func (result i32) i32.const 1))").expect("input");
        let output = wat::parse_str("(module (func (result i32) i32.const 1 drop i32.const 2))")
            .expect("output");
        let pairs = [(0usize, 0u32)];
        assert!(
            build_remap_from_parts(&input, 0, &output, &pairs).is_none(),
            "operator-count mismatch must yield None (fall back to strip)"
        );
    }

    // ---- Phase 3 (#144): adapter-span enumeration ----

    /// A component-attributed synthetic (`origin.2 == u32::MAX`) is
    /// reported as an adapter span at its real output body range; source
    /// functions are not.
    #[test]
    fn adapter_spans_identifies_component_synthetic() {
        let wat = r#"(module
            (func (result i32) i32.const 1)
            (func (result i32) i32.const 2)
            (func (result i32) i32.const 3))"#;
        let bytes = wat::parse_str(wat).expect("assemble wat");
        // func 1 is meld-generated; 0 and 2 are original source.
        let roles = [None, Some(AdapterRole::Generated), None];

        let spans = adapter_spans_from_parts(&roles, &bytes);
        assert_eq!(spans.len(), 1, "exactly one generated function");
        assert_eq!(spans[0].output_defined_idx, 1);
        assert_eq!(spans[0].role, AdapterRole::Generated);
        assert_eq!(spans[0].role.adapter_line(), 1);

        // The span must match func 1's real layout in the output.
        let layouts = module_function_layouts(&bytes).expect("layouts");
        assert_eq!(spans[0].output_body_start, layouts[1].body_start);
        assert_eq!(spans[0].output_body_end, layouts[1].body_end);
        assert!(
            spans[0].output_body_end > spans[0].output_body_start,
            "body range must be non-empty"
        );
    }

    /// The fully-synthetic sentinel `(usize::MAX, usize::MAX, 0)` is also
    /// recognised even though `origin.2` is a plausible real index (0).
    #[test]
    fn adapter_spans_recognises_fully_synthetic_sentinel() {
        let wat = r#"(module (func (result i32) i32.const 7))"#;
        let bytes = wat::parse_str(wat).expect("assemble wat");
        let roles = [Some(AdapterRole::StartWrapper)];

        let spans = adapter_spans_from_parts(&roles, &bytes);
        assert_eq!(spans.len(), 1);
        assert_eq!(spans[0].output_defined_idx, 0);
        assert_eq!(spans[0].role.adapter_line(), 7);
    }

    /// An all-original module produces no adapter spans.
    #[test]
    fn adapter_spans_empty_when_all_source() {
        let wat = r#"(module
            (func (result i32) i32.const 1)
            (func (result i32) i32.const 2))"#;
        let bytes = wat::parse_str(wat).expect("assemble wat");
        let roles = [None, None];
        assert!(adapter_spans_from_parts(&roles, &bytes).is_empty());
    }

    /// Adapter ranges must be disjoint from every source-function range —
    /// otherwise a synthetic DIE would double-attribute a code byte that a
    /// remapped original DIE already covers.
    #[test]
    fn adapter_spans_disjoint_from_source_ranges() {
        let wat = r#"(module
            (func (result i32) i32.const 1)
            (func (result i32) i32.const 2)
            (func (result i32) i32.const 3))"#;
        let bytes = wat::parse_str(wat).expect("assemble wat");
        let roles = [None, Some(AdapterRole::MemoryCopy), None];

        let adapters = adapter_spans_from_parts(&roles, &bytes);
        let layouts = module_function_layouts(&bytes).expect("layouts");
        for a in &adapters {
            for (i, l) in layouts.iter().enumerate() {
                if roles[i].is_some() {
                    continue;
                }
                let disjoint =
                    a.output_body_end <= l.body_start || a.output_body_start >= l.body_end;
                assert!(disjoint, "adapter span overlaps source function {i}");
            }
        }
    }

    // ---- Phase 3 (#144) inc 2: synthetic DWARF emission ----

    /// Oracle for inc 2: build a synthetic `<meld-adapter>` DWARF unit from
    /// adapter spans, then re-parse it and run the line-number program —
    /// every adapter body-start address must resolve to file
    /// `<meld-adapter>` line 1 (non-zero, so it is not a DWARF "no line").
    /// This exercises the full hand-built line-program write → gimli-read
    /// round-trip, the genuinely new and fidelity-risky code path.
    #[test]
    fn build_adapter_dwarf_attributes_ranges_to_meld_adapter() {
        use gimli::{EndianSlice, LittleEndian};

        let spans = vec![
            AdapterSpan {
                output_defined_idx: 3,
                output_body_start: 0x100,
                output_body_end: 0x140,
                role: AdapterRole::Generated,
            },
            AdapterSpan {
                output_defined_idx: 5,
                output_body_start: 0x200,
                output_body_end: 0x230,
                role: AdapterRole::Generated,
            },
        ];
        let sections = build_adapter_dwarf(&spans).expect("build synthetic dwarf");
        assert!(
            sections.iter().any(|(n, _)| n == ".debug_line"),
            "must emit a .debug_line section"
        );

        let section_data = |name: &str| -> &[u8] {
            sections
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, d)| d.as_slice())
                .unwrap_or(&[])
        };
        let load = |id: gimli::SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
            Ok(EndianSlice::new(section_data(id.name()), LittleEndian))
        };
        let dwarf = gimli::Dwarf::load(load).expect("load synthetic dwarf");
        let mut units = dwarf.units();
        let header = units.next().expect("units iter").expect("exactly one unit");
        let unit = dwarf.unit(header).expect("parse unit");
        let program = unit
            .line_program
            .clone()
            .expect("synthetic unit carries a line program");

        let mut rows = program.rows();
        let mut found_starts = std::collections::BTreeSet::new();
        while let Some((hdr, row)) = rows.next_row().expect("read row") {
            if row.end_sequence() {
                continue;
            }
            let file = row.file(hdr).expect("row has a file entry");
            let fname = match file.path_name() {
                gimli::AttributeValue::String(s) => String::from_utf8_lossy(s.slice()).into_owned(),
                _ => String::new(),
            };
            assert_eq!(
                fname, ADAPTER_SOURCE_NAME,
                "every adapter row must point at <meld-adapter>"
            );
            assert_eq!(
                row.line().map(|l| l.get()),
                Some(1),
                "adapter line must be 1 (non-zero — DWARF line 0 means 'no line')"
            );
            found_starts.insert(row.address());
        }
        assert!(
            found_starts.contains(&0x100) && found_starts.contains(&0x200),
            "both adapter span starts must produce line rows; got {found_starts:?}"
        );
    }

    /// No spans → no synthetic DWARF (nothing to attribute).
    #[test]
    fn build_adapter_dwarf_none_when_no_spans() {
        assert!(build_adapter_dwarf(&[]).is_none());
    }

    /// #144 inc 4: every adapter class maps to a distinct, non-zero
    /// `<meld-adapter>` line — the stable contract witness consumes.
    /// Line 0 means "no source line" in DWARF and would read back as
    /// `unknown`; two classes sharing a line would be indistinguishable.
    #[test]
    fn adapter_lines_are_distinct_and_nonzero() {
        let all = [
            AdapterRole::Generated,
            AdapterRole::Direct,
            AdapterRole::MemoryCopy,
            AdapterRole::Transcode,
            AdapterRole::Async,
            AdapterRole::HandleTable,
            AdapterRole::StartWrapper,
            AdapterRole::AdapterShim,
            AdapterRole::TaskReturnShim,
        ];
        let mut seen = std::collections::BTreeSet::new();
        for role in all {
            let line = role.adapter_line();
            assert!(line > 0, "{role:?} must not use DWARF line 0");
            assert!(seen.insert(line), "{role:?} reuses line {line}");
        }
    }

    /// #208 inc 1 oracle: two independently converted+remapped source
    /// DWARFs merge into ONE coherent section set. Build two sources
    /// with gimli (a.rs:5 covering [0x10,0x30); b.rs:9 covering
    /// [0x40,0x60)), remap them to disjoint fused ranges, merge via the
    /// bounded relocator, re-parse the MERGED set and assert each
    /// remapped address resolves to ITS OWN file:line — proving the
    /// abbrev/str/line offset relocations all landed (any miss makes
    /// gimli fail the parse or resolve the wrong file).
    #[test]
    fn ls_d_3_multi_source_merge_round_trips_both_units() {
        use gimli::write::{
            Address, AttributeValue, Dwarf, EndianVec, LineProgram, LineString, Sections, Unit,
        };
        use gimli::{Encoding, EndianSlice, Format, LineEncoding, LittleEndian, constants};

        let encoding = Encoding {
            format: Format::Dwarf32,
            version: 4,
            address_size: 4,
        };

        let build_source = |file: &str, line: u64, addr: u64, len: u64| -> Vec<(String, Vec<u8>)> {
            let mut lp = LineProgram::new(
                encoding,
                LineEncoding::default(),
                LineString::String(b"/src".to_vec()),
                LineString::String(file.as_bytes().to_vec()),
                None,
            );
            let dir = lp.default_directory();
            let fid = lp.add_file(LineString::String(file.as_bytes().to_vec()), dir, None);
            lp.begin_sequence(Some(Address::Constant(addr)));
            {
                let row = lp.row();
                row.address_offset = 0;
                row.file = fid;
                row.line = line;
                row.is_statement = true;
            }
            lp.generate_row();
            lp.end_sequence(len);

            let mut dwarf = Dwarf::new();
            let unit_id = dwarf.units.add(Unit::new(encoding, lp));
            let unit = dwarf.units.get_mut(unit_id);
            let root = unit.root();
            unit.get_mut(root).set(
                constants::DW_AT_name,
                AttributeValue::String(file.as_bytes().to_vec()),
            );
            // Use a StringRef so the source actually exercises
            // DW_FORM_strp relocation (inline strings would not).
            let producer = dwarf.strings.add(format!("producer-of-{file}"));
            // A string SHARED by both sources, so the merge has real
            // overlap to pool (#208 inc 2).
            let comp_dir = dwarf.strings.add("shared-comp-dir");
            let unit = dwarf.units.get_mut(unit_id);
            let root = unit.root();
            unit.get_mut(root).set(
                constants::DW_AT_producer,
                AttributeValue::StringRef(producer),
            );
            unit.get_mut(root).set(
                constants::DW_AT_comp_dir,
                AttributeValue::StringRef(comp_dir),
            );
            let sp = unit.add(root, constants::DW_TAG_subprogram);
            unit.get_mut(sp).set(
                constants::DW_AT_low_pc,
                AttributeValue::Address(Address::Constant(addr)),
            );
            unit.get_mut(sp)
                .set(constants::DW_AT_high_pc, AttributeValue::Udata(len));

            let mut sections = Sections::new(EndianVec::new(LittleEndian));
            dwarf.write(&mut sections).expect("write source dwarf");
            let mut out = Vec::new();
            sections
                .for_each(|id, data| {
                    if !data.slice().is_empty() {
                        out.push((id.name().to_string(), data.slice().to_vec()));
                    }
                    Ok::<(), gimli::Error>(())
                })
                .expect("collect");
            out
        };

        let src_a = build_source("a.rs", 5, 0x10, 0x20);
        let src_b = build_source("b.rs", 9, 0x40, 0x20);

        let remap_for = |in_start: u32, out_start: u32| {
            let mut remap = AddressRemap::new();
            remap.insert(FunctionSpan {
                input_start: in_start,
                input_end: in_start + 0x20,
                output_body_start: out_start,
                output_body_end: out_start + 0x20,
                locals_prefix_len: 0,
                instr_offsets: InstrOffsetMap {
                    entries: vec![InstrOffset { old: 0, new: 0 }],
                },
            });
            remap
        };
        let set_a =
            rewrite_debug_sections(&src_a, &remap_for(0x10, 0x100), &[]).expect("convert source a");
        let set_b =
            rewrite_debug_sections(&src_b, &remap_for(0x40, 0x200), &[]).expect("convert source b");

        let sum_str: usize = [&set_a, &set_b]
            .iter()
            .map(|s| section_of(s, ".debug_str").len())
            .sum();
        let sum_abbrev: usize = [&set_a, &set_b]
            .iter()
            .map(|s| section_of(s, ".debug_abbrev").len())
            .sum();
        let merged =
            concat_dwarf_section_sets(&[set_a, set_b]).expect("bounded merge must succeed");
        // #208 inc 2: identical abbrev tables are reused and overlapping
        // strings pooled — the merged sections must be smaller than the
        // naive concatenation (the two sources share gimli's emitted
        // comp-dir/name strings and identical abbrev shapes).
        assert!(
            section_of(&merged, ".debug_abbrev").len() < sum_abbrev,
            "byte-identical abbrev tables must be reused"
        );
        assert!(
            section_of(&merged, ".debug_str").len() < sum_str,
            "overlapping strings must be pooled"
        );

        // Re-parse the merged set.
        let section_data = |name: &str| -> &[u8] { section_of(&merged, name) };
        let load = |id: gimli::SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
            Ok(EndianSlice::new(section_data(id.name()), LittleEndian))
        };
        let dwarf = gimli::Dwarf::load(load).expect("merged dwarf must load");

        let mut rows_seen: Vec<(u64, String, u64)> = Vec::new();
        let mut producers: Vec<String> = Vec::new();
        let mut unit_count = 0;
        let mut units = dwarf.units();
        while let Some(header) = units.next().expect("units") {
            unit_count += 1;
            let unit = dwarf.unit(header).expect("merged unit must parse");
            // DW_AT_producer goes through .debug_str — proves strp
            // relocation for the second unit.
            {
                let mut entries = unit.entries();
                if let Some((_, root)) = entries.next_dfs().expect("root")
                    && let Some(attr) = root.attr(constants::DW_AT_producer).expect("attr read")
                    && let Ok(sref) = dwarf.attr_string(&unit, attr.value())
                {
                    producers.push(String::from_utf8_lossy(sref.slice()).into_owned());
                }
            }
            let Some(program) = unit.line_program.clone() else {
                continue;
            };
            let mut rows = program.rows();
            while let Some((hdr, row)) = rows.next_row().expect("row") {
                if row.end_sequence() {
                    continue;
                }
                let fname = row
                    .file(hdr)
                    .map(|f| match f.path_name() {
                        gimli::AttributeValue::String(sl) => {
                            String::from_utf8_lossy(sl.slice()).into_owned()
                        }
                        _ => String::new(),
                    })
                    .unwrap_or_default();
                rows_seen.push((row.address(), fname, row.line().map_or(0, |l| l.get())));
            }
        }

        assert_eq!(unit_count, 2, "both units survive the merge");
        assert!(
            rows_seen.contains(&(0x100, "a.rs".to_string(), 5)),
            "source A resolves at its remapped address; rows: {rows_seen:?}"
        );
        assert!(
            rows_seen.contains(&(0x200, "b.rs".to_string(), 9)),
            "source B resolves at its remapped address; rows: {rows_seen:?}"
        );
        assert!(
            producers.contains(&"producer-of-a.rs".to_string())
                && producers.contains(&"producer-of-b.rs".to_string()),
            "strp-referenced strings must survive relocation; got {producers:?}"
        );
    }

    /// #144 inc 4: spans carry per-class roles and the indices stay
    /// aligned with output layout — including entries appended AFTER the
    /// merged functions (the FACT-adapter positions that were previously
    /// un-enumerated). Round-trip through `build_adapter_dwarf` and
    /// assert each address resolves to its class's line.
    #[test]
    fn per_class_spans_round_trip_to_distinct_lines() {
        use gimli::{EndianSlice, LittleEndian};

        let wat = r#"(module
            (func (result i32) i32.const 1)
            (func (result i32) i32.const 2)
            (func (result i32) i32.const 3))"#;
        let bytes = wat::parse_str(wat).expect("assemble wat");
        // func 0 = real source; func 1 = merger handle-table helper;
        // func 2 = appended FACT transcode adapter.
        let roles = [
            None,
            Some(AdapterRole::HandleTable),
            Some(AdapterRole::Transcode),
        ];
        let spans = adapter_spans_from_parts(&roles, &bytes);
        assert_eq!(spans.len(), 2);

        let sections = build_adapter_dwarf(&spans).expect("build");
        let section_data = |name: &str| -> &[u8] {
            sections
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, d)| d.as_slice())
                .unwrap_or(&[])
        };
        let load = |id: gimli::SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
            Ok(EndianSlice::new(section_data(id.name()), LittleEndian))
        };
        let dwarf = gimli::Dwarf::load(load).expect("load");
        let mut by_addr = std::collections::BTreeMap::new();
        let mut units = dwarf.units();
        while let Some(header) = units.next().expect("units") {
            let unit = dwarf.unit(header).expect("unit");
            let Some(program) = unit.line_program.clone() else {
                continue;
            };
            let mut rows = program.rows();
            while let Some((_, row)) = rows.next_row().expect("row") {
                if !row.end_sequence() {
                    by_addr.insert(row.address(), row.line().map_or(0, |l| l.get()));
                }
            }
        }
        for span in &spans {
            assert_eq!(
                by_addr.get(&u64::from(span.output_body_start)).copied(),
                Some(u64::from(span.role.adapter_line())),
                "span at {:#x} must resolve to its class line",
                span.output_body_start
            );
        }
        // And the two classes resolved to DIFFERENT lines.
        let lines: std::collections::BTreeSet<u64> = by_addr.values().copied().collect();
        assert_eq!(lines.len(), 2, "two classes, two distinct lines");
    }

    /// Inc 3 oracle: source DWARF and the synthetic `<meld-adapter>` unit
    /// go through ONE `dwarf.write()` and must coexist in the output.
    /// Build real input DWARF (one unit, line program attributing
    /// [0x10,0x40) to `orig.rs:7`), remap 0x10 → 0x200 through
    /// [`rewrite_debug_sections`] WITH an adapter span at [0x300,0x320),
    /// then re-parse the single output `.debug_line` and assert BOTH:
    /// the original row landed at its remapped address still pointing at
    /// `orig.rs:7`, and the adapter row points at `<meld-adapter>:1`.
    /// This falsifies the naive concat approach — two independently
    /// written unit sets would collide on cross-section offsets and fail
    /// the re-parse. (`ls_d_2_` prefix: LS-D-2 regression, run by the
    /// LS-N verification gate.)
    #[test]
    fn ls_d_2_rewrite_emits_source_and_adapter_units_in_one_write() {
        use gimli::write::{
            Address, AttributeValue, Dwarf, EndianVec, LineProgram, LineString, Sections, Unit,
        };
        use gimli::{Encoding, EndianSlice, Format, LineEncoding, LittleEndian, constants};

        // --- Input DWARF: one unit whose line program maps 0x10 → orig.rs:7.
        let encoding = Encoding {
            format: Format::Dwarf32,
            version: 4,
            address_size: 4,
        };
        let mut line_program = LineProgram::new(
            encoding,
            LineEncoding::default(),
            LineString::String(b"/src".to_vec()),
            LineString::String(b"orig.rs".to_vec()),
            None,
        );
        let dir = line_program.default_directory();
        let file = line_program.add_file(LineString::String(b"orig.rs".to_vec()), dir, None);
        line_program.begin_sequence(Some(Address::Constant(0x10)));
        {
            let row = line_program.row();
            row.address_offset = 0;
            row.file = file;
            row.line = 7;
            row.is_statement = true;
        }
        line_program.generate_row();
        line_program.end_sequence(0x30);

        let mut in_dwarf = Dwarf::new();
        let unit_id = in_dwarf.units.add(Unit::new(encoding, line_program));
        let unit = in_dwarf.units.get_mut(unit_id);
        let root = unit.root();
        unit.get_mut(root).set(
            constants::DW_AT_name,
            AttributeValue::String(b"orig.rs".to_vec()),
        );

        let mut sections = Sections::new(EndianVec::new(LittleEndian));
        in_dwarf.write(&mut sections).expect("write input dwarf");
        let mut input: Vec<(String, Vec<u8>)> = Vec::new();
        sections
            .for_each(|id, data| {
                input.push((id.name().to_string(), data.slice().to_vec()));
                Ok::<(), gimli::Error>(())
            })
            .expect("collect input sections");

        // --- Remap input 0x10 → output 0x200; adapter span at [0x300,0x320).
        let mut remap = AddressRemap::new();
        remap.insert(FunctionSpan {
            input_start: 0x10,
            input_end: 0x40,
            output_body_start: 0x200,
            output_body_end: 0x230,
            locals_prefix_len: 0,
            instr_offsets: InstrOffsetMap {
                entries: vec![InstrOffset { old: 0, new: 0 }],
            },
        });
        let spans = vec![AdapterSpan {
            output_defined_idx: 9,
            output_body_start: 0x300,
            output_body_end: 0x320,
            role: AdapterRole::Generated,
        }];

        let out = rewrite_debug_sections(&input, &remap, &spans)
            .expect("combined rewrite must serialise");

        // --- Re-parse the OUTPUT and walk every unit's line program.
        let section_data = |name: &str| -> &[u8] {
            out.iter()
                .find(|(n, _)| n == name)
                .map(|(_, d)| d.as_slice())
                .unwrap_or(&[])
        };
        let load = |id: gimli::SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
            Ok(EndianSlice::new(section_data(id.name()), LittleEndian))
        };
        let dwarf = gimli::Dwarf::load(load).expect("load combined dwarf");

        // (address, file, line) rows across all units.
        let mut attributed: Vec<(u64, String, u64)> = Vec::new();
        let mut unit_count = 0usize;
        let mut units = dwarf.units();
        while let Some(header) = units.next().expect("units iter") {
            unit_count += 1;
            let unit = dwarf.unit(header).expect("parse unit");
            let Some(program) = unit.line_program.clone() else {
                continue;
            };
            let mut rows = program.rows();
            while let Some((hdr, row)) = rows.next_row().expect("read row") {
                if row.end_sequence() {
                    continue;
                }
                let fname = row
                    .file(hdr)
                    .map(|f| match f.path_name() {
                        gimli::AttributeValue::String(s) => {
                            String::from_utf8_lossy(s.slice()).into_owned()
                        }
                        _ => String::new(),
                    })
                    .unwrap_or_default();
                attributed.push((row.address(), fname, row.line().map_or(0, |l| l.get())));
            }
        }

        assert_eq!(unit_count, 2, "remapped original unit + synthetic unit");
        assert!(
            attributed
                .iter()
                .any(|(a, f, l)| *a == 0x200 && f == "orig.rs" && *l == 7),
            "original code must resolve at its REMAPPED address to its real \
             source; rows = {attributed:?}"
        );
        assert!(
            attributed
                .iter()
                .any(|(a, f, l)| *a == 0x300 && f == ADAPTER_SOURCE_NAME && *l == 1),
            "adapter range must resolve to <meld-adapter>:1 in the same \
             .debug_line; rows = {attributed:?}"
        );
    }
}
