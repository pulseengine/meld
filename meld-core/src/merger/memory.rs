//! Shared/rebased memory planning, memory-type combination and conversion,
//! data-extent and heap-base analysis extracted from the merger.

use super::*;

#[derive(Debug, Clone)]
pub(crate) struct SharedMemoryPlan {
    pub(crate) memory: EncoderMemoryType,
    pub(crate) import: Option<(String, String)>,
    pub(crate) bases: HashMap<(usize, usize), u64>,
}

impl Merger {
    pub(crate) fn compute_shared_memory_plan(
        &self,
        components: &[ParsedComponent],
    ) -> Result<Option<SharedMemoryPlan>> {
        let mut memory_types = Vec::new();
        let mut import_names: Vec<(String, String)> = Vec::new();
        let mut has_defined = false;
        // (key, module memory type, used-data extent). The extent is
        // `Some(bytes)` only under `--pack-rebase` and only when every active
        // data segment has a constant offset; `None` means "cannot pack — fall
        // back to the declared page stride" (SR-57).
        let mut module_memories: Vec<((usize, usize), MemoryType, Option<u64>)> = Vec::new();

        for (comp_idx, component) in components.iter().enumerate() {
            for (mod_idx, module) in component.core_modules.iter().enumerate() {
                for import in &module.imports {
                    if let ImportKind::Memory(mem) = &import.kind {
                        memory_types.push(mem.clone());
                        import_names.push((import.module.clone(), import.name.clone()));
                    }
                }

                if !module.memories.is_empty() {
                    has_defined = true;
                    memory_types.extend(module.memories.iter().cloned());
                }

                if self.address_rebasing {
                    if let Some(module_memory) = module_memory_type(module)? {
                        let extent = if self.pack_rebase {
                            module_used_data_extent(module, &module_memory, comp_idx, mod_idx)?
                        } else {
                            None
                        };
                        module_memories.push(((comp_idx, mod_idx), module_memory, extent));
                    }
                }
            }
        }

        if memory_types.is_empty() {
            return Ok(None);
        }

        let mut combined = if self.address_rebasing {
            combine_memory_types_rebased(&memory_types)?
        } else {
            combine_memory_types_shared(&memory_types)?
        };

        let import = if has_defined {
            None
        } else {
            let Some((module, name)) = import_names.first().cloned() else {
                return Ok(None);
            };
            if import_names.iter().any(|(m, n)| *m != module || *n != name) {
                return Err(Error::MemoryStrategyUnsupported(
                    "shared memory requires a single import module/name".to_string(),
                ));
            }
            Some((module, name))
        };

        let mut bases = HashMap::new();
        if self.address_rebasing {
            // Byte-granular running base. Under the default page-granular
            // strategy each module strides by its declared page count; under
            // `--pack-rebase` it strides by its 16-byte-aligned used data
            // extent (SR-57). 16-byte alignment keeps `v128` accesses aligned
            // after the uniform `+base` shift.
            const PACK_ALIGN: u64 = 16;
            let overflow =
                || Error::MemoryStrategyUnsupported("shared memory size overflow".to_string());
            let mut next_base: u64 = 0;
            for (key, module_memory, extent) in &module_memories {
                let base_bytes = next_base;
                if !combined.memory64 && base_bytes > u64::from(u32::MAX) {
                    return Err(Error::MemoryStrategyUnsupported(
                        "shared memory base offset exceeds 32-bit address space".to_string(),
                    ));
                }
                bases.insert(*key, base_bytes);

                // Stride: packed extent when available, else the declared page
                // count (the fallback also covers a module whose data offsets
                // are non-constant and therefore cannot be safely packed).
                let stride = match (self.pack_rebase, extent) {
                    (true, Some(bytes)) => (*bytes)
                        .checked_next_multiple_of(PACK_ALIGN)
                        .ok_or_else(overflow)?,
                    _ => module_memory
                        .initial
                        .checked_mul(WASM_PAGE_SIZE)
                        .ok_or_else(overflow)?,
                };
                next_base = next_base.checked_add(stride).ok_or_else(overflow)?;
            }

            // Compact the combined memory to the packed total. Without this the
            // combined minimum stays the sum of declared pages, so the bases
            // would be compact inside an uncompacted memory and `--pack-rebase`
            // would deliver none of its size benefit (SR-57).
            if self.pack_rebase {
                combined.initial = next_base.div_ceil(WASM_PAGE_SIZE).max(1);
                if let Some(max) = combined.maximum {
                    combined.maximum = Some(max.max(combined.initial));
                }
            }
        }

        Ok(Some(SharedMemoryPlan {
            memory: convert_memory_type(&combined),
            import,
            bases,
        }))
    }
}

pub(crate) fn module_memory_type(module: &CoreModule) -> Result<Option<MemoryType>> {
    let mut memory_type: Option<MemoryType> = None;

    for import in &module.imports {
        if let ImportKind::Memory(mem) = &import.kind {
            if memory_type.is_some() {
                return Err(Error::MemoryStrategyUnsupported(
                    "shared memory rebasing supports a single memory per module".to_string(),
                ));
            }
            memory_type = Some(mem.clone());
        }
    }

    for mem in &module.memories {
        if memory_type.is_some() {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory rebasing supports a single memory per module".to_string(),
            ));
        }
        memory_type = Some(mem.clone());
    }

    Ok(memory_type)
}

pub(crate) fn combine_memory_types_shared(memories: &[MemoryType]) -> Result<MemoryType> {
    let Some(first) = memories.first() else {
        return Err(Error::MemoryStrategyUnsupported(
            "shared memory requires at least one memory".to_string(),
        ));
    };

    let mut minimum = first.initial;
    let mut maximum = first.maximum;

    for mem in memories.iter().skip(1) {
        if mem.memory64 != first.memory64 {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory requires matching memory64 settings".to_string(),
            ));
        }
        if mem.shared != first.shared {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory requires matching shared settings".to_string(),
            ));
        }

        minimum = minimum.max(mem.initial);
        maximum = match (maximum, mem.maximum) {
            (Some(a), Some(b)) => Some(a.min(b)),
            _ => None,
        };
    }

    if let Some(max) = maximum {
        if minimum > max {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory minimum exceeds maximum".to_string(),
            ));
        }
    }

    Ok(MemoryType {
        memory64: first.memory64,
        shared: first.shared,
        initial: minimum,
        maximum,
    })
}

pub(crate) fn combine_memory_types_rebased(memories: &[MemoryType]) -> Result<MemoryType> {
    let Some(first) = memories.first() else {
        return Err(Error::MemoryStrategyUnsupported(
            "shared memory requires at least one memory".to_string(),
        ));
    };

    let mut minimum = 0u64;
    let mut maximum: Option<u64> = Some(0);

    for mem in memories {
        if mem.memory64 != first.memory64 {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory requires matching memory64 settings".to_string(),
            ));
        }
        if mem.shared != first.shared {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory requires matching shared settings".to_string(),
            ));
        }

        minimum = minimum
            .checked_add(mem.initial)
            .ok_or_else(|| Error::MemoryStrategyUnsupported("memory size overflow".to_string()))?;

        maximum = match (maximum, mem.maximum) {
            (Some(a), Some(b)) => a.checked_add(b),
            _ => None,
        };
    }

    if !first.memory64 {
        let max_pages = u64::from(u32::MAX) / WASM_PAGE_SIZE;
        if minimum > max_pages {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory exceeds 32-bit address space".to_string(),
            ));
        }
        if let Some(max) = maximum {
            if max > max_pages {
                return Err(Error::MemoryStrategyUnsupported(
                    "shared memory maximum exceeds 32-bit address space".to_string(),
                ));
            }
        }
    }

    Ok(MemoryType {
        memory64: first.memory64,
        shared: first.shared,
        initial: minimum,
        maximum,
    })
}

/// Convert parser MemoryType to encoder MemoryType
pub(crate) fn convert_memory_type(mem: &MemoryType) -> EncoderMemoryType {
    EncoderMemoryType {
        minimum: mem.initial,
        maximum: mem.maximum,
        memory64: mem.memory64,
        shared: mem.shared,
        page_size_log2: None,
    }
}

/// Whether `module` performs any *direct* (non-bulk) linear-memory access — an
/// `i32.load`/`i32.store` family instruction whose effective address may embed
/// a baked-in absolute address.
///
/// Bulk-memory ops (`memory.copy`/`fill`/`init`) are deliberately excluded: the
/// rewriter rebases their runtime address operands dynamically
/// ([`crate::rewriter`]'s `append_rebased_address`), so a module whose only
/// memory touches are bulk ops is safe to place at a non-zero shared-memory
/// base even without relocation metadata. This is what lets #326's path-F gate
/// fire precisely — on modules that could hide an un-rebased absolute address —
/// without rejecting the (safe) bulk-only case.
///
/// KNOWN LIMITATION (#326 Finding A, tracked follow-up): this catches an
/// address embedded in a load/store, but NOT an `i32.const`/`i64.const` whose
/// value is itself an absolute address used purely as a *value* (handed to an
/// imported `memcpy`/`fd_write` or returned across the module boundary) with no
/// direct access. Such a no-reloc module still slips the gate. A sound fix
/// needs data-flow (a bare const is indistinguishable from an integer, and
/// bulk-op-consumed consts ARE safe — rejecting all consts regresses the
/// legitimate bulk-only case, `test_address_rebasing_end_to_end`). Note this
/// residual gap does NOT affect the supported path: `--emit-relocs` inputs
/// carry reloc metadata, so their address consts are rebased via `reloc.CODE`.
/// SR-57 / #370: the module's used STATIC extent — the highest linear-memory
/// address it uses — for compact `--pack-rebase` placement. Returns `Some(top)`
/// when a sound compact extent is known; otherwise `None`, and the caller
/// strides by the declared page count (page-granular). The page-granular stride
/// is a safe reservation ONLY for a DEFINED memory (nothing can be accessed
/// beyond `initial` pages without `memory.grow`, which the rebase path forbids);
/// for an IMPORTED memory `initial` is only a floor, so the imported case is
/// handled explicitly below and NEVER strides below the visible extent.
///
/// ## Why a data-segment scan alone is not enough (#370)
///
/// The v0.43.0 implementation returned the maximum end (`offset + len`) across
/// ACTIVE data segments, `D`. That is UNSOUND whenever a module uses memory
/// above `D`: a zero-init `.bss`/arena region (relay#327 replaces a growing
/// allocator with a bounded static arena that lives in `.bss`, NOT a data
/// segment), a heap reached through a runtime bump pointer, a shadow stack, or
/// a computed/MMIO address. None of those appear in the segment table, so
/// packing by `D` UNDER-reserves the tail `[D, declared)` and the next packed
/// component overlaps it. SR-56's overlap check is ACTIVE-data-only, so it does
/// NOT catch a `.bss` collision — the result is silent corruption. Measured on
/// the real target (falcon-v1.133.0): 17 declared pages, active-data extent
/// `D ≈ 1048672`, declared `P = 1114112` — a 65440-byte tail invisible to `D`.
///
/// ## The sound rule
///
/// Reclaiming the tail `[D, declared)` is sound only when the module publishes
/// an authoritative "top of used static memory" marker — an immutable-const
/// `__heap_base` global (exported, or named in the `name` section). Everything
/// above `__heap_base` is unused under the `--pack-rebase` contract (grow
/// killed; any arena lives below it in `.bss`). With the marker we reserve
/// `max(__heap_base, D)`, clamped down to `declared` only for a DEFINED memory
/// (for an imported memory `declared` is a floor, so clamping would
/// under-reserve). WITHOUT the marker we do NOT guess — fall back to the
/// page-granular declared stride (`None`) and warn, EXCEPT when the visible data
/// already exceeds `declared` (only possible for an imported memory), where
/// page-granular would under-reserve, so we reserve `D` and warn. The
/// `__heap_base` symbol is NOT present in default toolchain output (verified:
/// absent from all six falcon exports, from the `--emit-relocs` linking symbol
/// table, and from the `name` section — only `__stack_pointer` is named), so
/// enabling compaction is a supplier precondition: build with
/// `-Wl,--export=__heap_base`.
///
/// The invariant every branch preserves: the reservation is always `>= D`, and
/// `declared` may only LOWER it for a DEFINED memory.
///
/// Returns `None` (page-granular) BEFORE the marker lookup — a `__heap_base`
/// marker does NOT rescue these, their used region is invisible no matter what
/// the marker says — when:
///   - an active segment has a non-constant (runtime/global) offset, or
///   - the module carries any PASSIVE segment (its `memory.init` destination is
///     not in the segment table).
///
/// A module with a memory but no static data (`D == 0`) and no marker also
/// declines (page-granular avoids the `align16(0) = 0` alias, CI Mythos SR-57
/// finding) — but here a marker DOES rescue it (its `.bss` top is authoritative).
fn module_used_data_extent(
    module: &CoreModule,
    memory: &MemoryType,
    comp_idx: usize,
    mod_idx: usize,
) -> Result<Option<u64>> {
    // `declared` = `initial` pages in bytes. Its meaning depends on whether the
    // memory is DEFINED here or IMPORTED (LS-M-?? / coordinator delta-pass):
    //   * DEFINED memory: `initial` is a true CAP — a valid module cannot
    //     address (or place active data) beyond it without `memory.grow`, which
    //     the rebase path forbids. `declared` may lower the extent.
    //   * IMPORTED memory: `initial` is only the declared MINIMUM the module
    //     needs; a dylink/PIC dylib legally imports `(memory 1 8)` and addresses
    //     far above page 1. `declared` is a FLOOR, NOT a cap, and must NEVER
    //     lower the extent.
    // The hard invariant enforced below in EVERY branch: the returned extent
    // (or the page-granular `None` stride) is always `>= max_end`, and
    // `declared` may only lower the extent for a DEFINED memory.
    let defined_memory = !module.memories.is_empty();
    let Some(declared) = memory.initial.checked_mul(WASM_PAGE_SIZE) else {
        return Ok(None);
    };

    // Active-data-segment extent `max_end` (constant offsets only). A passive or
    // non-constant-offset segment makes the used region invisible → decline.
    let segments = crate::segments::parse_data_segments(module)?;
    let mut max_end: u64 = 0;
    for seg in &segments {
        match &seg.mode {
            crate::segments::DataSegmentMode_::Active { offset_value, .. } => {
                let start = match offset_value {
                    Some(crate::segments::ConstExprValue::I32(v)) => u64::from(*v as u32),
                    Some(crate::segments::ConstExprValue::I64(v)) => *v as u64,
                    None => return Ok(None),
                };
                max_end = max_end.max(start.saturating_add(seg.data.len() as u64));
            }
            crate::segments::DataSegmentMode_::Passive => return Ok(None),
        }
    }

    // Compaction below `declared` is sound only with an authoritative marker.
    match module_heap_base_marker(module) {
        Some(heap_base) => {
            // Marker present: the authoritative top of used static memory.
            // Never below the visible data (`max_end`) — the hard invariant.
            let mut extent = heap_base.max(max_end);
            // Clamp DOWN to `declared` only for a DEFINED memory, where it is a
            // real cap (a stale/oversized marker must not stride past the
            // module's own memory). For an IMPORTED memory `declared` is a floor,
            // so clamping would under-reserve — do NOT clamp (regression the
            // delta-pass caught: `.min(declared)` shrank a legit extent).
            if defined_memory {
                extent = extent.min(declared);
            }
            if extent == 0 {
                // Degenerate (no data, marker at 0): nothing to reserve; let the
                // caller stride page-granular rather than alias at base 0.
                return Ok(None);
            }
            Ok(Some(extent))
        }
        None if max_end == 0 => {
            // Memory but no static data and no marker: real usage (a `.bss`/heap
            // region, or reloc-flagged above-zero access as in the #326 harness)
            // is invisible to a segment scan. Page-granular keeps the reservation
            // >= anything within `declared` and avoids the `align16(0) = 0` alias.
            Ok(None)
        }
        None if max_end > declared => {
            // No marker AND the visible data already exceeds `declared` — only
            // possible for an IMPORTED memory (a defined memory's active data
            // cannot exceed its own `initial`). The page-granular `declared`
            // stride would UNDER-reserve the visible data (the regression), so we
            // reserve at least `max_end`. Loud: an invisible arena ABOVE max_end
            // still can't be seen without a marker.
            log::warn!(
                "--pack-rebase: component {comp_idx} module {mod_idx} imports a memory whose \
                 declared minimum is {declared} bytes but has static data up to {max_end} and no \
                 immutable-const `__heap_base` marker; reserving {max_end} bytes (the visible \
                 extent) — any arena above it is invisible. Build the input with \
                 `-Wl,--export=__heap_base` to reserve the true static top."
            );
            Ok(Some(max_end))
        }
        None => {
            // `max_end <= declared`: the page-granular `declared` stride is a
            // sound reservation (>= max_end). Warn only when we are declining a
            // requested compaction (there is slack we cannot prove unused).
            if max_end < declared {
                // LOUD, never silent under-reserve (#370): the module declares
                // more memory than its visible static data and gives no
                // __heap_base marker, so its tail may hold a `.bss`/arena we
                // cannot see. Pack conservatively (page-granular) rather than
                // risk a collision SR-56 cannot catch.
                log::warn!(
                    "--pack-rebase: component {comp_idx} module {mod_idx} declares {declared} \
                     bytes of memory but only {max_end} are visible as static data, and it \
                     publishes no immutable-const `__heap_base` marker; packing to the declared \
                     page stride (no compaction) to avoid under-reserving a possible .bss/arena. \
                     Build the input with `-Wl,--export=__heap_base` to enable compaction."
                );
            }
            Ok(None)
        }
    }
}

/// Discover a module's `__heap_base` marker — the immutable-const linear-memory
/// address that is the top of its used static data (data + `.bss`). Returns the
/// address when a defined, immutable `i32` global named `__heap_base` (via the
/// export table or the `name` section) initialises to a single `i32.const`.
///
/// This is the ONLY signal that lets `--pack-rebase` compact below the declared
/// page count soundly (see [`module_used_data_extent`]). `__data_end` is
/// deliberately NOT accepted: in the default wasm-ld layout the shadow stack can
/// sit ABOVE `__data_end` (measured: `__data_end = 5136`, `__heap_base = 70672`,
/// a 64 KiB stack between), so packing to `__data_end` would under-reserve the
/// stack. `__heap_base` is the true top of static usage.
fn module_heap_base_marker(module: &CoreModule) -> Option<u64> {
    const MARKER: &str = "__heap_base";
    let import_globals = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Global(_)))
        .count() as u32;

    // Prefer the export table (what a supplier controls via --export=__heap_base
    // and what survives `wasm-tools component new`); fall back to the name
    // section's global-name subsection.
    let global_index = module
        .exports
        .iter()
        .find(|e| matches!(e.kind, ExportKind::Global) && e.name == MARKER)
        .map(|e| e.index)
        .or_else(|| module_named_global_index(module, MARKER))?;

    // Only a DEFINED global carries a readable initialiser (imported globals do
    // not). Must be an immutable `i32` initialised to a single `i32.const`.
    if global_index < import_globals {
        return None;
    }
    let defined = (global_index - import_globals) as usize;
    let g = module.globals.get(defined)?;
    if g.mutable || g.content_type != ValType::I32 {
        return None;
    }
    crate::segments::const_i32_init_value(&g.init_expr_bytes).map(|v| u64::from(v as u32))
}

/// Absolute index of the global named `name` in the module's `name` section
/// global-name subsection, if present.
fn module_named_global_index(module: &CoreModule, name: &str) -> Option<u32> {
    let (_, data) = module.custom_sections.iter().find(|(n, _)| n == "name")?;
    let reader = wasmparser::NameSectionReader::new(wasmparser::BinaryReader::new(data, 0));
    for subsection in reader {
        if let Ok(wasmparser::Name::Global(namemap)) = subsection {
            for naming in namemap {
                let Ok(naming) = naming else { continue };
                if naming.name == name {
                    return Some(naming.index);
                }
            }
        }
    }
    None
}

pub(crate) fn module_has_direct_memory_access(module: &CoreModule) -> Result<bool> {
    let Some((start, end)) = module.code_section_range else {
        return Ok(false);
    };
    let code_bytes = &module.bytes[start..end];
    let reader = wasmparser::CodeSectionReader::new(wasmparser::BinaryReader::new(code_bytes, 0))?;
    for body in reader {
        let body = body?;
        for op in body.get_operators_reader()? {
            if is_direct_memory_access(&op?) {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

/// True for the standard integer/float load & store operators (the ones that
/// carry a `memarg`). See [`module_has_direct_memory_access`].
fn is_direct_memory_access(op: &wasmparser::Operator<'_>) -> bool {
    use wasmparser::Operator::*;
    matches!(
        op,
        I32Load { .. }
            | I64Load { .. }
            | F32Load { .. }
            | F64Load { .. }
            | I32Load8S { .. }
            | I32Load8U { .. }
            | I32Load16S { .. }
            | I32Load16U { .. }
            | I64Load8S { .. }
            | I64Load8U { .. }
            | I64Load16S { .. }
            | I64Load16U { .. }
            | I64Load32S { .. }
            | I64Load32U { .. }
            | I32Store { .. }
            | I64Store { .. }
            | F32Store { .. }
            | F64Store { .. }
            | I32Store8 { .. }
            | I32Store16 { .. }
            | I64Store8 { .. }
            | I64Store16 { .. }
            | I64Store32 { .. }
    )
}
