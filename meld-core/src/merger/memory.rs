//! Shared/rebased memory planning, memory-type combination and conversion,
//! data-extent and heap-base analysis extracted from the merger.

use super::*;

#[derive(Debug, Clone)]
pub(crate) struct SharedMemoryPlan {
    pub(crate) memory: EncoderMemoryType,
    pub(crate) import: Option<(String, String)>,
    pub(crate) bases: HashMap<(usize, usize), u64>,
    /// SR-66 / #380: top of the single shared shadow-stack region under
    /// `--share-stack` (`max_i(sp_i)`). `None` when `--share-stack` is off.
    pub(crate) shared_stack_top: Option<u64>,
}

impl Merger {
    pub(crate) fn compute_shared_memory_plan(
        &self,
        components: &[ParsedComponent],
        graph: &DependencyGraph,
    ) -> Result<Option<SharedMemoryPlan>> {
        let mut memory_types = Vec::new();
        let mut import_names: Vec<(String, String)> = Vec::new();
        let mut has_defined = false;
        // (key, module memory type, used-data extent). The extent is
        // `Some(bytes)` only under `--pack-rebase` and only when every active
        // data segment has a constant offset; `None` means "cannot pack — fall
        // back to the declared page stride" (SR-57).
        let mut module_memories: Vec<((usize, usize), MemoryType, Option<u64>)> = Vec::new();
        // SR-66 / #380: per rebased module `(key, sp_i, extent_i)` for the
        // shared-stack layout. Only populated (and gated) under `--share-stack`.
        let mut share_entries: Vec<((usize, usize), u64, u64)> = Vec::new();

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
                        if self.share_stack {
                            share_entries
                                .push(self.share_stack_entry(module, extent, comp_idx, mod_idx)?);
                        }
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
        let mut shared_stack_top: Option<u64> = None;
        // 16-byte alignment keeps `v128` accesses aligned after the uniform
        // `+base` shift (shared by the pack and share-stack strides below).
        const PACK_ALIGN: u64 = 16;
        let overflow =
            || Error::MemoryStrategyUnsupported("shared memory size overflow".to_string());

        if self.address_rebasing && self.share_stack {
            // SR-66 / #380: ONE shadow-stack region of `max_i(sp_i)` at fused
            // base 0; each provider's data (which begins at `sp_i` under the
            // stack-first gate enforced in `share_stack_entry`) packs directly
            // above it. `base_i = align16(max sp) - sp_i` (a uniform shift, so
            // the rewriter is untouched); `stride = align16(extent_i - sp_i)`.
            let s_raw = share_entries
                .iter()
                .map(|&(_, sp, _)| sp)
                .max()
                .unwrap_or(0);
            // `next_base` starts at the top of the shared stack region and only
            // grows, so `next_base >= s_raw >= sp_i` for every provider — the
            // `base_i` and `extent_i - sp_i` subtractions below never underflow.
            let mut next_base = s_raw
                .checked_next_multiple_of(PACK_ALIGN)
                .ok_or_else(overflow)?;
            for &(key, sp, extent) in &share_entries {
                let base = next_base - sp;
                if !combined.memory64 && base > u64::from(u32::MAX) {
                    return Err(Error::MemoryStrategyUnsupported(
                        "shared memory base offset exceeds 32-bit address space".to_string(),
                    ));
                }
                bases.insert(key, base);
                let stride = (extent - sp)
                    .checked_next_multiple_of(PACK_ALIGN)
                    .ok_or_else(overflow)?;
                next_base = next_base.checked_add(stride).ok_or_else(overflow)?;
            }
            combined.initial = next_base.div_ceil(WASM_PAGE_SIZE).max(1);
            if let Some(max) = combined.maximum {
                combined.maximum = Some(max.max(combined.initial));
            }
            shared_stack_top = Some(s_raw);

            // SR-67 / #382: the shared region is sized `max_i(sp_i)`, sound only
            // while at most one provider's stack is live. Check the fused-set
            // call graph and refuse a cycle (unbounded live stack); warn on a DAG
            // whose worst call chain exceeds the region.
            self.check_share_stack_call_topology(graph, components, &share_entries, s_raw)?;
        } else if self.address_rebasing {
            // Byte-granular running base. Under the default page-granular
            // strategy each module strides by its declared page count; under
            // `--pack-rebase` it strides by its 16-byte-aligned used data
            // extent (SR-57).
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
            shared_stack_top,
        }))
    }

    /// SR-66 / #380: validate one rebased module for `--share-stack` and return
    /// its `(key, sp_i, extent_i)`. Hard-fails (loud, never silent) when the
    /// shared-stack preconditions do not hold — an opt-in flag must refuse a
    /// layout it cannot make sound rather than silently fall back:
    ///   * the module cannot be compacted (`extent` is `None` — no `__heap_base`
    ///     marker, or a passive/no-data region the extent scan can't see);
    ///   * it carries no `__stack_pointer` marker (mutable `i32`, const init);
    ///   * it is not stack-first (an active data segment starts BELOW `sp_i`, so
    ///     subtracting the `[0, sp)` stack region would cut into data);
    ///   * `sp_i > extent_i` (the stack claims to sit above the used top).
    fn share_stack_entry(
        &self,
        module: &CoreModule,
        extent: Option<u64>,
        comp_idx: usize,
        mod_idx: usize,
    ) -> Result<((usize, usize), u64, u64)> {
        let extent = extent.ok_or_else(|| {
            Error::MemoryStrategyUnsupported(format!(
                "--share-stack: component {comp_idx} module {mod_idx} cannot be compacted \
                 (no immutable-const `__heap_base` marker, or a passive/no-data region the \
                 extent scan cannot measure); shared-stack packing requires a packable extent. \
                 Build the input with `-Wl,--export=__heap_base`."
            ))
        })?;
        let sp = module_stack_pointer_marker(module).ok_or_else(|| {
            Error::MemoryStrategyUnsupported(format!(
                "--share-stack: component {comp_idx} module {mod_idx} has no `__stack_pointer` \
                 marker (a mutable `i32` global with a single `i32.const` init, named in the \
                 export table or `name` section); cannot place a shared shadow stack it cannot \
                 locate."
            ))
        })?;
        if sp > extent {
            return Err(Error::MemoryStrategyUnsupported(format!(
                "--share-stack: component {comp_idx} module {mod_idx} `__stack_pointer` ({sp}) \
                 sits above its used-memory top `__heap_base` ({extent}); expected a stack-first \
                 layout with the stack below the data."
            )));
        }
        // Bulk-op / no-reloc soundness (Mythos SR-66 delta-pass): under
        // `--share-stack` the shared stack is left UN-rebased at `[0, s_raw)` and
        // the coalesced SP is rewritten to the absolute top, so an sp-derived
        // runtime address must NOT be shifted. But the legacy no-reloc rebasing
        // path (`rewriter::append_rebased_address`) adds `base_i` to EVERY
        // bulk-memory op's runtime address operand — correct for a data-derived
        // operand, WRONG for an sp-derived one (it lands `base_i` bytes off, into
        // a neighbour's window; runtime-confirmed). A reloc-covered provider
        // skips that path entirely (data addresses rebase at their source,
        // sp-derived operands are left alone), so it is sound. Direct load/store
        // without relocs is already rejected upstream (#326 path-F), but the
        // bulk-only case is exempt there — gate it here. `has_reloc_metadata` is
        // the exact signal `resolve_address_plan` uses to populate
        // `code_addr_relocs`, so this cannot drift from the rewriter.
        if module_has_bulk_memory_op(module)?
            && !crate::reloc::has_reloc_metadata(&module.custom_sections)
        {
            return Err(Error::MemoryStrategyUnsupported(format!(
                "--share-stack: component {comp_idx} module {mod_idx} uses a bulk-memory op \
                 (memory.copy/fill/init) but carries no reloc metadata; a stack-derived bulk-op \
                 address would be silently mis-rebased under the shared stack (shifted by the \
                 module base). Rebuild with `--emit-relocs` so meld rebases data addresses at \
                 their source and leaves stack-derived operands alone."
            )));
        }

        // Stack-first gate: every active data segment must start AT OR ABOVE the
        // stack pointer. A constant-offset scan suffices — a non-constant or
        // passive segment already forced `extent` to `None` above (rejected).
        for seg in &crate::segments::parse_data_segments(module)? {
            if let crate::segments::DataSegmentMode_::Active {
                offset_value: Some(off),
                ..
            } = &seg.mode
            {
                let start = match off {
                    crate::segments::ConstExprValue::I32(v) => u64::from(*v as u32),
                    crate::segments::ConstExprValue::I64(v) => *v as u64,
                };
                if start < sp {
                    return Err(Error::MemoryStrategyUnsupported(format!(
                        "--share-stack: component {comp_idx} module {mod_idx} has an active data \
                         segment at {start}, below its `__stack_pointer` ({sp}) — not a \
                         stack-first layout. Rebuild with `-Wl,--stack-first` so the shadow \
                         stack sits below the data."
                    )));
                }
            }
        }
        Ok(((comp_idx, mod_idx), sp, extent))
    }

    /// SR-67 / #382: the `--share-stack` call-topology envelope check. The shared
    /// region is `max_i(sp_i)`, sound only while at most one stack is live at a
    /// time. But the region is per-MODULE, not per-component:
    /// `mcu_dissolve::coalesce_stack_pointers` collapses EVERY `__stack_pointer`
    /// across all components AND modules onto one survivor, so every module's
    /// stack lives in the single `[0, s_raw)` region. A call from one
    /// memory-bearing module into another (whether cross-component or
    /// intra-component cross-module) chains their `sp`s in that region.
    ///
    /// Nodes are therefore `(component, module)` and edges are cross-module
    /// function calls from two sources (Mythos SR-67 delta-pass, Finding 1):
    ///   - `graph.adapter_sites` — every internalized cross-component call, plus
    ///     intra-component encoding-differing calls (both carry distinct
    ///     `(from_module, to_module)`);
    ///   - function-kind `graph.module_resolutions` — intra-component cross-module
    ///     calls that never become adapter sites (under `SharedMemory` only an
    ///     encoding difference makes one, so plain cross-module calls stay here).
    ///
    /// Resource-op and async-lift calls count too (they still execute callee code
    /// on the shared stack). Over-approximating yields a false warn/refuse at
    /// worst, never a silent under-reservation.
    ///
    /// Verdict (via [`analyze_call_topology`], weighting each node by its `sp`):
    ///   - no cross-module edges → sound; proceed silently.
    ///   - acyclic DAG, worst root-to-leaf `sp`-sum > region → `log::warn!`.
    ///   - a call cycle → unbounded live stack → hard-fail.
    ///
    /// KNOWN GAP (Finding 3, unconfirmed): a standalone resource-DESTRUCTOR
    /// invocation (drop of an owned handle → the defining component's dtor) that
    /// is routed through handle tables rather than an adapter site would not
    /// appear here. Narrow for the scalar MCU driver shape `--share-stack`
    /// targets (no resources); documented rather than claimed-covered.
    fn check_share_stack_call_topology(
        &self,
        graph: &DependencyGraph,
        components: &[ParsedComponent],
        share_entries: &[((usize, usize), u64, u64)],
        region: u64,
    ) -> Result<()> {
        // No shared region to protect (defensive — Finding 2). Unreachable via
        // the plan (a non-empty memory set always yields entries), but explicit.
        if share_entries.is_empty() {
            return Ok(());
        }

        // Intern `(component, module)` keys to dense ids so the pure analysis
        // stays integer-keyed; `label` maps back for diagnostics.
        let mut id_of: HashMap<(usize, usize), usize> = HashMap::new();
        let mut label: Vec<(usize, usize)> = Vec::new();
        let mut intern = |key: (usize, usize)| -> usize {
            *id_of.entry(key).or_insert_with(|| {
                label.push(key);
                label.len() - 1
            })
        };

        // Per-module stack weight.
        let mut sp: HashMap<usize, u64> = HashMap::new();
        for &(key, weight, _) in share_entries {
            let id = intern(key);
            sp.insert(id, weight);
        }

        // Cross-module call edges from both sources (exclude same-module).
        let mut edges: Vec<(usize, usize)> = Vec::new();
        for site in &graph.adapter_sites {
            let from = (site.from_component, site.from_module);
            let to = (site.to_component, site.to_module);
            if from != to {
                edges.push((intern(from), intern(to)));
            }
        }
        for res in &graph.module_resolutions {
            if res.from_module == res.to_module {
                continue;
            }
            // FUNCTION-kind only: a memory/global/table wiring is not a call.
            let is_call = components
                .get(res.component_idx)
                .and_then(|c| c.core_modules.get(res.to_module))
                .is_some_and(|m| {
                    m.exports.iter().any(|e| {
                        e.name == res.export_name && matches!(e.kind, ExportKind::Function)
                    })
                });
            if is_call {
                let from = (res.component_idx, res.from_module);
                let to = (res.component_idx, res.to_module);
                edges.push((intern(from), intern(to)));
            }
        }

        let describe =
            |ids: &[usize]| -> Vec<(usize, usize)> { ids.iter().map(|&id| label[id]).collect() };

        match analyze_call_topology(&edges, &sp) {
            CallTopology::NoEdges => Ok(()),
            CallTopology::Acyclic {
                worst_sum,
                worst_path,
            } => {
                if worst_sum > region {
                    let chain = describe(&worst_path);
                    log::warn!(
                        "--share-stack: the fused set is not mutually-non-calling — the \
                         (component, module) call chain {chain:?} needs up to {worst_sum} bytes of \
                         shadow stack (the sum along the chain), but the shared region is sized \
                         {region} bytes (the largest single module). At most one module's stack is \
                         assumed live at a time; a live caller+callee needs their sum. Sound only \
                         if the chain's true peak fits {region} — verify against your per-stage \
                         stack bounds (e.g. a scry static bound). If it does not, do not use \
                         --share-stack for this composition."
                    );
                }
                Ok(())
            }
            CallTopology::Cyclic { cycle } => {
                let chain = describe(&cycle);
                Err(Error::MemoryStrategyUnsupported(format!(
                    "--share-stack: the fused set contains a (component, module) call CYCLE \
                     {chain:?} — the live shadow-stack depth is unbounded, so a single region \
                     sized to the largest module cannot be sound. --share-stack requires a \
                     non-recursive, one-live-at-a-time composition; remove the cycle or drop \
                     --share-stack."
                )))
            }
        }
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
    // `__heap_base` is IMMUTABLE (the top of static data never moves).
    module_marker_global(module, "__heap_base", false)
}

/// Discover a module's `__stack_pointer` marker — the MUTABLE `i32` linear-memory
/// address the shadow stack descends from (SR-66 / #380). Returns the init value
/// when a defined, mutable `i32` global named `__stack_pointer` (via the export
/// table or the `name` section) initialises to a single `i32.const`.
///
/// Same lookup as [`module_heap_base_marker`] but requires MUTABLE (a stack
/// pointer is written at runtime; an immutable global cannot be one). Kept
/// consistent with `mcu_dissolve::coalesce_stack_pointers`, which reads the same
/// name-section signal — the plan gate and the coalescer must agree on which
/// globals are stack pointers, or one could pass while the other declines and
/// leave two SPs over one shared region.
fn module_stack_pointer_marker(module: &CoreModule) -> Option<u64> {
    module_marker_global(module, "__stack_pointer", true)
}

/// Shared marker lookup: the init value of a DEFINED `i32` global named `name`
/// (export table preferred — what `-Wl,--export=<name>` controls and what
/// survives `wasm-tools component new` — then the `name` section fallback), whose
/// mutability matches `want_mutable` and whose init is a single `i32.const`.
fn module_marker_global(module: &CoreModule, name: &str, want_mutable: bool) -> Option<u64> {
    let import_globals = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Global(_)))
        .count() as u32;

    let global_index = module
        .exports
        .iter()
        .find(|e| matches!(e.kind, ExportKind::Global) && e.name == name)
        .map(|e| e.index)
        .or_else(|| module_named_global_index(module, name))?;

    // Only a DEFINED global carries a readable initialiser (imported globals do
    // not).
    if global_index < import_globals {
        return None;
    }
    let defined = (global_index - import_globals) as usize;
    let g = module.globals.get(defined)?;
    if g.mutable != want_mutable || g.content_type != ValType::I32 {
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

/// True if the module contains any bulk-memory operator (`memory.copy`,
/// `memory.fill`, `memory.init`) whose runtime address operand the legacy
/// no-reloc rebasing path (`rewriter::append_rebased_address`) would shift by
/// `+base_i`. Used by the `--share-stack` gate (SR-66): such a shift is wrong for
/// an sp-derived operand under the shared un-rebased stack, so a bulk-op provider
/// must be reloc-covered (which skips that path) to be sound.
fn module_has_bulk_memory_op(module: &CoreModule) -> Result<bool> {
    let Some((start, end)) = module.code_section_range else {
        return Ok(false);
    };
    let code_bytes = &module.bytes[start..end];
    let reader = wasmparser::CodeSectionReader::new(wasmparser::BinaryReader::new(code_bytes, 0))?;
    for body in reader {
        let body = body?;
        for op in body.get_operators_reader()? {
            if matches!(
                op?,
                wasmparser::Operator::MemoryCopy { .. }
                    | wasmparser::Operator::MemoryFill { .. }
                    | wasmparser::Operator::MemoryInit { .. }
            ) {
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

/// SR-67 / #382: verdict of the fused-set call-topology analysis for
/// `--share-stack`. The shared shadow-stack region is sized `max_i(sp_i)`, which
/// is sound only when at most one provider's stack is live at a time. A
/// cross-component call makes a caller live while its callee runs, so the live
/// requirement becomes the sum of stacks along the call chain.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum CallTopology {
    /// No cross-component call edges — mutually-non-calling; `max_i(sp_i)` is
    /// sound. The current gale (F100) shape. Pass silently.
    NoEdges,
    /// Acyclic call graph (an orchestrator DAG). `worst_sum` is the maximum
    /// root-to-leaf sum of `sp` along any path and `worst_path` the component
    /// indices on it. The caller warns only when `worst_sum` exceeds the region
    /// (the region may be undersized, but boundedly so).
    Acyclic {
        worst_sum: u64,
        worst_path: Vec<usize>,
    },
    /// A call cycle (A→…→A, or recursion through a sibling) — the live stack is
    /// unbounded. The caller hard-fails.
    Cyclic { cycle: Vec<usize> },
}

/// Analyse the fused-set cross-component call graph for the `--share-stack`
/// envelope (SR-67 / #382). Nodes are component indices; `edges` are
/// `(from_component, to_component)` function-call edges (self-edges excluded by
/// the caller). `sp` maps a component to its shadow-stack size (node weight).
///
/// Pure and deterministic (sorted iteration) so the graph logic — cycle
/// detection and longest weighted path — is unit-testable and Mythos-checkable
/// independently of the fusion pipeline.
pub(crate) fn analyze_call_topology(
    edges: &[(usize, usize)],
    sp: &HashMap<usize, u64>,
) -> CallTopology {
    use std::collections::{BTreeMap, BTreeSet};

    if edges.is_empty() {
        return CallTopology::NoEdges;
    }

    // Deterministic adjacency (sorted, deduped successors) + node set.
    let mut adj: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut nodes: BTreeSet<usize> = BTreeSet::new();
    for &(f, t) in edges {
        nodes.insert(f);
        nodes.insert(t);
        adj.entry(f).or_default().push(t);
    }
    for succ in adj.values_mut() {
        succ.sort_unstable();
        succ.dedup();
    }

    // Iterative DFS with colours (0 = white, 1 = gray/on-path, 2 = black/done).
    // A back edge to a gray node is a cycle; capture it from `path`. Finish
    // order accumulates into `topo` (= reverse topological order).
    let mut colour: BTreeMap<usize, u8> = nodes.iter().map(|&n| (n, 0u8)).collect();
    let mut topo: Vec<usize> = Vec::new();
    for &start in &nodes {
        if colour[&start] != 0 {
            continue;
        }
        *colour.get_mut(&start).unwrap() = 1;
        let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
        let mut path: Vec<usize> = vec![start];
        while let Some(&(node, idx)) = stack.last() {
            let next = adj.get(&node).and_then(|s| s.get(idx).copied());
            match next {
                Some(n) => {
                    stack.last_mut().unwrap().1 += 1;
                    match colour[&n] {
                        0 => {
                            *colour.get_mut(&n).unwrap() = 1;
                            stack.push((n, 0));
                            path.push(n);
                        }
                        1 => {
                            let pos = path.iter().position(|&x| x == n).unwrap();
                            return CallTopology::Cyclic {
                                cycle: path[pos..].to_vec(),
                            };
                        }
                        _ => {}
                    }
                }
                None => {
                    *colour.get_mut(&node).unwrap() = 2;
                    topo.push(node);
                    path.pop();
                    stack.pop();
                }
            }
        }
    }

    // Longest weighted path over the DAG. `topo` is in finish order, so every
    // node's successors (which finish earlier) are already resolved when we
    // reach it. `best[n]` = heaviest sp-sum of a path starting at `n`.
    let mut best: BTreeMap<usize, u64> = BTreeMap::new();
    let mut nexthop: BTreeMap<usize, Option<usize>> = BTreeMap::new();
    for &node in &topo {
        let w = *sp.get(&node).unwrap_or(&0);
        let mut bsum = w;
        let mut bnext = None;
        if let Some(succs) = adj.get(&node) {
            for &s in succs {
                let cand = w.saturating_add(best[&s]);
                if cand > bsum {
                    bsum = cand;
                    bnext = Some(s);
                }
            }
        }
        best.insert(node, bsum);
        nexthop.insert(node, bnext);
    }

    // Worst path = argmax over nodes of `best`; reconstruct via `nexthop`.
    // Ties break to the lowest index (BTreeMap order) for determinism.
    let start = best
        .iter()
        .max_by(|a, b| a.1.cmp(b.1).then(b.0.cmp(a.0)))
        .map(|(&n, _)| n)
        .unwrap();
    let mut worst_path = vec![start];
    let mut cur = start;
    while let Some(&Some(n)) = nexthop.get(&cur) {
        worst_path.push(n);
        cur = n;
    }
    CallTopology::Acyclic {
        worst_sum: best[&start],
        worst_path,
    }
}

#[cfg(test)]
mod topology_tests {
    use super::{CallTopology, analyze_call_topology};
    use std::collections::HashMap;

    fn sp(pairs: &[(usize, u64)]) -> HashMap<usize, u64> {
        pairs.iter().copied().collect()
    }

    #[test]
    fn no_edges_is_mutually_non_calling() {
        assert_eq!(
            analyze_call_topology(&[], &sp(&[(0, 100), (1, 200)])),
            CallTopology::NoEdges
        );
    }

    #[test]
    fn chain_sums_along_the_path() {
        // 0 -> 1 -> 2, sp 10/20/30 => worst path 0,1,2 sum 60.
        let v = analyze_call_topology(&[(0, 1), (1, 2)], &sp(&[(0, 10), (1, 20), (2, 30)]));
        assert_eq!(
            v,
            CallTopology::Acyclic {
                worst_sum: 60,
                worst_path: vec![0, 1, 2]
            }
        );
    }

    #[test]
    fn fanout_takes_the_heavier_branch() {
        // 0 -> 1, 0 -> 2, sp 10/5/40 => 0,2 = 50 (heavier than 0,1 = 15).
        let v = analyze_call_topology(&[(0, 1), (0, 2)], &sp(&[(0, 10), (1, 5), (2, 40)]));
        assert_eq!(
            v,
            CallTopology::Acyclic {
                worst_sum: 50,
                worst_path: vec![0, 2]
            }
        );
    }

    #[test]
    fn diamond_takes_the_longest_route() {
        // 0->1, 0->2, 1->3, 2->3, sp 1/10/2/100 => 0,1,3 = 111 vs 0,2,3 = 103.
        let v = analyze_call_topology(
            &[(0, 1), (0, 2), (1, 3), (2, 3)],
            &sp(&[(0, 1), (1, 10), (2, 2), (3, 100)]),
        );
        assert_eq!(
            v,
            CallTopology::Acyclic {
                worst_sum: 111,
                worst_path: vec![0, 1, 3]
            }
        );
    }

    #[test]
    fn two_cycle_is_cyclic() {
        match analyze_call_topology(&[(0, 1), (1, 0)], &sp(&[(0, 10), (1, 20)])) {
            CallTopology::Cyclic { cycle } => {
                assert!(cycle.contains(&0) && cycle.contains(&1), "cycle: {cycle:?}");
            }
            other => panic!("expected Cyclic, got {other:?}"),
        }
    }

    #[test]
    fn cycle_beats_dag_when_both_present() {
        // 0->1->2->1 : the 1<->2 back edge is a cycle even though 0->1 is a DAG edge.
        match analyze_call_topology(&[(0, 1), (1, 2), (2, 1)], &sp(&[(0, 1), (1, 1), (2, 1)])) {
            CallTopology::Cyclic { cycle } => {
                assert!(cycle.contains(&1) && cycle.contains(&2), "cycle: {cycle:?}");
            }
            other => panic!("expected Cyclic, got {other:?}"),
        }
    }

    #[test]
    fn self_referential_weight_of_isolated_max_still_bounds() {
        // Edges only among small nodes; the single heavy node is isolated, so
        // the worst path (2->3 = 6) is far below it — the caller compares to the
        // region and would NOT warn. Confirms worst_sum reflects paths, not the
        // global max node.
        let v = analyze_call_topology(&[(2, 3)], &sp(&[(2, 2), (3, 4)]));
        assert_eq!(
            v,
            CallTopology::Acyclic {
                worst_sum: 6,
                worst_path: vec![2, 3]
            }
        );
    }

    // --- method-level: graph.adapter_sites -> verdict -> action (SR-67 gate) ---

    use crate::MemoryStrategy;
    use crate::merger::Merger;
    use crate::resolver::{AdapterRequirements, AdapterSite, DependencyGraph};

    /// A `((from_component, from_module), (to_component, to_module))` call edge.
    type ModEdge = ((usize, usize), (usize, usize));

    fn site_mod(fc: usize, fm: usize, tc: usize, tm: usize) -> AdapterSite {
        AdapterSite {
            from_component: fc,
            from_module: fm,
            import_name: "f".into(),
            import_module: "m".into(),
            import_func_type_idx: None,
            to_component: tc,
            to_module: tm,
            export_name: "f".into(),
            export_func_idx: 0,
            crosses_memory: false,
            is_async_lift: false,
            requirements: AdapterRequirements::default(),
        }
    }

    /// Component-level edges (module 0 on both sides).
    fn graph(edges: &[(usize, usize)]) -> DependencyGraph {
        graph_sites(edges.iter().map(|&(f, t)| site_mod(f, 0, t, 0)).collect())
    }

    /// `(component, module)` edges.
    fn graph_mods(edges: &[ModEdge]) -> DependencyGraph {
        graph_sites(
            edges
                .iter()
                .map(|&((fc, fm), (tc, tm))| site_mod(fc, fm, tc, tm))
                .collect(),
        )
    }

    fn graph_sites(adapter_sites: Vec<AdapterSite>) -> DependencyGraph {
        DependencyGraph {
            instantiation_order: Vec::new(),
            resolved_imports: HashMap::new(),
            unresolved_imports: Vec::new(),
            adapter_sites,
            resource_graph: None,
            stream_pair_graph: None,
            module_resolutions: Vec::new(),
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
        }
    }

    fn share_merger() -> Merger {
        Merger::new(MemoryStrategy::SharedMemory, true)
            .with_pack_rebase(true)
            .with_share_stack(true)
    }

    // share_entries: two providers, comp 0 sp=100, comp 1 sp=50.
    fn entries() -> Vec<((usize, usize), u64, u64)> {
        vec![((0, 0), 100, 200), ((1, 0), 50, 100)]
    }

    #[test]
    fn gate_passes_with_no_cross_component_calls() {
        // gale shape: no adapter sites -> mutually-non-calling -> Ok.
        let m = share_merger();
        assert!(
            m.check_share_stack_call_topology(&graph(&[]), &[], &entries(), 100)
                .is_ok()
        );
    }

    #[test]
    fn gate_ignores_intra_component_self_edges() {
        // from == to is an intra-component promotion, not a sibling call.
        let m = share_merger();
        assert!(
            m.check_share_stack_call_topology(&graph(&[(0, 0), (1, 1)]), &[], &entries(), 100)
                .is_ok()
        );
    }

    #[test]
    fn gate_hard_fails_on_a_call_cycle() {
        // 0 -> 1 -> 0 : unbounded live stack -> refuse.
        let m = share_merger();
        let err = m
            .check_share_stack_call_topology(&graph(&[(0, 1), (1, 0)]), &[], &entries(), 100)
            .expect_err("a call cycle must be refused");
        let msg = err.to_string();
        assert!(
            msg.contains("cycle") || msg.contains("CYCLE"),
            "error must name the cycle: {msg}"
        );
    }

    #[test]
    fn gate_allows_a_dag_that_fits_the_region() {
        // 0 -> 1, sum 150, region 200 -> fits -> Ok, silent.
        let m = share_merger();
        assert!(
            m.check_share_stack_call_topology(&graph(&[(0, 1)]), &[], &entries(), 200)
                .is_ok()
        );
    }

    #[test]
    fn gate_warns_but_allows_a_dag_that_exceeds_the_region() {
        // 0 -> 1, sum 150, region 100 -> exceeds -> warn, still Ok (bounded).
        let m = share_merger();
        assert!(
            m.check_share_stack_call_topology(&graph(&[(0, 1)]), &[], &entries(), 100)
                .is_ok()
        );
    }

    // share_entries for a SINGLE component with TWO memory-bearing modules.
    fn multimodule_entries() -> Vec<((usize, usize), u64, u64)> {
        vec![((0, 0), 100, 200), ((0, 1), 80, 160)]
    }

    #[test]
    fn gate_catches_intra_component_cross_module_cycle() {
        // Mythos SR-67 Finding 1: the shared stack is per-MODULE, so two modules
        // in ONE component that call each other (comp0/mod0 <-> comp0/mod1) form
        // a cycle in the shared region. The old per-component gate dropped these
        // as `from == to` self-edges and passed silently; per-module nodes catch
        // it. (A cycle asserts detection unambiguously via the Err.)
        let m = share_merger();
        let g = graph_mods(&[((0, 0), (0, 1)), ((0, 1), (0, 0))]);
        let err = m
            .check_share_stack_call_topology(&g, &[], &multimodule_entries(), 100)
            .expect_err("an intra-component cross-module call cycle must be refused");
        assert!(
            err.to_string().contains("CYCLE"),
            "error must name the cycle: {err}"
        );
    }

    #[test]
    fn gate_warns_on_intra_component_cross_module_dag_over_region() {
        // comp0/mod0 -> comp0/mod1, sp 100 + 80 = 180 > region 100 -> warn, Ok.
        // The old per-component gate saw a self-edge, dropped it, and was silent.
        let m = share_merger();
        let g = graph_mods(&[((0, 0), (0, 1))]);
        assert!(
            m.check_share_stack_call_topology(&g, &[], &multimodule_entries(), 100)
                .is_ok()
        );
    }
}
