//! The per-core-module merge pass and duplicate-instantiation guard,
//! the largest slice of the merger's `impl Merger` block.

use super::*;

impl Merger {
    /// Check that no component instantiates the same core module more than once.
    ///
    /// The merger's index-space merging model assumes each module index appears
    /// at most once in the instantiation order. Multiply-instantiated modules
    /// would produce duplicate function/memory/table entries with conflicting
    /// index offsets, causing silent data corruption (LS-M-5, SR-31).
    pub(crate) fn check_no_duplicate_instantiations(components: &[ParsedComponent]) -> Result<()> {
        for (comp_idx, component) in components.iter().enumerate() {
            let mut seen_modules = std::collections::HashSet::new();
            for instance in &component.instances {
                if let crate::parser::InstanceKind::Instantiate { module_idx, .. } = &instance.kind
                {
                    if !seen_modules.insert(*module_idx) {
                        return Err(Error::DuplicateModuleInstantiation {
                            component_idx: comp_idx,
                            module_idx: *module_idx,
                        });
                    }
                }
            }
        }
        Ok(())
    }

    /// Merge a single core module
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn merge_core_module(
        &self,
        comp_idx: usize,
        mod_idx: usize,
        module: &CoreModule,
        components: &[ParsedComponent],
        graph: &DependencyGraph,
        merged: &mut MergedModule,
        shared_memory_plan: Option<&SharedMemoryPlan>,
        unresolved_assignments: &UnresolvedImportAssignments,
    ) -> Result<()> {
        // Merge types.
        //
        // Two passes: first record every type's old->merged index mapping, then
        // build the merged types. The split is required because a func type's
        // param/result may be a concrete typed-ref `(ref $t)` whose index `t`
        // can forward-reference another type in this same module; remapping it
        // needs the *complete* mapping for the module to already be in place.
        let type_offset = merged.types.len() as u32;
        for (old_idx, _ty) in module.types.iter().enumerate() {
            merged.type_index_map.insert(
                (comp_idx, mod_idx, old_idx as u32),
                type_offset + old_idx as u32,
            );
        }
        for ty in module.types.iter() {
            merged.types.push(MergedFuncType {
                params: ty
                    .params
                    .iter()
                    .map(|&p| remap_concrete_val_type(p, comp_idx, mod_idx, merged))
                    .collect(),
                results: ty
                    .results
                    .iter()
                    .map(|&r| remap_concrete_val_type(r, comp_idx, mod_idx, merged))
                    .collect(),
            });
        }

        // Track import counts for index calculations
        let mut import_func_count = 0u32;
        let mut import_table_count = 0u32;
        let mut import_mem_count = 0u32;
        let mut import_global_count = 0u32;

        // Count imports (they contribute to index space)
        for import in &module.imports {
            match &import.kind {
                ImportKind::Function(_) => import_func_count += 1,
                ImportKind::Table(_) => import_table_count += 1,
                ImportKind::Memory(_) => import_mem_count += 1,
                ImportKind::Global(_) => import_global_count += 1,
            }
        }

        // Merge memories
        if self.memory_strategy == MemoryStrategy::SharedMemory {
            let total_memories = import_mem_count + module.memories.len() as u32;
            for idx in 0..total_memories {
                merged.memory_index_map.insert((comp_idx, mod_idx, idx), 0);
            }
        } else {
            // Multi-memory: each component keeps its own memory.
            // Both imported and defined memories get unique indices.
            let mem_offset = merged.memories.len() as u32;
            let mut next_idx = 0u32;

            // Track which imported memory indices get resolved via module_resolutions
            // so we can skip creating standalone memories for them.
            let mut resolved_import_mem_indices: HashSet<u32> = HashSet::new();

            // Pre-scan: identify imported memories that are resolved via
            // module_resolutions (e.g., Module 1 imports memory from Module 0).
            {
                let mut scan_mem_idx = 0u32;
                for imp in &module.imports {
                    if !matches!(imp.kind, ImportKind::Memory(_)) {
                        continue;
                    }
                    let intra = graph.module_resolutions.iter().find(|res| {
                        res.component_idx == comp_idx
                            && res.from_module == mod_idx
                            && imp.name == res.import_name
                            && (res.from_import_module.is_empty()
                                || res.from_import_module == imp.module)
                    });
                    if let Some(res) = intra {
                        let target_module =
                            &components[res.component_idx].core_modules[res.to_module];
                        if let Some(export) = target_module
                            .exports
                            .iter()
                            .find(|e| e.name == res.export_name && e.kind == ExportKind::Memory)
                        {
                            if let Some(&target_idx) = merged.memory_index_map.get(&(
                                res.component_idx,
                                res.to_module,
                                export.index,
                            )) {
                                // Map this imported memory to the target module's memory
                                merged
                                    .memory_index_map
                                    .insert((comp_idx, mod_idx, scan_mem_idx), target_idx);
                                resolved_import_mem_indices.insert(scan_mem_idx);
                            }
                        }
                    }
                    scan_mem_idx += 1;
                }
            }

            // Imported memories — only create new memories for unresolved ones
            let mut import_mem_local_idx = 0u32;
            for import in &module.imports {
                if let ImportKind::Memory(mem) = &import.kind {
                    if !resolved_import_mem_indices.contains(&import_mem_local_idx) {
                        let new_idx = mem_offset + next_idx;
                        merged
                            .memory_index_map
                            .insert((comp_idx, mod_idx, import_mem_local_idx), new_idx);
                        merged.memories.push(convert_memory_type(mem));
                        next_idx += 1;
                    }
                    import_mem_local_idx += 1;
                }
            }

            // Defined memories
            for (old_idx, mem) in module.memories.iter().enumerate() {
                let new_idx = mem_offset + next_idx + old_idx as u32;
                merged.memory_index_map.insert(
                    (comp_idx, mod_idx, import_mem_count + old_idx as u32),
                    new_idx,
                );
                merged.memories.push(convert_memory_type(mem));
            }
        }

        // Merge tables (defined tables only; imported tables handled below)
        let table_offset = merged.tables.len() as u32;
        for (old_idx, table) in module.tables.iter().enumerate() {
            let old_table_idx = import_table_count + old_idx as u32;
            let new_idx = merged.import_counts.table + table_offset + old_idx as u32;
            log::debug!(
                "table defined: ({},{},{}) → {} (offset={}, import_count={})",
                comp_idx,
                mod_idx,
                old_table_idx,
                new_idx,
                table_offset,
                merged.import_counts.table,
            );
            merged
                .table_index_map
                .insert((comp_idx, mod_idx, old_table_idx), new_idx);
            merged
                .tables
                .push(convert_table_type(table, comp_idx, mod_idx, merged));
        }

        // Resolve imported global indices via intra-component module_resolutions.
        // This mirrors how function imports are resolved below: if module A
        // imports a global that module B exports, map A's imported global index
        // to B's defined global's merged index.
        //
        // This MUST run before converting THIS module's defined-global init
        // exprs below: an extended-const initializer may reference an imported
        // global (`i32.const N; global.get $__memory_base; i32.add`, #338), and
        // `convert_init_expr` remaps that global through `global_index_map`. If
        // the imported-global entries were populated only afterwards (the prior
        // ordering), the remap silently missed and emitted the un-remapped local
        // index — reading the wrong global whenever fusion shifted the import
        // off index 0.
        {
            let mut import_global_idx = 0u32;
            for imp in &module.imports {
                if !matches!(imp.kind, ImportKind::Global(_)) {
                    continue;
                }

                // Intra-component: check module_resolutions
                let intra = graph.module_resolutions.iter().find(|res| {
                    res.component_idx == comp_idx
                        && res.from_module == mod_idx
                        && imp.name == res.import_name
                        && (res.from_import_module.is_empty()
                            || res.from_import_module == imp.module)
                });
                if let Some(res) = intra {
                    let target_module = &components[res.component_idx].core_modules[res.to_module];
                    if let Some(export) = target_module
                        .exports
                        .iter()
                        .find(|e| e.name == res.export_name && e.kind == ExportKind::Global)
                    {
                        if let Some(&target_idx) = merged.global_index_map.get(&(
                            res.component_idx,
                            res.to_module,
                            export.index,
                        )) {
                            merged
                                .global_index_map
                                .insert((comp_idx, mod_idx, import_global_idx), target_idx);
                        }
                    }
                }

                // Map unresolved global imports to their merged import index
                if let std::collections::hash_map::Entry::Vacant(e) = merged
                    .global_index_map
                    .entry((comp_idx, mod_idx, import_global_idx))
                {
                    if let Some(&import_index) = unresolved_assignments.global.get(&(
                        comp_idx,
                        mod_idx,
                        imp.module.clone(),
                        imp.name.clone(),
                    )) {
                        e.insert(import_index);
                    }
                }

                import_global_idx += 1;
            }
        }

        // Merge globals (defined globals only; imported globals handled above).
        // Runs AFTER imported-global resolution so init exprs can remap any
        // `global.get` of an imported global (#338).
        let global_offset = merged.globals.len() as u32;
        for (old_idx, global) in module.globals.iter().enumerate() {
            let new_idx = merged.import_counts.global + global_offset + old_idx as u32;
            merged.global_index_map.insert(
                (comp_idx, mod_idx, import_global_count + old_idx as u32),
                new_idx,
            );
            let init_expr = convert_init_expr(
                &global.init_expr_bytes,
                comp_idx,
                mod_idx,
                merged,
                &global.content_type,
            );
            // #353: record this DEFINED global's constant i32 value (if any) so a
            // data/element offset that `global.get`s it (a post-fusion
            // `__memory_base`) can be folded to `i32.const` — a data const-expr
            // cannot `global.get` a defined global. Restricted to IMMUTABLE
            // globals: a `__memory_base` base is immutable, and folding an init
            // value is only unambiguously the segment-init-time value for a
            // constant, non-mutable global. (Active segments are initialised
            // before any start function, so even a mutable const-init would read
            // its init value — but immutable removes all doubt.)
            if !global.mutable
                && let Some(v) = crate::segments::const_i32_init_value(&global.init_expr_bytes)
            {
                merged.defined_global_i32_const.insert(new_idx, v);
            }
            let ty = convert_global_type(global, comp_idx, mod_idx, merged);
            merged.globals.push(MergedGlobal { ty, init_expr });
        }

        // Resolve imported table indices via intra-component module_resolutions.
        // Same pattern as global import resolution above.
        {
            let mut import_table_idx = 0u32;
            for imp in &module.imports {
                if !matches!(imp.kind, ImportKind::Table(_)) {
                    continue;
                }

                // Intra-component: check module_resolutions
                let intra = graph.module_resolutions.iter().find(|res| {
                    res.component_idx == comp_idx
                        && res.from_module == mod_idx
                        && imp.name == res.import_name
                        && (res.from_import_module.is_empty()
                            || res.from_import_module == imp.module)
                });
                if let Some(res) = intra {
                    let target_module = &components[res.component_idx].core_modules[res.to_module];
                    if let Some(export) = target_module
                        .exports
                        .iter()
                        .find(|e| e.name == res.export_name && e.kind == ExportKind::Table)
                    {
                        if let Some(&target_idx) = merged.table_index_map.get(&(
                            res.component_idx,
                            res.to_module,
                            export.index,
                        )) {
                            merged
                                .table_index_map
                                .insert((comp_idx, mod_idx, import_table_idx), target_idx);
                        }
                    }
                }

                // Map unresolved table imports to their merged import index
                if let std::collections::hash_map::Entry::Vacant(e) = merged
                    .table_index_map
                    .entry((comp_idx, mod_idx, import_table_idx))
                {
                    if let Some(&import_index) = unresolved_assignments.table.get(&(
                        comp_idx,
                        mod_idx,
                        imp.module.clone(),
                        imp.name.clone(),
                    )) {
                        e.insert(import_index);
                    }
                }

                import_table_idx += 1;
            }
        }

        // Resolve function imports that have been matched to exports in other
        // modules (cross-component and intra-component via adapter_sites,
        // remaining intra-component direct calls via module_resolutions).
        // adapter_sites is checked first because it includes both cross-component
        // adapters AND intra-component adapters (for module pairs with different
        // canonical options). module_resolutions is the fallback for
        // intra-component calls that don't need adapters.
        // This populates function_index_map for imported function indices so the
        // body rewriter can replace call targets.
        {
            let mut import_func_idx = 0u32;
            for imp in &module.imports {
                if !matches!(imp.kind, ImportKind::Function(_)) {
                    continue;
                }

                // Check adapter_sites first (cross-component + intra-component adapters).
                let resolved = graph.adapter_sites.iter().find(|site| {
                    site.from_component == comp_idx
                        && site.from_module == mod_idx
                        && (imp.name == site.import_name || imp.module == site.import_name)
                        && (imp.module == site.import_module || imp.name == site.import_module)
                });
                if let Some(site) = resolved {
                    if let Some(&target_idx) = merged.function_index_map.get(&(
                        site.to_component,
                        site.to_module,
                        site.export_func_idx,
                    )) {
                        log::debug!(
                            "Adapter site resolved: comp {} mod {} import {:?} -> func {}",
                            comp_idx,
                            mod_idx,
                            imp.name,
                            target_idx
                        );
                        merged
                            .function_index_map
                            .insert((comp_idx, mod_idx, import_func_idx), target_idx);
                    } else {
                        log::debug!(
                            "Adapter site MISS: comp {} mod {} import {:?} -> \
                             target comp {} mod {} func {} NOT in function_index_map",
                            comp_idx,
                            mod_idx,
                            imp.name,
                            site.to_component,
                            site.to_module,
                            site.export_func_idx
                        );
                    }
                } else if imp.module.contains("test:numbers") {
                    log::debug!(
                        "NO adapter site for: comp {} mod {} module={:?} name={:?} \
                         (total sites: {})",
                        comp_idx,
                        mod_idx,
                        imp.module,
                        imp.name,
                        graph.adapter_sites.len()
                    );
                }

                // Intra-component fallback: check module_resolutions for direct
                // calls that don't need adapters (adapter-needing ones were
                // already promoted to adapter_sites by the resolver).
                if !merged
                    .function_index_map
                    .contains_key(&(comp_idx, mod_idx, import_func_idx))
                {
                    let intra = graph.module_resolutions.iter().find(|res| {
                        res.component_idx == comp_idx
                            && res.from_module == mod_idx
                            && imp.name == res.import_name
                            && (res.from_import_module.is_empty()
                                || res.from_import_module == imp.module)
                    });
                    if let Some(res) = intra {
                        // Look up the target module's export to find its function index
                        let target_module =
                            &components[res.component_idx].core_modules[res.to_module];
                        if let Some(export) = target_module
                            .exports
                            .iter()
                            .find(|e| e.name == res.export_name && e.kind == ExportKind::Function)
                        {
                            if let Some(&target_idx) = merged.function_index_map.get(&(
                                res.component_idx,
                                res.to_module,
                                export.index,
                            )) {
                                log::debug!(
                                    "intra-comp func resolve: comp {} mod {} import {}({}) -> comp {} mod {} export {}[{}] = merged {}",
                                    comp_idx,
                                    mod_idx,
                                    imp.name,
                                    import_func_idx,
                                    res.component_idx,
                                    res.to_module,
                                    res.export_name,
                                    export.index,
                                    target_idx,
                                );
                                merged
                                    .function_index_map
                                    .insert((comp_idx, mod_idx, import_func_idx), target_idx);
                            } else {
                                log::warn!(
                                    "intra-comp func resolve MISS: comp {} mod {} import {}({}) -> comp {} mod {} export {}[{}] NOT IN function_index_map",
                                    comp_idx,
                                    mod_idx,
                                    imp.name,
                                    import_func_idx,
                                    res.component_idx,
                                    res.to_module,
                                    res.export_name,
                                    export.index,
                                );
                            }
                        }
                    }
                }

                // Map unresolved function imports to their merged import index
                if let std::collections::hash_map::Entry::Vacant(e) = merged
                    .function_index_map
                    .entry((comp_idx, mod_idx, import_func_idx))
                {
                    if let Some(&import_index) = unresolved_assignments.func.get(&(
                        comp_idx,
                        mod_idx,
                        imp.module.clone(),
                        imp.name.clone(),
                    )) {
                        log::debug!(
                            "unresolved func assign: comp {} mod {} import {}::{}({}) = merged import {}",
                            comp_idx,
                            mod_idx,
                            imp.module,
                            imp.name,
                            import_func_idx,
                            import_index,
                        );
                        e.insert(import_index);
                    } else {
                        log::debug!(
                            "UNMAPPED func import: comp {} mod {} import {}::{}({})",
                            comp_idx,
                            mod_idx,
                            imp.module,
                            imp.name,
                            import_func_idx,
                        );
                    }
                }

                import_func_idx += 1;
            }
        }

        // First pass: build all function index mappings.
        // Values are absolute wasm indices: import_count + array position.
        let func_offset = merged.functions.len() as u32;
        let mut func_type_indices = Vec::new();

        for (old_idx, &type_idx) in module.functions.iter().enumerate() {
            let new_func_idx = merged.import_counts.func + func_offset + old_idx as u32;
            let old_func_idx = import_func_count + old_idx as u32;

            merged
                .function_index_map
                .insert((comp_idx, mod_idx, old_func_idx), new_func_idx);

            // Get the remapped type index
            let new_type_idx = *merged
                .type_index_map
                .get(&(comp_idx, mod_idx, type_idx))
                .ok_or(Error::IndexOutOfBounds {
                    kind: "type",
                    index: type_idx,
                    max: module.types.len() as u32,
                })?;

            func_type_indices.push((old_idx, old_func_idx, new_type_idx, type_idx));
        }

        // Build IndexMaps for this module's function bodies
        let memory_base_offset = shared_memory_plan
            .and_then(|plan| plan.bases.get(&(comp_idx, mod_idx)).copied())
            .unwrap_or(0);

        // Address / memory strategy (ADR-7 path-H): resolve which relocation
        // sites this module needs rebased for its shared-memory placement. The
        // full decision + validation (path-F MissingRelocMetadata, memory64
        // reject, the #351 MisalignedReloc backstop) lives in
        // `address_strategy`; `has_direct_memory_access` is passed as a closure
        // so it stays lazily evaluated (only a non-zero-base, no-reloc module
        // pays the check — the original short-circuit).
        let address_plan = crate::address_strategy::resolve_address_plan(
            &module.custom_sections,
            module.code_section_range,
            &module.bytes,
            memory_base_offset,
            self.address_rebasing,
            &component_display_name(components, comp_idx),
            mod_idx,
            || module_has_direct_memory_access(module),
        )?;
        let data_addr_relocs = address_plan.data_addr_relocs;
        let code_addr_relocs = address_plan.code_addr_relocs;

        let module_memory = if self.address_rebasing {
            module_memory_type(module)?
        } else {
            None
        };
        let memory64 = module_memory
            .as_ref()
            .map(|mem| mem.memory64)
            .unwrap_or(false);
        let memory_initial_pages = module_memory.as_ref().map(|mem| mem.initial);

        // Segment base offsets: this module's local segment indices land in
        // the concatenated section at `base + local`. Capture the bases NOW,
        // before this module's own segments are appended (lines below), so
        // they count only PRIOR modules' segments — exactly mirroring how
        // `func_offset = merged.functions.len()` is captured before this
        // module's functions are pushed. Record them on `merged` so the
        // post-merge re-rewrite pass (resource-import redirect) can recover
        // the correct base after `.len()` no longer equals it.
        let data_segment_base = merged.data_segments.len() as u32;
        let elem_segment_base = merged.elements.len() as u32;
        merged
            .segment_bases
            .insert((comp_idx, mod_idx), (data_segment_base, elem_segment_base));

        let mut index_maps = build_index_maps_for_module(
            comp_idx,
            mod_idx,
            module,
            merged,
            self.memory_strategy,
            self.address_rebasing,
            memory_base_offset,
            memory64,
            memory_initial_pages,
            data_segment_base,
            elem_segment_base,
            code_addr_relocs,
        );
        // #353: hand the data/element offset reindex the set of DEFINED
        // constant-i32 globals so a `global.get` of a post-fusion `__memory_base`
        // in an offset is folded to `i32.const` (imported globals stay verbatim).
        index_maps
            .defined_global_i32_consts
            .clone_from(&merged.defined_global_i32_const);
        // #298: only under the upstream vestigial-allocator verdict does a
        // `memory.grow` reached during rebasing become `unreachable` (the
        // allocator is provably dead) instead of a hard error. Inert when
        // `address_rebasing` is off (the rewriter checks it only under rebase).
        index_maps.defer_grow_under_rebase = self.defer_grow_under_rebase;

        // Second pass: extract and rewrite function bodies
        for (old_idx, old_func_idx, new_type_idx, type_idx) in func_type_indices {
            let param_count = module
                .types
                .get(type_idx as usize)
                .map(|ty| ty.params.len() as u32)
                .unwrap_or(0);
            let body = extract_function_body(module, old_idx, param_count, &index_maps)?;

            merged.functions.push(MergedFunction {
                type_idx: new_type_idx,
                body,
                origin: (comp_idx, mod_idx, old_func_idx),
                synthetic_kind: None,
            });
        }

        // Merge exports (with component prefix if multiple components)
        for export in &module.exports {
            let (kind, old_idx) = match export.kind {
                ExportKind::Function => {
                    let new_idx = *merged
                        .function_index_map
                        .get(&(comp_idx, mod_idx, export.index))
                        .unwrap_or(&export.index);
                    (EncoderExportKind::Func, new_idx)
                }
                ExportKind::Table => {
                    let new_idx = *merged
                        .table_index_map
                        .get(&(comp_idx, mod_idx, export.index))
                        .unwrap_or(&export.index);
                    (EncoderExportKind::Table, new_idx)
                }
                ExportKind::Memory => {
                    let new_idx = *merged
                        .memory_index_map
                        .get(&(comp_idx, mod_idx, export.index))
                        .unwrap_or(&export.index);
                    (EncoderExportKind::Memory, new_idx)
                }
                ExportKind::Global => {
                    let new_idx = *merged
                        .global_index_map
                        .get(&(comp_idx, mod_idx, export.index))
                        .unwrap_or(&export.index);
                    (EncoderExportKind::Global, new_idx)
                }
            };

            // Export deduplication: in multi-memory mode, suffix duplicate
            // export names with the component index. Each component's shim
            // module exports numeric function names ("0", "1", ...) and a
            // "$imports" table that must remain distinct — deduplication
            // would wire the fixup module to the wrong component's indirect
            // table. In shared-memory mode, first-wins dedup is correct
            // since all components share one memory.
            // #245: `cabi_realloc` is named by the per-memory path below
            // (`cabi_realloc$<mem_idx>`), which is the convention the P2
            // wrapper consumes (component_wrap.rs looks reallocs up by
            // memory index). The generic comp_idx-suffixed dedup here must
            // NOT also mint into that namespace: when a colliding export's
            // comp_idx coincides with another realloc's mem_idx the two
            // schemes emit the same `cabi_realloc$N` twice and the output
            // fails validation ("duplicate export name"). A colliding
            // `cabi_realloc` is always comp_idx >= 1 with its own mem_idx
            // >= 1, so the per-memory path is guaranteed to publish it;
            // skip the redundant generic copy here. (Component 0's realloc
            // is the non-colliding first occurrence and still flows through
            // the else branch as plain `cabi_realloc`.)
            if self.memory_strategy == MemoryStrategy::MultiMemory
                && export.name == "cabi_realloc"
                && merged.exports.iter().any(|e| e.name == export.name)
            {
                continue;
            }
            let export_name = if self.memory_strategy == MemoryStrategy::MultiMemory
                && merged.exports.iter().any(|e| e.name == export.name)
            {
                format!("{}${}", export.name, comp_idx)
            } else if self.memory_strategy != MemoryStrategy::MultiMemory
                && merged.exports.iter().any(|e| e.name == export.name)
            {
                continue; // first-wins dedup in shared-memory mode
            } else {
                export.name.clone()
            };

            merged.exports.push(MergedExport {
                name: export_name,
                kind,
                index: old_idx,
            });
        }

        // Detect cabi_realloc for adapter generation.
        // 1. Check canonical section Realloc options (takes priority)
        //
        // The canonical section's Realloc(idx) refers to the *component-level*
        // core function index space, which spans all modules in the component
        // (and includes core functions from canon lower / aliases). For
        // single-module components the component-level index equals the
        // module-local index. For multi-module components, we decompose the
        // component-level index by accumulating per-module function counts.
        let mut realloc_from_canonical = false;

        // Helper: check if a merged function has the cabi_realloc signature
        // (i32, i32, i32, i32) -> i32.
        let is_realloc_sig = |merged: &MergedModule, merged_idx: u32| -> bool {
            if let Some(func) = merged.defined_func(merged_idx) {
                if let Some(ty) = merged.types.get(func.type_idx as usize) {
                    return ty.params.len() == 4
                        && ty.results.len() == 1
                        && ty.params.iter().all(|p| *p == wasm_encoder::ValType::I32)
                        && ty.results[0] == wasm_encoder::ValType::I32;
                }
            }
            // Import functions — accept if we can't verify
            (merged_idx as usize) < merged.import_counts.func as usize
        };

        for entry in &components[comp_idx].canonical_functions {
            let realloc_idx = match entry {
                crate::parser::CanonicalEntry::Lift { options, .. } => options.realloc,
                crate::parser::CanonicalEntry::Lower { options, .. } => options.realloc,
                _ => None,
            };
            if let Some(core_func_idx) = realloc_idx {
                // Decompose component-level core function index to
                // (target_module_idx, module_local_func_idx).
                if let Some((target_mod_idx, local_func_idx)) =
                    decompose_component_core_func_index(&components[comp_idx], core_func_idx)
                {
                    // Only store the realloc for the module currently being
                    // merged (mod_idx).
                    if target_mod_idx == mod_idx {
                        if let Some(&merged_idx) = merged.function_index_map.get(&(
                            comp_idx,
                            target_mod_idx,
                            local_func_idx,
                        )) {
                            // Validate signature: decompose_component_core_func_index
                            // can produce incorrect mappings for multi-module components
                            // because the component core function space includes canon
                            // lower entries that aren't in any module's function space.
                            if is_realloc_sig(merged, merged_idx) {
                                merged.realloc_map.insert((comp_idx, mod_idx), merged_idx);
                                realloc_from_canonical = true;
                                log::debug!(
                                    "Found canonical realloc in component {} module {}: \
                                     component core func {} -> module-local {} -> merged idx {}",
                                    comp_idx,
                                    mod_idx,
                                    core_func_idx,
                                    local_func_idx,
                                    merged_idx
                                );
                                break;
                            } else {
                                log::debug!(
                                    "Canonical realloc candidate in component {} module {} \
                                     (core func {} -> local {} -> merged {}) has wrong signature, skipping",
                                    comp_idx,
                                    mod_idx,
                                    core_func_idx,
                                    local_func_idx,
                                    merged_idx
                                );
                            }
                        }
                    }
                } else {
                    // Decomposition failed -- the index may refer to a core
                    // function created by canon lower or an alias, which lives
                    // outside any module's function space. Try a direct lookup
                    // as a fallback (works for single-module components where
                    // component-level == module-local).
                    if let Some(&merged_idx) =
                        merged
                            .function_index_map
                            .get(&(comp_idx, mod_idx, core_func_idx))
                    {
                        if is_realloc_sig(merged, merged_idx) {
                            merged.realloc_map.insert((comp_idx, mod_idx), merged_idx);
                            realloc_from_canonical = true;
                            log::debug!(
                                "Found canonical realloc (direct fallback) in component {} module {}: \
                                 core func {} -> merged idx {}",
                                comp_idx,
                                mod_idx,
                                core_func_idx,
                                merged_idx
                            );
                            break;
                        }
                    }
                }
            }
        }

        // 2. Fall back to name-based detection if canonical section didn't provide one
        if !realloc_from_canonical {
            for export in &module.exports {
                if export.name == "cabi_realloc" && export.kind == ExportKind::Function {
                    if let Some(&merged_idx) =
                        merged
                            .function_index_map
                            .get(&(comp_idx, mod_idx, export.index))
                    {
                        merged.realloc_map.insert((comp_idx, mod_idx), merged_idx);
                        log::debug!(
                            "Found cabi_realloc by name in component {} module {}: merged idx {}",
                            comp_idx,
                            mod_idx,
                            merged_idx
                        );
                    }
                }
            }
        }

        // In multi-memory mode, export per-component cabi_realloc and memories
        // so the P2 wrapper can reference the correct allocator and memory per import.
        if self.memory_strategy == MemoryStrategy::MultiMemory {
            // Export cabi_realloc$N using the MEMORY INDEX as suffix (not comp_idx).
            // The P2 wrapper looks up cabi_realloc$N by memory index, so these must match.
            let mem_idx = merged
                .memory_index_map
                .get(&(comp_idx, mod_idx, 0))
                .copied();
            if let (Some(mem_idx), Some(&realloc_idx)) =
                (mem_idx, merged.realloc_map.get(&(comp_idx, mod_idx)))
            {
                if mem_idx > 0 {
                    let export_name = format!("cabi_realloc${}", mem_idx);
                    if !merged.exports.iter().any(|e| e.name == export_name) {
                        merged.exports.push(MergedExport {
                            name: export_name,
                            kind: EncoderExportKind::Func,
                            index: realloc_idx,
                        });
                    }
                }
            }

            // Note: memory$N exports are NOT needed on the fused module.
            // The P2 wrapper's stubs module provides all memories with
            // the $N naming convention. The fused module imports them.
        }

        // Merge custom sections
        for (name, data) in &module.custom_sections {
            // #328: the `name` section carries function indices in THIS
            // module's index space. Copying it verbatim produces duplicate
            // `name` sections (llvm-dwarfdump rejects the module) whose
            // indices point at the wrong fused functions. Instead, remap its
            // function-name entries into the fused index space and accumulate
            // them; a single coalesced `name` section is emitted at encode
            // time under `preserve_names`. Function merge above has already
            // populated `function_index_map` for this module.
            if name == "name" {
                accumulate_remapped_function_names(
                    data,
                    comp_idx,
                    mod_idx,
                    &merged.function_index_map,
                    &mut merged.fused_function_names,
                );
                continue;
            }
            merged.custom_sections.push((name.clone(), data.clone()));
        }

        // Parse and merge element segments with reindexing
        let element_segments = crate::segments::parse_element_segments(module)?;
        for segment in element_segments {
            let reindexed = crate::segments::reindex_element_segment(&segment, &index_maps);
            merged.elements.push(reindexed);
        }

        // Parse and merge data segments with reindexing.
        let data_segments = crate::segments::parse_data_segments(module)?;
        for mut segment in data_segments {
            // #326 Part C: rebase absolute pointers baked into a data segment's
            // payload. `reloc.DATA` MEMORY_ADDR_I32 sites name the 4-byte LE
            // pointers; each segment's `content_offset` places its bytes in the
            // same data-section-content coordinate space as those sites.
            if memory_base_offset != 0 && !data_addr_relocs.is_empty() {
                let base = u32::try_from(memory_base_offset).map_err(|_| {
                    Error::MemoryStrategyUnsupported(
                        "shared memory base offset exceeds 32-bit address space".to_string(),
                    )
                })?;
                crate::reloc::rebase_data_segment_pointers(
                    &mut segment.data,
                    segment.content_offset,
                    &data_addr_relocs,
                    base,
                );
            }
            let reindexed = crate::segments::reindex_data_segment(&segment, &index_maps)?;
            merged.data_segments.push(reindexed);
        }

        Ok(())
    }
}
