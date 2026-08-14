//! Unresolved-import assignment, deduplication, and name-remap accounting
//! extracted from the merger.

use super::*;

/// Pre-computed mapping from unresolved import identity to its
/// position in the merged import index space (per entity kind).
pub(crate) struct UnresolvedImportAssignments {
    pub(crate) func: HashMap<(usize, usize, String, String), u32>,
    pub(crate) global: HashMap<(usize, usize, String, String), u32>,
    pub(crate) table: HashMap<(usize, usize, String, String), u32>,
}

/// Dedup key type for unresolved imports.
///
/// In multi-memory mode, each component gets its own import slot even for
/// the same `(module, field)`, because each needs a different canon lower
/// with Memory(N) and Realloc(N). The optional `usize` is the component
/// index — `Some(comp_idx)` in multi-memory mode, `None` in shared-memory
/// mode (preserving existing dedup behavior).
type DedupKey = (String, String, Option<usize>);

/// Deduplication metadata for unresolved imports.
///
/// Tracks which effective `(module, field)` pairs have already been assigned
/// an import position and which WASI version string to use for each dedup key.
pub(crate) struct ImportDedupInfo {
    /// For each dedup key, the full module name with the highest WASI version
    /// seen across all occurrences.
    pub(crate) best_module_version: HashMap<DedupKey, String>,
    /// Entries where dedup was skipped because the function type didn't match
    /// the first occurrence with the same effective (module, field) key.
    /// Keyed by (component_idx, module_idx, module_name, field_name).
    pub(crate) type_mismatch_entries: HashSet<(usize, usize, String, String)>,
}

/// Compute the effective `(module, field)` dedup key for an unresolved import.
///
/// Uses display names (from canon-lower WASI tracing) when available, falls
/// back to original core module import names. The module name is then
/// version-normalized so that `wasi:io/error@0.2.0` and `@0.2.6` map to
/// the same key.
fn effective_import_key(unresolved: &crate::resolver::UnresolvedImport) -> (String, String) {
    let module = unresolved
        .display_module
        .as_ref()
        .unwrap_or(&unresolved.module_name);
    let field = unresolved
        .display_field
        .as_ref()
        .unwrap_or(&unresolved.field_name);
    (
        normalize_wasi_module_name(module).to_string(),
        field.clone(),
    )
}

/// Return the effective module name (with display override) for an unresolved import.
fn effective_module_name(unresolved: &crate::resolver::UnresolvedImport) -> &str {
    unresolved
        .display_module
        .as_ref()
        .unwrap_or(&unresolved.module_name)
}

/// Resolve the imports-vector index whose name exactly matches
/// `expected_name` by scanning the values of a per-component
/// resource-tracking map. Exact match (not `ends_with`) — the prior
/// `imp.name.ends_with(rn)` form silently conflated two resources
/// whose names shared a suffix (e.g. `float` matched both
/// `[resource-rep]float` and `[resource-rep]bigfloat`), letting the
/// dedup-skip path register the wrong import for the wrong-suffix
/// component. See LS-A-19 for the regression.
pub(crate) fn find_exact_resource_import_idx(
    tracking: &HashMap<(usize, String), u32>,
    imports: &[MergedImport],
    expected_name: &str,
) -> Option<u32> {
    tracking.values().copied().find(|&idx| {
        imports
            .get(idx as usize)
            .is_some_and(|imp| imp.name == expected_name)
    })
}

impl Merger {
    /// Add remaining unresolved imports to the merged module.
    ///
    /// **Invariant**: This function MUST iterate `graph.unresolved_imports` in
    /// exactly the same order as [`compute_unresolved_import_assignments`], and
    /// must produce the same per-entity-kind position for each import. If these
    /// two functions diverge, import indices will be silently misaligned,
    /// producing incorrect wasm output. Debug assertions below verify this
    /// invariant at development/test time.
    ///
    /// **Deduplication**: When multiple unresolved imports share the same
    /// effective `(module, field)` after WASI version normalization, only the
    /// first occurrence is emitted. Subsequent duplicates are skipped but their
    /// assignments (from `compute_unresolved_import_assignments`) already point
    /// to the same position, so `function_index_map` etc. remain correct.
    pub(crate) fn add_unresolved_imports(
        &self,
        graph: &DependencyGraph,
        merged: &mut MergedModule,
        shared_memory_plan: Option<&SharedMemoryPlan>,
        dedup_info: &ImportDedupInfo,
    ) -> Result<()> {
        let mut shared_memory_import_added = false;

        // Track per-kind positions so we can assert alignment with
        // compute_unresolved_import_assignments.
        let mut func_position: u32 = 0;
        let mut table_position: u32 = 0;
        let mut memory_position: u32 = 0;
        let mut global_position: u32 = 0;

        // Track already-emitted dedup keys per entity kind (includes component
        // dimension in multi-memory mode so each component gets its own slot).
        let mut emitted_func: HashSet<DedupKey> = HashSet::new();
        let mut emitted_table: HashSet<DedupKey> = HashSet::new();
        let mut emitted_global: HashSet<DedupKey> = HashSet::new();

        // Track base (module, field) names already emitted for function imports
        // so we can suffix duplicates in multi-memory mode.
        let mut emitted_base_func: HashSet<(String, String)> = HashSet::new();
        // Same for tables/globals: type-mismatched same-named imports need a
        // unique (module, field) in multi-memory mode.
        let mut emitted_base_table: HashSet<(String, String)> = HashSet::new();
        let mut emitted_base_global: HashSet<(String, String)> = HashSet::new();

        for unresolved in &graph.unresolved_imports {
            // Skip imports resolved by adapter sites (must match the
            // filter in compute_unresolved_import_assignments).
            let resolved_by_adapter = graph.adapter_sites.iter().any(|site| {
                if site.from_component != unresolved.component_idx {
                    return false;
                }
                let direct = site.from_module == unresolved.module_idx
                    && site.import_name == unresolved.field_name;
                let display = unresolved.display_field.as_deref() == Some(&site.import_name);
                direct || display
            });
            if resolved_by_adapter {
                continue;
            }

            if let (Some(plan), ImportKind::Memory(_)) = (shared_memory_plan, &unresolved.kind) {
                if let Some((module, name)) = &plan.import {
                    if !shared_memory_import_added {
                        merged.imports.push(MergedImport {
                            module: module.clone(),
                            name: name.clone(),
                            entity_type: EntityType::Memory(plan.memory),
                            component_idx: None,
                        });
                        shared_memory_import_added = true;
                        memory_position += 1;
                    }
                }
                continue;
            }

            let (eff_module_norm, eff_field) = effective_import_key(unresolved);
            let comp_dim = if self.memory_strategy == MemoryStrategy::MultiMemory {
                Some(unresolved.component_idx)
            } else {
                None
            };
            let dedup_key: DedupKey = (eff_module_norm, eff_field, comp_dim);

            match &unresolved.kind {
                ImportKind::Function(type_idx) => {
                    // Check if this entry was marked as type-mismatched (not safe
                    // to dedup). If so, always emit even if the dedup_key was seen.
                    let is_type_mismatch = dedup_info.type_mismatch_entries.contains(&(
                        unresolved.component_idx,
                        unresolved.module_idx,
                        unresolved.module_name.clone(),
                        unresolved.field_name.clone(),
                    ));
                    if !is_type_mismatch && !emitted_func.insert(dedup_key.clone()) {
                        // Duplicate with matching type — skip emitting.
                        // Still record per-component resource tracking: find the
                        // func index already assigned to this resource name.
                        let eff_field = &dedup_key.1;
                        // Exact-match the full `[resource-{rep,new}]<name>`
                        // import name. The prior `ends_with(rn)` matched any
                        // resource whose name had `rn` as a suffix (e.g.
                        // `rn = "float"` collided with both
                        // `[resource-rep]float` and `[resource-rep]bigfloat`),
                        // letting `resource_rep_by_component` track the
                        // wrong import for the wrong-suffix collision — silent
                        // cross-resource confusion (LS-A-19).
                        if let Some(rn) = eff_field.strip_prefix("[resource-rep]") {
                            let expected = format!("[resource-rep]{rn}");
                            if let Some(idx) = find_exact_resource_import_idx(
                                &merged.resource_rep_by_component,
                                &merged.imports,
                                &expected,
                            ) {
                                merged
                                    .resource_rep_by_component
                                    .insert((unresolved.component_idx, rn.to_string()), idx);
                            }
                        } else if let Some(rn) = eff_field.strip_prefix("[resource-new]") {
                            let expected = format!("[resource-new]{rn}");
                            if let Some(idx) = find_exact_resource_import_idx(
                                &merged.resource_new_by_component,
                                &merged.imports,
                                &expected,
                            ) {
                                merged
                                    .resource_new_by_component
                                    .insert((unresolved.component_idx, rn.to_string()), idx);
                            }
                        }
                        continue;
                    }

                    debug_assert!(
                        func_position < merged.import_counts.func,
                        "add_unresolved_imports: func import position {} exceeds \
                         pre-computed count {} — iteration order has diverged from \
                         compute_unresolved_import_assignments",
                        func_position,
                        merged.import_counts.func,
                    );
                    func_position += 1;

                    // Remap type index
                    let new_type_idx = *merged
                        .type_index_map
                        .get(&(unresolved.component_idx, unresolved.module_idx, *type_idx))
                        .unwrap_or(type_idx);

                    // Use best version module name from dedup_info
                    let module = dedup_info
                        .best_module_version
                        .get(&dedup_key)
                        .cloned()
                        .unwrap_or_else(|| {
                            unresolved
                                .display_module
                                .as_ref()
                                .unwrap_or(&unresolved.module_name)
                                .clone()
                        });

                    // In multi-memory mode, suffix the field name with $comp_idx
                    // when a different component already emitted the same base name.
                    // This ensures unique (module, field) pairs in the wasm binary.
                    let base_key = (dedup_key.0.clone(), dedup_key.1.clone());
                    let needs_suffix = self.memory_strategy == MemoryStrategy::MultiMemory
                        && !emitted_base_func.insert(base_key);
                    let name = if needs_suffix {
                        format!("{}${}", dedup_key.1, unresolved.component_idx)
                    } else {
                        dedup_key.1.clone()
                    };

                    // Populate per-import metadata for component_wrap
                    let mem_idx = component_memory_index(merged, unresolved.component_idx);
                    let realloc_idx = component_realloc_index(merged, unresolved.component_idx);
                    merged.import_memory_indices.push(mem_idx);
                    merged.import_realloc_indices.push(realloc_idx);

                    merged.imports.push(MergedImport {
                        module,
                        name,
                        entity_type: EntityType::Function(new_type_idx),
                        component_idx: Some(unresolved.component_idx),
                    });

                    // Track per-component resource import indices.
                    // Strip $N suffix (multi-memory dedup) from the resource name
                    // so the adapter can look up by bare name (e.g., "float" not "float$5").
                    let merged_func_idx = func_position - 1;
                    let eff_field = &dedup_key.1;
                    if let Some(rn) = eff_field.strip_prefix("[resource-rep]") {
                        let bare_rn = rn.rsplit_once('$').map_or(rn, |(base, _)| base);
                        merged
                            .resource_rep_by_component
                            .entry((unresolved.component_idx, bare_rn.to_string()))
                            .or_insert(merged_func_idx);
                    } else if let Some(rn) = eff_field.strip_prefix("[resource-new]") {
                        let bare_rn = rn.rsplit_once('$').map_or(rn, |(base, _)| base);
                        merged
                            .resource_new_by_component
                            .entry((unresolved.component_idx, bare_rn.to_string()))
                            .or_insert(merged_func_idx);
                    }
                }
                ImportKind::Table(t) => {
                    // Type-mismatched entries must emit a separate import even
                    // when the dedup key was already seen (mirrors the function
                    // arm). Same-typed duplicates still collapse to one slot.
                    let is_type_mismatch = dedup_info.type_mismatch_entries.contains(&(
                        unresolved.component_idx,
                        unresolved.module_idx,
                        unresolved.module_name.clone(),
                        unresolved.field_name.clone(),
                    ));
                    if !is_type_mismatch && !emitted_table.insert(dedup_key.clone()) {
                        continue;
                    }

                    debug_assert!(
                        table_position < merged.import_counts.table,
                        "add_unresolved_imports: table import position {} exceeds \
                         pre-computed count {} — iteration order has diverged from \
                         compute_unresolved_import_assignments",
                        table_position,
                        merged.import_counts.table,
                    );
                    table_position += 1;

                    let module = dedup_info
                        .best_module_version
                        .get(&dedup_key)
                        .cloned()
                        .unwrap_or_else(|| {
                            unresolved
                                .display_module
                                .as_ref()
                                .unwrap_or(&unresolved.module_name)
                                .clone()
                        });
                    // In multi-memory mode, suffix the field with $comp_idx when
                    // a different component already emitted the same base name,
                    // keeping (module, field) pairs unique (mirrors func arm).
                    let base_key = (dedup_key.0.clone(), dedup_key.1.clone());
                    let needs_suffix = self.memory_strategy == MemoryStrategy::MultiMemory
                        && !emitted_base_table.insert(base_key);
                    let name = if needs_suffix {
                        format!("{}${}", dedup_key.1, unresolved.component_idx)
                    } else {
                        dedup_key.1.clone()
                    };

                    merged.imports.push(MergedImport {
                        module,
                        name,
                        entity_type: EntityType::Table(convert_table_type(
                            t,
                            unresolved.component_idx,
                            unresolved.module_idx,
                            merged,
                        )),
                        component_idx: Some(unresolved.component_idx),
                    });
                }
                ImportKind::Memory(m) => {
                    memory_position += 1;

                    let module = unresolved
                        .display_module
                        .as_ref()
                        .unwrap_or(&unresolved.module_name)
                        .clone();
                    let name = unresolved
                        .display_field
                        .as_ref()
                        .unwrap_or(&unresolved.field_name)
                        .clone();
                    merged.imports.push(MergedImport {
                        module,
                        name,
                        entity_type: EntityType::Memory(convert_memory_type(m)),
                        component_idx: Some(unresolved.component_idx),
                    });
                }
                ImportKind::Global(g) => {
                    // Type-mismatched entries must emit a separate import even
                    // when the dedup key was already seen (mirrors the function
                    // arm). Same-typed duplicates still collapse to one slot.
                    let is_type_mismatch = dedup_info.type_mismatch_entries.contains(&(
                        unresolved.component_idx,
                        unresolved.module_idx,
                        unresolved.module_name.clone(),
                        unresolved.field_name.clone(),
                    ));
                    if !is_type_mismatch && !emitted_global.insert(dedup_key.clone()) {
                        continue;
                    }

                    debug_assert!(
                        global_position < merged.import_counts.global,
                        "add_unresolved_imports: global import position {} exceeds \
                         pre-computed count {} — iteration order has diverged from \
                         compute_unresolved_import_assignments",
                        global_position,
                        merged.import_counts.global,
                    );
                    global_position += 1;

                    let module = dedup_info
                        .best_module_version
                        .get(&dedup_key)
                        .cloned()
                        .unwrap_or_else(|| {
                            unresolved
                                .display_module
                                .as_ref()
                                .unwrap_or(&unresolved.module_name)
                                .clone()
                        });
                    // In multi-memory mode, suffix the field with $comp_idx when
                    // a different component already emitted the same base name,
                    // keeping (module, field) pairs unique (mirrors func arm).
                    let base_key = (dedup_key.0.clone(), dedup_key.1.clone());
                    let needs_suffix = self.memory_strategy == MemoryStrategy::MultiMemory
                        && !emitted_base_global.insert(base_key);
                    let name = if needs_suffix {
                        format!("{}${}", dedup_key.1, unresolved.component_idx)
                    } else {
                        dedup_key.1.clone()
                    };

                    merged.imports.push(MergedImport {
                        module,
                        name,
                        entity_type: EntityType::Global(convert_global_type(
                            g,
                            unresolved.component_idx,
                            unresolved.module_idx,
                            merged,
                        )),
                        component_idx: Some(unresolved.component_idx),
                    });
                }
            };
        }

        if let Some(plan) = shared_memory_plan {
            if let Some((module, name)) = &plan.import {
                if !shared_memory_import_added {
                    merged.imports.push(MergedImport {
                        module: module.clone(),
                        name: name.clone(),
                        entity_type: EntityType::Memory(plan.memory),
                        component_idx: None,
                    });
                    memory_position += 1;
                }
            }
        }

        // Final totals must match what compute_unresolved_import_assignments produced.
        debug_assert_eq!(
            func_position, merged.import_counts.func,
            "add_unresolved_imports: final func count ({}) != pre-computed ({}). \
             The iteration order has diverged from compute_unresolved_import_assignments.",
            func_position, merged.import_counts.func,
        );
        debug_assert_eq!(
            table_position, merged.import_counts.table,
            "add_unresolved_imports: final table count ({}) != pre-computed ({}). \
             The iteration order has diverged from compute_unresolved_import_assignments.",
            table_position, merged.import_counts.table,
        );
        debug_assert_eq!(
            memory_position, merged.import_counts.memory,
            "add_unresolved_imports: final memory count ({}) != pre-computed ({}). \
             The iteration order has diverged from compute_unresolved_import_assignments.",
            memory_position, merged.import_counts.memory,
        );
        debug_assert_eq!(
            global_position, merged.import_counts.global,
            "add_unresolved_imports: final global count ({}) != pre-computed ({}). \
             The iteration order has diverged from compute_unresolved_import_assignments.",
            global_position, merged.import_counts.global,
        );

        Ok(())
    }
}

///
/// # Import Order Invariant
///
/// This function and [`Merger::add_unresolved_imports`] **must** iterate
/// `graph.unresolved_imports` in exactly the same order and apply the same
/// skip/dedup logic for shared-memory imports.  The indices assigned here
/// are used during `merge_core_module` to populate `function_index_map`,
/// `global_index_map`, and `table_index_map` for unresolved imports.
/// Later, `add_unresolved_imports` emits the actual import entries at those
/// same positions.  If the two functions diverge, an import at position N
/// in the merged section will have a different entity than the index maps
/// expect, producing silently incorrect wasm output.
///
/// `add_unresolved_imports` contains `debug_assert!` checks that verify
/// the per-kind counts match what this function computed.  These fire in
/// debug/test builds if the invariant is ever broken.
pub(crate) fn compute_unresolved_import_assignments(
    graph: &DependencyGraph,
    shared_memory_plan: Option<&SharedMemoryPlan>,
    components: &[ParsedComponent],
    memory_strategy: MemoryStrategy,
) -> (ImportCounts, UnresolvedImportAssignments, ImportDedupInfo) {
    use crate::parser::FuncType;

    let mut counts = ImportCounts::default();
    let mut assignments = UnresolvedImportAssignments {
        func: HashMap::new(),
        global: HashMap::new(),
        table: HashMap::new(),
    };
    let mut shared_memory_import_counted = false;

    // Per-kind dedup: map dedup key → (first-assigned position, type signature).
    // In multi-memory mode the key includes the component index so each
    // component gets its own import slot for per-component canon lower.
    let mut seen_func: HashMap<DedupKey, (u32, Option<FuncType>)> = HashMap::new();
    // Table/global dedup maps also carry the entity TYPE alongside the first
    // assigned position, mirroring the function arm. Two same-named imports
    // with structurally different types must NOT be merged into one slot — the
    // second importer's code would then operate on the wrong-typed entity,
    // producing an invalid fused module. Type identity:
    //   TableType  = (element_type, initial, maximum)
    //   GlobalType = (content_type, mutable)
    // (init_expr_bytes is irrelevant: imported globals carry no initializer.)
    type TableSig = (ValType, u64, Option<u64>);
    type GlobalSig = (ValType, bool);
    let mut seen_table: HashMap<DedupKey, (u32, TableSig)> = HashMap::new();
    let mut seen_global: HashMap<DedupKey, (u32, GlobalSig)> = HashMap::new();

    // Track highest version for each dedup key
    let mut best_module_version: HashMap<DedupKey, String> = HashMap::new();
    // Track entries where type mismatch prevented deduplication
    let mut type_mismatch_entries: HashSet<(usize, usize, String, String)> = HashSet::new();

    let mut adapter_skip_count = 0usize;
    for unresolved in &graph.unresolved_imports {
        // Skip imports that are resolved by adapter sites (cross-component
        // or per-function interface wiring).  Match on both raw core names
        // (module_name/field_name) and display names (display_module/display_field)
        // because indirect-table shim modules use synthetic names (module="",
        // field="0") while their display names carry the original interface names.
        let resolved_by_adapter = graph.adapter_sites.iter().any(|site| {
            if site.from_component != unresolved.component_idx {
                return false;
            }
            // Direct match: same module, field matches import_name
            let direct = site.from_module == unresolved.module_idx
                && site.import_name == unresolved.field_name;
            // Display match: display_field matches import_name (for shim modules
            // whose raw field is a numeric index)
            let display = unresolved.display_field.as_deref() == Some(&site.import_name);
            direct || display
        });
        if resolved_by_adapter {
            adapter_skip_count += 1;
            continue;
        }

        if let (Some(plan), ImportKind::Memory(_)) = (shared_memory_plan, &unresolved.kind) {
            if plan.import.is_some() && !shared_memory_import_counted {
                counts.memory += 1;
                shared_memory_import_counted = true;
            }
            continue;
        }

        let (eff_module_norm, eff_field) = effective_import_key(unresolved);
        let comp_dim = if memory_strategy == MemoryStrategy::MultiMemory {
            Some(unresolved.component_idx)
        } else {
            None
        };
        let dedup_key: DedupKey = (eff_module_norm, eff_field, comp_dim);
        let eff_module = effective_module_name(unresolved);

        // Update best version for this dedup key
        match best_module_version.entry(dedup_key.clone()) {
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(eff_module.to_string());
            }
            std::collections::hash_map::Entry::Occupied(mut e) => {
                let existing_ver = extract_version(e.get());
                let new_ver = extract_version(eff_module);
                if let (Some(ev), Some(nv)) = (existing_ver, new_ver) {
                    if compare_version(nv, ev) == std::cmp::Ordering::Greater {
                        e.insert(eff_module.to_string());
                    }
                }
            }
        }

        match &unresolved.kind {
            ImportKind::Function(type_idx) => {
                // Look up the structural function type for compatibility checking.
                let func_type = components
                    .get(unresolved.component_idx)
                    .and_then(|c| c.core_modules.get(unresolved.module_idx))
                    .and_then(|m| m.types.get(*type_idx as usize))
                    .cloned();

                let position = match seen_func.entry(dedup_key) {
                    std::collections::hash_map::Entry::Occupied(e) => {
                        let (pos, ref first_type) = *e.get();
                        // Type compatibility check: only dedup if the function
                        // signatures match structurally. If they differ, this is
                        // NOT the same function despite matching (module, field)
                        // names — allocate a fresh position.
                        if first_type == &func_type {
                            pos
                        } else {
                            log::warn!(
                                "Import dedup: type mismatch for {:?} — \
                                 first={:?}, current={:?}; skipping dedup",
                                e.key(),
                                first_type,
                                func_type,
                            );
                            type_mismatch_entries.insert((
                                unresolved.component_idx,
                                unresolved.module_idx,
                                unresolved.module_name.clone(),
                                unresolved.field_name.clone(),
                            ));
                            let pos = counts.func;
                            counts.func += 1;
                            pos
                        }
                    }
                    std::collections::hash_map::Entry::Vacant(e) => {
                        let pos = counts.func;
                        e.insert((pos, func_type));
                        counts.func += 1;
                        pos
                    }
                };
                // Always insert the assignment so merge_core_module lookup works
                // for every (comp_idx, mod_idx, module_name, field_name) tuple.
                assignments.func.insert(
                    (
                        unresolved.component_idx,
                        unresolved.module_idx,
                        unresolved.module_name.clone(),
                        unresolved.field_name.clone(),
                    ),
                    position,
                );
            }
            ImportKind::Table(table_type) => {
                let table_sig: TableSig = (
                    table_type.element_type,
                    table_type.initial,
                    table_type.maximum,
                );
                let position = match seen_table.entry(dedup_key) {
                    std::collections::hash_map::Entry::Occupied(e) => {
                        let (pos, ref first_sig) = *e.get();
                        // Type compatibility: only dedup if element type AND
                        // limits match the first occurrence. Otherwise this is
                        // a distinct table despite the matching (module, field)
                        // names — allocate a fresh slot (mirrors function arm).
                        if first_sig == &table_sig {
                            pos
                        } else {
                            log::warn!(
                                "Import dedup: table type mismatch for {:?} — \
                                 first={:?}, current={:?}; skipping dedup",
                                e.key(),
                                first_sig,
                                table_sig,
                            );
                            type_mismatch_entries.insert((
                                unresolved.component_idx,
                                unresolved.module_idx,
                                unresolved.module_name.clone(),
                                unresolved.field_name.clone(),
                            ));
                            let pos = counts.table;
                            counts.table += 1;
                            pos
                        }
                    }
                    std::collections::hash_map::Entry::Vacant(e) => {
                        let pos = counts.table;
                        e.insert((pos, table_sig));
                        counts.table += 1;
                        pos
                    }
                };
                assignments.table.insert(
                    (
                        unresolved.component_idx,
                        unresolved.module_idx,
                        unresolved.module_name.clone(),
                        unresolved.field_name.clone(),
                    ),
                    position,
                );
            }
            ImportKind::Memory(_) => {
                counts.memory += 1;
            }
            ImportKind::Global(global_type) => {
                let global_sig: GlobalSig = (global_type.content_type, global_type.mutable);
                let position = match seen_global.entry(dedup_key) {
                    std::collections::hash_map::Entry::Occupied(e) => {
                        let (pos, ref first_sig) = *e.get();
                        // Type compatibility: only dedup if content type AND
                        // mutability match the first occurrence. Otherwise this
                        // is a distinct global despite the matching (module,
                        // field) names — allocate a fresh slot (mirrors
                        // function arm).
                        if first_sig == &global_sig {
                            pos
                        } else {
                            log::warn!(
                                "Import dedup: global type mismatch for {:?} — \
                                 first={:?}, current={:?}; skipping dedup",
                                e.key(),
                                first_sig,
                                global_sig,
                            );
                            type_mismatch_entries.insert((
                                unresolved.component_idx,
                                unresolved.module_idx,
                                unresolved.module_name.clone(),
                                unresolved.field_name.clone(),
                            ));
                            let pos = counts.global;
                            counts.global += 1;
                            pos
                        }
                    }
                    std::collections::hash_map::Entry::Vacant(e) => {
                        let pos = counts.global;
                        e.insert((pos, global_sig));
                        counts.global += 1;
                        pos
                    }
                };
                assignments.global.insert(
                    (
                        unresolved.component_idx,
                        unresolved.module_idx,
                        unresolved.module_name.clone(),
                        unresolved.field_name.clone(),
                    ),
                    position,
                );
            }
        }
    }

    // Trailing shared memory import (same as add_unresolved_imports)
    if let Some(plan) = shared_memory_plan {
        if plan.import.is_some() && !shared_memory_import_counted {
            counts.memory += 1;
        }
    }

    if adapter_skip_count > 0 {
        log::debug!(
            "compute_unresolved_import_assignments: skipped {} adapter-resolved imports \
             (remaining: {} func, {} table, {} global, {} memory)",
            adapter_skip_count,
            counts.func,
            counts.table,
            counts.global,
            counts.memory
        );
    }

    let dedup_info = ImportDedupInfo {
        best_module_version,
        type_mismatch_entries,
    };

    (counts, assignments, dedup_info)
}

/// #328: parse a WASM `name` custom section and accumulate its
/// function-name entries into `out`, remapping each function index from
/// this module's index space `(comp_idx, mod_idx, orig_idx)` into the
/// fused index space via `function_index_map`.
///
/// Entries with no mapping (a dead / internalized function) are dropped —
/// the coalesced section must never carry a wrong index (LS-D-1: correct or
/// nothing). Non-function subsections (module / local / label / type / …
/// names) are ignored in this pass: their indices would also need
/// remapping, and dropping them keeps the emitted section correct rather
/// than plausibly-wrong. A malformed section is dropped whole.
pub(crate) fn accumulate_remapped_function_names(
    data: &[u8],
    comp_idx: usize,
    mod_idx: usize,
    function_index_map: &HashMap<(usize, usize, u32), u32>,
    out: &mut std::collections::BTreeMap<u32, String>,
) {
    let reader = wasmparser::NameSectionReader::new(wasmparser::BinaryReader::new(data, 0));
    for subsection in reader {
        let Ok(subsection) = subsection else {
            return; // malformed — never guess
        };
        if let wasmparser::Name::Function(namemap) = subsection {
            for naming in namemap {
                let Ok(naming) = naming else { continue };
                if let Some(&fused) = function_index_map.get(&(comp_idx, mod_idx, naming.index)) {
                    out.insert(fused, naming.name.to_string());
                }
            }
        }
    }
}
