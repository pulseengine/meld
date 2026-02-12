//! Module merging for component fusion
//!
//! This module handles combining multiple core modules into a single module,
//! reindexing all references (functions, tables, memories, globals).

// Allow nested ifs for Bazel compatibility (rules_rust doesn't support if-let chains yet)
#![allow(clippy::collapsible_if)]

use crate::parser::{
    CoreModule, ExportKind, GlobalType, ImportKind, MemoryType, ParsedComponent, TableType,
};
use crate::resolver::DependencyGraph;
use crate::rewriter::{IndexMaps, rewrite_function_body};
use crate::{Error, MemoryStrategy, Result};
use std::collections::HashMap;
use wasm_encoder::{
    ConstExpr, EntityType, ExportKind as EncoderExportKind, Function,
    GlobalType as EncoderGlobalType, MemoryType as EncoderMemoryType, RefType,
    TableType as EncoderTableType, ValType,
};

const WASM_PAGE_SIZE: u64 = 65536;

/// A merged WebAssembly module ready for encoding
#[derive(Debug, Clone)]
pub struct MergedModule {
    /// Merged type section
    pub types: Vec<MergedFuncType>,

    /// Remaining imports (unresolved)
    pub imports: Vec<MergedImport>,

    /// Merged functions
    pub functions: Vec<MergedFunction>,

    /// Merged tables
    pub tables: Vec<EncoderTableType>,

    /// Merged memories
    pub memories: Vec<EncoderMemoryType>,

    /// Merged globals
    pub globals: Vec<MergedGlobal>,

    /// Merged exports
    pub exports: Vec<MergedExport>,

    /// Start function index (if any)
    pub start_function: Option<u32>,

    /// Element segments (parsed and reindexed)
    pub elements: Vec<crate::segments::ReindexedElementSegment>,

    /// Data segments (parsed and reindexed)
    pub data_segments: Vec<crate::segments::ReindexedDataSegment>,

    /// Custom sections
    pub custom_sections: Vec<(String, Vec<u8>)>,

    /// Index mapping for function references
    pub function_index_map: HashMap<(usize, usize, u32), u32>,

    /// Index mapping for memory references
    pub memory_index_map: HashMap<(usize, usize, u32), u32>,

    /// Index mapping for table references
    pub table_index_map: HashMap<(usize, usize, u32), u32>,

    /// Index mapping for global references
    pub global_index_map: HashMap<(usize, usize, u32), u32>,

    /// Index mapping for type references
    pub type_index_map: HashMap<(usize, usize, u32), u32>,

    /// Merged index of each module's cabi_realloc function, if exported
    /// Maps (component_idx, module_idx) -> merged function index
    pub realloc_map: HashMap<(usize, usize), u32>,
}

/// Function type in merged module
#[derive(Debug, Clone)]
pub struct MergedFuncType {
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
}

/// Import in merged module
#[derive(Debug, Clone)]
pub struct MergedImport {
    pub module: String,
    pub name: String,
    pub entity_type: EntityType,
}

/// Function in merged module
#[derive(Debug, Clone)]
pub struct MergedFunction {
    /// Type index in merged type section
    pub type_idx: u32,
    /// Function body
    pub body: Function,
    /// Original location (component_idx, module_idx, function_idx)
    pub origin: (usize, usize, u32),
}

/// Global in merged module
#[derive(Debug, Clone)]
pub struct MergedGlobal {
    pub ty: EncoderGlobalType,
    pub init_expr: ConstExpr,
}

/// Export in merged module
#[derive(Debug, Clone)]
pub struct MergedExport {
    pub name: String,
    pub kind: EncoderExportKind,
    pub index: u32,
}

/// Module merger
pub struct Merger {
    memory_strategy: MemoryStrategy,
    address_rebasing: bool,
}

#[derive(Debug, Clone)]
struct SharedMemoryPlan {
    memory: EncoderMemoryType,
    import: Option<(String, String)>,
    bases: HashMap<(usize, usize), u64>,
}

impl Merger {
    /// Create a new merger with the specified memory strategy
    pub fn new(memory_strategy: MemoryStrategy, address_rebasing: bool) -> Self {
        Self {
            memory_strategy,
            address_rebasing,
        }
    }

    fn compute_shared_memory_plan(
        &self,
        components: &[ParsedComponent],
    ) -> Result<Option<SharedMemoryPlan>> {
        let mut memory_types = Vec::new();
        let mut import_names: Vec<(String, String)> = Vec::new();
        let mut has_defined = false;
        let mut module_memories: Vec<((usize, usize), MemoryType)> = Vec::new();

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
                        module_memories.push(((comp_idx, mod_idx), module_memory));
                    }
                }
            }
        }

        if memory_types.is_empty() {
            return Ok(None);
        }

        let combined = if self.address_rebasing {
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
            let mut next_base_pages: u64 = 0;
            for (key, module_memory) in module_memories {
                let base_pages = next_base_pages;
                let base_bytes = base_pages.checked_mul(WASM_PAGE_SIZE).ok_or_else(|| {
                    Error::MemoryStrategyUnsupported(
                        "shared memory base offset overflow".to_string(),
                    )
                })?;
                if !combined.memory64 && base_bytes > u64::from(u32::MAX) {
                    return Err(Error::MemoryStrategyUnsupported(
                        "shared memory base offset exceeds 32-bit address space".to_string(),
                    ));
                }
                bases.insert(key, base_bytes);
                next_base_pages = next_base_pages
                    .checked_add(module_memory.initial)
                    .ok_or_else(|| {
                        Error::MemoryStrategyUnsupported("shared memory size overflow".to_string())
                    })?;
            }
        }

        Ok(Some(SharedMemoryPlan {
            memory: convert_memory_type(&combined),
            import,
            bases,
        }))
    }

    /// Merge components into a single module
    pub fn merge(
        &self,
        components: &[ParsedComponent],
        graph: &DependencyGraph,
    ) -> Result<MergedModule> {
        let shared_memory_plan = if self.memory_strategy == MemoryStrategy::SharedMemory {
            self.compute_shared_memory_plan(components)?
        } else {
            None
        };

        let mut merged = MergedModule {
            types: Vec::new(),
            imports: Vec::new(),
            functions: Vec::new(),
            tables: Vec::new(),
            memories: Vec::new(),
            globals: Vec::new(),
            exports: Vec::new(),
            start_function: None,
            elements: Vec::new(),
            data_segments: Vec::new(),
            custom_sections: Vec::new(),
            function_index_map: HashMap::new(),
            memory_index_map: HashMap::new(),
            table_index_map: HashMap::new(),
            global_index_map: HashMap::new(),
            type_index_map: HashMap::new(),
            realloc_map: HashMap::new(),
        };

        // Process components in topological order
        for &comp_idx in &graph.instantiation_order {
            let component = &components[comp_idx];
            self.merge_component(
                comp_idx,
                component,
                graph,
                &mut merged,
                shared_memory_plan.as_ref(),
            )?;
        }

        // Handle unresolved imports
        self.add_unresolved_imports(graph, &mut merged, shared_memory_plan.as_ref())?;

        // Handle start functions
        self.resolve_start_functions(components, &mut merged)?;

        if let Some(plan) = shared_memory_plan {
            if plan.import.is_none() {
                merged.memories.clear();
                merged.memories.push(plan.memory);
            } else {
                merged.memories.clear();
            }
        }

        Ok(merged)
    }

    /// Merge a single component into the merged module
    fn merge_component(
        &self,
        comp_idx: usize,
        component: &ParsedComponent,
        graph: &DependencyGraph,
        merged: &mut MergedModule,
        shared_memory_plan: Option<&SharedMemoryPlan>,
    ) -> Result<()> {
        for (mod_idx, module) in component.core_modules.iter().enumerate() {
            self.merge_core_module(comp_idx, mod_idx, module, graph, merged, shared_memory_plan)?;
        }

        Ok(())
    }

    /// Merge a single core module
    fn merge_core_module(
        &self,
        comp_idx: usize,
        mod_idx: usize,
        module: &CoreModule,
        _graph: &DependencyGraph,
        merged: &mut MergedModule,
        shared_memory_plan: Option<&SharedMemoryPlan>,
    ) -> Result<()> {
        // Merge types
        let type_offset = merged.types.len() as u32;
        for (old_idx, ty) in module.types.iter().enumerate() {
            merged.type_index_map.insert(
                (comp_idx, mod_idx, old_idx as u32),
                type_offset + old_idx as u32,
            );
            merged.types.push(MergedFuncType {
                params: ty.params.clone(),
                results: ty.results.clone(),
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
            let mem_offset = merged.memories.len() as u32;
            for (old_idx, mem) in module.memories.iter().enumerate() {
                let new_idx = mem_offset + old_idx as u32;
                merged.memory_index_map.insert(
                    (comp_idx, mod_idx, import_mem_count + old_idx as u32),
                    new_idx,
                );
                merged.memories.push(convert_memory_type(mem));
            }
        }

        // Merge tables
        let table_offset = merged.tables.len() as u32;
        for (old_idx, table) in module.tables.iter().enumerate() {
            let new_idx = table_offset + old_idx as u32;
            merged.table_index_map.insert(
                (comp_idx, mod_idx, import_table_count + old_idx as u32),
                new_idx,
            );
            merged.tables.push(convert_table_type(table));
        }

        // Merge globals
        let global_offset = merged.globals.len() as u32;
        for (old_idx, global) in module.globals.iter().enumerate() {
            let new_idx = global_offset + old_idx as u32;
            merged.global_index_map.insert(
                (comp_idx, mod_idx, import_global_count + old_idx as u32),
                new_idx,
            );
            // Create a placeholder init expression
            // Real implementation would parse from module bytes
            let init_expr = create_global_init(&global.content_type);
            merged.globals.push(MergedGlobal {
                ty: convert_global_type(global),
                init_expr,
            });
        }

        // First pass: build all function index mappings
        let func_offset = merged.functions.len() as u32;
        let mut func_type_indices = Vec::new();

        for (old_idx, &type_idx) in module.functions.iter().enumerate() {
            let new_func_idx = func_offset + old_idx as u32;
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
        let index_maps = build_index_maps_for_module(
            comp_idx,
            mod_idx,
            module,
            merged,
            self.memory_strategy,
            self.address_rebasing,
            memory_base_offset,
            memory64,
            memory_initial_pages,
        );

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

            // Check for duplicate exports
            if merged.exports.iter().any(|e| e.name == export.name) {
                // Skip duplicate exports (could also error or prefix)
                log::warn!("Skipping duplicate export: {}", export.name);
                continue;
            }

            merged.exports.push(MergedExport {
                name: export.name.clone(),
                kind,
                index: old_idx,
            });
        }

        // Detect cabi_realloc export for adapter generation
        for export in &module.exports {
            if export.name == "cabi_realloc" && export.kind == ExportKind::Function {
                if let Some(&merged_idx) =
                    merged
                        .function_index_map
                        .get(&(comp_idx, mod_idx, export.index))
                {
                    merged.realloc_map.insert((comp_idx, mod_idx), merged_idx);
                    log::debug!(
                        "Found cabi_realloc in component {} module {}: merged idx {}",
                        comp_idx,
                        mod_idx,
                        merged_idx
                    );
                }
            }
        }

        // Merge custom sections
        for (name, data) in &module.custom_sections {
            merged.custom_sections.push((name.clone(), data.clone()));
        }

        // Parse and merge element segments with reindexing
        let element_segments = crate::segments::parse_element_segments(module)?;
        for segment in element_segments {
            let reindexed = crate::segments::reindex_element_segment(&segment, &index_maps);
            merged.elements.push(reindexed);
        }

        // Parse and merge data segments with reindexing
        let data_segments = crate::segments::parse_data_segments(module)?;
        for segment in data_segments {
            let reindexed = crate::segments::reindex_data_segment(&segment, &index_maps)?;
            merged.data_segments.push(reindexed);
        }

        Ok(())
    }

    /// Add remaining unresolved imports
    fn add_unresolved_imports(
        &self,
        graph: &DependencyGraph,
        merged: &mut MergedModule,
        shared_memory_plan: Option<&SharedMemoryPlan>,
    ) -> Result<()> {
        let mut shared_memory_import_added = false;

        for unresolved in &graph.unresolved_imports {
            if let (Some(plan), ImportKind::Memory(_)) = (shared_memory_plan, &unresolved.kind) {
                if let Some((module, name)) = &plan.import {
                    if !shared_memory_import_added {
                        merged.imports.push(MergedImport {
                            module: module.clone(),
                            name: name.clone(),
                            entity_type: EntityType::Memory(plan.memory),
                        });
                        shared_memory_import_added = true;
                    }
                }
                continue;
            }

            let entity_type = match &unresolved.kind {
                ImportKind::Function(type_idx) => {
                    // Remap type index
                    let new_type_idx = *merged
                        .type_index_map
                        .get(&(unresolved.component_idx, unresolved.module_idx, *type_idx))
                        .unwrap_or(type_idx);
                    EntityType::Function(new_type_idx)
                }
                ImportKind::Table(t) => EntityType::Table(convert_table_type(t)),
                ImportKind::Memory(m) => EntityType::Memory(convert_memory_type(m)),
                ImportKind::Global(g) => EntityType::Global(convert_global_type(g)),
            };

            merged.imports.push(MergedImport {
                module: unresolved.module_name.clone(),
                name: unresolved.field_name.clone(),
                entity_type,
            });
        }

        if let Some(plan) = shared_memory_plan {
            if let Some((module, name)) = &plan.import {
                if !shared_memory_import_added {
                    merged.imports.push(MergedImport {
                        module: module.clone(),
                        name: name.clone(),
                        entity_type: EntityType::Memory(plan.memory),
                    });
                }
            }
        }

        Ok(())
    }

    /// Resolve start functions from multiple components
    fn resolve_start_functions(
        &self,
        components: &[ParsedComponent],
        merged: &mut MergedModule,
    ) -> Result<()> {
        // Collect all start functions
        let mut start_funcs = Vec::new();
        for (comp_idx, component) in components.iter().enumerate() {
            for (mod_idx, module) in component.core_modules.iter().enumerate() {
                if let Some(start_idx) = module.start {
                    if let Some(&new_idx) = merged
                        .function_index_map
                        .get(&(comp_idx, mod_idx, start_idx))
                    {
                        start_funcs.push(new_idx);
                    }
                }
            }
        }

        // If exactly one start function, use it
        // If multiple, we'd need to generate a wrapper that calls all of them
        if start_funcs.len() == 1 {
            merged.start_function = Some(start_funcs[0]);
        } else if start_funcs.len() > 1 {
            // TODO: Generate a start wrapper that calls all start functions in order
            log::warn!("Multiple start functions found, using first one");
            merged.start_function = Some(start_funcs[0]);
        }

        Ok(())
    }
}

fn module_memory_type(module: &CoreModule) -> Result<Option<MemoryType>> {
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

fn combine_memory_types_shared(memories: &[MemoryType]) -> Result<MemoryType> {
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

fn combine_memory_types_rebased(memories: &[MemoryType]) -> Result<MemoryType> {
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
fn convert_memory_type(mem: &MemoryType) -> EncoderMemoryType {
    EncoderMemoryType {
        minimum: mem.initial,
        maximum: mem.maximum,
        memory64: mem.memory64,
        shared: mem.shared,
        page_size_log2: None,
    }
}

/// Convert parser TableType to encoder TableType
fn convert_table_type(table: &TableType) -> EncoderTableType {
    EncoderTableType {
        element_type: match table.element_type {
            ValType::Ref(rt) => rt,
            _ => RefType::FUNCREF,
        },
        table64: false,
        minimum: table.initial,
        maximum: table.maximum,
        shared: false,
    }
}

/// Convert parser GlobalType to encoder GlobalType
fn convert_global_type(global: &GlobalType) -> EncoderGlobalType {
    EncoderGlobalType {
        val_type: global.content_type,
        mutable: global.mutable,
        shared: false,
    }
}

/// Build IndexMaps for a module from the merger's index maps
///
/// This creates a local view of index remappings for a specific module,
/// which is used when rewriting function bodies.
#[allow(clippy::too_many_arguments)]
fn build_index_maps_for_module(
    comp_idx: usize,
    mod_idx: usize,
    module: &CoreModule,
    merged: &MergedModule,
    memory_strategy: MemoryStrategy,
    address_rebasing: bool,
    memory_base_offset: u64,
    memory64: bool,
    memory_initial_pages: Option<u64>,
) -> IndexMaps {
    let mut maps = IndexMaps::new();
    maps.address_rebasing = address_rebasing;
    maps.memory_base_offset = memory_base_offset;
    maps.memory64 = memory64;
    maps.memory_initial_pages = memory_initial_pages;

    // Build function map (including imported functions)
    let import_func_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Function(_)))
        .count() as u32;

    // Map imported functions (they're resolved elsewhere, map to self for now)
    for i in 0..import_func_count {
        if let Some(&new_idx) = merged.function_index_map.get(&(comp_idx, mod_idx, i)) {
            maps.functions.insert(i, new_idx);
        }
    }

    // Map defined functions
    for old_idx in 0..module.functions.len() as u32 {
        let full_idx = import_func_count + old_idx;
        if let Some(&new_idx) = merged
            .function_index_map
            .get(&(comp_idx, mod_idx, full_idx))
        {
            maps.functions.insert(full_idx, new_idx);
        }
    }

    // Build type map
    for old_idx in 0..module.types.len() as u32 {
        if let Some(&new_idx) = merged.type_index_map.get(&(comp_idx, mod_idx, old_idx)) {
            maps.types.insert(old_idx, new_idx);
        }
    }

    // Build global map
    let import_global_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Global(_)))
        .count() as u32;

    for old_idx in 0..module.globals.len() as u32 {
        let full_idx = import_global_count + old_idx;
        if let Some(&new_idx) = merged.global_index_map.get(&(comp_idx, mod_idx, full_idx)) {
            maps.globals.insert(full_idx, new_idx);
        }
    }

    // Build table map
    let import_table_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Table(_)))
        .count() as u32;

    for old_idx in 0..module.tables.len() as u32 {
        let full_idx = import_table_count + old_idx;
        if let Some(&new_idx) = merged.table_index_map.get(&(comp_idx, mod_idx, full_idx)) {
            maps.tables.insert(full_idx, new_idx);
        }
    }

    // Build memory map
    let import_mem_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Memory(_)))
        .count() as u32;

    let total_memories = import_mem_count + module.memories.len() as u32;
    if memory_strategy == MemoryStrategy::SharedMemory {
        for idx in 0..total_memories {
            maps.memories.insert(idx, 0);
        }
    } else {
        for old_idx in 0..module.memories.len() as u32 {
            let full_idx = import_mem_count + old_idx;
            if let Some(&new_idx) = merged.memory_index_map.get(&(comp_idx, mod_idx, full_idx)) {
                maps.memories.insert(full_idx, new_idx);
            }
        }
    }

    maps
}

/// Create a default global initializer expression
fn create_global_init(val_type: &ValType) -> ConstExpr {
    match val_type {
        ValType::I32 => ConstExpr::i32_const(0),
        ValType::I64 => ConstExpr::i64_const(0),
        ValType::F32 => ConstExpr::f32_const(0.0),
        ValType::F64 => ConstExpr::f64_const(0.0),
        ValType::V128 => ConstExpr::v128_const(0),
        ValType::Ref(rt) => ConstExpr::ref_null(rt.heap_type),
    }
}

/// Extract and rewrite function body from module bytes
///
/// This function:
/// 1. Parses the code section from the module bytes
/// 2. Finds the function body at the specified index
/// 3. Rewrites all index references using the provided maps
fn extract_function_body(
    module: &CoreModule,
    func_idx: usize,
    param_count: u32,
    maps: &IndexMaps,
) -> Result<Function> {
    // If no code section, return an unreachable function
    let Some((start, end)) = module.code_section_range else {
        let mut func = Function::new([]);
        func.instruction(&wasm_encoder::Instruction::Unreachable);
        func.instruction(&wasm_encoder::Instruction::End);
        return Ok(func);
    };

    // Parse the code section to find the function body
    let code_bytes = &module.bytes[start..end];
    let binary_reader = wasmparser::BinaryReader::new(code_bytes, 0);
    let reader = wasmparser::CodeSectionReader::new(binary_reader)?;

    let mut current_func_idx = 0;
    for body in reader {
        let body = body?;
        if current_func_idx == func_idx {
            // Found the function - rewrite it with the index maps
            return rewrite_function_body(&body, param_count, maps);
        }
        current_func_idx += 1;
    }

    // Function not found - return unreachable
    Err(Error::IndexOutOfBounds {
        kind: "function",
        index: func_idx as u32,
        max: current_func_idx as u32,
    })
}

impl Default for Merger {
    fn default() -> Self {
        Self::new(MemoryStrategy::SharedMemory, false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_convert_memory_type() {
        let mem = MemoryType {
            memory64: false,
            shared: false,
            initial: 1,
            maximum: Some(10),
        };
        let converted = convert_memory_type(&mem);
        assert_eq!(converted.minimum, 1);
        assert_eq!(converted.maximum, Some(10));
        assert!(!converted.memory64);
        assert!(!converted.shared);
    }

    #[test]
    fn test_create_global_init() {
        let expr = create_global_init(&ValType::I32);
        // The expression should be valid (we can't easily inspect it)
        let _ = expr;

        let expr = create_global_init(&ValType::F64);
        let _ = expr;
    }

    #[test]
    fn test_combine_memory_types_rebased() {
        let mem_a = MemoryType {
            memory64: false,
            shared: false,
            initial: 2,
            maximum: Some(5),
        };
        let mem_b = MemoryType {
            memory64: false,
            shared: false,
            initial: 3,
            maximum: Some(7),
        };

        let combined = combine_memory_types_rebased(&[mem_a, mem_b]).unwrap();
        assert_eq!(combined.initial, 5);
        assert_eq!(combined.maximum, Some(12));
    }

    #[test]
    fn test_combine_memory_types_shared() {
        let mem_a = MemoryType {
            memory64: false,
            shared: false,
            initial: 2,
            maximum: Some(10),
        };
        let mem_b = MemoryType {
            memory64: false,
            shared: false,
            initial: 4,
            maximum: Some(8),
        };

        let combined = combine_memory_types_shared(&[mem_a, mem_b]).unwrap();
        assert_eq!(combined.initial, 4);
        assert_eq!(combined.maximum, Some(8));
    }
}
