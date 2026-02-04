//! Module merging for component fusion
//!
//! This module handles combining multiple core modules into a single module,
//! reindexing all references (functions, tables, memories, globals).

use crate::parser::{
    CoreModule, ExportKind, GlobalType, ImportKind, MemoryType,
    ParsedComponent, TableType,
};
use crate::resolver::DependencyGraph;
use crate::{Error, MemoryStrategy, Result};
use std::collections::HashMap;
use wasm_encoder::{
    ConstExpr, EntityType, ExportKind as EncoderExportKind,
    Function, GlobalType as EncoderGlobalType, MemoryType as EncoderMemoryType,
    RefType, TableType as EncoderTableType, ValType,
};

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

    /// Element segments (raw bytes for now)
    pub elements: Vec<Vec<u8>>,

    /// Data segments (raw bytes for now)
    pub data_segments: Vec<Vec<u8>>,

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
}

impl Merger {
    /// Create a new merger with the specified memory strategy
    pub fn new(memory_strategy: MemoryStrategy) -> Self {
        Self { memory_strategy }
    }

    /// Merge components into a single module
    pub fn merge(
        &self,
        components: &[ParsedComponent],
        graph: &DependencyGraph,
    ) -> Result<MergedModule> {
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
        };

        // Process components in topological order
        for &comp_idx in &graph.instantiation_order {
            let component = &components[comp_idx];
            self.merge_component(comp_idx, component, graph, &mut merged)?;
        }

        // Handle unresolved imports
        self.add_unresolved_imports(graph, &mut merged)?;

        // Handle start functions
        self.resolve_start_functions(components, &mut merged)?;

        Ok(merged)
    }

    /// Merge a single component into the merged module
    fn merge_component(
        &self,
        comp_idx: usize,
        component: &ParsedComponent,
        graph: &DependencyGraph,
        merged: &mut MergedModule,
    ) -> Result<()> {
        for (mod_idx, module) in component.core_modules.iter().enumerate() {
            self.merge_core_module(comp_idx, mod_idx, module, graph, merged)?;
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
        let mem_offset = merged.memories.len() as u32;
        for (old_idx, mem) in module.memories.iter().enumerate() {
            let new_idx = mem_offset + old_idx as u32;
            merged.memory_index_map.insert(
                (comp_idx, mod_idx, import_mem_count + old_idx as u32),
                new_idx,
            );
            merged.memories.push(convert_memory_type(mem));
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

        // Merge functions
        let func_offset = merged.functions.len() as u32;
        for (old_idx, &type_idx) in module.functions.iter().enumerate() {
            let new_func_idx = func_offset + old_idx as u32;
            let old_func_idx = import_func_count + old_idx as u32;

            merged.function_index_map.insert(
                (comp_idx, mod_idx, old_func_idx),
                new_func_idx,
            );

            // Get the remapped type index
            let new_type_idx = *merged.type_index_map
                .get(&(comp_idx, mod_idx, type_idx))
                .ok_or_else(|| Error::IndexOutOfBounds {
                    kind: "type",
                    index: type_idx,
                    max: module.types.len() as u32,
                })?;

            // Create function body
            // In a real implementation, we would extract and rewrite the actual bytecode
            // For now, create a placeholder that will be filled in by actual parsing
            let body = extract_function_body(module, old_idx)?;

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
                    let new_idx = *merged.function_index_map
                        .get(&(comp_idx, mod_idx, export.index))
                        .unwrap_or(&export.index);
                    (EncoderExportKind::Func, new_idx)
                }
                ExportKind::Table => {
                    let new_idx = *merged.table_index_map
                        .get(&(comp_idx, mod_idx, export.index))
                        .unwrap_or(&export.index);
                    (EncoderExportKind::Table, new_idx)
                }
                ExportKind::Memory => {
                    let new_idx = *merged.memory_index_map
                        .get(&(comp_idx, mod_idx, export.index))
                        .unwrap_or(&export.index);
                    (EncoderExportKind::Memory, new_idx)
                }
                ExportKind::Global => {
                    let new_idx = *merged.global_index_map
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

        // Merge custom sections
        for (name, data) in &module.custom_sections {
            merged.custom_sections.push((name.clone(), data.clone()));
        }

        Ok(())
    }

    /// Add remaining unresolved imports
    fn add_unresolved_imports(
        &self,
        graph: &DependencyGraph,
        merged: &mut MergedModule,
    ) -> Result<()> {
        for unresolved in &graph.unresolved_imports {
            let entity_type = match &unresolved.kind {
                ImportKind::Function(type_idx) => {
                    // Remap type index
                    let new_type_idx = *merged.type_index_map
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
                    if let Some(&new_idx) = merged.function_index_map
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
        minimum: table.initial as u64,
        maximum: table.maximum.map(|m| m as u64),
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

/// Extract function body from module bytes
/// In a real implementation, this would parse the code section
fn extract_function_body(_module: &CoreModule, _func_idx: usize) -> Result<Function> {
    // For now, create an empty function body
    // Real implementation would:
    // 1. Parse the code section from module.bytes
    // 2. Rewrite all indices (functions, globals, tables, memories)
    // 3. Return the rewritten function
    let mut func = Function::new([]);
    func.instruction(&wasm_encoder::Instruction::Unreachable);
    func.instruction(&wasm_encoder::Instruction::End);
    Ok(func)
}

impl Default for Merger {
    fn default() -> Self {
        Self::new(MemoryStrategy::SharedMemory)
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
}
