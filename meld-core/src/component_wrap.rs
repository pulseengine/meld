//! Wrap a fused core module as a P2 component.
//!
//! After fusion, meld outputs a core wasm module with WASI-style import names
//! (e.g., `wasi:io/streams@0.2.6`). This module wraps that core module back
//! into a P2 component that has the same WIT interface as the original input
//! component(s), allowing `wasmtime run` to execute it identically.
//!
//! ## Architecture
//!
//! ```text
//! Fused core module → Component wrapping → P2 Component
//!                                           ├── Replayed type/import sections
//!                                           ├── Stubs module (memory + forwarding funcs)
//!                                           ├── Fused module (memory imported)
//!                                           ├── Fixup module (fills indirect table)
//!                                           ├── canon lower (WASI funcs)
//!                                           ├── Core instances (stubs, fused, fixup)
//!                                           ├── canon lift (exports)
//!                                           └── Component exports
//! ```
//!
//! ### The Memory Problem
//!
//! `canon lower` needs `(memory N)` and `(realloc N)` pointing to a core
//! memory and realloc function. But the fused module defines its own memory
//! internally — we can't instantiate it without first lowering imports, and
//! we can't lower without a memory.
//!
//! **Solution**: An indirect table pattern (same as wit-component):
//! 1. A stubs module provides memory + a funcref table + forwarding functions
//!    that call through the table via `call_indirect`.
//! 2. The fused module is instantiated with stubs as its imports.
//! 3. `canon lower` uses the fused module's real `cabi_realloc`.
//! 4. A fixup module fills the indirect table with the lowered functions.

use crate::merger::{MergedModule, ht_export_suffix};
use crate::parser::{self, ParsedComponent};
use crate::resolver::DependencyGraph;
use crate::{Error, MemoryStrategy, Result};

/// Wrap fused core module bytes as a P2 component.
///
/// Uses depth-0 sections from the original component(s) to reconstruct the
/// component-level type and import declarations, then wires the fused module
/// through stubs + fixup for memory sharing.
pub fn wrap_as_component(
    fused_module: &[u8],
    components: &[ParsedComponent],
    original_components: &[ParsedComponent],
    _graph: &DependencyGraph,
    merged: &MergedModule,
    memory_strategy: MemoryStrategy,
) -> Result<Vec<u8>> {
    // Pick the component with the most depth_0_sections (widest interface).
    // Prefer original (un-flattened) components since flattening may drop
    // the outer shell that carries the depth_0_sections.
    let source = original_components
        .iter()
        .chain(components.iter())
        .max_by_key(|c| c.depth_0_sections.len())
        .ok_or(Error::NoComponents)?;

    // Parse the fused module to extract its imports, exports, and memory info
    let fused_info = parse_fused_module(fused_module)?;

    // Build import_types from each func_import's type_idx
    let import_types: Vec<(Vec<wasm_encoder::ValType>, Vec<wasm_encoder::ValType>)> = fused_info
        .func_imports
        .iter()
        .map(|(_, _, type_idx)| {
            fused_info
                .func_types
                .get(*type_idx as usize)
                .cloned()
                .ok_or_else(|| {
                    Error::EncodingError(format!("import type index {} out of range", type_idx))
                })
        })
        .collect::<Result<_>>()?;

    // Build the stubs module (provides memory + forwarding funcs via indirect table)
    let stubs_bytes = build_stubs_module(&fused_info.memories, &import_types);

    // Build the fixup module (fills indirect table with lowered functions)
    let fixup_bytes = build_fixup_module(&import_types);

    // Build the caller module (invokes deferred start function after fixup)
    let caller_bytes = if fused_info.start_func_export.is_some() {
        Some(build_caller_module())
    } else {
        None
    };

    // Convert fused module: memory definition → memory import from stubs
    // (also strips start section if present — it's deferred to the caller module)
    let modified_fused = convert_memory_to_import(fused_module, &fused_info)?;

    // Assemble the P2 component
    assemble_component(
        source,
        &stubs_bytes,
        &modified_fused,
        &fixup_bytes,
        caller_bytes.as_deref(),
        &fused_info,
        merged,
        memory_strategy,
        components,
    )
}

/// Information extracted from the fused core module.
struct FusedModuleInfo {
    /// Function imports: (module_name, field_name, type_index)
    func_imports: Vec<(String, String, u32)>,
    /// Exports: (name, kind, index)
    exports: Vec<(String, wasmparser::ExternalKind, u32)>,
    /// All memories: (initial_pages, max_pages, memory64)
    memories: Vec<(u64, Option<u64>, bool)>,
    /// Number of function types in the type section
    #[allow(dead_code)]
    type_count: u32,
    /// The function types themselves (params, results)
    func_types: Vec<(Vec<wasm_encoder::ValType>, Vec<wasm_encoder::ValType>)>,
    /// Start section function index (if any)
    start_func: Option<u32>,
    /// If the fused module has a start section, the export name of the start function.
    /// Reactor components (libraries) use `_initialize` as a start function that must
    /// be deferred until after the indirect table is filled.
    start_func_export: Option<String>,
}

/// How a fused module import should be resolved in the P2 wrapper.
#[derive(Debug, Clone)]
enum ImportResolution {
    /// Import resolves to a function on a component import instance.
    /// Used for WASI and other externally-imported interfaces.
    Instance {
        instance_idx: u32,
        func_name: String,
    },
    /// Import requires a locally-defined resource type.
    ///
    /// `[export]`-prefixed modules (e.g., `[export]imports`, `[export]exports`)
    /// provide `canon resource.drop/new/rep` for resources whose lifecycle is
    /// managed by the component model runtime. Non-`[export]` modules that contain
    /// resource drops for internal inter-component resources also use this variant.
    LocalResource {
        /// The canon resource operation: "drop", "new", or "rep"
        operation: ResourceOp,
        /// The resource type name (e.g., "y", "x", "kebab-case")
        resource_name: String,
        /// The `[export]`-stripped module name used to find the dtor export.
        /// For `[export]imports`, this is `"imports"`.
        /// For plain `exports`, this is `"exports"`.
        interface_name: String,
        /// Source component index (reserved for future handle table routing)
        #[allow(dead_code)]
        component_idx: Option<usize>,
    },
    /// Import resolves to a P3 task/async canonical built-in.
    ///
    /// These are emitted as `canon task.return`, `canon context.get`, etc.
    /// They appear in the fused module as imports from `[export]<iface>` modules
    /// (for `[task-return]`) or from `$root` (for runtime builtins like
    /// `[context-get-0]`, `[waitable-set-new]`, etc.).
    TaskBuiltin {
        /// The specific P3 canonical operation to emit.
        op: P3BuiltinOp,
    },
}

/// A canonical resource operation.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ResourceOp {
    Drop,
    New,
    Rep,
}

/// A P3 task/async canonical built-in operation.
///
/// Each variant corresponds to a `canon` instruction in the component model
/// for P3 async primitives. The fused core module imports these as regular
/// functions; the component wrapper re-emits them as canonical operations.
#[derive(Debug, Clone)]
enum P3BuiltinOp {
    /// `canon task.return` — return a result from a lifted async export.
    /// The associated `CanonicalEntry::TaskReturn` from one of the parsed
    /// components provides the result type and options.
    TaskReturn {
        /// `(component_index, canon_index)` into the all_components array
        /// and that component's canonical_functions, for recovering the
        /// result type and options.
        source_location: Option<(usize, usize)>,
    },
    /// `canon task.cancel` — acknowledge cancellation of the current task.
    TaskCancel,
    /// `canon context.get <slot>` — get task-local context slot.
    ContextGet(u32),
    /// `canon context.set <slot>` — set task-local context slot.
    ContextSet(u32),
    /// `canon waitable.join` — add an item to a waitable-set.
    WaitableJoin,
    /// `canon waitable-set.new` — create a waitable-set pseudo-resource.
    WaitableSetNew,
    /// `canon waitable-set.drop` — dispose a waitable-set pseudo-resource.
    WaitableSetDrop,
    /// `canon waitable-set.poll` — non-blocking check on a waitable-set.
    WaitableSetPoll,
    /// `canon backpressure.inc` — increment the backpressure counter.
    BackpressureInc,
    /// `canon backpressure.dec` — decrement the backpressure counter.
    BackpressureDec,
    /// `canon subtask.drop` — drop a completed subtask.
    SubtaskDrop,
}

/// Parse the fused module to extract structural info needed for wrapping.
fn parse_fused_module(bytes: &[u8]) -> Result<FusedModuleInfo> {
    let parser = wasmparser::Parser::new(0);
    let mut func_imports = Vec::new();
    let mut exports = Vec::new();
    let mut memories: Vec<(u64, Option<u64>, bool)> = Vec::new();
    let mut type_count = 0u32;
    let mut func_types = Vec::new();
    let mut start_func: Option<u32> = None;

    for payload in parser.parse_all(bytes) {
        let payload = payload.map_err(|e| Error::ParseError(e.to_string()))?;
        match payload {
            wasmparser::Payload::TypeSection(reader) => {
                type_count = reader.count();
                for rec_group in reader {
                    let rec_group = rec_group.map_err(|e| Error::ParseError(e.to_string()))?;
                    for subtype in rec_group.into_types() {
                        if let wasmparser::CompositeInnerType::Func(ft) =
                            &subtype.composite_type.inner
                        {
                            let params: Vec<_> =
                                ft.params().iter().map(|t| convert_val_type(*t)).collect();
                            let results: Vec<_> =
                                ft.results().iter().map(|t| convert_val_type(*t)).collect();
                            func_types.push((params, results));
                        }
                    }
                }
            }
            wasmparser::Payload::ImportSection(reader) => {
                for imp in reader.into_imports() {
                    let imp = imp.map_err(|e| Error::ParseError(e.to_string()))?;
                    if let wasmparser::TypeRef::Func(type_idx) = imp.ty {
                        func_imports.push((imp.module.to_string(), imp.name.to_string(), type_idx));
                    }
                }
            }
            wasmparser::Payload::MemorySection(reader) => {
                for mem in reader {
                    let mem = mem.map_err(|e| Error::ParseError(e.to_string()))?;
                    memories.push((mem.initial, mem.maximum, mem.memory64));
                }
            }
            wasmparser::Payload::ExportSection(reader) => {
                for exp in reader {
                    let exp = exp.map_err(|e| Error::ParseError(e.to_string()))?;
                    exports.push((exp.name.to_string(), exp.kind, exp.index));
                }
            }
            wasmparser::Payload::StartSection { func, .. } => {
                start_func = Some(func);
            }
            _ => {}
        }
    }

    if memories.is_empty() {
        return Err(Error::EncodingError(
            "fused module has no memory section".to_string(),
        ));
    }
    // If there's a start section, find its export name (or assign a synthetic one)
    let start_func_export = start_func.map(|func_idx| {
        exports
            .iter()
            .find_map(|(name, kind, idx)| {
                if *kind == wasmparser::ExternalKind::Func && *idx == func_idx {
                    Some(name.clone())
                } else {
                    None
                }
            })
            .unwrap_or_else(|| "$meld_start".to_string())
    });

    Ok(FusedModuleInfo {
        func_imports,
        exports,
        memories,
        type_count,
        func_types,
        start_func,
        start_func_export,
    })
}

/// Build a stubs module with forwarding functions that call through an indirect table.
///
/// Each forwarding function pushes all its parameters, then uses `call_indirect`
/// through a funcref table. The table starts empty and gets filled by the fixup
/// module after the fused module is instantiated and `canon lower` can use the
/// real `cabi_realloc`.
///
/// For N imports, the module exports:
/// - `"memory"` — shared linear memory
/// - `"$imports"` — funcref table of size N (only if N > 0)
/// - `"0"` .. `"N-1"` — forwarding functions
fn build_stubs_module(
    all_memories: &[(u64, Option<u64>, bool)],
    import_types: &[(Vec<wasm_encoder::ValType>, Vec<wasm_encoder::ValType>)],
) -> Vec<u8> {
    let (min_pages, max_pages) = if all_memories.is_empty() {
        (1u64, None)
    } else {
        (all_memories[0].0, all_memories[0].1)
    };
    use wasm_encoder::*;

    let n = import_types.len();
    let mut module = Module::new();

    if n > 0 {
        // Deduplicate type signatures → local type indices
        let mut unique_types: Vec<(Vec<ValType>, Vec<ValType>)> = Vec::new();
        let mut type_indices: Vec<u32> = Vec::new();

        for (params, results) in import_types {
            if let Some(idx) = unique_types
                .iter()
                .position(|(p, r)| p == params && r == results)
            {
                type_indices.push(idx as u32);
            } else {
                type_indices.push(unique_types.len() as u32);
                unique_types.push((params.clone(), results.clone()));
            }
        }

        // Type section
        let mut types = TypeSection::new();
        for (params, results) in &unique_types {
            types
                .ty()
                .function(params.iter().copied(), results.iter().copied());
        }
        module.section(&types);

        // Function section: N forwarding functions
        let mut functions = FunctionSection::new();
        for idx in &type_indices {
            functions.function(*idx);
        }
        module.section(&functions);

        // Table section: funcref table of size N
        let mut tables = TableSection::new();
        tables.table(TableType {
            element_type: RefType::FUNCREF,
            minimum: n as u64,
            maximum: Some(n as u64),
            table64: false,
            shared: false,
        });
        module.section(&tables);

        // Memory section — one memory per component
        let mut mem_section = MemorySection::new();
        for (i, &(init, max, m64)) in all_memories.iter().enumerate() {
            if i == 0 {
                mem_section.memory(MemoryType {
                    minimum: min_pages,
                    maximum: max_pages,
                    memory64: m64,
                    shared: false,
                    page_size_log2: None,
                });
            } else {
                mem_section.memory(MemoryType {
                    minimum: init,
                    maximum: max,
                    memory64: m64,
                    shared: false,
                    page_size_log2: None,
                });
            }
        }
        if all_memories.is_empty() {
            mem_section.memory(MemoryType {
                minimum: min_pages,
                maximum: max_pages,
                memory64: false,
                shared: false,
                page_size_log2: None,
            });
        }
        module.section(&mem_section);

        // Export section — all memories + table + forwarding funcs
        let mut exports = ExportSection::new();
        exports.export("memory", ExportKind::Memory, 0);
        for i in 1..all_memories.len() {
            exports.export(&format!("memory${}", i), ExportKind::Memory, i as u32);
        }
        exports.export("$imports", ExportKind::Table, 0);
        for i in 0..n {
            exports.export(&i.to_string(), ExportKind::Func, i as u32);
        }
        module.section(&exports);

        // Code section: N forwarding function bodies
        let mut code = CodeSection::new();
        for i in 0..n {
            let (params, _) = &import_types[i];
            let mut body = Function::new([]);
            // Push all parameters
            for j in 0..params.len() {
                body.instruction(&Instruction::LocalGet(j as u32));
            }
            // Push table slot index and call_indirect
            body.instruction(&Instruction::I32Const(i as i32));
            body.instruction(&Instruction::CallIndirect {
                type_index: type_indices[i],
                table_index: 0,
            });
            body.instruction(&Instruction::End);
            code.function(&body);
        }
        module.section(&code);
    } else {
        // No imports: memories only
        let mut mem_section = MemorySection::new();
        for &(init, max, m64) in all_memories {
            mem_section.memory(MemoryType {
                minimum: init,
                maximum: max,
                memory64: m64,
                shared: false,
                page_size_log2: None,
            });
        }
        if all_memories.is_empty() {
            mem_section.memory(MemoryType {
                minimum: 1,
                maximum: None,
                memory64: false,
                shared: false,
                page_size_log2: None,
            });
        }
        module.section(&mem_section);

        let mut exports = ExportSection::new();
        exports.export("memory", ExportKind::Memory, 0);
        for i in 1..all_memories.len() {
            exports.export(&format!("memory${}", i), ExportKind::Memory, i as u32);
        }
        module.section(&exports);
    }

    module.finish()
}

/// Build a fixup module that fills the indirect table with real lowered functions.
///
/// The fixup module imports the `$imports` table and N functions from module `""`,
/// then uses an active element section to fill `table[0..N-1]` with function refs
/// to the imported (lowered) functions. This runs as a side effect of instantiation.
fn build_fixup_module(
    import_types: &[(Vec<wasm_encoder::ValType>, Vec<wasm_encoder::ValType>)],
) -> Vec<u8> {
    use wasm_encoder::*;

    let n = import_types.len();
    let mut module = Module::new();

    if n == 0 {
        return module.finish();
    }

    // Deduplicate type signatures (same mapping as stubs)
    let mut unique_types: Vec<(Vec<ValType>, Vec<ValType>)> = Vec::new();
    let mut type_indices: Vec<u32> = Vec::new();

    for (params, results) in import_types {
        if let Some(idx) = unique_types
            .iter()
            .position(|(p, r)| p == params && r == results)
        {
            type_indices.push(idx as u32);
        } else {
            type_indices.push(unique_types.len() as u32);
            unique_types.push((params.clone(), results.clone()));
        }
    }

    // Type section
    let mut types = TypeSection::new();
    for (params, results) in &unique_types {
        types
            .ty()
            .function(params.iter().copied(), results.iter().copied());
    }
    module.section(&types);

    // Import section: table + N functions
    let mut imports = ImportSection::new();
    imports.import(
        "",
        "$imports",
        EntityType::Table(TableType {
            element_type: RefType::FUNCREF,
            minimum: n as u64,
            maximum: Some(n as u64),
            table64: false,
            shared: false,
        }),
    );
    for (i, &ty_idx) in type_indices.iter().enumerate() {
        imports.import("", &i.to_string(), EntityType::Function(ty_idx));
    }
    module.section(&imports);

    // Element section: active segment fills table[0..N-1] with imported func refs
    let mut elements = ElementSection::new();
    let func_indices: Vec<u32> = (0..n as u32).collect();
    let offset = ConstExpr::i32_const(0);
    elements.segment(ElementSegment {
        mode: ElementMode::Active {
            table: Some(0),
            offset: &offset,
        },
        elements: Elements::Functions(func_indices.as_slice().into()),
    });
    module.section(&elements);

    module.finish()
}

/// Build a tiny caller module that invokes a single imported function via its start section.
///
/// Used for reactor components where `_initialize` must run after the indirect table
/// is filled. The caller module imports `""."0"` as a `() -> ()` function and uses
/// a wasm start section to call it on instantiation.
fn build_caller_module() -> Vec<u8> {
    use wasm_encoder::*;

    let mut module = Module::new();

    // Type section: () -> ()
    let mut types = TypeSection::new();
    types.ty().function([], []);
    module.section(&types);

    // Import section: one function
    let mut imports = ImportSection::new();
    imports.import("", "0", EntityType::Function(0));
    module.section(&imports);

    // Start section: call import 0
    module.section(&wasm_encoder::StartSection { function_index: 0 });

    module.finish()
}

/// Convert the fused module's first memory definition to a memory import.
///
/// The fused module defines memory 0 internally. To share it with the shim
/// module, we convert that definition to an import from `"meld:shim"`.
/// All memory indices stay the same (memory 0 is still at index 0).
fn convert_memory_to_import(original_bytes: &[u8], info: &FusedModuleInfo) -> Result<Vec<u8>> {
    use wasm_encoder::*;

    let parser = wasmparser::Parser::new(0);
    let mut module = Module::new();

    // We need to add the memory as an import, which means it goes into the
    // import section. The original import section only has function imports.
    // We'll prepend a memory import, which shifts the memory index space
    // (memory 0 = the import) but since the original module only had memory 0
    // defined, everything still references memory 0.
    //
    // IMPORTANT: Memory imports must NOT change function import count, so
    // we add the memory import at the end of the import section (after all
    // function imports). This preserves all function index numbering.

    let mut wrote_imports = false;

    for payload in parser.parse_all(original_bytes) {
        let payload = payload.map_err(|e| Error::ParseError(e.to_string()))?;
        match payload {
            wasmparser::Payload::Version { .. } => {
                // Module header handled by Module::new()
            }
            wasmparser::Payload::TypeSection(reader) => {
                let mut types = TypeSection::new();
                for rec_group in reader {
                    let rec_group = rec_group.map_err(|e| Error::ParseError(e.to_string()))?;
                    for subtype in rec_group.into_types() {
                        if let wasmparser::CompositeInnerType::Func(ft) =
                            &subtype.composite_type.inner
                        {
                            let params: Vec<_> =
                                ft.params().iter().map(|t| convert_val_type(*t)).collect();
                            let results: Vec<_> =
                                ft.results().iter().map(|t| convert_val_type(*t)).collect();
                            types.ty().function(params, results);
                        }
                    }
                }
                module.section(&types);
            }
            wasmparser::Payload::ImportSection(reader) => {
                let mut imports = ImportSection::new();
                // Re-emit all original imports
                for imp in reader.into_imports() {
                    let imp = imp.map_err(|e| Error::ParseError(e.to_string()))?;
                    let entity = convert_type_ref(imp.ty)?;
                    imports.import(imp.module, imp.name, entity);
                }
                // Append ALL memory imports at the end (after all function imports)
                for (i, &(init, max, m64)) in info.memories.iter().enumerate() {
                    let name = if i == 0 {
                        "memory".to_string()
                    } else {
                        format!("memory${}", i)
                    };
                    imports.import(
                        "meld:shim",
                        &name,
                        EntityType::Memory(MemoryType {
                            minimum: init,
                            maximum: max,
                            memory64: m64,
                            shared: false,
                            page_size_log2: None,
                        }),
                    );
                }
                module.section(&imports);
                wrote_imports = true;
            }
            wasmparser::Payload::MemorySection(_reader) => {
                // Skip entire memory section — all memories are now imports
            }
            // For all other sections, copy them raw
            wasmparser::Payload::FunctionSection(reader) => {
                // If there was no import section, add one with all memories
                if !wrote_imports {
                    let mut imports = ImportSection::new();
                    for (i, &(init, max, m64)) in info.memories.iter().enumerate() {
                        let name = if i == 0 {
                            "memory".to_string()
                        } else {
                            format!("memory${}", i)
                        };
                        imports.import(
                            "meld:shim",
                            &name,
                            EntityType::Memory(MemoryType {
                                minimum: init,
                                maximum: max,
                                memory64: m64,
                                shared: false,
                                page_size_log2: None,
                            }),
                        );
                    }
                    module.section(&imports);
                    wrote_imports = true;
                }
                let mut functions = FunctionSection::new();
                for func in reader {
                    let func = func.map_err(|e| Error::ParseError(e.to_string()))?;
                    functions.function(func);
                }
                module.section(&functions);
            }
            wasmparser::Payload::TableSection(reader) => {
                let raw = &original_bytes[reader.range().start..reader.range().end];
                module.section(&RawSection { id: 4, data: raw });
            }
            wasmparser::Payload::GlobalSection(reader) => {
                let raw = &original_bytes[reader.range().start..reader.range().end];
                module.section(&RawSection { id: 6, data: raw });
            }
            wasmparser::Payload::ExportSection(reader) => {
                // Re-encode the export section to optionally add a synthetic export
                // for the start function (if it wasn't already exported)
                let needs_synthetic_start =
                    info.start_func_export.as_deref() == Some("$meld_start");
                if needs_synthetic_start {
                    let mut exports = ExportSection::new();
                    for exp in reader {
                        let exp = exp.map_err(|e| Error::ParseError(e.to_string()))?;
                        let kind = match exp.kind {
                            wasmparser::ExternalKind::Func => ExportKind::Func,
                            wasmparser::ExternalKind::Table => ExportKind::Table,
                            wasmparser::ExternalKind::Memory => ExportKind::Memory,
                            wasmparser::ExternalKind::Global => ExportKind::Global,
                            _ => continue,
                        };
                        exports.export(exp.name, kind, exp.index);
                    }
                    if let Some(start_idx) = info.start_func {
                        exports.export("$meld_start", ExportKind::Func, start_idx);
                    }
                    module.section(&exports);
                } else {
                    let raw = &original_bytes[reader.range().start..reader.range().end];
                    module.section(&RawSection { id: 7, data: raw });
                }
            }
            wasmparser::Payload::StartSection { .. } => {
                // Strip the start section — it will be invoked by a caller module
                // after the indirect table is filled by the fixup module.
            }
            wasmparser::Payload::ElementSection(reader) => {
                let raw = &original_bytes[reader.range().start..reader.range().end];
                module.section(&RawSection { id: 9, data: raw });
            }
            wasmparser::Payload::DataCountSection { count, .. } => {
                module.section(&wasm_encoder::DataCountSection { count });
            }
            wasmparser::Payload::CodeSectionStart { range, .. } => {
                let raw = &original_bytes[range.start..range.end];
                module.section(&RawSection { id: 10, data: raw });
            }
            wasmparser::Payload::DataSection(reader) => {
                let raw = &original_bytes[reader.range().start..reader.range().end];
                module.section(&RawSection { id: 11, data: raw });
            }
            wasmparser::Payload::CustomSection(reader) => {
                module.section(&wasm_encoder::CustomSection {
                    name: std::borrow::Cow::Borrowed(reader.name()),
                    data: std::borrow::Cow::Borrowed(reader.data()),
                });
            }
            _ => {}
        }
    }

    Ok(module.finish())
}

/// Assemble the final P2 component from replayed sections + stubs + fused + fixup + caller.
#[allow(clippy::too_many_arguments)]
fn assemble_component(
    source: &ParsedComponent,
    stubs_bytes: &[u8],
    fused_bytes: &[u8],
    fixup_bytes: &[u8],
    caller_bytes: Option<&[u8]>,
    fused_info: &FusedModuleInfo,
    merged: &MergedModule,
    memory_strategy: MemoryStrategy,
    all_components: &[ParsedComponent],
) -> Result<Vec<u8>> {
    use wasm_encoder::*;

    let mut component = Component::new();
    let n = fused_info.func_imports.len();

    // -----------------------------------------------------------------------
    // 1. Replay depth-0 Type and Import sections from the original component.
    //    These define the component-level instance types and import declarations
    //    that the runtime validates against.
    // -----------------------------------------------------------------------
    for (section_id, data) in &source.depth_0_sections {
        component.section(&RawSection {
            id: *section_id,
            data,
        });
    }

    // -----------------------------------------------------------------------
    // 2. Resolve fused imports to component instances or local resources.
    //
    //    Imports fall into three categories:
    //    A. `[export]`-prefixed modules: local resource table management
    //       (resource.drop/new/rep for component-defined resources)
    //    B. Non-WASI modules with unresolvable resource drops: internal
    //       inter-component resource lifecycle
    //    C. Everything else: WASI and other external imports resolved to
    //       component import instances
    // -----------------------------------------------------------------------
    let instance_map = build_instance_func_map(source);

    let mut import_resolutions: Vec<ImportResolution> = Vec::new();
    for (import_idx, (module_name, field_name, _type_idx)) in
        fused_info.func_imports.iter().enumerate()
    {
        // Look up the source component_idx from the merged import metadata
        let comp_idx = merged
            .imports
            .get(import_idx)
            .and_then(|imp| imp.component_idx);

        // Category A: [export]-prefixed modules provide canon resource operations
        //             OR P3 task built-ins ([task-return], [task-cancel], etc.)
        if let Some(_inner_module) = module_name.strip_prefix("[export]") {
            // Check for P3 task built-in first (before resource ops)
            if let Some(p3_op) = parse_p3_builtin_field(field_name) {
                // For task-return, find the matching source canon entry by
                // comparing the core function type signature. Use the source
                // component index from the merged import metadata to narrow
                // the search.
                let op = match p3_op {
                    P3BuiltinOp::TaskReturn { .. } => {
                        let import_ty = fused_info
                            .func_types
                            .get(*_type_idx as usize)
                            .cloned()
                            .unwrap_or_default();
                        let location =
                            find_task_return_for_import(all_components, comp_idx, &import_ty);
                        P3BuiltinOp::TaskReturn {
                            source_location: location,
                        }
                    }
                    other => other,
                };
                import_resolutions.push(ImportResolution::TaskBuiltin { op });
                continue;
            }

            let inner_module = module_name.strip_prefix("[export]").unwrap();
            let (op, resource_name) = parse_resource_field(field_name).ok_or_else(|| {
                Error::EncodingError(format!(
                    "[export]-prefixed import has unexpected field name: {}::{}",
                    module_name, field_name
                ))
            })?;
            import_resolutions.push(ImportResolution::LocalResource {
                operation: op,
                resource_name,
                interface_name: inner_module.to_string(),
                component_idx: comp_idx,
            });
            continue;
        }

        // Category P3-root: $root-prefixed P3 runtime builtins
        // (e.g., $root::[context-get-0], $root::[waitable-set-new])
        if module_name == "$root"
            && let Some(p3_op) = parse_p3_builtin_field(field_name)
        {
            let op = match p3_op {
                P3BuiltinOp::TaskReturn { .. } => {
                    let import_ty = fused_info
                        .func_types
                        .get(*_type_idx as usize)
                        .cloned()
                        .unwrap_or_default();
                    let location =
                        find_task_return_for_import(all_components, comp_idx, &import_ty);
                    P3BuiltinOp::TaskReturn {
                        source_location: location,
                    }
                }
                other => other,
            };
            import_resolutions.push(ImportResolution::TaskBuiltin { op });
            continue;
        }

        // Category C: try resolving to a component import instance
        if let Some((inst_idx, func_name)) =
            resolve_import_to_instance(source, module_name, field_name, &instance_map)
        {
            import_resolutions.push(ImportResolution::Instance {
                instance_idx: inst_idx,
                func_name,
            });
            continue;
        }

        // Category B: unresolvable resource drop — treat as a local resource
        if let Some((op, resource_name)) = parse_resource_field(field_name)
            && op == ResourceOp::Drop
        {
            import_resolutions.push(ImportResolution::LocalResource {
                operation: op,
                resource_name,
                interface_name: module_name.clone(),
                component_idx: comp_idx,
            });
            continue;
        }

        return Err(Error::EncodingError(format!(
            "cannot resolve fused import {}::{} to a component instance",
            module_name, field_name
        )));
    }

    // -----------------------------------------------------------------------
    // 3. Embed core modules (section ID 1 = CoreModule)
    // -----------------------------------------------------------------------
    // Module 0: stubs (memory + forwarding funcs via indirect table)
    component.section(&RawSection {
        id: 1,
        data: stubs_bytes,
    });
    // Module 1: fused module (memory imported from stubs)
    component.section(&RawSection {
        id: 1,
        data: fused_bytes,
    });
    // Module 2: fixup (fills indirect table on instantiation)
    component.section(&RawSection {
        id: 1,
        data: fixup_bytes,
    });
    // Module 3 (optional): caller (invokes deferred start function)
    let caller_module_idx = if let Some(caller) = caller_bytes {
        component.section(&RawSection {
            id: 1,
            data: caller,
        });
        Some(3u32)
    } else {
        None
    };

    // -----------------------------------------------------------------------
    // 4. Instantiate the stubs module (no imports needed)
    // -----------------------------------------------------------------------
    let mut core_instances = InstanceSection::new();
    let no_args: Vec<(&str, ModuleArg)> = vec![];
    core_instances.instantiate(0, no_args);
    component.section(&core_instances);

    // -----------------------------------------------------------------------
    // 5. Alias stubs exports: forwarding funcs, table, and all memories
    // -----------------------------------------------------------------------
    // core instance 0 = stubs instance
    //
    // After aliasing:
    //   core func 0..N-1     = stubs forwarding functions
    //   core table 0         = indirect funcref table (only if N > 0)
    //   core memory 0..M-1   = per-component memories
    let num_memories = fused_info.memories.len().max(1);
    let mut core_func_idx = 0u32;
    // Track core memory indices for use in canon lower/lift
    let mut memory_core_indices: Vec<u32> = Vec::new();

    if n > 0 {
        let mut aliases = ComponentAliasSection::new();
        for i in 0..n {
            aliases.alias(Alias::CoreInstanceExport {
                instance: 0,
                kind: ExportKind::Func,
                name: &i.to_string(),
            });
        }
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Table,
            name: "$imports",
        });
        // Alias all memories from stubs.
        // Core aliases go into per-kind index spaces, so memory aliases
        // start at core memory 0 regardless of how many func/table aliases exist.
        for i in 0..num_memories {
            let mem_name = if i == 0 {
                "memory".to_string()
            } else {
                format!("memory${}", i)
            };
            aliases.alias(Alias::CoreInstanceExport {
                instance: 0,
                kind: ExportKind::Memory,
                name: &mem_name,
            });
            memory_core_indices.push(i as u32);
        }
        component.section(&aliases);
        core_func_idx = n as u32;
    } else {
        let mut aliases = ComponentAliasSection::new();
        for i in 0..num_memories {
            let mem_name = if i == 0 {
                "memory".to_string()
            } else {
                format!("memory${}", i)
            };
            aliases.alias(Alias::CoreInstanceExport {
                instance: 0,
                kind: ExportKind::Memory,
                name: &mem_name,
            });
            memory_core_indices.push(i as u32);
        }
        component.section(&aliases);
    }

    // -----------------------------------------------------------------------
    // 6. Create FromExports instances for fused module's import namespaces
    //    using the stubs forwarding functions.
    // -----------------------------------------------------------------------
    // Group fused imports by module name
    let mut module_groups: Vec<(String, Vec<(String, u32)>)> = Vec::new();
    for (i, (module_name, field_name, _)) in fused_info.func_imports.iter().enumerate() {
        let core_idx = i as u32; // core func i = stubs forwarding func i
        if let Some(group) = module_groups.iter_mut().find(|(m, _)| m == module_name) {
            group.1.push((field_name.clone(), core_idx));
        } else {
            module_groups.push((module_name.clone(), vec![(field_name.clone(), core_idx)]));
        }
    }

    // Core instance counter: 0 = stubs instance, then 1..M = import instances
    let mut next_core_instance = 1u32;
    let mut module_instance_map: Vec<(String, u32)> = Vec::new();

    for (module_name, fields) in &module_groups {
        let mut inst = InstanceSection::new();
        let exports: Vec<(&str, ExportKind, u32)> = fields
            .iter()
            .map(|(name, idx)| (name.as_str(), ExportKind::Func, *idx))
            .collect();
        inst.export_items(exports);
        component.section(&inst);
        module_instance_map.push((module_name.clone(), next_core_instance));
        next_core_instance += 1;
    }

    // Create a FromExports instance for the "meld:shim" module (all memories)
    {
        let mut inst = InstanceSection::new();
        let mut mem_exports: Vec<(String, ExportKind, u32)> = Vec::new();
        for (i, &core_mem_idx) in memory_core_indices.iter().enumerate() {
            let name = if i == 0 {
                "memory".to_string()
            } else {
                format!("memory${}", i)
            };
            mem_exports.push((name, ExportKind::Memory, core_mem_idx));
        }
        let exports_ref: Vec<(&str, ExportKind, u32)> = mem_exports
            .iter()
            .map(|(n, k, i)| (n.as_str(), *k, *i))
            .collect();
        inst.export_items(exports_ref);
        component.section(&inst);
        module_instance_map.push(("meld:shim".to_string(), next_core_instance));
        next_core_instance += 1;
    }

    // -----------------------------------------------------------------------
    // 7. Instantiate the fused module with stubs as its imports
    // -----------------------------------------------------------------------
    {
        let mut inst = InstanceSection::new();
        let args: Vec<(&str, ModuleArg)> = module_instance_map
            .iter()
            .map(|(name, idx)| (name.as_str(), ModuleArg::Instance(*idx)))
            .collect();
        inst.instantiate(1, args);
        component.section(&inst);
    }
    let fused_instance = next_core_instance;
    next_core_instance += 1;

    // -----------------------------------------------------------------------
    // 8. Alias fused module's cabi_realloc(s) (if we have non-resource-drop imports)
    //
    // In multi-memory mode, each component may have its own cabi_realloc:
    //   - cabi_realloc   (component 0)
    //   - cabi_realloc$1 (component 1)
    //   - cabi_realloc$2 (component 2)
    //   ...
    // We alias all of them and track core func indices per-memory.
    // -----------------------------------------------------------------------
    let has_non_resource_op = fused_info.func_imports.iter().any(|(_, field, _)| {
        !field.starts_with("[resource-drop]")
            && !field.starts_with("[resource-new]")
            && !field.starts_with("[resource-rep]")
            && !is_p3_builtin_field(field)
    });

    // realloc_core_indices[memory_idx] = core func idx of that component's cabi_realloc
    let mut realloc_core_indices: Vec<Option<u32>> = vec![None; num_memories];

    if has_non_resource_op && n > 0 {
        // Alias cabi_realloc for component 0
        let has_realloc = fused_info.exports.iter().any(|(name, kind, _)| {
            *kind == wasmparser::ExternalKind::Func && name == "cabi_realloc"
        });
        if !has_realloc {
            return Err(Error::EncodingError(
                "fused module has non-resource-drop imports but no cabi_realloc export".to_string(),
            ));
        }

        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: fused_instance,
            kind: ExportKind::Func,
            name: "cabi_realloc",
        });
        component.section(&aliases);
        realloc_core_indices[0] = Some(core_func_idx);
        core_func_idx += 1;

        // In multi-memory mode, alias per-component cabi_realloc$N
        if memory_strategy == MemoryStrategy::MultiMemory {
            for i in 1..num_memories {
                let realloc_name = format!("cabi_realloc${}", i);
                let has_it = fused_info.exports.iter().any(|(name, kind, _)| {
                    *kind == wasmparser::ExternalKind::Func && *name == realloc_name
                });
                if has_it {
                    let mut aliases = ComponentAliasSection::new();
                    aliases.alias(Alias::CoreInstanceExport {
                        instance: fused_instance,
                        kind: ExportKind::Func,
                        name: &realloc_name,
                    });
                    component.section(&aliases);
                    realloc_core_indices[i] = Some(core_func_idx);
                    core_func_idx += 1;
                } else {
                    // Fall back to component 0's realloc
                    realloc_core_indices[i] = realloc_core_indices[0];
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // 9. Canon lower / resource operations for ALL imports
    //
    // Three kinds of imports:
    //   a) Instance — alias func from component instance, canon lower
    //   b) Instance resource-drop — alias type from component instance,
    //      canon resource.drop
    //   c) LocalResource — define resource type (with dtor from fused
    //      module), then canon resource.drop/new/rep
    //
    // In multi-memory mode, each regular import uses the memory and
    // cabi_realloc belonging to the component that originally imported it.
    // -----------------------------------------------------------------------
    let mut component_func_idx = 0u32;
    let mut component_type_idx = count_replayed_types(source);
    let mut lowered_func_indices: Vec<u32> = Vec::new();

    // Source type index → wrapper type index mapping (for recursive type defs).
    // Shared between import resolution (P3 task-return types) and export lifting.
    let mut type_remap: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();

    // Cache: resource_name → component type index.
    // All components share one canonical resource type per resource name,
    // regardless of interface. Re-exporters import and export the same
    // resource under different interface names (imports, exports, test:…/test)
    // but must share one wasmtime handle table.
    let mut local_resource_types: std::collections::HashMap<String, u32> =
        std::collections::HashMap::new();

    // Pre-define component function types for async lift/lower imports.
    for (i, resolution) in import_resolutions.iter().enumerate() {
        match resolution {
            ImportResolution::Instance {
                instance_idx,
                func_name,
            } => {
                let field_name = &fused_info.func_imports[i].1;

                if field_name.starts_with("[resource-drop]") {
                    // Resource-drop from an external instance: alias the TYPE
                    // from the instance, then canon resource.drop.
                    let type_name = func_name
                        .strip_prefix("[resource-drop]")
                        .unwrap_or(func_name);
                    let mut alias_section = ComponentAliasSection::new();
                    alias_section.alias(Alias::InstanceExport {
                        instance: *instance_idx,
                        kind: ComponentExportKind::Type,
                        name: type_name,
                    });
                    component.section(&alias_section);

                    let mut canon = CanonicalFunctionSection::new();
                    canon.resource_drop(component_type_idx);
                    component.section(&canon);

                    component_type_idx += 1;
                    lowered_func_indices.push(core_func_idx);
                    core_func_idx += 1;
                } else {
                    // Regular function: alias from instance, then canon lower
                    // with correct memory and realloc for the importing component.
                    let mut alias_section = ComponentAliasSection::new();
                    alias_section.alias(Alias::InstanceExport {
                        instance: *instance_idx,
                        kind: ComponentExportKind::Func,
                        name: func_name,
                    });
                    component.section(&alias_section);

                    let mem_idx = if memory_strategy == MemoryStrategy::MultiMemory {
                        merged.import_memory_indices.get(i).copied().unwrap_or(0) as usize
                    } else {
                        0
                    };

                    let core_mem = memory_core_indices
                        .get(mem_idx)
                        .copied()
                        .unwrap_or(memory_core_indices[0]);

                    let realloc_idx = realloc_core_indices
                        .get(mem_idx)
                        .and_then(|r| *r)
                        .or_else(|| realloc_core_indices[0])
                        .expect("realloc_core_idx must be set for non-resource-drop");

                    let mut canon = CanonicalFunctionSection::new();
                    canon.lower(
                        component_func_idx,
                        [
                            CanonicalOption::Memory(core_mem),
                            CanonicalOption::Realloc(realloc_idx),
                            CanonicalOption::UTF8,
                        ],
                    );
                    component.section(&canon);

                    component_func_idx += 1;
                    lowered_func_indices.push(core_func_idx);
                    core_func_idx += 1;
                }
            }

            ImportResolution::LocalResource {
                operation,
                resource_name,
                interface_name,
                component_idx,
            } => {
                // Check if any component has a handle table export for this
                // (interface, resource) — the export naming is per-(component,
                // interface, resource) so we look first at the importer's own
                // index, then fall back to ANY component that exports a
                // handle table for the same (iface, rn). Consumers (like the
                // runner in a 3-component chain) hold handles allocated by
                // the re-exporter's ht_new and must drop them through that
                // same table — even though they don't own a handle table
                // themselves. See meld-core/src/merger.rs::ht_export_suffix.
                let op_prefix = match operation {
                    ResourceOp::New => "$ht_new_",
                    ResourceOp::Rep => "$ht_rep_",
                    ResourceOp::Drop => "$ht_drop_",
                };
                let ht_export: Option<String> = component_idx
                    .and_then(|cidx| {
                        let suffix = ht_export_suffix(cidx, interface_name, resource_name);
                        let name = format!("{}{}", op_prefix, suffix);
                        fused_info
                            .exports
                            .iter()
                            .find(|(n, k, _)| *k == wasmparser::ExternalKind::Func && *n == name)
                            .map(|_| name)
                    })
                    .or_else(|| {
                        // Resource is owned by a different component (e.g. a
                        // re-exporter); find any handle-table export matching
                        // _<iface_safe>_<rn>.
                        let safe_iface: String = interface_name
                            .chars()
                            .map(|c| match c {
                                ':' | '/' | '@' | '.' | '-' => '_',
                                other => other,
                            })
                            .collect();
                        let tail = format!("_{}_{}", safe_iface, resource_name);
                        fused_info
                            .exports
                            .iter()
                            .find(|(n, k, _)| {
                                *k == wasmparser::ExternalKind::Func
                                    && n.starts_with(op_prefix)
                                    && n.ends_with(&tail)
                            })
                            .map(|(n, _, _)| n.clone())
                    });

                if let Some(ht_name) = ht_export {
                    // Re-exporter: alias the handle table function directly
                    // from the fused instance instead of using canon resource ops.
                    log::debug!(
                        "using ht export {} for {:?} comp {:?}",
                        ht_name,
                        operation,
                        component_idx
                    );
                    let mut aliases = ComponentAliasSection::new();
                    aliases.alias(Alias::CoreInstanceExport {
                        instance: fused_instance,
                        kind: ExportKind::Func,
                        name: &ht_name,
                    });
                    component.section(&aliases);

                    lowered_func_indices.push(core_func_idx);
                    core_func_idx += 1;
                } else {
                    // Standard path: canonical resource operations.
                    let res_type_key = resource_name.clone();
                    let res_type_idx =
                        if let Some(&existing) = local_resource_types.get(&res_type_key) {
                            existing
                        } else {
                            let dtor_export_name =
                                format!("{}#[dtor]{}", interface_name, resource_name);
                            let has_dtor = fused_info.exports.iter().any(|(n, k, _)| {
                                *k == wasmparser::ExternalKind::Func && *n == dtor_export_name
                            });

                            let dtor_core_func = if has_dtor {
                                let mut aliases = ComponentAliasSection::new();
                                aliases.alias(Alias::CoreInstanceExport {
                                    instance: fused_instance,
                                    kind: ExportKind::Func,
                                    name: &dtor_export_name,
                                });
                                component.section(&aliases);
                                let idx = core_func_idx;
                                core_func_idx += 1;
                                Some(idx)
                            } else {
                                None
                            };

                            let mut types = ComponentTypeSection::new();
                            types.ty().resource(ValType::I32, dtor_core_func);
                            component.section(&types);

                            let idx = component_type_idx;
                            component_type_idx += 1;
                            local_resource_types.insert(res_type_key, idx);
                            idx
                        };

                    let mut canon = CanonicalFunctionSection::new();
                    match operation {
                        ResourceOp::Drop => canon.resource_drop(res_type_idx),
                        ResourceOp::New => canon.resource_new(res_type_idx),
                        ResourceOp::Rep => canon.resource_rep(res_type_idx),
                    };
                    component.section(&canon);

                    lowered_func_indices.push(core_func_idx);
                    core_func_idx += 1;
                }
            }

            ImportResolution::TaskBuiltin { op } => {
                // Check if this task.return has a shim export in the fused module.
                // If so, alias the shim instead of using canonical task.return.
                if let P3BuiltinOp::TaskReturn { .. } = op {
                    let shim_name = format!("$task_return_shim_{}", i);
                    let has_shim = fused_info
                        .exports
                        .iter()
                        .any(|(n, k, _)| *k == wasmparser::ExternalKind::Func && *n == shim_name);
                    if has_shim {
                        let mut alias_section = ComponentAliasSection::new();
                        alias_section.alias(Alias::CoreInstanceExport {
                            instance: fused_instance,
                            kind: ExportKind::Func,
                            name: &shim_name,
                        });
                        component.section(&alias_section);
                        lowered_func_indices.push(core_func_idx);
                        core_func_idx += 1;
                        continue;
                    }
                }

                let mut canon = CanonicalFunctionSection::new();
                match op {
                    P3BuiltinOp::TaskReturn {
                        source_location, ..
                    } => {
                        // Recover the result type and options from the matching
                        // component's canonical function entry, if available.
                        let (result_ty, options, source_comp) = source_location
                            .as_ref()
                            .and_then(|(comp_idx, canon_idx)| {
                                let comp = all_components.get(*comp_idx)?;
                                let entry = comp.canonical_functions.get(*canon_idx)?;
                                match entry {
                                    parser::CanonicalEntry::TaskReturn { result, options } => {
                                        Some((result.clone(), options.clone(), Some(comp)))
                                    }
                                    _ => None,
                                }
                            })
                            .unwrap_or_else(|| (None, parser::CanonicalOptions::default(), None));

                        // Use the source component for type resolution if available,
                        // otherwise fall back to the wrapper source component.
                        let type_source = source_comp.unwrap_or(source);
                        let enc_result = result_ty
                            .as_ref()
                            .map(|cvt| {
                                convert_parser_val_to_encoder(
                                    &mut component,
                                    type_source,
                                    cvt,
                                    &mut component_type_idx,
                                    &mut type_remap,
                                )
                            })
                            .transpose()?;

                        let mut enc_options: Vec<CanonicalOption> = Vec::new();
                        if let Some(mem) = options.memory {
                            enc_options
                                .push(CanonicalOption::Memory(memory_core_indices[mem as usize]));
                        }
                        match options.string_encoding {
                            parser::CanonStringEncoding::Utf8 => {
                                enc_options.push(CanonicalOption::UTF8);
                            }
                            parser::CanonStringEncoding::Utf16 => {
                                enc_options.push(CanonicalOption::UTF16);
                            }
                            parser::CanonStringEncoding::CompactUtf16 => {
                                enc_options.push(CanonicalOption::CompactUTF16);
                            }
                        }
                        canon.task_return(enc_result, enc_options);
                    }
                    P3BuiltinOp::TaskCancel => {
                        canon.task_cancel();
                    }
                    P3BuiltinOp::ContextGet(slot) => {
                        canon.context_get(*slot);
                    }
                    P3BuiltinOp::ContextSet(slot) => {
                        canon.context_set(*slot);
                    }
                    P3BuiltinOp::WaitableJoin => {
                        canon.waitable_join();
                    }
                    P3BuiltinOp::WaitableSetNew => {
                        canon.waitable_set_new();
                    }
                    P3BuiltinOp::WaitableSetDrop => {
                        canon.waitable_set_drop();
                    }
                    P3BuiltinOp::WaitableSetPoll => {
                        // waitable-set.poll requires async flag and memory index.
                        // Default: async_=false, memory=0
                        canon.waitable_set_poll(false, memory_core_indices[0]);
                    }
                    P3BuiltinOp::BackpressureInc => {
                        canon.backpressure_inc();
                    }
                    P3BuiltinOp::BackpressureDec => {
                        canon.backpressure_dec();
                    }
                    P3BuiltinOp::SubtaskDrop => {
                        canon.subtask_drop();
                    }
                }
                component.section(&canon);

                lowered_func_indices.push(core_func_idx);
                core_func_idx += 1;
            }
        }
    }

    // -----------------------------------------------------------------------
    // 10. Instantiate the fixup module to fill the indirect table
    // -----------------------------------------------------------------------
    if n > 0 {
        // Create a FromExports instance with the table + lowered functions
        let export_names: Vec<String> = (0..n).map(|i| i.to_string()).collect();
        let mut fixup_exports: Vec<(&str, ExportKind, u32)> = Vec::new();
        fixup_exports.push(("$imports", ExportKind::Table, 0)); // core table 0
        for (i, &idx) in lowered_func_indices.iter().enumerate() {
            fixup_exports.push((&export_names[i], ExportKind::Func, idx));
        }
        let mut inst = InstanceSection::new();
        inst.export_items(fixup_exports);
        component.section(&inst);
        let fixup_exports_instance = next_core_instance;
        next_core_instance += 1;

        // Instantiate fixup module (module 2) — fills the table as a side effect
        let mut fixup_inst = InstanceSection::new();
        fixup_inst.instantiate(2, [("", ModuleArg::Instance(fixup_exports_instance))]);
        component.section(&fixup_inst);
        next_core_instance += 1;
    }

    // -----------------------------------------------------------------------
    // 10b. Instantiate the caller module (invokes deferred start function)
    // -----------------------------------------------------------------------
    if let (Some(start_export_name), Some(caller_mod_idx)) =
        (&fused_info.start_func_export, caller_module_idx)
    {
        // Alias the start function from the fused instance
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: fused_instance,
            kind: ExportKind::Func,
            name: start_export_name,
        });
        component.section(&aliases);
        let start_core_func = core_func_idx;
        core_func_idx += 1;

        // Create a FromExports instance for the caller module
        let mut inst = InstanceSection::new();
        inst.export_items([("0", ExportKind::Func, start_core_func)]);
        component.section(&inst);
        let caller_exports_instance = next_core_instance;
        next_core_instance += 1;

        // Instantiate caller — triggers deferred start function via start section
        let mut caller_inst = InstanceSection::new();
        caller_inst.instantiate(
            caller_mod_idx,
            [("", ModuleArg::Instance(caller_exports_instance))],
        );
        component.section(&caller_inst);
        next_core_instance += 1;
    }
    let _ = next_core_instance; // may be unused after this point

    // -----------------------------------------------------------------------
    // 11. Export: alias core exports, define types, canon lift, wrap in
    //     component instances, and export as named interfaces.
    //
    //    WASI runtimes expect exported interfaces as component instances,
    //    not bare functions. For example, `wasi:cli/run@0.2.6` must be an
    //    instance containing a `run` function.
    //
    //    The fused module exports functions using the naming convention
    //    `<interface>#<function>` (e.g., `wasi:cli/run@0.2.6#run`).
    //    We group these by interface, lift each function, bundle them into
    //    a component instance, and export that instance.
    // -----------------------------------------------------------------------

    // Group fused module exports by interface name (everything before '#')
    let mut interface_exports: std::collections::BTreeMap<String, Vec<ExportFuncInfo>> =
        std::collections::BTreeMap::new();

    for (name, kind, _idx) in &fused_info.exports {
        if *kind == wasmparser::ExternalKind::Func
            && let Some(hash_pos) = name.find('#')
        {
            let interface = name[..hash_pos].to_string();
            let func_name = name[hash_pos + 1..].to_string();
            let post_return_name = format!("cabi_post_{}", name);
            let has_post_return = fused_info
                .exports
                .iter()
                .any(|(n, k, _)| *k == wasmparser::ExternalKind::Func && *n == post_return_name);
            interface_exports
                .entry(interface)
                .or_default()
                .push(ExportFuncInfo {
                    func_name,
                    core_export_name: name.clone(),
                    has_post_return,
                });
        }
    }

    // Track component instance index (starts after import instances)
    let mut component_instance_idx = source
        .imports
        .iter()
        .filter(|imp| matches!(imp.ty, wasmparser::ComponentTypeRef::Instance(_)))
        .count() as u32;

    for comp_export in &source.exports {
        if comp_export.kind != wasmparser::ComponentExternalKind::Instance {
            continue;
        }

        let interface_name = &comp_export.name;
        let funcs = match interface_exports.get(interface_name) {
            Some(f) => f,
            None => continue,
        };

        let mut lifted_funcs: Vec<(String, u32)> = Vec::new();

        for func_info in funcs {
            // Alias the core function from the fused instance
            let mut alias_section = ComponentAliasSection::new();
            alias_section.alias(Alias::CoreInstanceExport {
                instance: fused_instance,
                kind: ExportKind::Func,
                name: &func_info.core_export_name,
            });
            component.section(&alias_section);
            let aliased_core_func = core_func_idx;
            core_func_idx += 1;

            // Optionally alias the post-return cleanup function
            let post_return_core_idx = if func_info.has_post_return {
                let post_name = format!("cabi_post_{}#{}", interface_name, func_info.func_name);
                let mut alias_section = ComponentAliasSection::new();
                alias_section.alias(Alias::CoreInstanceExport {
                    instance: fused_instance,
                    kind: ExportKind::Func,
                    name: &post_name,
                });
                component.section(&alias_section);
                let idx = core_func_idx;
                core_func_idx += 1;
                Some(idx)
            } else {
                None
            };

            // Find the source component's lift type and canonical options for
            // this export function.
            let lift_info =
                find_lift_type_for_interface_func(source, interface_name, &func_info.func_name);

            // Define the component function type in our wrapper
            let wrapper_func_type = if let Some((source_type_idx, _)) = &lift_info {
                define_source_type_in_wrapper(
                    &mut component,
                    source,
                    *source_type_idx,
                    &mut component_type_idx,
                    &mut type_remap,
                )?
            } else {
                // Fallback: define a simple func() -> result type
                define_default_run_type(&mut component, &mut component_type_idx)
            };

            // Canon lift with appropriate options
            let mut lift_options: Vec<CanonicalOption> = Vec::new();
            if func_info.has_post_return {
                // String/list-returning functions need memory + encoding + post-return
                lift_options.push(CanonicalOption::Memory(0)); // shim memory = shared memory
                lift_options.push(CanonicalOption::UTF8);
                if let Some(pr_idx) = post_return_core_idx {
                    lift_options.push(CanonicalOption::PostReturn(pr_idx));
                }
            }
            // Propagate P3 async/callback from source component's canon lift
            if let Some((_, ref source_opts)) = lift_info {
                if source_opts.async_ {
                    lift_options.push(CanonicalOption::Async);
                    // async requires memory
                    if !lift_options
                        .iter()
                        .any(|o| matches!(o, CanonicalOption::Memory(_)))
                    {
                        lift_options.push(CanonicalOption::Memory(0));
                    }
                    if !lift_options.iter().any(|o| {
                        matches!(
                            o,
                            CanonicalOption::UTF8
                                | CanonicalOption::UTF16
                                | CanonicalOption::CompactUTF16
                        )
                    }) {
                        lift_options.push(CanonicalOption::UTF8);
                    }
                }
                if source_opts.callback.is_some() {
                    // Callback function is exported from the fused module as
                    // [callback][async-lift]<interface>#<func>
                    let cb_name = format!(
                        "[callback][async-lift]{}#{}",
                        interface_name, func_info.func_name
                    );
                    let mut alias_section = ComponentAliasSection::new();
                    alias_section.alias(Alias::CoreInstanceExport {
                        instance: fused_instance,
                        kind: ExportKind::Func,
                        name: &cb_name,
                    });
                    component.section(&alias_section);
                    lift_options.push(CanonicalOption::Callback(core_func_idx));
                    core_func_idx += 1;
                }
            }

            let mut canon = CanonicalFunctionSection::new();
            canon.lift(aliased_core_func, wrapper_func_type, lift_options);
            component.section(&canon);

            lifted_funcs.push((func_info.func_name.clone(), component_func_idx));
            component_func_idx += 1;
        }

        // Create a component instance wrapping the lifted functions
        let mut inst = ComponentInstanceSection::new();
        let exports: Vec<_> = lifted_funcs
            .iter()
            .map(|(name, idx)| (name.as_str(), ComponentExportKind::Func, *idx))
            .collect();
        inst.export_items(exports);
        component.section(&inst);

        // Export the component instance as the interface name
        let mut exp = ComponentExportSection::new();
        exp.export(
            interface_name,
            ComponentExportKind::Instance,
            component_instance_idx,
            None,
        );
        component.section(&exp);
        component_instance_idx += 1;
    }

    // Handle bare function exports (e.g., "run" without an interface wrapper).
    // These are exported as ComponentExternalKind::Func in the source component
    // and appear as plain names (no '#' separator) in the fused core module.
    for comp_export in &source.exports {
        if comp_export.kind != wasmparser::ComponentExternalKind::Func {
            continue;
        }

        let func_name = &comp_export.name;

        // Check that the fused module actually exports this function
        let has_export = fused_info
            .exports
            .iter()
            .any(|(n, k, _)| *k == wasmparser::ExternalKind::Func && n == func_name);
        if !has_export {
            continue;
        }

        // Alias the core function from the fused instance
        let mut alias_section = ComponentAliasSection::new();
        alias_section.alias(Alias::CoreInstanceExport {
            instance: fused_instance,
            kind: ExportKind::Func,
            name: func_name,
        });
        component.section(&alias_section);
        let aliased_core_func = core_func_idx;
        core_func_idx += 1;

        // Define the function type — use default run type (func() -> void)
        let wrapper_func_type = define_bare_func_type(&mut component, &mut component_type_idx);

        // Canon lift (bare functions like `run` take no arguments and return nothing)
        let mut canon = CanonicalFunctionSection::new();
        canon.lift(aliased_core_func, wrapper_func_type, []);
        component.section(&canon);

        // Export as a bare function
        let mut exp = ComponentExportSection::new();
        exp.export(
            func_name,
            ComponentExportKind::Func,
            component_func_idx,
            None,
        );
        component.section(&exp);
        component_func_idx += 1;
    }

    Ok(component.finish())
}

/// Map from (wasi_module, wasi_field) → (component_instance_index, field_name).
///
/// The component imports create component instances. Each instance provides
/// a set of functions. We build a map from the fused module's import names
/// to the component instance that provides them.
fn build_instance_func_map(
    source: &ParsedComponent,
) -> std::collections::HashMap<(&str, &str), (u32, String)> {
    use std::collections::HashMap;

    let mut map: HashMap<(&str, &str), (u32, String)> = HashMap::new();

    // Walk through component_instance_defs to find Import entries.
    // Each Import(idx) creates a component instance from imports[idx].
    // The import name is like "wasi:io/streams@0.2.6".
    // Functions within that instance are referenced as
    // (module="wasi:io/streams@0.2.6", field="[method]output-stream.write").
    //
    // We need to know which functions each instance provides. The component
    // aliases tell us: InstanceExport { instance_index, name } pulls a function
    // from an instance. But for our purposes, we just need to map
    // (wasi_module, wasi_field) → (instance_index, field_name).
    //
    // The wasi_module in the fused core module's imports matches the component
    // import name (e.g., "wasi:io/streams@0.2.6"). The field_name is the
    // function name within that interface.

    // Populate with all known (module, field) pairs from the original
    // component's aliases — these are the functions available from instances.
    for alias in &source.component_aliases {
        if let parser::ComponentAliasEntry::InstanceExport {
            kind: wasmparser::ComponentExternalKind::Func,
            instance_index,
            name,
        } = alias
            && let Some(parser::ComponentInstanceDef::Import(import_idx)) =
                source.component_instance_defs.get(*instance_index as usize)
        {
            let import = &source.imports[*import_idx];
            map.insert((&import.name, name), (*instance_index, name.clone()));
        }
    }

    // Resource-drop fields use [resource-drop]<type> naming. These are valid
    // instance exports even if not explicitly aliased as Func in the original
    // component. They are handled by the resolve_import_to_instance fallback.

    map
}

/// Extended lookup that handles both aliased functions and resource-drops.
///
/// In multi-memory mode, the fused module may have suffixed field names like
/// `get-environment$1` to distinguish imports from different components that
/// share the same WASI function. We strip the `$N` suffix before looking up
/// the original component instance.
fn resolve_import_to_instance(
    source: &ParsedComponent,
    module_name: &str,
    field_name: &str,
    instance_func_map: &std::collections::HashMap<(&str, &str), (u32, String)>,
) -> Option<(u32, String)> {
    // Try direct lookup first
    if let Some(result) = instance_func_map.get(&(module_name, field_name)) {
        return Some(result.clone());
    }

    // Strip $N suffix and retry (multi-memory mode uses suffixed field names)
    let base_field = if let Some(dollar_pos) = field_name.rfind('$') {
        let suffix = &field_name[dollar_pos + 1..];
        if suffix.chars().all(|c| c.is_ascii_digit()) {
            Some(&field_name[..dollar_pos])
        } else {
            None
        }
    } else {
        None
    };

    if let Some(base) = base_field
        && let Some(result) = instance_func_map.get(&(module_name, base))
    {
        return Some(result.clone());
    }

    // Fall back to module name matching (for resource-drops and other fields
    // not explicitly in the alias list).
    // Use base field name (without suffix) for the returned name so the component
    // runtime can find the actual function.
    let resolved_name = base_field.unwrap_or(field_name);
    for (inst_idx, def) in source.component_instance_defs.iter().enumerate() {
        if let parser::ComponentInstanceDef::Import(import_idx) = def {
            let import = &source.imports[*import_idx];
            if import.name == module_name {
                return Some((inst_idx as u32, resolved_name.to_string()));
            }
        }
    }

    None
}

/// Count total component-level types defined in the replayed depth_0_sections.
///
/// Parses the replayed section bytes to count type allocations:
/// - ComponentTypeSection (id=7): each entry defines a type
/// - ComponentAlias (id=6): InstanceExport of kind Type defines a type
/// - ComponentImport (id=10): imports with Type refs define a type
fn count_replayed_types(source: &ParsedComponent) -> u32 {
    let mut count = 0u32;
    for (section_id, data) in &source.depth_0_sections {
        match section_id {
            7 => {
                // ComponentTypeSection: count is first LEB128 in data
                if let Some((n, _)) = read_leb128_with_len(data) {
                    count += n;
                }
            }
            6 => {
                // ComponentAlias: parse to find Type aliases
                // Each alias entry may define a type if it's InstanceExport of kind Type
                count += count_type_aliases_in_section(data);
            }
            10 => {
                // ComponentImport: imports with Type refs define types
                count += count_type_imports_in_section(data);
            }
            _ => {}
        }
    }
    count
}

/// Count Type aliases in a ComponentAlias section.
/// Uses wasmparser to parse the section accurately.
fn count_type_aliases_in_section(data: &[u8]) -> u32 {
    // Build a minimal component containing just this alias section
    // and parse it to count Type aliases.
    // Simpler approach: use wasmparser's SectionLimited reader.
    // Unfortunately we can't directly construct a reader from raw bytes
    // without the full component context.
    //
    // Alternative: parse the LEB128 count and walk entries manually.
    // ComponentAlias entries have a tag byte indicating the kind.
    //
    // Actually, the simplest approach is to iterate through the source
    // component's component_aliases and count InstanceExport Type entries
    // that appear before the first core module. But we don't have a direct
    // mapping from alias → section.
    //
    // For correctness, let's count all InstanceExport Type aliases
    // in the depth_0_sections by examining the raw bytes.
    //
    // Alias section binary format:
    //   count: u32 (LEB128)
    //   for each alias:
    //     sort_byte1: u8 (ComponentExternalKind discriminant)
    //       0x01=Func, 0x02=Value, 0x03=Type, 0x04=Component, 0x05=Instance
    //       0x00=Module prefix (followed by sort_byte2=0x11)
    //     [sort_byte2]: u8 (only if sort_byte1==0x00)
    //     tag: u8
    //       0x00 = InstanceExport { instance: u32, name: string }
    //       0x01 = CoreInstanceExport { kind: u8, instance: u32, name: string }
    //       0x02 = Outer { count: u32, index: u32 }
    let mut count = 0u32;
    let mut pos = 0;

    let (entry_count, bytes_read) = match read_leb128_with_len(&data[pos..]) {
        Some(v) => v,
        None => return 0,
    };
    pos += bytes_read;

    for _ in 0..entry_count {
        if pos >= data.len() {
            break;
        }
        // Read sort byte(s) — determines the kind
        let sort_byte1 = data[pos];
        pos += 1;
        if sort_byte1 == 0x00 {
            // Module prefix: skip sort_byte2
            if pos >= data.len() {
                break;
            }
            pos += 1; // sort_byte2
        }
        let is_type = sort_byte1 == 0x03; // ComponentExternalKind::Type

        if pos >= data.len() {
            break;
        }
        let tag = data[pos];
        pos += 1;

        match tag {
            0x00 => {
                // InstanceExport { instance, name }
                if let Some((_, n)) = read_leb128_with_len(&data[pos..]) {
                    pos += n;
                }
                if let Some((name_len, n)) = read_leb128_with_len(&data[pos..]) {
                    pos += n + name_len as usize;
                }
                if is_type {
                    count += 1;
                }
            }
            0x01 => {
                // CoreInstanceExport { kind, instance, name }
                if pos < data.len() {
                    pos += 1; // core ExternalKind byte
                }
                if let Some((_, n)) = read_leb128_with_len(&data[pos..]) {
                    pos += n;
                }
                if let Some((name_len, n)) = read_leb128_with_len(&data[pos..]) {
                    pos += n + name_len as usize;
                }
            }
            0x02 => {
                // Outer { count, index }
                if let Some((_, n)) = read_leb128_with_len(&data[pos..]) {
                    pos += n;
                }
                if let Some((_, n)) = read_leb128_with_len(&data[pos..]) {
                    pos += n;
                }
            }
            _ => break,
        }
    }

    count
}

/// Count Type imports in a ComponentImport section.
fn count_type_imports_in_section(data: &[u8]) -> u32 {
    // ComponentImport entries:
    //   count: u32 (LEB128)
    //   for each:
    //     name: ComponentName (encoded as string)
    //     ty: ComponentTypeRef (tag + index)
    //
    // ComponentTypeRef tags (externdesc per binary format spec):
    //   0x00+0x11 = Module, 0x01 = Func, 0x02 = Value, 0x03 = Type, 0x04 = Component, 0x05 = Instance
    //
    // Type imports (tag 0x04) allocate a type index.
    let mut count = 0u32;
    let mut pos = 0;

    let (entry_count, bytes_read) = match read_leb128_with_len(&data[pos..]) {
        Some(v) => v,
        None => return 0,
    };
    pos += bytes_read;

    for _ in 0..entry_count {
        if pos >= data.len() {
            break;
        }
        // Skip name (component name is a discriminated union: tag + string)
        // Tag 0x00 = kebab-name, 0x01 = interface-name, etc.
        // Format: tag:u8, name_len:u32, name_bytes
        // Actually in practice it's: 0x00 len bytes OR 0x01 len bytes
        if pos >= data.len() {
            break;
        }
        let _name_tag = data[pos];
        pos += 1;
        if let Some((name_len, n)) = read_leb128_with_len(&data[pos..]) {
            pos += n + name_len as usize;
        }
        // Read ComponentTypeRef
        if pos >= data.len() {
            break;
        }
        let ty_tag = data[pos];
        pos += 1;
        // Skip the index (LEB128) and optional bounds for Type
        if ty_tag == 0x03 {
            // Type (externdesc 0x03): has bounds tag + index
            if pos < data.len() {
                let _bounds_tag = data[pos];
                pos += 1;
                if let Some((_, n)) = read_leb128_with_len(&data[pos..]) {
                    pos += n;
                }
            }
            count += 1;
        } else {
            // Other: just an index
            if let Some((_, n)) = read_leb128_with_len(&data[pos..]) {
                pos += n;
            }
        }
    }

    count
}

/// Read a LEB128 u32, returning (value, bytes_consumed).
fn read_leb128_with_len(data: &[u8]) -> Option<(u32, usize)> {
    let mut result = 0u32;
    let mut shift = 0;
    for (i, &byte) in data.iter().enumerate() {
        result |= ((byte & 0x7f) as u32) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            return Some((result, i + 1));
        }
        if shift >= 35 {
            return None;
        }
    }
    None
}

/// Find a `TaskReturn` entry for a given fused module import.
///
/// Uses the source component index (from merged import metadata) to
/// search the correct component first, then falls back to all components.
/// Matches by comparing the flat core type of each TaskReturn's result
/// against the import's core function parameters.
///
/// Returns `(component_index, canon_index)`.
fn find_task_return_for_import(
    all_components: &[ParsedComponent],
    source_comp_idx: Option<usize>,
    import_type: &(Vec<wasm_encoder::ValType>, Vec<wasm_encoder::ValType>),
) -> Option<(usize, usize)> {
    let import_params = &import_type.0;

    // Helper: search one component for a matching TaskReturn
    let search_comp = |comp_idx: usize, comp: &ParsedComponent| -> Option<(usize, usize)> {
        for (canon_idx, entry) in comp.canonical_functions.iter().enumerate() {
            if let parser::CanonicalEntry::TaskReturn { result, .. } = entry {
                let expected_params = flat_task_return_params_resolved(result.as_ref(), comp);
                if expected_params == *import_params {
                    return Some((comp_idx, canon_idx));
                }
            }
        }
        None
    };

    // Prefer the source component if known
    if let Some(src_idx) = source_comp_idx
        && let Some(comp) = all_components.get(src_idx)
        && let Some(result) = search_comp(src_idx, comp)
    {
        return Some(result);
    }

    // Search all components
    for (comp_idx, comp) in all_components.iter().enumerate() {
        if let Some(result) = search_comp(comp_idx, comp) {
            return Some(result);
        }
    }

    // Fallback: return the first TaskReturn entry from any component
    for (comp_idx, comp) in all_components.iter().enumerate() {
        for (canon_idx, entry) in comp.canonical_functions.iter().enumerate() {
            if matches!(entry, parser::CanonicalEntry::TaskReturn { .. }) {
                return Some((comp_idx, canon_idx));
            }
        }
    }

    None
}

/// Recursively resolve all `Type(idx)` references in a `ComponentValType`,
/// inlining the referenced definition. Returns a self-contained type tree
/// that does not depend on the source component's type table.
///
/// Used when storing typed result info for the adapter to use later, since
/// the adapter only sees the merged module and not the source components.
pub(crate) fn resolve_component_val_type(
    ty: &parser::ComponentValType,
    comp: &ParsedComponent,
) -> parser::ComponentValType {
    use parser::ComponentValType as CVT;
    match ty {
        CVT::Type(idx) => {
            if let Some(td) = comp.get_type_definition(*idx) {
                if let parser::ComponentTypeKind::Defined(inner) = &td.kind {
                    resolve_component_val_type(inner, comp)
                } else {
                    ty.clone()
                }
            } else {
                ty.clone()
            }
        }
        CVT::List(inner) => CVT::List(Box::new(resolve_component_val_type(inner, comp))),
        CVT::FixedSizeList(inner, n) => {
            CVT::FixedSizeList(Box::new(resolve_component_val_type(inner, comp)), *n)
        }
        CVT::Record(fields) => CVT::Record(
            fields
                .iter()
                .map(|(n, t)| (n.clone(), resolve_component_val_type(t, comp)))
                .collect(),
        ),
        CVT::Tuple(elems) => CVT::Tuple(
            elems
                .iter()
                .map(|t| resolve_component_val_type(t, comp))
                .collect(),
        ),
        CVT::Option(inner) => CVT::Option(Box::new(resolve_component_val_type(inner, comp))),
        CVT::Result { ok, err } => CVT::Result {
            ok: ok
                .as_ref()
                .map(|t| Box::new(resolve_component_val_type(t, comp))),
            err: err
                .as_ref()
                .map(|t| Box::new(resolve_component_val_type(t, comp))),
        },
        CVT::Variant(cases) => CVT::Variant(
            cases
                .iter()
                .map(|(n, t)| {
                    (
                        n.clone(),
                        t.as_ref().map(|t| resolve_component_val_type(t, comp)),
                    )
                })
                .collect(),
        ),
        CVT::Primitive(_) | CVT::String | CVT::Own(_) | CVT::Borrow(_) => ty.clone(),
    }
}

/// Compute flat task.return params with Type(idx) resolution.
///
/// Unlike `flat_task_return_params`, this version resolves `Type(idx)`
/// references using the component's type definitions.
pub(crate) fn flat_task_return_params_resolved(
    result: Option<&parser::ComponentValType>,
    comp: &ParsedComponent,
) -> Vec<wasm_encoder::ValType> {
    match result {
        None => vec![],
        Some(ty) => flat_component_val_type_resolved(ty, comp),
    }
}

/// Compute flat core representation with Type(idx) resolution.
fn flat_component_val_type_resolved(
    ty: &parser::ComponentValType,
    comp: &ParsedComponent,
) -> Vec<wasm_encoder::ValType> {
    use wasm_encoder::ValType;
    match ty {
        parser::ComponentValType::Type(idx) => {
            // Resolve the type index to its definition
            if let Some(type_def) = comp.get_type_definition(*idx) {
                match &type_def.kind {
                    parser::ComponentTypeKind::Defined(inner) => {
                        flat_component_val_type_resolved(inner, comp)
                    }
                    _ => vec![ValType::I32], // function types etc. → handle
                }
            } else {
                vec![ValType::I32] // unknown → default i32
            }
        }
        parser::ComponentValType::Record(fields) => {
            let mut params = Vec::new();
            for (_, field_ty) in fields {
                params.extend(flat_component_val_type_resolved(field_ty, comp));
            }
            params
        }
        parser::ComponentValType::Tuple(elems) => {
            let mut params = Vec::new();
            for elem in elems {
                params.extend(flat_component_val_type_resolved(elem, comp));
            }
            params
        }
        parser::ComponentValType::List(_) | parser::ComponentValType::FixedSizeList(_, _) => {
            vec![ValType::I32, ValType::I32]
        }
        parser::ComponentValType::String => vec![ValType::I32, ValType::I32],
        parser::ComponentValType::Option(inner) => {
            let mut params = vec![ValType::I32]; // discriminant
            params.extend(flat_component_val_type_resolved(inner, comp));
            params
        }
        parser::ComponentValType::Result { ok, err } => {
            let ok_flat = ok
                .as_ref()
                .map(|t| flat_component_val_type_resolved(t, comp))
                .unwrap_or_default();
            let err_flat = err
                .as_ref()
                .map(|t| flat_component_val_type_resolved(t, comp))
                .unwrap_or_default();
            let mut params = vec![ValType::I32]; // discriminant
            let longer = if ok_flat.len() >= err_flat.len() {
                &ok_flat
            } else {
                &err_flat
            };
            params.extend_from_slice(longer);
            params
        }
        parser::ComponentValType::Variant(cases) => {
            let mut params = vec![ValType::I32]; // discriminant
            let mut max_flat: Vec<ValType> = Vec::new();
            for (_, case_ty) in cases {
                if let Some(ct) = case_ty {
                    let case_flat = flat_component_val_type_resolved(ct, comp);
                    if case_flat.len() > max_flat.len() {
                        max_flat = case_flat;
                    }
                }
            }
            params.extend(max_flat);
            params
        }
        // Simple/primitive types
        parser::ComponentValType::Primitive(p) => vec![match p {
            parser::PrimitiveValType::Bool
            | parser::PrimitiveValType::U8
            | parser::PrimitiveValType::S8
            | parser::PrimitiveValType::U16
            | parser::PrimitiveValType::S16
            | parser::PrimitiveValType::U32
            | parser::PrimitiveValType::S32
            | parser::PrimitiveValType::Char => wasm_encoder::ValType::I32,
            parser::PrimitiveValType::U64 | parser::PrimitiveValType::S64 => {
                wasm_encoder::ValType::I64
            }
            parser::PrimitiveValType::F32 => wasm_encoder::ValType::F32,
            parser::PrimitiveValType::F64 => wasm_encoder::ValType::F64,
        }],
        parser::ComponentValType::Own(_) | parser::ComponentValType::Borrow(_) => {
            vec![wasm_encoder::ValType::I32]
        }
    }
}

/// Info about a fused module export that belongs to a component interface.
struct ExportFuncInfo {
    /// Function name within the interface (e.g., "run", "greet")
    func_name: String,
    /// Full export name in the fused module (e.g., "wasi:cli/run@0.2.6#run")
    core_export_name: String,
    /// Whether a `cabi_post_*` cleanup function exists for this export
    has_post_return: bool,
}

/// Find the source component's lift type index for a function within an interface.
///
/// Traces: source export (Instance) → component instance → shim component
/// instantiation → lifted function → canonical lift → type_index.
///
/// Falls back to scanning all Lift entries for one whose core export name
/// matches the `<interface>#<func_name>` pattern.
/// Returns (type_index, canonical_options) for the source component's lift
/// entry that matches the given interface function.
fn find_lift_type_for_interface_func(
    source: &ParsedComponent,
    interface_name: &str,
    func_name: &str,
) -> Option<(u32, parser::CanonicalOptions)> {
    let target_export_name = format!("{}#{}", interface_name, func_name);

    // Strategy 1: Find a Lift entry whose core function is exported with the
    // target name. Walk canonical_functions for Lift entries, then check if
    // the core_func_index matches an export with our target name.
    //
    // The source component's core module exports include the target name.
    // The Lift entry references the core function by its core_func_index.
    // We can match by looking at core aliases that reference the export name.
    for (canon_idx, canon) in source.canonical_functions.iter().enumerate() {
        if let parser::CanonicalEntry::Lift {
            type_index,
            options,
            ..
        } = canon
        {
            // Check if any component_func_def points to this lift, and if
            // the corresponding export matches our interface
            for func_def in &source.component_func_defs {
                if let parser::ComponentFuncDef::Lift(idx) = func_def
                    && *idx == canon_idx
                {
                    // This is a lifted function. Check if the source
                    // component exports it as our interface.
                    return Some((*type_index, options.clone()));
                }
            }
        }
    }

    // Strategy 2: Look for any Lift entry (fallback for simple components
    // with only one export).
    for canon in &source.canonical_functions {
        if let parser::CanonicalEntry::Lift {
            type_index,
            options,
            ..
        } = canon
        {
            return Some((*type_index, options.clone()));
        }
    }

    // No lift found — export type unknown
    let _ = target_export_name; // suppress unused warning
    None
}

/// Define a source component's type in our wrapper, recursively defining
/// any referenced sub-types. Returns the wrapper's type index.
fn define_source_type_in_wrapper(
    component: &mut wasm_encoder::Component,
    source: &ParsedComponent,
    source_type_idx: u32,
    component_type_idx: &mut u32,
    type_remap: &mut std::collections::HashMap<u32, u32>,
) -> Result<u32> {
    // Already defined in wrapper?
    if let Some(&wrapper_idx) = type_remap.get(&source_type_idx) {
        return Ok(wrapper_idx);
    }

    let type_def = source.get_type_definition(source_type_idx).ok_or_else(|| {
        Error::EncodingError(format!(
            "cannot find source type definition at index {}",
            source_type_idx
        ))
    })?;

    // Clone to avoid borrow issues
    let kind = type_def.kind.clone();

    match &kind {
        parser::ComponentTypeKind::Defined(val_type) => {
            // Define the value type (result, list, option, etc.)
            emit_defined_type(component, source, val_type, component_type_idx, type_remap)
        }
        parser::ComponentTypeKind::Function { params, results } => {
            // First, recursively define any referenced types in params/results
            let enc_params: Vec<(String, wasm_encoder::ComponentValType)> = params
                .iter()
                .map(|(name, ty)| {
                    let enc = convert_parser_val_to_encoder(
                        component,
                        source,
                        ty,
                        component_type_idx,
                        type_remap,
                    )?;
                    Ok((name.clone(), enc))
                })
                .collect::<Result<_>>()?;

            let enc_results: Vec<(Option<String>, wasm_encoder::ComponentValType)> = results
                .iter()
                .map(|(name, ty)| {
                    let enc = convert_parser_val_to_encoder(
                        component,
                        source,
                        ty,
                        component_type_idx,
                        type_remap,
                    )?;
                    Ok((name.clone(), enc))
                })
                .collect::<Result<_>>()?;

            // Emit the function type. Note: params() must be called before
            // result()/results(), even if empty.
            let mut types = wasm_encoder::ComponentTypeSection::new();
            {
                let mut func_enc = types.function();
                let p: Vec<_> = enc_params.iter().map(|(n, t)| (n.as_str(), *t)).collect();
                func_enc.params(p);
                if enc_results.len() == 1 && enc_results[0].0.is_none() {
                    func_enc.result(Some(enc_results[0].1));
                } else if !enc_results.is_empty() {
                    // Component model now only supports a single anonymous result;
                    // emit the first result type.
                    func_enc.result(Some(enc_results[0].1));
                }
            }
            component.section(&types);

            let wrapper_idx = *component_type_idx;
            *component_type_idx += 1;
            type_remap.insert(source_type_idx, wrapper_idx);
            Ok(wrapper_idx)
        }
        _ => Err(Error::EncodingError(format!(
            "unsupported type kind for export at index {}",
            source_type_idx
        ))),
    }
}

/// Emit a component defined type (result, list, option, etc.) in the wrapper.
fn emit_defined_type(
    component: &mut wasm_encoder::Component,
    source: &ParsedComponent,
    val_type: &parser::ComponentValType,
    component_type_idx: &mut u32,
    type_remap: &mut std::collections::HashMap<u32, u32>,
) -> Result<u32> {
    let mut types = wasm_encoder::ComponentTypeSection::new();

    match val_type {
        parser::ComponentValType::Result { ok, err } => {
            let ok_enc = ok
                .as_ref()
                .map(|t| {
                    convert_parser_val_to_encoder(
                        component,
                        source,
                        t,
                        component_type_idx,
                        type_remap,
                    )
                })
                .transpose()?;
            let err_enc = err
                .as_ref()
                .map(|t| {
                    convert_parser_val_to_encoder(
                        component,
                        source,
                        t,
                        component_type_idx,
                        type_remap,
                    )
                })
                .transpose()?;
            types.defined_type().result(ok_enc, err_enc);
        }
        parser::ComponentValType::List(inner) => {
            let inner_enc = convert_parser_val_to_encoder(
                component,
                source,
                inner,
                component_type_idx,
                type_remap,
            )?;
            types.defined_type().list(inner_enc);
        }
        parser::ComponentValType::FixedSizeList(elem, len) => {
            let elem_enc = convert_parser_val_to_encoder(
                component,
                source,
                elem,
                component_type_idx,
                type_remap,
            )?;
            types.defined_type().fixed_length_list(elem_enc, *len);
        }
        parser::ComponentValType::Option(inner) => {
            let inner_enc = convert_parser_val_to_encoder(
                component,
                source,
                inner,
                component_type_idx,
                type_remap,
            )?;
            types.defined_type().option(inner_enc);
        }
        parser::ComponentValType::Record(fields) => {
            let enc_fields: Vec<(&str, wasm_encoder::ComponentValType)> = fields
                .iter()
                .map(|(name, ty)| {
                    let enc = convert_parser_val_to_encoder(
                        component,
                        source,
                        ty,
                        component_type_idx,
                        type_remap,
                    )?;
                    Ok((name.as_str(), enc))
                })
                .collect::<Result<_>>()?;
            types.defined_type().record(enc_fields);
        }
        parser::ComponentValType::Tuple(elems) => {
            let enc_elems: Vec<wasm_encoder::ComponentValType> = elems
                .iter()
                .map(|ty| {
                    convert_parser_val_to_encoder(
                        component,
                        source,
                        ty,
                        component_type_idx,
                        type_remap,
                    )
                })
                .collect::<Result<_>>()?;
            types.defined_type().tuple(enc_elems);
        }
        parser::ComponentValType::Variant(cases) => {
            let enc_cases: Vec<(&str, Option<wasm_encoder::ComponentValType>)> = cases
                .iter()
                .map(|(name, ty)| {
                    let enc = ty
                        .as_ref()
                        .map(|t| {
                            convert_parser_val_to_encoder(
                                component,
                                source,
                                t,
                                component_type_idx,
                                type_remap,
                            )
                        })
                        .transpose()?;
                    Ok((name.as_str(), enc))
                })
                .collect::<Result<_>>()?;
            types.defined_type().variant(enc_cases);
        }
        _ => {
            return Err(Error::EncodingError(format!(
                "unsupported defined type for export: {:?}",
                val_type
            )));
        }
    }

    component.section(&types);
    let wrapper_idx = *component_type_idx;
    *component_type_idx += 1;
    Ok(wrapper_idx)
}

/// Convert a parser ComponentValType to a wasm_encoder ComponentValType,
/// recursively defining any referenced types in the wrapper.
fn convert_parser_val_to_encoder(
    component: &mut wasm_encoder::Component,
    source: &ParsedComponent,
    ty: &parser::ComponentValType,
    component_type_idx: &mut u32,
    type_remap: &mut std::collections::HashMap<u32, u32>,
) -> Result<wasm_encoder::ComponentValType> {
    match ty {
        parser::ComponentValType::String => Ok(wasm_encoder::ComponentValType::Primitive(
            wasm_encoder::PrimitiveValType::String,
        )),
        parser::ComponentValType::Primitive(p) => Ok(wasm_encoder::ComponentValType::Primitive(
            convert_parser_primitive(p),
        )),
        parser::ComponentValType::Type(idx) => {
            let wrapper_idx = define_source_type_in_wrapper(
                component,
                source,
                *idx,
                component_type_idx,
                type_remap,
            )?;
            Ok(wasm_encoder::ComponentValType::Type(wrapper_idx))
        }
        parser::ComponentValType::Result { .. } => {
            // Inline result — must define as a standalone type
            let wrapper_idx =
                emit_defined_type(component, source, ty, component_type_idx, type_remap)?;
            Ok(wasm_encoder::ComponentValType::Type(wrapper_idx))
        }
        parser::ComponentValType::List(_)
        | parser::ComponentValType::FixedSizeList(_, _)
        | parser::ComponentValType::Option(_)
        | parser::ComponentValType::Record(_)
        | parser::ComponentValType::Tuple(_)
        | parser::ComponentValType::Variant(_) => {
            let wrapper_idx =
                emit_defined_type(component, source, ty, component_type_idx, type_remap)?;
            Ok(wasm_encoder::ComponentValType::Type(wrapper_idx))
        }
        _ => Err(Error::EncodingError(format!(
            "unsupported value type for export encoding: {:?}",
            ty
        ))),
    }
}

/// Fallback: define a `func() -> result` type for simple CLI run exports.
fn define_default_run_type(
    component: &mut wasm_encoder::Component,
    component_type_idx: &mut u32,
) -> u32 {
    // Define (result) — no ok/err payloads
    let mut types = wasm_encoder::ComponentTypeSection::new();
    types.defined_type().result(None, None);
    component.section(&types);
    let result_type_idx = *component_type_idx;
    *component_type_idx += 1;

    // Define (func (result <result_type>))
    let mut types2 = wasm_encoder::ComponentTypeSection::new();
    let empty_params: Vec<(&str, wasm_encoder::ComponentValType)> = vec![];
    types2
        .function()
        .params(empty_params)
        .result(Some(wasm_encoder::ComponentValType::Type(result_type_idx)));
    component.section(&types2);
    let func_type_idx = *component_type_idx;
    *component_type_idx += 1;

    func_type_idx
}

/// Define a bare function type: `func()` with no params and no results.
/// Used for exported functions like `run` that aren't wrapped in an interface.
fn define_bare_func_type(
    component: &mut wasm_encoder::Component,
    component_type_idx: &mut u32,
) -> u32 {
    let mut types = wasm_encoder::ComponentTypeSection::new();
    let empty: Vec<(&str, wasm_encoder::ComponentValType)> = vec![];
    types.function().params(empty).result(None);
    component.section(&types);
    let func_type_idx = *component_type_idx;
    *component_type_idx += 1;

    func_type_idx
}

/// Convert a parser PrimitiveValType to wasm_encoder PrimitiveValType.
fn convert_parser_primitive(p: &parser::PrimitiveValType) -> wasm_encoder::PrimitiveValType {
    match p {
        parser::PrimitiveValType::Bool => wasm_encoder::PrimitiveValType::Bool,
        parser::PrimitiveValType::S8 => wasm_encoder::PrimitiveValType::S8,
        parser::PrimitiveValType::U8 => wasm_encoder::PrimitiveValType::U8,
        parser::PrimitiveValType::S16 => wasm_encoder::PrimitiveValType::S16,
        parser::PrimitiveValType::U16 => wasm_encoder::PrimitiveValType::U16,
        parser::PrimitiveValType::S32 => wasm_encoder::PrimitiveValType::S32,
        parser::PrimitiveValType::U32 => wasm_encoder::PrimitiveValType::U32,
        parser::PrimitiveValType::S64 => wasm_encoder::PrimitiveValType::S64,
        parser::PrimitiveValType::U64 => wasm_encoder::PrimitiveValType::U64,
        parser::PrimitiveValType::F32 => wasm_encoder::PrimitiveValType::F32,
        parser::PrimitiveValType::F64 => wasm_encoder::PrimitiveValType::F64,
        parser::PrimitiveValType::Char => wasm_encoder::PrimitiveValType::Char,
    }
}

/// Convert wasmparser ValType to wasm-encoder ValType.
fn convert_val_type(ty: wasmparser::ValType) -> wasm_encoder::ValType {
    match ty {
        wasmparser::ValType::I32 => wasm_encoder::ValType::I32,
        wasmparser::ValType::I64 => wasm_encoder::ValType::I64,
        wasmparser::ValType::F32 => wasm_encoder::ValType::F32,
        wasmparser::ValType::F64 => wasm_encoder::ValType::F64,
        wasmparser::ValType::V128 => wasm_encoder::ValType::V128,
        wasmparser::ValType::Ref(rt) => {
            if rt.is_func_ref() {
                wasm_encoder::ValType::Ref(wasm_encoder::RefType::FUNCREF)
            } else {
                wasm_encoder::ValType::Ref(wasm_encoder::RefType::EXTERNREF)
            }
        }
    }
}

/// Parse a resource-related field name into a (ResourceOp, resource_name) pair.
///
/// Field names follow the convention `[resource-drop]NAME`, `[resource-new]NAME`,
/// or `[resource-rep]NAME`. The `$N` suffix (multi-memory deduplication) is
/// stripped before matching.
///
/// Returns `None` if the field doesn't match any resource operation prefix.
fn parse_resource_field(field_name: &str) -> Option<(ResourceOp, String)> {
    // Strip $N suffix if present (multi-memory deduplication)
    let base = if let Some(dollar_pos) = field_name.rfind('$') {
        let suffix = &field_name[dollar_pos + 1..];
        if suffix.chars().all(|c| c.is_ascii_digit()) {
            &field_name[..dollar_pos]
        } else {
            field_name
        }
    } else {
        field_name
    };

    let prefixes: &[(&str, ResourceOp)] = &[
        ("[resource-drop]", ResourceOp::Drop),
        ("[resource-new]", ResourceOp::New),
        ("[resource-rep]", ResourceOp::Rep),
    ];
    prefixes.iter().find_map(|(prefix, op)| {
        base.strip_prefix(prefix)
            .map(|name| (op.clone(), name.to_string()))
    })
}

/// Parse a P3 task/async built-in field name into a `P3BuiltinOp`.
///
/// Recognizes field names like `[task-return]is-prime`, `[task-cancel]`,
/// `[context-get-0]`, `[waitable-set-new]`, `[backpressure-inc]`, etc.
///
/// The `$N` suffix (multi-memory deduplication) is stripped before matching.
///
/// Returns `None` if the field doesn't match any P3 built-in prefix.
fn parse_p3_builtin_field(field_name: &str) -> Option<P3BuiltinOp> {
    // Strip $N suffix if present (multi-memory deduplication)
    let base = if let Some(dollar_pos) = field_name.rfind('$') {
        let suffix = &field_name[dollar_pos + 1..];
        if suffix.chars().all(|c| c.is_ascii_digit()) {
            &field_name[..dollar_pos]
        } else {
            field_name
        }
    } else {
        field_name
    };

    // [task-return]<name> — return a result from an async export
    if base.starts_with("[task-return]") {
        return Some(P3BuiltinOp::TaskReturn {
            source_location: None,
        });
    }

    // Exact-match builtins (no trailing name)
    match base {
        "[task-cancel]" => return Some(P3BuiltinOp::TaskCancel),
        "[waitable-join]" => return Some(P3BuiltinOp::WaitableJoin),
        "[waitable-set-new]" => return Some(P3BuiltinOp::WaitableSetNew),
        "[waitable-set-drop]" => return Some(P3BuiltinOp::WaitableSetDrop),
        "[waitable-set-poll]" => return Some(P3BuiltinOp::WaitableSetPoll),
        "[backpressure-inc]" => return Some(P3BuiltinOp::BackpressureInc),
        "[backpressure-dec]" => return Some(P3BuiltinOp::BackpressureDec),
        "[subtask-drop]" => return Some(P3BuiltinOp::SubtaskDrop),
        _ => {}
    }

    // [context-get-N] and [context-set-N] — slot index encoded in the name
    if let Some(rest) = base.strip_prefix("[context-get-")
        && let Some(idx_str) = rest.strip_suffix(']')
        && let Ok(slot) = idx_str.parse::<u32>()
    {
        return Some(P3BuiltinOp::ContextGet(slot));
    }
    if let Some(rest) = base.strip_prefix("[context-set-")
        && let Some(idx_str) = rest.strip_suffix(']')
        && let Ok(slot) = idx_str.parse::<u32>()
    {
        return Some(P3BuiltinOp::ContextSet(slot));
    }

    None
}

/// Check whether a field name is a P3 task/async built-in.
///
/// Used to distinguish P3 fields from resource operations when processing
/// `[export]`-prefixed imports.
fn is_p3_builtin_field(field_name: &str) -> bool {
    parse_p3_builtin_field(field_name).is_some()
}

/// Convert wasmparser TypeRef to wasm-encoder EntityType.
fn convert_type_ref(ty: wasmparser::TypeRef) -> Result<wasm_encoder::EntityType> {
    match ty {
        wasmparser::TypeRef::Func(idx) => Ok(wasm_encoder::EntityType::Function(idx)),
        wasmparser::TypeRef::Table(t) => {
            let element_type = if t.element_type.is_func_ref() {
                wasm_encoder::RefType::FUNCREF
            } else {
                wasm_encoder::RefType::EXTERNREF
            };
            Ok(wasm_encoder::EntityType::Table(wasm_encoder::TableType {
                element_type,
                minimum: t.initial,
                maximum: t.maximum,
                table64: false,
                shared: false,
            }))
        }
        wasmparser::TypeRef::Memory(m) => {
            Ok(wasm_encoder::EntityType::Memory(wasm_encoder::MemoryType {
                minimum: m.initial,
                maximum: m.maximum,
                memory64: m.memory64,
                shared: m.shared,
                page_size_log2: None,
            }))
        }
        wasmparser::TypeRef::Global(g) => {
            Ok(wasm_encoder::EntityType::Global(wasm_encoder::GlobalType {
                val_type: convert_val_type(g.content_type),
                mutable: g.mutable,
                shared: false,
            }))
        }
        wasmparser::TypeRef::Tag(_) => Err(Error::UnsupportedFeature(
            "exception handling tags".to_string(),
        )),
        wasmparser::TypeRef::FuncExact(idx) => Ok(wasm_encoder::EntityType::Function(idx)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_count_replayed_types_hello_c_cli() {
        let path = "../tests/wit_bindgen/fixtures/release-0.2.0/hello_c_cli.wasm";
        let Ok(bytes) = std::fs::read(path) else {
            eprintln!("skipping: fixture not found at {path}");
            return;
        };
        let parser = crate::ComponentParser::new();
        let parsed = parser.parse(&bytes).unwrap();

        let count = count_replayed_types(&parsed);
        // hello_c_cli has 14 ComponentType entries + 7 Type aliases = 21 types
        // defined in the interface sections before core modules
        assert_eq!(count, 21, "expected 21 replayed types for hello_c_cli");
    }

    #[test]
    fn test_build_stubs_module_validates() {
        use wasm_encoder::ValType;
        let import_types = vec![
            (vec![ValType::I32; 4], vec![ValType::I32]), // realloc-like
            (vec![ValType::I32], vec![]),                // resource-drop-like
            (vec![ValType::I32, ValType::I32], vec![ValType::I32]), // read-like
        ];
        let memories = vec![(1u64, None, false)];
        let stubs = build_stubs_module(&memories, &import_types);
        let mut features = wasmparser::WasmFeatures::default();
        features |= wasmparser::WasmFeatures::REFERENCE_TYPES;
        let mut validator = wasmparser::Validator::new_with_features(features);
        validator
            .validate_all(&stubs)
            .expect("stubs module should validate");
    }

    #[test]
    fn test_build_stubs_module_with_max() {
        use wasm_encoder::ValType;
        let import_types = vec![(vec![ValType::I32; 4], vec![ValType::I32])];
        let memories = vec![(2u64, Some(256u64), false)];
        let stubs = build_stubs_module(&memories, &import_types);
        let mut features = wasmparser::WasmFeatures::default();
        features |= wasmparser::WasmFeatures::REFERENCE_TYPES;
        let mut validator = wasmparser::Validator::new_with_features(features);
        validator
            .validate_all(&stubs)
            .expect("stubs module with max should validate");

        // Verify it has the right memory limits
        let parser = wasmparser::Parser::new(0);
        for payload in parser.parse_all(&stubs) {
            if let Ok(wasmparser::Payload::MemorySection(reader)) = payload {
                for mem in reader {
                    let mem = mem.unwrap();
                    assert_eq!(mem.initial, 2);
                    assert_eq!(mem.maximum, Some(256));
                }
            }
        }
    }

    #[test]
    fn test_build_stubs_module_zero_imports() {
        let memories = vec![(1u64, None, false)];
        let stubs = build_stubs_module(&memories, &[]);
        let mut validator = wasmparser::Validator::new();
        validator
            .validate_all(&stubs)
            .expect("stubs module with zero imports should validate");

        // Should have memory but no table or functions
        let parser = wasmparser::Parser::new(0);
        let mut has_memory = false;
        let mut has_table = false;
        for payload in parser.parse_all(&stubs) {
            match payload {
                Ok(wasmparser::Payload::MemorySection(_)) => has_memory = true,
                Ok(wasmparser::Payload::TableSection(_)) => has_table = true,
                _ => {}
            }
        }
        assert!(has_memory, "stubs should have memory");
        assert!(!has_table, "stubs with no imports should have no table");
    }

    #[test]
    fn test_build_fixup_module_validates() {
        use wasm_encoder::ValType;
        let import_types = vec![
            (vec![ValType::I32; 4], vec![ValType::I32]),
            (vec![ValType::I32], vec![]),
        ];
        let fixup = build_fixup_module(&import_types);
        let mut features = wasmparser::WasmFeatures::default();
        features |= wasmparser::WasmFeatures::REFERENCE_TYPES;
        features |= wasmparser::WasmFeatures::BULK_MEMORY;
        let mut validator = wasmparser::Validator::new_with_features(features);
        validator
            .validate_all(&fixup)
            .expect("fixup module should validate");
    }

    #[test]
    fn test_build_fixup_module_zero_imports() {
        let fixup = build_fixup_module(&[]);
        let mut validator = wasmparser::Validator::new();
        validator
            .validate_all(&fixup)
            .expect("empty fixup module should validate");
    }

    // -----------------------------------------------------------------------
    // Multi-memory stubs module tests
    // -----------------------------------------------------------------------

    /// Verify that build_stubs_module with multiple memories creates the
    /// correct number of memory exports with $N naming convention.
    #[test]
    fn test_build_stubs_module_multi_memory_exports() {
        use wasm_encoder::ValType;

        let memories = vec![
            (1u64, None, false),        // component 0: memory
            (2u64, None, false),        // component 1: memory$1
            (4u64, Some(16u64), false), // component 2: memory$2
        ];
        let import_types = vec![
            (vec![ValType::I32], vec![]), // one import
            (vec![ValType::I32], vec![]), // another import
        ];
        let stubs = build_stubs_module(&memories, &import_types);

        // Validate the module
        let mut features = wasmparser::WasmFeatures::default();
        features |= wasmparser::WasmFeatures::REFERENCE_TYPES;
        features |= wasmparser::WasmFeatures::MULTI_MEMORY;
        let mut validator = wasmparser::Validator::new_with_features(features);
        validator
            .validate_all(&stubs)
            .expect("multi-memory stubs module should validate");

        // Parse exports to verify memory naming
        let parser = wasmparser::Parser::new(0);
        let mut memory_exports: Vec<String> = Vec::new();
        let mut memory_count = 0u32;
        for payload in parser.parse_all(&stubs) {
            match payload {
                Ok(wasmparser::Payload::MemorySection(reader)) => {
                    memory_count = reader.count();
                }
                Ok(wasmparser::Payload::ExportSection(reader)) => {
                    for export in reader {
                        let export = export.unwrap();
                        if export.kind == wasmparser::ExternalKind::Memory {
                            memory_exports.push(export.name.to_string());
                        }
                    }
                }
                _ => {}
            }
        }

        // Should have 3 memories defined
        assert_eq!(memory_count, 3, "stubs module should define 3 memories");

        // Should export "memory", "memory$1", "memory$2"
        assert_eq!(
            memory_exports.len(),
            3,
            "should export 3 memories, got: {:?}",
            memory_exports
        );
        assert!(
            memory_exports.contains(&"memory".to_string()),
            "should export 'memory'"
        );
        assert!(
            memory_exports.contains(&"memory$1".to_string()),
            "should export 'memory$1'"
        );
        assert!(
            memory_exports.contains(&"memory$2".to_string()),
            "should export 'memory$2'"
        );
    }

    /// Verify that build_stubs_module with a single memory only exports
    /// "memory" (no $N suffix).
    #[test]
    fn test_build_stubs_module_single_memory_no_suffix() {
        use wasm_encoder::ValType;

        let memories = vec![(1u64, None, false)];
        let import_types = vec![(vec![ValType::I32], vec![])];
        let stubs = build_stubs_module(&memories, &import_types);

        let parser = wasmparser::Parser::new(0);
        let mut memory_exports: Vec<String> = Vec::new();
        for payload in parser.parse_all(&stubs) {
            if let Ok(wasmparser::Payload::ExportSection(reader)) = payload {
                for export in reader {
                    let export = export.unwrap();
                    if export.kind == wasmparser::ExternalKind::Memory {
                        memory_exports.push(export.name.to_string());
                    }
                }
            }
        }

        assert_eq!(
            memory_exports.len(),
            1,
            "single memory should produce exactly one memory export"
        );
        assert_eq!(
            memory_exports[0], "memory",
            "single memory should export as 'memory' without suffix"
        );
    }

    /// Verify that build_stubs_module preserves memory64 and max limits
    /// for each memory in multi-memory mode.
    #[test]
    fn test_build_stubs_module_multi_memory_limits_preserved() {
        use wasm_encoder::ValType;

        let memories = vec![
            (1u64, Some(100u64), false), // component 0
            (4u64, Some(256u64), true),  // component 1 (memory64)
        ];
        let import_types = vec![(vec![ValType::I32; 4], vec![ValType::I32])];
        let stubs = build_stubs_module(&memories, &import_types);

        let mut features = wasmparser::WasmFeatures::default();
        features |= wasmparser::WasmFeatures::REFERENCE_TYPES;
        features |= wasmparser::WasmFeatures::MULTI_MEMORY;
        features |= wasmparser::WasmFeatures::MEMORY64;
        let mut validator = wasmparser::Validator::new_with_features(features);
        validator
            .validate_all(&stubs)
            .expect("multi-memory stubs with memory64 should validate");

        let parser = wasmparser::Parser::new(0);
        let mut parsed_memories: Vec<(u64, Option<u64>, bool)> = Vec::new();
        for payload in parser.parse_all(&stubs) {
            if let Ok(wasmparser::Payload::MemorySection(reader)) = payload {
                for mem in reader {
                    let mem = mem.unwrap();
                    parsed_memories.push((mem.initial, mem.maximum, mem.memory64));
                }
            }
        }

        assert_eq!(parsed_memories.len(), 2);
        // Memory 0
        assert_eq!(parsed_memories[0].0, 1, "memory 0 initial");
        assert_eq!(parsed_memories[0].1, Some(100), "memory 0 max");
        assert!(!parsed_memories[0].2, "memory 0 not memory64");
        // Memory 1
        assert_eq!(parsed_memories[1].0, 4, "memory 1 initial");
        assert_eq!(parsed_memories[1].1, Some(256), "memory 1 max");
        assert!(parsed_memories[1].2, "memory 1 is memory64");
    }

    // -----------------------------------------------------------------------
    // resolve_import_to_instance $N suffix stripping tests
    // -----------------------------------------------------------------------

    /// Verify that resolve_import_to_instance strips $N suffixes when the
    /// direct lookup fails. This is the core mechanism that allows multi-memory
    /// mode's suffixed field names to resolve back to the original instance.
    #[test]
    fn test_resolve_import_to_instance_strips_suffix() {
        use crate::parser::{ComponentImport, ComponentInstanceDef};
        use wasmparser::ComponentTypeRef;

        // Build a source component with one import "wasi:cli/stderr"
        // that creates component instance 0.
        let source = ParsedComponent {
            name: None,
            core_modules: Vec::new(),
            imports: vec![ComponentImport {
                name: "wasi:cli/stderr@0.2.6".to_string(),
                ty: ComponentTypeRef::Instance(0),
            }],
            exports: Vec::new(),
            types: Vec::new(),
            instances: Vec::new(),
            canonical_functions: Vec::new(),
            sub_components: Vec::new(),
            component_aliases: Vec::new(),
            component_instances: Vec::new(),
            core_entity_order: Vec::new(),
            component_func_defs: Vec::new(),
            component_instance_defs: vec![ComponentInstanceDef::Import(0)],
            component_type_defs: Vec::new(),
            original_size: 0,
            original_hash: String::new(),
            depth_0_sections: Vec::new(),
            p3_async_features: Vec::new(),
        };

        // Build an instance_func_map with the base field name (no suffix)
        let mut instance_func_map = std::collections::HashMap::new();
        instance_func_map.insert(
            ("wasi:cli/stderr@0.2.6", "get-stderr"),
            (0u32, "get-stderr".to_string()),
        );

        // Direct lookup: should succeed
        let direct = resolve_import_to_instance(
            &source,
            "wasi:cli/stderr@0.2.6",
            "get-stderr",
            &instance_func_map,
        );
        assert!(direct.is_some(), "direct lookup should succeed");
        assert_eq!(direct.unwrap().1, "get-stderr");

        // Suffixed lookup: "get-stderr$1" should strip $1 and find "get-stderr"
        let suffixed = resolve_import_to_instance(
            &source,
            "wasi:cli/stderr@0.2.6",
            "get-stderr$1",
            &instance_func_map,
        );
        assert!(
            suffixed.is_some(),
            "suffixed lookup should succeed by stripping $1"
        );
        assert_eq!(
            suffixed.unwrap().1,
            "get-stderr",
            "resolved name should be the base name without suffix"
        );
    }

    /// Verify that non-numeric suffixes after $ are NOT stripped.
    /// "get-stderr$abc" should not match "get-stderr".
    #[test]
    fn test_resolve_import_to_instance_non_numeric_suffix_not_stripped() {
        use crate::parser::{ComponentImport, ComponentInstanceDef};
        use wasmparser::ComponentTypeRef;

        let source = ParsedComponent {
            name: None,
            core_modules: Vec::new(),
            imports: vec![ComponentImport {
                name: "wasi:cli/stderr@0.2.6".to_string(),
                ty: ComponentTypeRef::Instance(0),
            }],
            exports: Vec::new(),
            types: Vec::new(),
            instances: Vec::new(),
            canonical_functions: Vec::new(),
            sub_components: Vec::new(),
            component_aliases: Vec::new(),
            component_instances: Vec::new(),
            core_entity_order: Vec::new(),
            component_func_defs: Vec::new(),
            component_instance_defs: vec![ComponentInstanceDef::Import(0)],
            component_type_defs: Vec::new(),
            original_size: 0,
            original_hash: String::new(),
            depth_0_sections: Vec::new(),
            p3_async_features: Vec::new(),
        };

        let mut instance_func_map = std::collections::HashMap::new();
        instance_func_map.insert(
            ("wasi:cli/stderr@0.2.6", "get-stderr"),
            (0u32, "get-stderr".to_string()),
        );

        // Non-numeric suffix: should fall back to module-name matching, which
        // will find the import but use the field name directly (not stripped).
        // The key observation: $abc is not numeric, so the suffix-stripping
        // branch does NOT fire.
        let result = resolve_import_to_instance(
            &source,
            "wasi:cli/stderr@0.2.6",
            "get-stderr$abc",
            &instance_func_map,
        );

        // The function should fall through to the module-name matching fallback.
        // It should succeed (because the module name matches the import name)
        // and return the original field name unchanged (since $abc is not numeric).
        assert!(result.is_some(), "module-name fallback should match");
        assert_eq!(
            result.unwrap().1,
            "get-stderr$abc",
            "non-numeric suffix should not be stripped"
        );
    }

    /// Verify that resolve_import_to_instance returns None for unknown modules.
    #[test]
    fn test_resolve_import_to_instance_unknown_module() {
        use crate::parser::{ComponentImport, ComponentInstanceDef};
        use wasmparser::ComponentTypeRef;

        let source = ParsedComponent {
            name: None,
            core_modules: Vec::new(),
            imports: vec![ComponentImport {
                name: "wasi:cli/stderr@0.2.6".to_string(),
                ty: ComponentTypeRef::Instance(0),
            }],
            exports: Vec::new(),
            types: Vec::new(),
            instances: Vec::new(),
            canonical_functions: Vec::new(),
            sub_components: Vec::new(),
            component_aliases: Vec::new(),
            component_instances: Vec::new(),
            core_entity_order: Vec::new(),
            component_func_defs: Vec::new(),
            component_instance_defs: vec![ComponentInstanceDef::Import(0)],
            component_type_defs: Vec::new(),
            original_size: 0,
            original_hash: String::new(),
            depth_0_sections: Vec::new(),
            p3_async_features: Vec::new(),
        };

        let instance_func_map = std::collections::HashMap::new();

        let result = resolve_import_to_instance(
            &source,
            "wasi:unknown/thing@0.2.6",
            "something$1",
            &instance_func_map,
        );
        assert!(result.is_none(), "unknown module should not resolve");
    }
}
