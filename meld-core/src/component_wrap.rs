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
//!                                           ├── Shim module (memory + realloc)
//!                                           ├── Fused module (memory imported)
//!                                           ├── canon lower (WASI funcs)
//!                                           ├── Core instances (shim, fused)
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
//! **Solution**: A tiny shim module provides memory + bump-allocator realloc.
//! The fused module's memory definition is converted to a memory import that
//! receives the shim's memory. Both modules share the same memory.

use crate::parser::{self, ParsedComponent};
use crate::resolver::DependencyGraph;
use crate::{Error, Result};

/// Wrap fused core module bytes as a P2 component.
///
/// Uses depth-0 sections from the original component(s) to reconstruct the
/// component-level type and import declarations, then wires the fused module
/// through a shim for memory sharing.
pub fn wrap_as_component(
    fused_module: &[u8],
    components: &[ParsedComponent],
    _graph: &DependencyGraph,
) -> Result<Vec<u8>> {
    // Pick the component with the most depth_0_sections (widest interface)
    let source = components
        .iter()
        .max_by_key(|c| c.depth_0_sections.len())
        .ok_or(Error::NoComponents)?;

    // Parse the fused module to extract its imports, exports, and memory info
    let fused_info = parse_fused_module(fused_module)?;

    // Build the shim module (provides memory + realloc)
    let shim_bytes = build_shim_module(fused_info.memory_initial, fused_info.memory_maximum);

    // Convert fused module: memory definition → memory import from shim
    let modified_fused = convert_memory_to_import(fused_module, &fused_info)?;

    // Assemble the P2 component
    assemble_component(source, &shim_bytes, &modified_fused, &fused_info)
}

/// Information extracted from the fused core module.
struct FusedModuleInfo {
    /// Function imports: (module_name, field_name, type_index)
    func_imports: Vec<(String, String, u32)>,
    /// Exports: (name, kind, index)
    exports: Vec<(String, wasmparser::ExternalKind, u32)>,
    /// Memory initial pages
    memory_initial: u64,
    /// Memory maximum pages
    memory_maximum: Option<u64>,
    /// Whether memory is 64-bit
    memory64: bool,
    /// Number of function types in the type section
    #[allow(dead_code)]
    type_count: u32,
    /// The function types themselves (params, results)
    #[allow(dead_code)]
    func_types: Vec<(Vec<wasm_encoder::ValType>, Vec<wasm_encoder::ValType>)>,
}

/// Parse the fused module to extract structural info needed for wrapping.
fn parse_fused_module(bytes: &[u8]) -> Result<FusedModuleInfo> {
    let parser = wasmparser::Parser::new(0);
    let mut func_imports = Vec::new();
    let mut exports = Vec::new();
    let mut memory_initial = 1u64;
    let mut memory_maximum = None;
    let mut memory64 = false;
    let mut type_count = 0u32;
    let mut func_types = Vec::new();
    let mut found_memory = false;

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
                for imp in reader {
                    let imp = imp.map_err(|e| Error::ParseError(e.to_string()))?;
                    if let wasmparser::TypeRef::Func(type_idx) = imp.ty {
                        func_imports.push((imp.module.to_string(), imp.name.to_string(), type_idx));
                    }
                }
            }
            wasmparser::Payload::MemorySection(reader) => {
                for mem in reader {
                    let mem = mem.map_err(|e| Error::ParseError(e.to_string()))?;
                    if !found_memory {
                        memory_initial = mem.initial;
                        memory_maximum = mem.maximum;
                        memory64 = mem.memory64;
                        found_memory = true;
                    }
                }
            }
            wasmparser::Payload::ExportSection(reader) => {
                for exp in reader {
                    let exp = exp.map_err(|e| Error::ParseError(e.to_string()))?;
                    exports.push((exp.name.to_string(), exp.kind, exp.index));
                }
            }
            _ => {}
        }
    }

    if !found_memory {
        return Err(Error::EncodingError(
            "fused module has no memory section".to_string(),
        ));
    }

    Ok(FusedModuleInfo {
        func_imports,
        exports,
        memory_initial,
        memory_maximum,
        memory64,
        type_count,
        func_types,
    })
}

/// Build a tiny shim module that provides memory and a bump-allocator realloc.
///
/// ```wasm
/// (module
///   (memory (export "memory") <min> <max>)
///   (global $bump (mut i32) (i32.const 0))
///   (func (export "realloc") (param i32 i32 i32 i32) (result i32)
///     global.get $bump
///     local.get 3  ;; new_size
///     global.get $bump
///     i32.add
///     global.set $bump
///   )
/// )
/// ```
fn build_shim_module(min_pages: u64, max_pages: Option<u64>) -> Vec<u8> {
    use wasm_encoder::*;

    let mut module = Module::new();

    // Type section: realloc type (i32, i32, i32, i32) -> i32
    let mut types = TypeSection::new();
    types.ty().function([ValType::I32; 4], [ValType::I32]);
    module.section(&types);

    // Function section
    let mut functions = FunctionSection::new();
    functions.function(0); // realloc is type 0
    module.section(&functions);

    // Memory section
    let mut memories = MemorySection::new();
    memories.memory(MemoryType {
        minimum: min_pages,
        maximum: max_pages,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    module.section(&memories);

    // Global section: bump pointer
    let mut globals = GlobalSection::new();
    globals.global(
        wasm_encoder::GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(0),
    );
    module.section(&globals);

    // Export section
    let mut exports = ExportSection::new();
    exports.export("memory", ExportKind::Memory, 0);
    exports.export("realloc", ExportKind::Func, 0);
    module.section(&exports);

    // Code section: realloc body
    let mut code = CodeSection::new();
    let mut realloc_body = Function::new([]);
    // Return current bump pointer, then advance by new_size (param 3)
    realloc_body.instruction(&Instruction::GlobalGet(0)); // push current bump
    realloc_body.instruction(&Instruction::LocalGet(3)); // push new_size
    realloc_body.instruction(&Instruction::GlobalGet(0)); // push current bump again
    realloc_body.instruction(&Instruction::I32Add); // bump + new_size
    realloc_body.instruction(&Instruction::GlobalSet(0)); // store new bump
    // Stack still has original bump value as return
    realloc_body.instruction(&Instruction::End);
    code.function(&realloc_body);
    module.section(&code);

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
                for imp in reader {
                    let imp = imp.map_err(|e| Error::ParseError(e.to_string()))?;
                    let entity = convert_type_ref(imp.ty)?;
                    imports.import(imp.module, imp.name, entity);
                }
                // Append memory import at the end (after all function imports)
                imports.import(
                    "meld:shim",
                    "memory",
                    EntityType::Memory(MemoryType {
                        minimum: info.memory_initial,
                        maximum: info.memory_maximum,
                        memory64: info.memory64,
                        shared: false,
                        page_size_log2: None,
                    }),
                );
                module.section(&imports);
                wrote_imports = true;
            }
            wasmparser::Payload::MemorySection(reader) => {
                // Skip the first memory (now imported), keep any others
                let mut memories = MemorySection::new();
                let mut skipped_first = false;
                for mem in reader {
                    let mem = mem.map_err(|e| Error::ParseError(e.to_string()))?;
                    if !skipped_first {
                        skipped_first = true;
                        continue; // Skip first memory — now imported
                    }
                    memories.memory(MemoryType {
                        minimum: mem.initial,
                        maximum: mem.maximum,
                        memory64: mem.memory64,
                        shared: mem.shared,
                        page_size_log2: None,
                    });
                }
                if !memories.is_empty() {
                    module.section(&memories);
                }
                // Memory is now imported instead of defined
            }
            // For all other sections, copy them raw
            wasmparser::Payload::FunctionSection(reader) => {
                // If there was no import section, add one with just the memory
                if !wrote_imports {
                    let mut imports = ImportSection::new();
                    imports.import(
                        "meld:shim",
                        "memory",
                        EntityType::Memory(MemoryType {
                            minimum: info.memory_initial,
                            maximum: info.memory_maximum,
                            memory64: info.memory64,
                            shared: false,
                            page_size_log2: None,
                        }),
                    );
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
                let raw = &original_bytes[reader.range().start..reader.range().end];
                module.section(&RawSection { id: 7, data: raw });
            }
            wasmparser::Payload::StartSection { func, .. } => {
                module.section(&wasm_encoder::StartSection {
                    function_index: func,
                });
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

/// Assemble the final P2 component from replayed sections + shim + fused module.
fn assemble_component(
    source: &ParsedComponent,
    shim_bytes: &[u8],
    fused_bytes: &[u8],
    fused_info: &FusedModuleInfo,
) -> Result<Vec<u8>> {
    use wasm_encoder::*;

    let mut component = Component::new();

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

    // Count how many component-level instances were created by imports.
    // Each import with Instance type creates a component instance.
    let _import_instance_count = source
        .imports
        .iter()
        .filter(|imp| matches!(imp.ty, wasmparser::ComponentTypeRef::Instance(_)))
        .count() as u32;

    // -----------------------------------------------------------------------
    // 2. Alias core functions out of each component import instance.
    //    For each fused module import, we need to trace it back to a component
    //    instance + function name, then alias that function out.
    // -----------------------------------------------------------------------

    // Build a map: (wasi_module, wasi_field) → which component instance index
    // provides it, based on the original component's import names.
    //
    // Component imports like "wasi:io/streams@0.2.6" create component instances.
    // Functions like "get-stderr" are exports of "wasi:cli/stderr@0.2.6".
    // The fused module imports are "(wasi:cli/stderr@0.2.6, get-stderr)".
    let instance_map = build_instance_func_map(source);

    // For each fused function import, find which component instance + function
    // name it corresponds to, then we'll:
    //   a) alias the function from the component instance
    //   b) canon lower it with memory/realloc options
    //
    // Track: for each fused import → (component_instance_idx, func_name)
    let mut import_resolutions: Vec<(u32, String)> = Vec::new();
    for (module_name, field_name, _type_idx) in &fused_info.func_imports {
        if let Some((inst_idx, func_name)) =
            resolve_import_to_instance(source, module_name, field_name, &instance_map)
        {
            import_resolutions.push((inst_idx, func_name));
        } else {
            return Err(Error::EncodingError(format!(
                "cannot resolve fused import {}::{} to a component instance",
                module_name, field_name
            )));
        }
    }

    // -----------------------------------------------------------------------
    // 3. Core type sections — declare shim and fused module types
    // -----------------------------------------------------------------------
    // We need core module types for instantiation. However, for simplicity
    // we can use `ModuleSection` to embed modules directly (which carries
    // its own type), and use `Instantiate` with named args.

    // -----------------------------------------------------------------------
    // 4. Embed core modules as raw sections (section ID 1 = CoreModule)
    // -----------------------------------------------------------------------
    // Module 0: shim (memory + realloc)
    component.section(&RawSection {
        id: 1, // ComponentSectionId::CoreModule
        data: shim_bytes,
    });
    // Module 1: fused module (memory imported from shim)
    component.section(&RawSection {
        id: 1, // ComponentSectionId::CoreModule
        data: fused_bytes,
    });

    // -----------------------------------------------------------------------
    // 5. Instantiate the shim module (no imports needed)
    // -----------------------------------------------------------------------
    let mut core_instances = InstanceSection::new();
    let no_args: Vec<(&str, ModuleArg)> = vec![];
    core_instances.instantiate(0, no_args); // shim module, no args
    component.section(&core_instances);

    // -----------------------------------------------------------------------
    // 6. Alias shim exports: memory and realloc
    // -----------------------------------------------------------------------
    // core instance 0 = shim instance
    // We need: core func "realloc" (for canon lower options)
    //          core memory "memory" (for canon lower options)
    //
    // After aliasing:
    //   core func 0 = shim realloc
    //   core memory 0 = shim memory
    let mut aliases = ComponentAliasSection::new();
    aliases.alias(Alias::CoreInstanceExport {
        instance: 0,
        kind: ExportKind::Func,
        name: "realloc",
    });
    // core func index 0 = shim realloc
    aliases.alias(Alias::CoreInstanceExport {
        instance: 0,
        kind: ExportKind::Memory,
        name: "memory",
    });
    // core memory index 0 = shim memory
    component.section(&aliases);

    // -----------------------------------------------------------------------
    // 7. For each fused import: either alias+lower a function, or alias a
    //    type and use canon resource.drop
    // -----------------------------------------------------------------------
    // Component func index counter starts after any funcs from imports
    // (none in our case since we only import instances).
    let mut component_func_idx = 0u32;
    // Component type index: tracks type aliases we create for resource-drops.
    // This starts after all types defined in the replayed depth_0_sections.
    // Count how many types were defined in the replayed sections.
    let mut component_type_idx = count_replayed_types(source);
    // Core func index counter: 0 = shim realloc, then 1..N = lowered/resource-drop
    let mut core_func_idx = 1u32; // 0 is shim realloc

    for (i, (inst_idx, func_name)) in import_resolutions.iter().enumerate() {
        let field_name = &fused_info.func_imports[i].1;

        if let Some(type_name) = field_name.strip_prefix("[resource-drop]") {
            // Resource-drop: alias the TYPE from the instance, then canon resource.drop

            let mut alias_section = ComponentAliasSection::new();
            alias_section.alias(Alias::InstanceExport {
                instance: *inst_idx,
                kind: ComponentExportKind::Type,
                name: type_name,
            });
            component.section(&alias_section);

            let mut canon = CanonicalFunctionSection::new();
            canon.resource_drop(component_type_idx);
            component.section(&canon);

            component_type_idx += 1;
            core_func_idx += 1;
        } else {
            // Regular function: alias from instance, then canon lower
            let mut alias_section = ComponentAliasSection::new();
            alias_section.alias(Alias::InstanceExport {
                instance: *inst_idx,
                kind: ComponentExportKind::Func,
                name: func_name,
            });
            component.section(&alias_section);

            let mut canon = CanonicalFunctionSection::new();
            canon.lower(
                component_func_idx,
                [
                    CanonicalOption::Memory(0),  // core memory 0 = shim memory
                    CanonicalOption::Realloc(0), // core func 0 = shim realloc
                    CanonicalOption::UTF8,
                ],
            );
            component.section(&canon);

            component_func_idx += 1;
            core_func_idx += 1;
        }
    }

    // -----------------------------------------------------------------------
    // 8. Instantiate the fused module with all its imports satisfied
    // -----------------------------------------------------------------------
    // The fused module (after conversion) expects:
    //   - N function imports (in order, matching original fused import names)
    //   - 1 memory import ("meld:shim" "memory")
    //
    // We need to build a list of (import_name, core_func/memory_index) pairs.
    // Core module instantiation uses named args matching the module's imports.
    //
    // Strategy: wrap all the lowered funcs + shim memory into a FromExports
    // instance for each import module name, then instantiate with those.

    // Group fused imports by module name
    let mut module_groups: Vec<(String, Vec<(String, u32)>)> = Vec::new();
    for (i, (module_name, field_name, _)) in fused_info.func_imports.iter().enumerate() {
        let core_idx = i as u32 + 1; // +1 because core func 0 = shim realloc
        if let Some(group) = module_groups.iter_mut().find(|(m, _)| m == module_name) {
            group.1.push((field_name.clone(), core_idx));
        } else {
            module_groups.push((module_name.clone(), vec![(field_name.clone(), core_idx)]));
        }
    }

    // Create a FromExports core instance for each import module
    // Core instance counter: 0 = shim instance, then 1..M = import instances
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

    // Create a FromExports instance for the "meld:shim" module (memory)
    {
        let mut inst = InstanceSection::new();
        inst.export_items([("memory", ExportKind::Memory, 0u32)]);
        component.section(&inst);
        module_instance_map.push(("meld:shim".to_string(), next_core_instance));
        next_core_instance += 1;
    }

    // Now instantiate the fused module (module 1) with all import instances
    {
        let mut inst = InstanceSection::new();
        let args: Vec<(&str, ModuleArg)> = module_instance_map
            .iter()
            .map(|(name, idx)| (name.as_str(), ModuleArg::Instance(*idx)))
            .collect();
        inst.instantiate(1, args);
        component.section(&inst);
        // This is core instance `next_core_instance`, let's call it fused_instance
    }
    let fused_instance = next_core_instance;

    // -----------------------------------------------------------------------
    // 9. Alias core exports from the fused instance, lift, and export
    // -----------------------------------------------------------------------
    // Find the "run" export (or whatever the component exports)
    // For hello_c_cli, the key export is "wasi:cli/run@0.2.6#run"
    //
    // We need to:
    //   a) alias the core function from the fused instance
    //   b) find the component function type for lifting
    //   c) canon lift
    //   d) component export

    // Find component-level exports from the source component
    for comp_export in &source.exports {
        // Find the matching core export name in the fused module
        let core_export_name = &comp_export.name;

        // Look for a matching export in the fused module
        let core_export = fused_info.exports.iter().find(|(name, kind, _)| {
            name == core_export_name && *kind == wasmparser::ExternalKind::Func
        });

        if let Some((export_name, _, _export_idx)) = core_export {
            // Alias the core function from the fused instance
            let mut alias_section = ComponentAliasSection::new();
            alias_section.alias(Alias::CoreInstanceExport {
                instance: fused_instance,
                kind: ExportKind::Func,
                name: export_name,
            });
            component.section(&alias_section);
            let aliased_core_func = core_func_idx;
            core_func_idx += 1;

            // Also alias memory from fused instance for the lift options
            let mut mem_alias = ComponentAliasSection::new();
            mem_alias.alias(Alias::CoreInstanceExport {
                instance: fused_instance,
                kind: ExportKind::Memory,
                name: "memory",
            });
            component.section(&mem_alias);
            // This creates core memory index 1 (0 was shim memory alias)
            // Actually, we only need one memory alias for lift. Let's track it.

            // Find the component type index for this export's function type.
            // We need to look at the source's canonical lift entries to find
            // the type_index for this export.
            let lift_type = find_lift_type_for_export(source, comp_export);

            if let Some(type_idx) = lift_type {
                // Canon lift
                let mut canon = CanonicalFunctionSection::new();
                canon.lift(
                    aliased_core_func,
                    type_idx,
                    [
                        CanonicalOption::Memory(0),  // shim memory
                        CanonicalOption::Realloc(0), // shim realloc
                        CanonicalOption::UTF8,
                    ],
                );
                component.section(&canon);

                // Component export
                let mut exports = ComponentExportSection::new();
                exports.export(
                    &comp_export.name,
                    ComponentExportKind::Func,
                    component_func_idx,
                    None,
                );
                component.section(&exports);
                component_func_idx += 1;
            }
        }
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

    // Fall back to module name matching (for resource-drops and other fields
    // not explicitly in the alias list)
    for (inst_idx, def) in source.component_instance_defs.iter().enumerate() {
        if let parser::ComponentInstanceDef::Import(import_idx) = def {
            let import = &source.imports[*import_idx];
            if import.name == module_name {
                return Some((inst_idx as u32, field_name.to_string()));
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
    // ComponentTypeRef tags:
    //   0x01 = Module, 0x02 = Func, 0x03 = Value, 0x04 = Type, 0x05 = Instance, 0x06 = Component
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
        if ty_tag == 0x04 {
            // Type: has bounds tag + index
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

/// Find the component type index used for lifting a given component export.
fn find_lift_type_for_export(
    source: &ParsedComponent,
    export: &parser::ComponentExport,
) -> Option<u32> {
    // The export references a component function by index.
    // That function was created by a canon lift entry.
    // The canon lift has a type_index.
    //
    // Walk component_func_defs to find the Lift entry at the export's index.
    if let Some(parser::ComponentFuncDef::Lift(canon_idx)) =
        source.component_func_defs.get(export.index as usize)
        && let Some(parser::CanonicalEntry::Lift { type_index, .. }) =
            source.canonical_functions.get(*canon_idx)
    {
        return Some(*type_index);
    }

    // For indirect exports (through sub-components), the export may reference
    // a function that was aliased, not directly lifted. In that case, look
    // for the lift in the sub-component chain. For now, try a simpler approach:
    // find any lift entry that matches by export name pattern.
    for canon in &source.canonical_functions {
        if let parser::CanonicalEntry::Lift { type_index, .. } = canon {
            // Use the first lift we find as a fallback
            return Some(*type_index);
        }
    }

    None
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
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_count_replayed_types_hello_c_cli() {
        let bytes = std::fs::read("../tests/wit_bindgen/fixtures/release-0.2.0/hello_c_cli.wasm")
            .expect("hello_c_cli fixture");
        let parser = crate::ComponentParser::new();
        let parsed = parser.parse(&bytes).unwrap();

        let count = count_replayed_types(&parsed);
        // hello_c_cli has 14 ComponentType entries + 7 Type aliases = 21 types
        // defined in the interface sections before core modules
        assert_eq!(count, 21, "expected 21 replayed types for hello_c_cli");
    }

    #[test]
    fn test_build_shim_module_validates() {
        let shim = build_shim_module(1, None);
        let mut validator = wasmparser::Validator::new();
        validator
            .validate_all(&shim)
            .expect("shim module should validate");
    }

    #[test]
    fn test_build_shim_module_with_max() {
        let shim = build_shim_module(2, Some(256));
        let mut validator = wasmparser::Validator::new();
        validator
            .validate_all(&shim)
            .expect("shim module with max should validate");

        // Verify it has the right memory limits
        let parser = wasmparser::Parser::new(0);
        for payload in parser.parse_all(&shim) {
            if let Ok(wasmparser::Payload::MemorySection(reader)) = payload {
                for mem in reader {
                    let mem = mem.unwrap();
                    assert_eq!(mem.initial, 2);
                    assert_eq!(mem.maximum, Some(256));
                }
            }
        }
    }
}
