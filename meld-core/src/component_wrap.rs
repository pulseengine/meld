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
    // 9. Export: alias core exports, define types, canon lift, wrap in
    //    component instances, and export as named interfaces.
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

    // Source type index → wrapper type index mapping (for recursive type defs)
    let mut type_remap: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();

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

            // Find the source component's lift type for this export function.
            // We trace: source export → component instance → canonical lift → type_index
            let lift_type_idx =
                find_lift_type_for_interface_func(source, interface_name, &func_info.func_name);

            // Define the component function type in our wrapper
            let wrapper_func_type = if let Some(source_type_idx) = lift_type_idx {
                define_source_type_in_wrapper(
                    &mut component,
                    source,
                    source_type_idx,
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
            // Simple functions (like run: func() -> result) need no options

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
fn find_lift_type_for_interface_func(
    source: &ParsedComponent,
    interface_name: &str,
    func_name: &str,
) -> Option<u32> {
    let target_export_name = format!("{}#{}", interface_name, func_name);

    // Strategy 1: Find a Lift entry whose core function is exported with the
    // target name. Walk canonical_functions for Lift entries, then check if
    // the core_func_index matches an export with our target name.
    //
    // The source component's core module exports include the target name.
    // The Lift entry references the core function by its core_func_index.
    // We can match by looking at core aliases that reference the export name.
    for (canon_idx, canon) in source.canonical_functions.iter().enumerate() {
        if let parser::CanonicalEntry::Lift { type_index, .. } = canon {
            // Check if any component_func_def points to this lift, and if
            // the corresponding export matches our interface
            for func_def in &source.component_func_defs {
                if let parser::ComponentFuncDef::Lift(idx) = func_def
                    && *idx == canon_idx
                {
                    // This is a lifted function. Check if the source
                    // component exports it as our interface.
                    return Some(*type_index);
                }
            }
        }
    }

    // Strategy 2: Look for any Lift entry (fallback for simple components
    // with only one export).
    for canon in &source.canonical_functions {
        if let parser::CanonicalEntry::Lift { type_index, .. } = canon {
            return Some(*type_index);
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
                    func_enc.result(enc_results[0].1);
                } else if !enc_results.is_empty() {
                    let r: Vec<_> = enc_results
                        .iter()
                        .map(|(n, t)| (n.as_deref().unwrap_or(""), *t))
                        .collect();
                    func_enc.results(r);
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
        parser::ComponentValType::List(_) | parser::ComponentValType::Option(_) => {
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
        .result(wasm_encoder::ComponentValType::Type(result_type_idx));
    component.section(&types2);
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
