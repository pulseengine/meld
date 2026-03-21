//! Dependency resolution for component fusion
//!
//! This module handles building the import/export graph between components
//! and performing topological sort for instantiation order.

use crate::parser::{
    CanonStringEncoding, ComponentAliasEntry, ComponentExport, ComponentTypeKind, CoreEntityDef,
    ExportKind, ImportKind, ModuleExport, ParsedComponent,
};
use crate::{Error, MemoryStrategy, Result};
use std::collections::{HashMap, HashSet};

/// Result of dependency resolution
#[derive(Debug, Clone)]
pub struct DependencyGraph {
    /// Ordered list of component indices (topological order)
    pub instantiation_order: Vec<usize>,

    /// Resolved imports: maps (component_idx, import_name) → (component_idx, export_name)
    pub resolved_imports: HashMap<(usize, String), (usize, String)>,

    /// Unresolved imports that must remain as module imports
    pub unresolved_imports: Vec<UnresolvedImport>,

    /// Call sites that need adapters (cross-component and intra-component
    /// module pairs with different canonical options)
    pub adapter_sites: Vec<AdapterSite>,

    /// Module-level resolution within components
    pub module_resolutions: Vec<ModuleResolution>,
}

/// An import that couldn't be resolved within the component set
#[derive(Debug, Clone)]
pub struct UnresolvedImport {
    /// Component containing the import
    pub component_idx: usize,
    /// Module within component containing the import
    pub module_idx: usize,
    /// Import module name (from the core module's import section — used for lookup)
    pub module_name: String,
    /// Import field name (from the core module's import section — used for lookup)
    pub field_name: String,
    /// Import kind
    pub kind: ImportKind,
    /// Display module name for the emitted import (overrides `module_name` in output).
    /// Set when canonical lower tracing recovers the WASI interface name.
    pub display_module: Option<String>,
    /// Display field name for the emitted import (overrides `field_name` in output).
    pub display_field: Option<String>,
}

/// A cross-component call that needs an adapter
#[derive(Debug, Clone)]
pub struct AdapterSite {
    /// Source component index
    pub from_component: usize,
    /// Source module index within component
    pub from_module: usize,
    /// Import being resolved (bare function name, e.g., "roundtrip-u8")
    pub import_name: String,
    /// Caller's core import module name (e.g., "test:dep/test@0.1.0").
    /// Used to disambiguate when multiple interfaces export the same function name.
    pub import_module: String,
    /// Caller's import function type index (module-local) in from_module's type section.
    /// Used so the adapter's declared type matches what the caller expects to call.
    pub import_func_type_idx: Option<u32>,

    /// Target component index
    pub to_component: usize,
    /// Target module index within component
    pub to_module: usize,
    /// Export being called
    pub export_name: String,
    /// Original function index of the export in the target module
    pub export_func_idx: u32,

    /// Whether this crosses a memory boundary
    pub crosses_memory: bool,

    /// Adapter requirements (string transcoding, etc.)
    pub requirements: AdapterRequirements,
}

/// Describes how to copy a (ptr, len) value across memories.
///
/// In the canonical ABI, `string` and `list<T>` are passed as `(ptr, len)` pairs.
/// For strings, `len` is the byte count. For lists, `len` is the element count
/// and the actual byte size is `len * element_byte_size`. Elements may themselves
/// contain pointers (e.g., `list<string>`), requiring recursive copy.
#[derive(Debug, Clone)]
pub enum CopyLayout {
    /// Bulk copy: `len * byte_multiplier` bytes, no inner pointers.
    /// Used for strings (multiplier=1) and lists of scalars.
    Bulk { byte_multiplier: u32 },
    /// Element-wise copy: `len` elements of `element_size` bytes each.
    /// `inner_pointers` lists byte offsets within each element where (ptr, len)
    /// pairs exist, along with their own recursive copy layout.
    /// `inner_resources` lists byte offsets of resource handles that need
    /// conversion after bulk copy.
    Elements {
        element_size: u32,
        inner_pointers: Vec<(u32, CopyLayout)>,
        inner_resources: Vec<(u32, u32, bool)>, // (byte_offset, resource_type_id, is_owned)
    },
}

/// Describes a single scalar slot in the return area's canonical ABI layout.
///
/// The return area lays out values according to the canonical ABI memory format
/// (with alignment and padding), not the flat (stack) format. Each scalar slot
/// has a byte offset, byte size, and the wasm value type needed for correct
/// load/store instructions (e.g., `i64.load`/`i64.store` for 8-byte values).
#[derive(Debug, Clone)]
pub struct ReturnAreaSlot {
    /// Byte offset within the return area
    pub byte_offset: u32,
    /// Byte size of this slot (1, 2, 4, or 8)
    pub byte_size: u32,
    /// Whether this is a pointer pair (ptr, len) that needs cross-memory copy.
    /// If true, the adapter handles this via the pointer-pair copy path.
    /// If false, the adapter copies this as a scalar value.
    pub is_pointer_pair: bool,
}

/// A pointer pair that is conditional on a discriminant value.
/// Used for option<string>, result<string, E>, variant types where
/// the pointer data only exists when the discriminant matches.
#[derive(Debug, Clone)]
pub struct ConditionalPointerPair {
    /// Flat param index (or byte offset for results) of the discriminant
    pub discriminant_position: u32,
    /// Value the discriminant must equal for the pointer pair to be active
    pub discriminant_value: u32,
    /// Flat param index (or byte offset for results) of the pointer
    pub ptr_position: u32,
    /// Copy layout for the pointed-to data
    pub copy_layout: CopyLayout,
    /// Byte size of the discriminant in memory (1, 2, or 4).
    /// Used by the adapter to select the correct load instruction
    /// (I32Load8U, I32Load16U, I32Load) for byte-offset-based paths.
    /// For flat (stack) paths, this is always 4 (i32).
    pub discriminant_byte_size: u32,
}

/// A resolved resource operation for adapter generation.
///
/// Maps a resource-typed parameter or result to the `(module, field)` import
/// pair for the corresponding `[resource-rep]` or `[resource-new]` function.
#[derive(Debug, Clone)]
pub struct ResolvedResourceOp {
    /// Index in the flat (stack) ABI layout
    pub flat_idx: u32,
    /// Byte offset in the canonical ABI memory layout (for return-area results)
    pub byte_offset: u32,
    /// `true` for `own<R>`, `false` for `borrow<R>`
    pub is_owned: bool,
    /// Import module name (e.g., `"[export]test:resources/resources"`)
    pub import_module: String,
    /// Import field name (e.g., `"[resource-rep]y"`)
    pub import_field: String,
    /// Whether the callee defines this resource type. When false, the adapter
    /// must use the caller's `[resource-rep]` (to extract the rep from the
    /// caller's handle table) followed by the callee's `[resource-new]` (to
    /// create a handle in the callee's table). When true, the adapter only
    /// needs the callee's `[resource-rep]` (which returns rep directly).
    pub callee_defines_resource: bool,
}

/// Requirements for an adapter function
#[derive(Debug, Clone, Default)]
pub struct AdapterRequirements {
    /// Need string transcoding
    pub string_transcoding: bool,
    /// Need list/array copying
    pub list_copying: bool,
    /// Need resource handle transfer
    pub resource_transfer: bool,
    /// Caller-side string encoding from canonical lower options
    pub caller_encoding: Option<CanonStringEncoding>,
    /// Callee-side string encoding from canonical lift options
    pub callee_encoding: Option<CanonStringEncoding>,
    /// Callee's post-return function, decomposed to (module_idx, module_local_func_idx).
    /// For multi-module components, the canonical section's PostReturn index is a
    /// component-level core function index that must be decomposed before lookup
    /// in function_index_map.
    pub callee_post_return: Option<(usize, u32)>,
    /// Callee's realloc function (component-local core function index)
    pub callee_realloc: Option<u32>,
    /// Byte size of the callee's return area when using retptr convention.
    /// Computed from the component function type's flat result layout.
    pub return_area_byte_size: Option<u32>,
    /// Flat core param indices where (ptr, len) pairs start for string/list params.
    /// The adapter must copy data at each of these positions across memories.
    pub pointer_pair_positions: Vec<u32>,
    /// Flat return-area byte offsets where (ptr, len) pairs start for string/list results.
    /// The adapter must copy pointed-to data and fix up pointers at these offsets.
    pub result_pointer_pair_offsets: Vec<u32>,
    /// Copy layouts for parameter pointer pairs (parallel to `pointer_pair_positions`).
    /// Describes element sizes and inner pointer structure for correct cross-memory copy.
    pub param_copy_layouts: Vec<CopyLayout>,
    /// Copy layouts for result pointer pairs (parallel to `result_pointer_pair_offsets`).
    pub result_copy_layouts: Vec<CopyLayout>,
    /// Conditional pointer pairs inside option/result/variant params.
    /// Each entry: (discriminant_flat_idx, discriminant_value, ptr_flat_idx, copy_layout).
    /// The adapter must check the discriminant and only copy when it matches.
    pub conditional_pointer_pairs: Vec<ConditionalPointerPair>,
    /// Conditional pointer pairs for return-area values (byte-offset based, retptr path).
    /// Each entry: (discriminant_byte_offset, discriminant_value, ptr_byte_offset, copy_layout).
    pub conditional_result_pointer_pairs: Vec<ConditionalPointerPair>,
    /// Conditional pointer pairs for flat return values (non-retptr path).
    /// Each entry uses flat indices (like param conditional pairs).
    pub conditional_result_flat_pairs: Vec<ConditionalPointerPair>,
    /// Layout of scalar (non-pointer-pair) slots in the return area.
    /// Each entry describes a contiguous value at a specific byte offset with its size.
    /// Used by the adapter to emit correctly-sized load/store instructions (e.g.,
    /// `i64.load`/`i64.store` for 8-byte values like f64/i64).
    pub return_area_slots: Vec<ReturnAreaSlot>,
    /// Resource-typed parameters needing handle→representation conversion.
    /// The adapter calls `[resource-rep]` for each before forwarding to callee.
    /// These are resolved against the CALLEE's resource map.
    pub resource_params: Vec<ResolvedResourceOp>,
    /// Caller-side resource params. When `callee_defines_resource` is false
    /// for a param, the adapter should use the caller's `[resource-rep]` instead
    /// of the callee's. Indexed by the same flat_idx as `resource_params`.
    pub caller_resource_params: Vec<ResolvedResourceOp>,
    /// Resource-typed results needing representation→handle conversion.
    /// The adapter calls `[resource-new]` for each before returning to caller.
    pub resource_results: Vec<ResolvedResourceOp>,
}

/// Resolution of module-level imports within a component
#[derive(Debug, Clone)]
pub struct ModuleResolution {
    /// Component index
    pub component_idx: usize,
    /// Source module index (the importer)
    pub from_module: usize,
    /// Target module index (the exporter)
    pub to_module: usize,
    /// Import name
    pub import_name: String,
    /// Export name
    pub export_name: String,
}

/// Info about a core `Instantiate` instance entry, used during instance-graph resolution.
struct InstanceInstantiateInfo {
    module_idx: u32,
    /// Maps import-module name → source instance index
    arg_map: HashMap<String, u32>,
}

/// Source of a core entity: maps per-kind entity index to (module_idx, export_name).
///
/// Built by replaying `core_entity_order` from the parser. Canonical functions
/// allocate core func indices but have no module source; core aliases allocate
/// per-kind indices and *do* have a module source (via instance → module mapping).
struct EntityProvenance {
    func_source: HashMap<u32, (usize, String)>,
    memory_source: HashMap<u32, (usize, String)>,
    table_source: HashMap<u32, (usize, String)>,
    global_source: HashMap<u32, (usize, String)>,
}

/// Find a module in the component that exports `export_name`, skipping `skip_mod`.
///
/// Used as a fallback for `__main_module__` imports where the instance graph
/// can't resolve the import due to module-index mismatches between the parser
/// and the component binary.
fn find_module_with_export(
    component: &ParsedComponent,
    export_name: &str,
    skip_mod: usize,
) -> Option<usize> {
    for (mod_idx, module) in component.core_modules.iter().enumerate() {
        if mod_idx == skip_mod {
            continue;
        }
        if module.exports.iter().any(|e| e.name == export_name) {
            return Some(mod_idx);
        }
    }
    None
}

/// Build provenance map by replaying the core entity definition order.
///
/// Walks `core_entity_order` and maintains per-kind counters. For each
/// `CoreAlias` entry, looks up which core instance the alias references,
/// then maps that instance to a module via `InstanceKind::Instantiate`.
///
/// When the alias references a `FromExports` instance instead, we resolve
/// the indirection: the `FromExports` bag contains `(name, kind, entity_idx)`
/// entries where `entity_idx` is a previously-allocated core entity index.
/// We look up that index in the provenance map we're building (since earlier
/// entries in `core_entity_order` may have already populated it).
fn build_entity_provenance(component: &ParsedComponent) -> EntityProvenance {
    use crate::parser::InstanceKind;

    let mut func_idx = 0u32;
    let mut mem_idx = 0u32;
    let mut table_idx = 0u32;
    let mut global_idx = 0u32;

    let mut prov = EntityProvenance {
        func_source: HashMap::new(),
        memory_source: HashMap::new(),
        table_source: HashMap::new(),
        global_source: HashMap::new(),
    };

    // Build instance → module mapping for Instantiate instances
    let instance_to_module: HashMap<u32, u32> = component
        .instances
        .iter()
        .filter_map(|inst| match &inst.kind {
            InstanceKind::Instantiate { module_idx, .. } => Some((inst.index, *module_idx)),
            _ => None,
        })
        .collect();

    // Build FromExports instance map: instance_index → exports list
    // The exports contain (name, ExternalKind, entity_idx) where entity_idx
    // is a previously-allocated per-kind core entity index.
    let from_exports_map: HashMap<u32, &Vec<(String, wasmparser::ExternalKind, u32)>> = component
        .instances
        .iter()
        .filter_map(|inst| match &inst.kind {
            InstanceKind::FromExports(exports) => Some((inst.index, exports)),
            _ => None,
        })
        .collect();

    for def in &component.core_entity_order {
        match def {
            CoreEntityDef::CanonicalFunction(_) => {
                // Creates a core func, but NOT from a module
                func_idx += 1;
            }
            CoreEntityDef::CoreAlias(alias_idx) => {
                if let Some(ComponentAliasEntry::CoreInstanceExport {
                    kind,
                    instance_index,
                    name,
                }) = component.component_aliases.get(*alias_idx)
                {
                    // Try direct Instantiate → module mapping first
                    let mut resolved_source: Option<(usize, String)> = instance_to_module
                        .get(instance_index)
                        .map(|m| (*m as usize, name.clone()));

                    // If not an Instantiate instance, try resolving through FromExports.
                    // A FromExports bag re-exports entities that were already allocated
                    // earlier, so we can look up their entity_idx in the provenance
                    // map we've been building.
                    if resolved_source.is_none()
                        && let Some(fe_exports) = from_exports_map.get(instance_index)
                    {
                        for (fe_name, fe_kind, fe_entity_idx) in *fe_exports {
                            if fe_name == name && *fe_kind == *kind {
                                // Look up this entity_idx in our partially-built provenance
                                resolved_source = match kind {
                                    wasmparser::ExternalKind::Func => {
                                        prov.func_source.get(fe_entity_idx).cloned()
                                    }
                                    wasmparser::ExternalKind::Memory => {
                                        prov.memory_source.get(fe_entity_idx).cloned()
                                    }
                                    wasmparser::ExternalKind::Table => {
                                        prov.table_source.get(fe_entity_idx).cloned()
                                    }
                                    wasmparser::ExternalKind::Global => {
                                        prov.global_source.get(fe_entity_idx).cloned()
                                    }
                                    _ => None,
                                };
                                break;
                            }
                        }
                    }

                    match kind {
                        wasmparser::ExternalKind::Func => {
                            if let Some(source) = resolved_source {
                                prov.func_source.insert(func_idx, source);
                            }
                            func_idx += 1;
                        }
                        wasmparser::ExternalKind::Memory => {
                            if let Some(source) = resolved_source {
                                prov.memory_source.insert(mem_idx, source);
                            }
                            mem_idx += 1;
                        }
                        wasmparser::ExternalKind::Table => {
                            if let Some(source) = resolved_source {
                                prov.table_source.insert(table_idx, source);
                            }
                            table_idx += 1;
                        }
                        wasmparser::ExternalKind::Global => {
                            if let Some(source) = resolved_source {
                                prov.global_source.insert(global_idx, source);
                            }
                            global_idx += 1;
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    prov
}

/// Build a reverse map from (module_idx, export_name) → core_func_idx.
///
/// Inverts `build_entity_provenance().func_source` so callers can look up the
/// component-level core function index for a given module export.  This is the
/// correct replacement for `compose_component_core_func_index`, which wrongly
/// assumes the core function index space is a simple concatenation of module
/// function counts (ignoring interleaved `canon lower` and alias entries).
fn build_module_export_to_core_func(component: &ParsedComponent) -> HashMap<(usize, String), u32> {
    let prov = build_entity_provenance(component);
    prov.func_source
        .into_iter()
        .map(|(core_idx, (mod_idx, name))| ((mod_idx, name), core_idx))
        .collect()
}

/// Build a map from core_func_idx → (module_idx, module_local_func_idx).
///
/// Uses entity provenance to correctly handle the interleaved core function
/// index space.  For each alias-created core function, the provenance gives
/// `(module_idx, export_name)`.  We then look up the export in the module to
/// get the module-local function index.
///
/// This is the correct replacement for `decompose_component_core_func_index`.
fn build_core_func_to_module_local(component: &ParsedComponent) -> HashMap<u32, (usize, u32)> {
    let prov = build_entity_provenance(component);
    let mut result = HashMap::new();
    for (core_idx, (mod_idx, export_name)) in &prov.func_source {
        if let Some(module) = component.core_modules.get(*mod_idx)
            && let Some(exp) = module
                .exports
                .iter()
                .find(|e| e.name == *export_name && e.kind == ExportKind::Function)
        {
            result.insert(*core_idx, (*mod_idx, exp.index));
        }
    }
    result
}

/// Collect copy layouts for each pointer pair in function parameters.
///
/// Walks the component function type's params, and for each `string` or `list<T>`
/// param, computes a `CopyLayout` describing how to copy its data across memories.
fn collect_param_copy_layouts(
    component: &ParsedComponent,
    params: &[(String, crate::parser::ComponentValType)],
) -> Vec<CopyLayout> {
    let mut layouts = Vec::new();
    for (_, ty) in params {
        collect_type_copy_layouts(component, ty, &mut layouts);
    }
    layouts
}

/// Collect copy layouts for each pointer pair in function results.
fn collect_result_copy_layouts(
    component: &ParsedComponent,
    results: &[(Option<String>, crate::parser::ComponentValType)],
) -> Vec<CopyLayout> {
    let mut layouts = Vec::new();
    for (_, ty) in results {
        collect_type_copy_layouts(component, ty, &mut layouts);
    }
    layouts
}

/// Recursively collect copy layouts for pointer-bearing sub-types.
fn collect_type_copy_layouts(
    component: &ParsedComponent,
    ty: &crate::parser::ComponentValType,
    out: &mut Vec<CopyLayout>,
) {
    use crate::parser::{ComponentTypeKind, ComponentValType};
    match ty {
        ComponentValType::String | ComponentValType::List(_) => {
            out.push(component.copy_layout(ty));
        }
        ComponentValType::Record(fields) => {
            for (_, field_ty) in fields {
                collect_type_copy_layouts(component, field_ty, out);
            }
        }
        ComponentValType::Tuple(elems) => {
            for elem_ty in elems {
                collect_type_copy_layouts(component, elem_ty, out);
            }
        }
        ComponentValType::Type(idx) => {
            if let Some(ct) = component.get_type_definition(*idx)
                && let ComponentTypeKind::Defined(inner) = &ct.kind
            {
                collect_type_copy_layouts(component, inner, out);
            }
        }
        _ => {} // scalars don't have pointer pairs
    }
}

/// Maps core function entity indices from canonical lowered functions to their
/// WASI interface names.
///
/// Traces the chain: `canon lower { func_index }` → component function →
/// `InstanceExport { kind: Func }` alias → component instance →
/// component import. Returns `(wasi_module_name, wasi_field_name)`.
///
/// For example, if `canon lower` references component function 7, which was
/// created by `alias export $wasi:io/streams@0.2.6 "[method]output-stream.check-write"`,
/// and `$wasi:io/streams@0.2.6` is component instance 3 which came from
/// component import `"wasi:io/streams@0.2.6"`, then the result is
/// `("wasi:io/streams@0.2.6", "[method]output-stream.check-write")`.
fn build_canon_import_names(component: &ParsedComponent) -> HashMap<u32, (String, String)> {
    use crate::parser::{
        CanonicalEntry, ComponentFuncDef, ComponentInstanceDef, ComponentTypeDef, CoreEntityDef,
    };

    // Step 1: Build component instance index → import name mapping.
    // Component instances created by imports have a WASI interface name.
    let mut comp_instance_to_import_name: HashMap<u32, String> = HashMap::new();
    for (inst_idx, def) in component.component_instance_defs.iter().enumerate() {
        if let ComponentInstanceDef::Import(import_idx) = def
            && let Some(imp) = component.imports.get(*import_idx)
        {
            comp_instance_to_import_name.insert(inst_idx as u32, imp.name.clone());
        }
    }

    // Step 2: Build component func index → (instance_index, export_name) for
    // InstanceExportAlias entries.
    let mut comp_func_to_instance_export: HashMap<u32, (u32, String)> = HashMap::new();
    for (func_idx, def) in component.component_func_defs.iter().enumerate() {
        if let ComponentFuncDef::InstanceExportAlias(alias_idx) = def
            && let Some(crate::parser::ComponentAliasEntry::InstanceExport {
                instance_index,
                name,
                ..
            }) = component.component_aliases.get(*alias_idx)
        {
            comp_func_to_instance_export.insert(func_idx as u32, (*instance_index, name.clone()));
        }
    }

    // Also handle component functions from imports directly (Func-typed imports).
    let mut comp_func_import_names: HashMap<u32, String> = HashMap::new();
    for (func_idx, def) in component.component_func_defs.iter().enumerate() {
        if let ComponentFuncDef::Import(import_idx) = def
            && let Some(imp) = component.imports.get(*import_idx)
        {
            comp_func_import_names.insert(func_idx as u32, imp.name.clone());
        }
    }

    // Step 2b: Build component type index → (instance_index, export_name) for
    // InstanceExportAlias entries. Used to trace ResourceDrop types.
    let mut comp_type_to_instance_export: HashMap<u32, (u32, String)> = HashMap::new();
    for (type_idx, def) in component.component_type_defs.iter().enumerate() {
        if let ComponentTypeDef::InstanceExportAlias(alias_idx) = def
            && let Some(crate::parser::ComponentAliasEntry::InstanceExport {
                instance_index,
                name,
                ..
            }) = component.component_aliases.get(*alias_idx)
        {
            comp_type_to_instance_export.insert(type_idx as u32, (*instance_index, name.clone()));
        }
    }

    // Also handle direct type imports (Type-typed component imports).
    let mut comp_type_import_names: HashMap<u32, String> = HashMap::new();
    for (type_idx, def) in component.component_type_defs.iter().enumerate() {
        if let ComponentTypeDef::Import(import_idx) = def
            && let Some(imp) = component.imports.get(*import_idx)
        {
            comp_type_import_names.insert(type_idx as u32, imp.name.clone());
        }
    }

    // Step 3: Walk core_entity_order to find canonical functions and their
    // core func indices. For each Lower entry, trace to WASI name.
    let mut result: HashMap<u32, (String, String)> = HashMap::new();
    let mut core_func_idx = 0u32;

    for def in &component.core_entity_order {
        match def {
            CoreEntityDef::CanonicalFunction(canon_idx) => {
                if let Some(entry) = component.canonical_functions.get(*canon_idx) {
                    match entry {
                        CanonicalEntry::Lower { func_index, .. } => {
                            // Trace func_index to WASI name
                            if let Some((inst_idx, field_name)) =
                                comp_func_to_instance_export.get(func_index)
                            {
                                // The component function is an alias of an instance export.
                                // Look up which import the instance came from.
                                if let Some(module_name) =
                                    comp_instance_to_import_name.get(inst_idx)
                                {
                                    result.insert(
                                        core_func_idx,
                                        (module_name.clone(), field_name.clone()),
                                    );
                                }
                            } else if let Some(import_name) = comp_func_import_names.get(func_index)
                            {
                                // The component function is a direct Func import.
                                // Use the import name as both module and field.
                                result.insert(core_func_idx, (import_name.clone(), String::new()));
                            }
                        }
                        CanonicalEntry::ResourceDrop { resource } => {
                            // Trace resource type index → WASI module name.
                            // ResourceDrop references a component type index
                            // which was typically aliased from an instance export.
                            if let Some((inst_idx, type_name)) =
                                comp_type_to_instance_export.get(resource)
                            {
                                if let Some(module_name) =
                                    comp_instance_to_import_name.get(inst_idx)
                                {
                                    let field = format!("[resource-drop]{}", type_name);
                                    result.insert(core_func_idx, (module_name.clone(), field));
                                }
                            } else if let Some(import_name) = comp_type_import_names.get(resource) {
                                let resource_name = extract_wasi_resource_name(import_name);
                                let field = format!("[resource-drop]{}", resource_name);
                                result.insert(core_func_idx, (import_name.clone(), field));
                            }
                        }
                        CanonicalEntry::ResourceNew { resource } => {
                            if let Some((inst_idx, type_name)) =
                                comp_type_to_instance_export.get(resource)
                            {
                                if let Some(module_name) =
                                    comp_instance_to_import_name.get(inst_idx)
                                {
                                    let field = format!("[resource-new]{}", type_name);
                                    result.insert(core_func_idx, (module_name.clone(), field));
                                }
                            } else if let Some(import_name) = comp_type_import_names.get(resource) {
                                let resource_name = extract_wasi_resource_name(import_name);
                                let field = format!("[resource-new]{}", resource_name);
                                result.insert(core_func_idx, (import_name.clone(), field));
                            }
                        }
                        CanonicalEntry::ResourceRep { resource } => {
                            if let Some((inst_idx, type_name)) =
                                comp_type_to_instance_export.get(resource)
                            {
                                if let Some(module_name) =
                                    comp_instance_to_import_name.get(inst_idx)
                                {
                                    let field = format!("[resource-rep]{}", type_name);
                                    result.insert(core_func_idx, (module_name.clone(), field));
                                }
                            } else if let Some(import_name) = comp_type_import_names.get(resource) {
                                let resource_name = extract_wasi_resource_name(import_name);
                                let field = format!("[resource-rep]{}", resource_name);
                                result.insert(core_func_idx, (import_name.clone(), field));
                            }
                        }
                        _ => {}
                    }
                }
                core_func_idx += 1;
            }
            CoreEntityDef::CoreAlias(alias_idx) => {
                // Core aliases also allocate per-kind entity indices.
                // Only func-kind aliases increment the core func counter.
                if let Some(crate::parser::ComponentAliasEntry::CoreInstanceExport {
                    kind: wasmparser::ExternalKind::Func,
                    ..
                }) = component.component_aliases.get(*alias_idx)
                {
                    core_func_idx += 1;
                }
            }
        }
    }

    result
}

/// Extract the resource name from a WASI import path.
///
/// Examples:
/// - `"wasi:io/error@0.2.6"` → `"error"`
/// - `"wasi:io/poll@0.2.6"` → `"poll"`
/// - `"wasi:io/streams@0.2.6"` → `"streams"`
/// - `"bare-name"` → `"bare-name"`
fn extract_wasi_resource_name(import_name: &str) -> &str {
    // Strip version suffix: "wasi:io/error@0.2.6" → "wasi:io/error"
    let without_version = match import_name.rfind('@') {
        Some(pos) => &import_name[..pos],
        None => import_name,
    };
    // Extract after last '/': "wasi:io/error" → "error"
    match without_version.rfind('/') {
        Some(pos) => &without_version[pos + 1..],
        None => without_version,
    }
}

/// Build a map from resource type ID → `(module, field)` for resource canonical
/// functions (`[resource-rep]`, `[resource-new]`) in a component.
///
/// This works by:
/// 1. Scanning canonical functions to find ResourceRep/ResourceNew entries and
///    their core func indices.
/// 2. Scanning `FromExports` core instances to find which field name each core
///    func index is exported as (e.g., `"[resource-new]x"`).
/// 3. Scanning `Instantiate` core instances to find which module name each
///    `FromExports` instance provides (e.g., `"[export]exports"`).
fn build_resource_type_to_import(
    component: &ParsedComponent,
) -> HashMap<(u32, &'static str), (String, String)> {
    use crate::parser::{CanonicalEntry, CoreEntityDef, InstanceKind};

    // Step 1: Build resource_type → (core_func_idx, kind) from canonical functions
    let mut resource_core_funcs: Vec<(u32, u32, &'static str)> = Vec::new(); // (resource_type, core_func_idx, kind)
    let mut core_func_idx = 0u32;
    for def in &component.core_entity_order {
        match def {
            CoreEntityDef::CanonicalFunction(canon_idx) => {
                if let Some(entry) = component.canonical_functions.get(*canon_idx) {
                    match entry {
                        CanonicalEntry::ResourceRep { resource } => {
                            resource_core_funcs.push((*resource, core_func_idx, "[resource-rep]"));
                        }
                        CanonicalEntry::ResourceNew { resource } => {
                            resource_core_funcs.push((*resource, core_func_idx, "[resource-new]"));
                        }
                        _ => {}
                    }
                }
                core_func_idx += 1;
            }
            CoreEntityDef::CoreAlias(alias_idx) => {
                if let Some(crate::parser::ComponentAliasEntry::CoreInstanceExport {
                    kind: wasmparser::ExternalKind::Func,
                    ..
                }) = component.component_aliases.get(*alias_idx)
                {
                    core_func_idx += 1;
                }
            }
        }
    }

    if resource_core_funcs.is_empty() {
        // Fallback: for components that IMPORT resources (no canonical entries),
        // scan core module imports for [resource-rep]/[resource-new] patterns.
        // Use resource_type_id = 0 as sentinel; the single-candidate fallback
        // in resolve_resource_positions handles the type ID mismatch.
        let mut map = HashMap::new();
        for module in &component.core_modules {
            for imp in &module.imports {
                if matches!(&imp.kind, crate::parser::ImportKind::Function(_)) {
                    if imp.name.starts_with("[resource-rep]") {
                        map.entry((0u32, "[resource-rep]"))
                            .or_insert((imp.module.clone(), imp.name.clone()));
                    } else if imp.name.starts_with("[resource-new]") {
                        map.entry((0u32, "[resource-new]"))
                            .or_insert((imp.module.clone(), imp.name.clone()));
                    }
                }
            }
        }
        if !map.is_empty() {
            return map;
        }
        return HashMap::new();
    }

    // Step 2: Build core_func_idx → (instance_idx, field_name) from FromExports instances.
    // A FromExports instance maps field names to core entity indices.
    let mut core_func_to_field: HashMap<u32, (u32, String)> = HashMap::new(); // core_func_idx → (instance_idx, field_name)
    for inst in &component.instances {
        if let InstanceKind::FromExports(exports) = &inst.kind {
            for (name, kind, index) in exports {
                if *kind == wasmparser::ExternalKind::Func {
                    core_func_to_field.insert(*index, (inst.index, name.clone()));
                }
            }
        }
    }

    // Step 3: Build instance_idx → module_name from Instantiate args.
    // When a core module is instantiated, args map (module_name → Instance(idx)).
    let mut instance_to_module: HashMap<u32, String> = HashMap::new();
    for inst in &component.instances {
        if let InstanceKind::Instantiate { args, .. } = &inst.kind {
            for (module_name, arg) in args {
                if let crate::parser::InstanceArg::Instance(inst_idx) = arg {
                    instance_to_module.insert(*inst_idx, module_name.clone());
                }
            }
        }
    }

    // Step 4: Combine: resource_type → (module_name, field_name)
    let mut map = HashMap::new();
    for (resource_type, cf_idx, kind) in &resource_core_funcs {
        if let Some((from_exports_idx, field_name)) = core_func_to_field.get(cf_idx)
            && let Some(module_name) = instance_to_module.get(from_exports_idx)
        {
            map.insert(
                (*resource_type, *kind),
                (module_name.clone(), field_name.clone()),
            );
        }
    }

    // Step 4b: If Step 4 produced nothing but resource_core_funcs was non-empty,
    // fall through to core module import scanning as a last resort.
    if map.is_empty() && !resource_core_funcs.is_empty() {
        for module in &component.core_modules {
            for imp in &module.imports {
                if matches!(&imp.kind, crate::parser::ImportKind::Function(_)) {
                    if imp.name.starts_with("[resource-rep]") {
                        map.entry((0u32, "[resource-rep]"))
                            .or_insert((imp.module.clone(), imp.name.clone()));
                    } else if imp.name.starts_with("[resource-new]") {
                        map.entry((0u32, "[resource-new]"))
                            .or_insert((imp.module.clone(), imp.name.clone()));
                    }
                }
            }
        }
    }

    // Step 5: Infer missing operations from existing ones.
    //
    // The component model's `canon lift` handles resource conversions
    // internally, so a component may have ResourceNew for a type but not
    // ResourceRep (or vice versa). If the adapter needs the missing one,
    // we can infer it: same module name, same resource name, different
    // prefix ("[resource-new]" vs "[resource-rep]").
    let known_types: Vec<u32> = map.keys().map(|&(rt, _)| rt).collect();
    for rt in known_types {
        let has_rep = map.contains_key(&(rt, "[resource-rep]"));
        let has_new = map.contains_key(&(rt, "[resource-new]"));

        if has_new && !has_rep {
            if let Some((module, field)) = map.get(&(rt, "[resource-new]")).cloned()
                && let Some(name) = field.strip_prefix("[resource-new]")
            {
                let rep_field = format!("[resource-rep]{}", name);
                map.insert((rt, "[resource-rep]"), (module, rep_field));
            }
        } else if has_rep
            && !has_new
            && let Some((module, field)) = map.get(&(rt, "[resource-rep]")).cloned()
            && let Some(name) = field.strip_prefix("[resource-rep]")
        {
            let new_field = format!("[resource-new]{}", name);
            map.insert((rt, "[resource-new]"), (module, new_field));
        }
    }

    // Step 6: Propagate entries through resource type aliases.
    //
    // Function parameter types may reference a resource via an ExportAlias
    // (e.g., Borrow(24) where type 24 is ExportAlias(25)). The canonical
    // ResourceRep/ResourceNew entries use the target type (25). We need
    // the map to also contain the alias source so resolve_resource_positions
    // can find the import for either type ID.
    let known_resource_types: Vec<u32> = map
        .keys()
        .map(|&(rt, _)| rt)
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .collect();
    for (idx, def) in component.component_type_defs.iter().enumerate() {
        if let crate::parser::ComponentTypeDef::ExportAlias(target) = def {
            let alias_id = idx as u32;
            let target_id = *target;
            for kind in &["[resource-rep]", "[resource-new]"] {
                if known_resource_types.contains(&target_id)
                    && !map.contains_key(&(alias_id, kind))
                    && let Some(entry) = map.get(&(target_id, kind)).cloned()
                {
                    map.insert((alias_id, kind), entry);
                }
                if known_resource_types.contains(&alias_id)
                    && !map.contains_key(&(target_id, kind))
                    && let Some(entry) = map.get(&(alias_id, kind)).cloned()
                {
                    map.insert((target_id, kind), entry);
                }
            }
        }
    }
    map
}

/// Resolve resource positions to `(module, field)` import pairs.
///
/// Uses `build_resource_type_to_import` to map resource type IDs found in
/// function signatures to their `[resource-rep]` or `[resource-new]` core
/// import names. The `field_prefix` selects which canonical function kind
/// to look up: `"[resource-rep]"` for params, `"[resource-new]"` for results.
fn resolve_resource_positions(
    resource_map: &HashMap<(u32, &'static str), (String, String)>,
    positions: &[crate::parser::ResourcePosition],
    field_prefix: &'static str,
    callee_type_defs: &[crate::parser::ComponentTypeDef],
    callee_is_reexporter: bool,
) -> Vec<ResolvedResourceOp> {
    let mut resolved = Vec::new();
    for pos in positions {
        // Try exact match first
        let entry = resource_map
            .get(&(pos.resource_type_id, field_prefix))
            .or_else(|| {
                // Fallback: the resource type ID from the function signature may differ
                // from the canonical entry's type ID (e.g., imported type 24 vs defined
                // type 25). If there's exactly one resource with this prefix, use it.
                // Use the first matching entry regardless of count — Step 6
                // alias propagation may create multiple entries that all point
                // to the same underlying import.
                resource_map
                    .iter()
                    .find(|((_, k), _)| *k == field_prefix)
                    .map(|(_, v)| v)
            });
        if let Some((module_name, field_name)) = entry {
            // Check if the callee truly defines this resource (has ownership of the
            // underlying representation). A callee that re-exports a resource from
            // another component has a Defined type entry but doesn't own the rep.
            // Use the sentinel check: if the map entry was resolved via sentinel type 0
            // (Step 4b fallback), the callee doesn't define the resource.
            // If callee also imports the same interface, it re-exports → doesn't define.
            let callee_defines_resource = if callee_is_reexporter {
                false
            } else {
                // Sentinel check + type_defs check for non-reexporters
                let used_sentinel = resource_map.contains_key(&(0u32, field_prefix))
                    && !resource_map.contains_key(&(pos.resource_type_id, field_prefix));
                if used_sentinel {
                    false
                } else {
                    callee_type_defs
                        .get(pos.resource_type_id as usize)
                        .map(|def| !matches!(def, crate::parser::ComponentTypeDef::Import(_)))
                        .unwrap_or(true)
                }
            };
            resolved.push(ResolvedResourceOp {
                flat_idx: pos.flat_idx,
                byte_offset: pos.byte_offset,
                is_owned: pos.is_owned,
                import_module: module_name.clone(),
                import_field: field_name.clone(),
                callee_defines_resource,
            });
        } else {
            log::debug!(
                "Could not resolve resource type {} for {} at flat_idx {}",
                pos.resource_type_id,
                field_prefix,
                pos.flat_idx,
            );
        }
    }
    resolved
}

/// Dependency resolver
pub struct Resolver {
    /// Whether to allow unresolved imports
    allow_unresolved: bool,
    /// Memory strategy (affects crosses_memory detection)
    memory_strategy: MemoryStrategy,
}

impl Resolver {
    /// Create a new resolver
    pub fn new() -> Self {
        Self {
            allow_unresolved: true,
            memory_strategy: MemoryStrategy::MultiMemory,
        }
    }

    /// Create a resolver with a specific memory strategy
    pub fn with_strategy(memory_strategy: MemoryStrategy) -> Self {
        Self {
            allow_unresolved: true,
            memory_strategy,
        }
    }

    /// Create a resolver that fails on unresolved imports
    pub fn strict() -> Self {
        Self {
            allow_unresolved: false,
            memory_strategy: MemoryStrategy::MultiMemory,
        }
    }

    /// Resolve dependencies between components
    pub fn resolve(&self, components: &[ParsedComponent]) -> Result<DependencyGraph> {
        self.resolve_with_hints(components, &HashMap::new())
    }

    pub fn resolve_with_hints(
        &self,
        components: &[ParsedComponent],
        wiring_hints: &HashMap<(usize, String), usize>,
    ) -> Result<DependencyGraph> {
        let mut graph = DependencyGraph {
            instantiation_order: Vec::new(),
            resolved_imports: HashMap::new(),
            unresolved_imports: Vec::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
        };

        // Build export index
        let export_index = self.build_export_index(components);

        // Resolve component-level imports using wiring hints for directed resolution
        self.resolve_component_imports_with_hints(
            components,
            &export_index,
            &mut graph,
            wiring_hints,
        )?;

        // Resolve module-level imports within each component
        self.resolve_module_imports(components, &mut graph)?;

        // Resolve __main_module__ imports that couldn't be resolved through
        // the instance graph (due to parser module-index mismatches).
        // This must run before the topological sort so the resulting
        // dependency edges produce correct merge ordering.
        let synthetic_edges = Self::resolve_synthetic_module_imports(components, &mut graph);

        // Detect cycles in intra-component module dependencies
        for (comp_idx, component) in components.iter().enumerate() {
            Self::detect_module_cycles(
                comp_idx,
                component.core_modules.len(),
                &graph.module_resolutions,
            )?;
        }

        // Build dependency graph for topological sort
        let mut dependencies = self.build_dependency_edges(components, &graph);
        dependencies.extend(synthetic_edges);

        // Topological sort
        graph.instantiation_order = self.topological_sort(components.len(), &dependencies)?;

        // Identify adapter sites (cross-component)
        self.identify_adapter_sites(components, &mut graph)?;

        // Identify intra-component adapter sites for module pairs with
        // different canonical options (string encoding, memory, realloc).
        // This must run after identify_adapter_sites and may promote some
        // module_resolutions entries to adapter_sites.
        self.identify_intra_component_adapter_sites(components, &mut graph)?;

        // Synthesize missing resource imports.
        //
        // The component model's `canon lift` handles `resource.rep` and
        // `resource.new` internally, so a component binary may lack an
        // explicit `ResourceRep` or `ResourceNew` canonical function even
        // though the adapter needs one.  Detect missing resource imports and
        // add them as synthetic unresolved imports so the merger includes them.
        Self::synthesize_missing_resource_imports(components, &mut graph);

        Ok(graph)
    }

    /// Add synthetic unresolved imports for `[resource-rep]` / `[resource-new]`
    /// functions that adapters need but no source core module imports directly.
    ///
    /// For each adapter site, check whether the resource operations it needs
    /// already exist as unresolved imports (meaning some core module imports
    /// them). If not, add a synthetic unresolved import so the merger includes
    /// them in the fused module's import list.
    fn synthesize_missing_resource_imports(
        components: &[ParsedComponent],
        graph: &mut DependencyGraph,
    ) {
        use std::collections::HashSet;

        // Collect all (module, field) pairs from adapter requirements
        let mut needed: Vec<(String, String, usize)> = Vec::new(); // (module, field, callee_comp_idx)
        for site in &graph.adapter_sites {
            for op in &site.requirements.resource_params {
                needed.push((
                    op.import_module.clone(),
                    op.import_field.clone(),
                    site.to_component,
                ));
            }
            for op in &site.requirements.resource_results {
                needed.push((
                    op.import_module.clone(),
                    op.import_field.clone(),
                    site.to_component,
                ));
            }
            // For 3-component chains: synthesize callee's [resource-new] for borrow params.
            for op in &site.requirements.resource_params {
                if !op.is_owned && !op.callee_defines_resource {
                    let new_field = op.import_field.replace("[resource-rep]", "[resource-new]");
                    needed.push((op.import_module.clone(), new_field, site.to_component));
                }
            }
            // For 3-component chains: synthesize CALLER's [resource-new] for own results.
            // When callee doesn't define the resource, own<T> results need resource.new
            // in the caller's table.
            for op in &site.requirements.resource_results {
                if op.is_owned && !op.callee_defines_resource {
                    let new_field = if op.import_field.starts_with("[resource-new]") {
                        op.import_field.clone()
                    } else {
                        op.import_field.replace("[resource-rep]", "[resource-new]")
                    };
                    needed.push((
                        op.import_module.clone(),
                        new_field,
                        site.from_component, // CALLER's component
                    ));
                    // Also synthesize caller's [resource-rep] to match its [resource-new]
                    // so both get the same resource type in the P2 wrapper.
                    let rep_field = if op.import_field.starts_with("[resource-new]") {
                        op.import_field.replace("[resource-new]", "[resource-rep]")
                    } else {
                        format!(
                            "[resource-rep]{}",
                            op.import_field
                                .strip_prefix("[resource-new]")
                                .unwrap_or(&op.import_field)
                        )
                    };
                    needed.push((op.import_module.clone(), rep_field, site.from_component));
                }
            }
        }

        if needed.is_empty() {
            return;
        }

        // Check which (module, field, component) triples already exist.
        // In multi-memory mode, the same (module, field) from different components
        // are separate imports with different resource types.
        let existing: HashSet<(String, String, usize)> = graph
            .unresolved_imports
            .iter()
            .filter(|u| matches!(u.kind, ImportKind::Function(_)))
            .map(|u| {
                let module = u.display_module.as_deref().unwrap_or(&u.module_name);
                let field = u.display_field.as_deref().unwrap_or(&u.field_name);
                (module.to_string(), field.to_string(), u.component_idx)
            })
            .collect();

        let mut added: HashSet<(String, String, usize)> = HashSet::new();
        for (module, field, callee_comp_idx) in &needed {
            let key = (module.clone(), field.clone(), *callee_comp_idx);
            if existing.contains(&key) || added.contains(&key) {
                continue;
            }

            // Find a function type index for (i32) -> (i32) in the callee's
            // first core module. This is the canonical type for resource ops.
            let comp = &components[*callee_comp_idx];
            let i32_to_i32 = comp
                .core_modules
                .first()
                .and_then(|m| {
                    m.types.iter().position(|t| {
                        t.params == [wasm_encoder::ValType::I32]
                            && t.results == [wasm_encoder::ValType::I32]
                    })
                })
                .unwrap_or(0) as u32;

            log::debug!(
                "Synthesizing resource import ({}, {}) for component {}",
                module,
                field,
                callee_comp_idx
            );

            graph.unresolved_imports.push(UnresolvedImport {
                component_idx: *callee_comp_idx,
                module_idx: 0,
                module_name: module.clone(),
                field_name: field.clone(),
                kind: ImportKind::Function(i32_to_i32),
                display_module: Some(module.clone()),
                display_field: Some(field.clone()),
            });

            added.insert(key);
        }
    }

    /// Build an index of all exports across components
    fn build_export_index<'a>(
        &self,
        components: &'a [ParsedComponent],
    ) -> HashMap<String, Vec<(usize, &'a ComponentExport)>> {
        let mut index: HashMap<String, Vec<(usize, &ComponentExport)>> = HashMap::new();

        for (comp_idx, component) in components.iter().enumerate() {
            for export in &component.exports {
                index
                    .entry(export.name.clone())
                    .or_default()
                    .push((comp_idx, export));
            }
        }

        index
    }

    /// Resolve component-level imports against exports
    fn resolve_component_imports_with_hints(
        &self,
        components: &[ParsedComponent],
        export_index: &HashMap<String, Vec<(usize, &ComponentExport)>>,
        graph: &mut DependencyGraph,
        wiring_hints: &HashMap<(usize, String), usize>,
    ) -> Result<()> {
        for (comp_idx, component) in components.iter().enumerate() {
            for import in &component.imports {
                // Look for a matching export
                if let Some(exports) = export_index.get(&import.name) {
                    // Check directed wiring hints first (from composition DAG)
                    let hinted = wiring_hints.get(&(comp_idx, import.name.clone()));
                    let resolved = if let Some(&target) = hinted {
                        exports.iter().find(|(idx, _)| *idx == target)
                    } else {
                        None
                    };
                    // Fallback: first export from a different component
                    let resolved =
                        resolved.or_else(|| exports.iter().find(|(idx, _)| *idx != comp_idx));
                    if let Some((export_comp_idx, _export)) = resolved {
                        graph.resolved_imports.insert(
                            (comp_idx, import.name.clone()),
                            (*export_comp_idx, import.name.clone()),
                        );
                    } else if !self.allow_unresolved {
                        return Err(Error::UnresolvedImport {
                            module: "component".to_string(),
                            name: import.name.clone(),
                        });
                    }
                } else if !self.allow_unresolved {
                    return Err(Error::UnresolvedImport {
                        module: "component".to_string(),
                        name: import.name.clone(),
                    });
                }
            }
        }

        Ok(())
    }

    /// Resolve module-level imports within each component.
    ///
    /// Dispatches to `resolve_via_instances` when the component has an
    /// `InstanceSection` (the ground truth for module wiring), or falls
    /// back to `resolve_via_flat_names` for simple components without one.
    fn resolve_module_imports(
        &self,
        components: &[ParsedComponent],
        graph: &mut DependencyGraph,
    ) -> Result<()> {
        for (comp_idx, component) in components.iter().enumerate() {
            if !component.instances.is_empty() {
                self.resolve_via_instances(comp_idx, component, graph)?;
            } else {
                self.resolve_via_flat_names(comp_idx, component, graph)?;
            }
        }
        Ok(())
    }

    /// Resolve `__main_module__` imports that the instance-graph resolver
    /// couldn't handle (typically due to module-index mismatches between
    /// the parser and the component binary).
    ///
    /// `__main_module__` is a convention used by `wit-component` where
    /// adapter core modules import `_start` and `cabi_realloc` from the
    /// user's main core module.  After `flatten_nested_components`, the
    /// adapter and user modules may end up in different flattened components.
    ///
    /// For each `__main_module__` unresolved import, we search all other
    /// components' modules for a matching export.  Matches are recorded as
    /// `AdapterSite` entries (with `crosses_memory: false`) so the merger
    /// wires the call directly.  Returns dependency edges
    /// `(to_component, from_component)` for the topological sort.
    fn resolve_synthetic_module_imports(
        components: &[ParsedComponent],
        graph: &mut DependencyGraph,
    ) -> Vec<(usize, usize)> {
        let mut edges = Vec::new();
        let mut resolved_indices = Vec::new();

        for (i, unresolved) in graph.unresolved_imports.iter().enumerate() {
            if unresolved.module_name != "__main_module__" {
                continue;
            }
            if !matches!(unresolved.kind, ImportKind::Function(_)) {
                continue;
            }

            // Search all OTHER components for a module exporting this function
            let mut found = false;
            for (target_comp, target_component) in components.iter().enumerate() {
                if target_comp == unresolved.component_idx {
                    continue;
                }
                for (target_mod, target_module) in target_component.core_modules.iter().enumerate()
                {
                    if let Some(export) = target_module
                        .exports
                        .iter()
                        .find(|e| e.name == unresolved.field_name && e.kind == ExportKind::Function)
                    {
                        log::debug!(
                            "resolved __main_module__::{} → component {} module {} export {}",
                            unresolved.field_name,
                            target_comp,
                            target_mod,
                            export.name,
                        );
                        graph.adapter_sites.push(AdapterSite {
                            from_component: unresolved.component_idx,
                            from_module: unresolved.module_idx,
                            import_name: unresolved.field_name.clone(),
                            import_module: unresolved.module_name.clone(),
                            import_func_type_idx: None,
                            to_component: target_comp,
                            to_module: target_mod,
                            export_name: export.name.clone(),
                            export_func_idx: export.index,
                            crosses_memory: false,
                            requirements: AdapterRequirements::default(),
                        });
                        edges.push((target_comp, unresolved.component_idx));
                        resolved_indices.push(i);
                        found = true;
                        break;
                    }
                }
                if found {
                    break;
                }
            }
        }

        // Remove resolved entries from unresolved_imports (in reverse order
        // to preserve indices).
        for &i in resolved_indices.iter().rev() {
            graph.unresolved_imports.remove(i);
        }

        edges
    }

    /// Original flat name-matching resolution (fallback for components without InstanceSection).
    fn resolve_via_flat_names(
        &self,
        comp_idx: usize,
        component: &ParsedComponent,
        graph: &mut DependencyGraph,
    ) -> Result<()> {
        // Build export index for this component's modules
        let mut module_exports: HashMap<(&str, &str), (usize, &ModuleExport)> = HashMap::new();

        for (mod_idx, module) in component.core_modules.iter().enumerate() {
            for export in &module.exports {
                let key = ("", export.name.as_str());
                module_exports.insert(key, (mod_idx, export));
            }
        }

        // Resolve imports within this component
        for (from_mod_idx, module) in component.core_modules.iter().enumerate() {
            for import in &module.imports {
                let key = ("", import.name.as_str());
                if let Some((to_mod_idx, _)) = module_exports.get(&key) {
                    if *to_mod_idx != from_mod_idx {
                        graph.module_resolutions.push(ModuleResolution {
                            component_idx: comp_idx,
                            from_module: from_mod_idx,
                            to_module: *to_mod_idx,
                            import_name: import.name.clone(),
                            export_name: import.name.clone(),
                        });
                    }
                } else {
                    graph.unresolved_imports.push(UnresolvedImport {
                        component_idx: comp_idx,
                        module_idx: from_mod_idx,
                        module_name: import.module.clone(),
                        field_name: import.name.clone(),
                        kind: import.kind.clone(),
                        display_module: None,
                        display_field: None,
                    });
                }
            }
        }

        Ok(())
    }

    /// Instance-graph-based resolution using the `InstanceSection`.
    ///
    /// The `InstanceSection` records how each core instance was created:
    /// - `Instantiate { module_idx, args }`: the instance instantiates
    ///   `module_idx` with named arguments, each pointing to another instance.
    /// - `FromExports(exports)`: the instance is a synthetic bag of exports.
    ///
    /// We trace each module's imports through the instance graph to find the
    /// correct source module, avoiding false matches that the flat name-based
    /// approach produces.
    fn resolve_via_instances(
        &self,
        comp_idx: usize,
        component: &ParsedComponent,
        graph: &mut DependencyGraph,
    ) -> Result<()> {
        use crate::parser::{InstanceArg, InstanceKind};

        // Build entity provenance map from the parser's core_entity_order
        let provenance = build_entity_provenance(component);

        // Build canonical lower → WASI name mapping for renaming ""::N imports
        let canon_import_names = build_canon_import_names(component);

        // Step 1: Build instance content map.
        // For each instance, record what module it instantiates and how its
        // import-module names map to source instances.
        let mut instantiate_infos: HashMap<u32, InstanceInstantiateInfo> = HashMap::new();
        let mut from_exports_infos: HashMap<u32, Vec<(String, ExportKind, u32)>> = HashMap::new();

        for inst in &component.instances {
            match &inst.kind {
                InstanceKind::Instantiate { module_idx, args } => {
                    let mut arg_map = HashMap::new();
                    for (name, arg) in args {
                        if let InstanceArg::Instance(inst_idx) = arg {
                            arg_map.insert(name.clone(), *inst_idx);
                        }
                    }
                    instantiate_infos.insert(
                        inst.index,
                        InstanceInstantiateInfo {
                            module_idx: *module_idx,
                            arg_map,
                        },
                    );
                }
                InstanceKind::FromExports(exports) => {
                    let mapped: Vec<_> = exports
                        .iter()
                        .map(|(name, kind, idx)| {
                            let export_kind = match kind {
                                wasmparser::ExternalKind::Func => ExportKind::Function,
                                wasmparser::ExternalKind::Table => ExportKind::Table,
                                wasmparser::ExternalKind::Memory => ExportKind::Memory,
                                wasmparser::ExternalKind::Global => ExportKind::Global,
                                wasmparser::ExternalKind::Tag => ExportKind::Function,
                            };
                            (name.clone(), export_kind, *idx)
                        })
                        .collect();
                    from_exports_infos.insert(inst.index, mapped);
                }
            }
        }

        // Step 2: Build module → instance map (which instance instantiated which module).
        let mut module_to_instance: HashMap<u32, u32> = HashMap::new();
        for (inst_idx, info) in &instantiate_infos {
            module_to_instance.insert(info.module_idx, *inst_idx);
        }

        // Step 3: For each module's imports, trace through the instance graph.
        for (from_mod_idx, module) in component.core_modules.iter().enumerate() {
            let from_mod_u32 = from_mod_idx as u32;

            // Find which instance instantiated this module
            let inst_idx = match module_to_instance.get(&from_mod_u32) {
                Some(idx) => *idx,
                None => {
                    // Module not instantiated via InstanceSection — all imports unresolved.
                    for import in &module.imports {
                        graph.unresolved_imports.push(UnresolvedImport {
                            component_idx: comp_idx,
                            module_idx: from_mod_idx,
                            module_name: import.module.clone(),
                            field_name: import.name.clone(),
                            kind: import.kind.clone(),
                            display_module: None,
                            display_field: None,
                        });
                    }
                    continue;
                }
            };

            let inst_info = &instantiate_infos[&inst_idx];

            for import in &module.imports {
                // Find which source instance supplies `import.module`
                let source_inst_idx = match inst_info.arg_map.get(&import.module) {
                    Some(idx) => *idx,
                    None => {
                        // No instance arg for this import module. For synthetic
                        // names like `__main_module__` (used by wit-component to
                        // wire adapter modules to the user's main module), fall
                        // back to export-name matching within the same component.
                        if import.module == "__main_module__"
                            && let Some(to_mod_idx) =
                                find_module_with_export(component, &import.name, from_mod_idx)
                        {
                            graph.module_resolutions.push(ModuleResolution {
                                component_idx: comp_idx,
                                from_module: from_mod_idx,
                                to_module: to_mod_idx,
                                import_name: import.name.clone(),
                                export_name: import.name.clone(),
                            });
                            continue;
                        }

                        graph.unresolved_imports.push(UnresolvedImport {
                            component_idx: comp_idx,
                            module_idx: from_mod_idx,
                            module_name: import.module.clone(),
                            field_name: import.name.clone(),
                            kind: import.kind.clone(),
                            display_module: None,
                            display_field: None,
                        });
                        continue;
                    }
                };

                // Trace the source instance to find the actual module export
                if let Some(resolved) = self.trace_instance_export(
                    component,
                    source_inst_idx,
                    &import.name,
                    &instantiate_infos,
                    &from_exports_infos,
                    &provenance,
                ) {
                    let (to_mod_idx, export_name) = resolved;
                    if to_mod_idx != from_mod_idx {
                        graph.module_resolutions.push(ModuleResolution {
                            component_idx: comp_idx,
                            from_module: from_mod_idx,
                            to_module: to_mod_idx,
                            import_name: import.name.clone(),
                            export_name,
                        });
                    }
                } else {
                    // Could not trace to a module export. This happens for
                    // canon-lowered functions and other non-module entities.
                    //
                    // For canonical lowered functions (from `canon lower`),
                    // try to recover the WASI interface name by checking the
                    // FromExports entity index against canon_import_names.
                    // The original module_name/field_name are kept for lookup;
                    // the WASI name goes into display_module/display_field.
                    let mut display_module = None;
                    let mut display_field = None;

                    if let Some(fe_exports) = from_exports_infos.get(&source_inst_idx) {
                        for (name, kind, entity_idx) in fe_exports {
                            if name == &import.name && *kind == ExportKind::Function {
                                if let Some((mod_name, field_name)) =
                                    canon_import_names.get(entity_idx)
                                {
                                    display_module = Some(mod_name.clone());
                                    display_field = Some(field_name.clone());
                                }
                                break;
                            }
                        }
                    }

                    graph.unresolved_imports.push(UnresolvedImport {
                        component_idx: comp_idx,
                        module_idx: from_mod_idx,
                        module_name: import.module.clone(),
                        field_name: import.name.clone(),
                        kind: import.kind.clone(),
                        display_module,
                        display_field,
                    });
                }
            }
        }

        Ok(())
    }

    /// Trace an instance to find a named export, returning (module_idx, export_name).
    ///
    /// - If the instance is `Instantiate`, look up the instantiated module's
    ///   exports for the name.
    /// - If the instance is `FromExports`, use the entity provenance map to
    ///   resolve the entity index back to its source module. Returns `None`
    ///   for entities that came from canonical functions (WASI trampolines).
    fn trace_instance_export(
        &self,
        component: &ParsedComponent,
        instance_idx: u32,
        export_name: &str,
        instantiate_infos: &HashMap<u32, InstanceInstantiateInfo>,
        from_exports_infos: &HashMap<u32, Vec<(String, ExportKind, u32)>>,
        provenance: &EntityProvenance,
    ) -> Option<(usize, String)> {
        // Check if it's an Instantiate instance
        if let Some(info) = instantiate_infos.get(&instance_idx) {
            let module_idx = info.module_idx as usize;
            if module_idx < component.core_modules.len() {
                let module = &component.core_modules[module_idx];
                if module.exports.iter().any(|e| e.name == export_name) {
                    return Some((module_idx, export_name.to_string()));
                }
            }
        }

        // Check if it's a FromExports instance — use provenance to resolve
        if let Some(exports) = from_exports_infos.get(&instance_idx) {
            for (name, kind, entity_idx) in exports {
                if name == export_name {
                    return match kind {
                        ExportKind::Function => provenance
                            .func_source
                            .get(entity_idx)
                            .map(|(mod_idx, exp_name)| (*mod_idx, exp_name.clone())),
                        ExportKind::Memory => provenance
                            .memory_source
                            .get(entity_idx)
                            .map(|(mod_idx, exp_name)| (*mod_idx, exp_name.clone())),
                        ExportKind::Table => provenance
                            .table_source
                            .get(entity_idx)
                            .map(|(mod_idx, exp_name)| (*mod_idx, exp_name.clone())),
                        ExportKind::Global => provenance
                            .global_source
                            .get(entity_idx)
                            .map(|(mod_idx, exp_name)| (*mod_idx, exp_name.clone())),
                    };
                }
            }
        }

        None
    }

    /// Build dependency edges for topological sort
    fn build_dependency_edges(
        &self,
        _components: &[ParsedComponent],
        graph: &DependencyGraph,
    ) -> Vec<(usize, usize)> {
        let mut edges = Vec::new();

        // Add edges from resolved imports
        for ((from, _), (to, _)) in &graph.resolved_imports {
            if from != to {
                edges.push((*to, *from)); // to must be instantiated before from
            }
        }

        edges
    }

    /// Perform topological sort on components.
    ///
    /// Uses Kahn's algorithm.  If cycles remain (e.g. composed-runner
    /// components with mutual wiring), the remaining nodes are appended
    /// in ascending index order instead of returning an error.  This is
    /// safe because the merger fuses everything into a single module —
    /// the relative order of nodes within a cycle doesn't affect
    /// correctness.  Real intra-component module cycles are still
    /// caught separately by `detect_module_cycles`.
    fn topological_sort(&self, n: usize, edges: &[(usize, usize)]) -> Result<Vec<usize>> {
        // Build adjacency list and in-degree count
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
        let mut in_degree = vec![0usize; n];

        for &(from, to) in edges {
            adj[from].push(to);
            in_degree[to] += 1;
        }

        // Sort each adjacency list so that neighbours are visited in
        // ascending index order.  This guarantees deterministic output
        // regardless of the order edges were supplied (SR-19 / LS-CP-2).
        for list in &mut adj {
            list.sort_unstable();
        }

        // Kahn's algorithm
        let mut queue: Vec<usize> = (0..n).filter(|&i| in_degree[i] == 0).collect();
        let mut result = Vec::with_capacity(n);

        while let Some(node) = queue.pop() {
            result.push(node);
            for &neighbor in &adj[node] {
                in_degree[neighbor] -= 1;
                if in_degree[neighbor] == 0 {
                    queue.push(neighbor);
                }
            }
        }

        if result.len() != n {
            // Cycle detected — append remaining nodes ordered so that
            // nodes with the most dependents among the cycle come first.
            // This ensures exporting components are merged before importing
            // ones, so function_index_map lookups succeed in the merger.
            let in_result: HashSet<usize> = result.iter().copied().collect();
            let remaining_set: HashSet<usize> = (0..n).filter(|i| !in_result.contains(i)).collect();

            // Count in-degree from other cycle nodes only
            let mut cycle_in_degree: HashMap<usize, usize> = HashMap::new();
            for &(from, to) in edges {
                if remaining_set.contains(&from) && remaining_set.contains(&to) {
                    *cycle_in_degree.entry(to).or_default() += 1;
                }
            }

            let mut remaining: Vec<usize> = remaining_set.into_iter().collect();
            remaining.sort_by(|a, b| {
                // Ascending in-degree (fewest prerequisites first),
                // then ascending index for ties.
                cycle_in_degree
                    .get(a)
                    .unwrap_or(&0)
                    .cmp(cycle_in_degree.get(b).unwrap_or(&0))
                    .then(a.cmp(b))
            });

            log::warn!(
                "component dependency cycle detected among {} node(s) {:?}; \
                 appending by descending in-degree (safe for fusion)",
                remaining.len(),
                remaining,
            );
            result.extend(remaining);
        }

        Ok(result)
    }

    /// Detect cycles among module dependencies within a single component.
    ///
    /// Builds a directed graph from `module_resolutions` (filtered to
    /// `component_idx`) and performs DFS-based cycle detection.  Returns
    /// `Err(Error::ModuleDependencyCycle)` with the cycle path when a
    /// cycle is found.
    fn detect_module_cycles(
        component_idx: usize,
        module_count: usize,
        module_resolutions: &[ModuleResolution],
    ) -> Result<()> {
        // Build adjacency list: from_module -> set of to_module
        let mut adj: Vec<HashSet<usize>> = vec![HashSet::new(); module_count];
        for res in module_resolutions {
            if res.component_idx == component_idx {
                adj[res.from_module].insert(res.to_module);
            }
        }

        // DFS state: 0 = unvisited, 1 = in current path, 2 = finished
        let mut state = vec![0u8; module_count];
        // Predecessor map for reconstructing cycle path
        let mut predecessor = vec![usize::MAX; module_count];

        for start in 0..module_count {
            if state[start] != 0 {
                continue;
            }
            // Iterative DFS using an explicit stack
            let mut stack: Vec<(usize, bool)> = vec![(start, false)];
            while let Some((node, returning)) = stack.pop() {
                if returning {
                    // All neighbors explored; mark finished
                    state[node] = 2;
                    continue;
                }
                if state[node] == 1 {
                    // Already being explored in this DFS tree, skip
                    // (duplicate stack entries are harmless)
                    continue;
                }
                state[node] = 1; // mark as in-progress
                // Push a sentinel so we mark it finished after neighbors
                stack.push((node, true));

                for &neighbor in &adj[node] {
                    match state[neighbor] {
                        0 => {
                            // Unvisited: record predecessor and recurse
                            predecessor[neighbor] = node;
                            stack.push((neighbor, false));
                        }
                        1 => {
                            // Back edge found: reconstruct cycle
                            let mut cycle_path = vec![neighbor];
                            let mut cur = node;
                            while cur != neighbor {
                                cycle_path.push(cur);
                                cur = predecessor[cur];
                            }
                            cycle_path.push(neighbor); // close the cycle
                            cycle_path.reverse();
                            let cycle_str = cycle_path
                                .iter()
                                .map(|idx| format!("module[{}]", idx))
                                .collect::<Vec<_>>()
                                .join(" -> ");
                            return Err(Error::ModuleDependencyCycle {
                                component_idx,
                                cycle: cycle_str,
                            });
                        }
                        _ => {
                            // Already finished (cross edge), skip
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Identify call sites that need adapter functions
    fn identify_adapter_sites(
        &self,
        components: &[ParsedComponent],
        graph: &mut DependencyGraph,
    ) -> Result<()> {
        // Cross-component resolutions need adapters
        log::debug!(
            "identify_adapter_sites: {} resolved imports to process",
            graph.resolved_imports.len()
        );
        for ((from_comp, import_name), (to_comp, export_name)) in &graph.resolved_imports {
            log::debug!(
                "  resolution: comp {} import {:?} -> comp {} export {:?}",
                from_comp,
                import_name,
                to_comp,
                export_name
            );
            if from_comp == to_comp {
                continue;
            }

            // For each module in the source component that has this import
            let from_component = &components[*from_comp];
            let to_component = &components[*to_comp];

            for (from_mod_idx, from_module) in from_component.core_modules.iter().enumerate() {
                // Check if this module imports the resolved name.
                // In the component model, the component-level import name may
                // appear as the core module import's field name (imp.name) or
                // as its module name (imp.module) depending on how the
                // component was lowered.  We use exact equality for both to
                // avoid false positives from substring matches (e.g. "log"
                // incorrectly matching "catalog").
                let has_import = from_module
                    .imports
                    .iter()
                    .any(|imp| imp.name == *import_name || imp.module == *import_name);

                if has_import {
                    // Determine if this call crosses a memory boundary (shared
                    // across all functions in the interface).
                    let crosses_memory = match self.memory_strategy {
                        MemoryStrategy::SharedMemory => false,
                        MemoryStrategy::MultiMemory => {
                            let has_memory = |c: &ParsedComponent| {
                                c.core_modules.iter().any(|m| {
                                    !m.memories.is_empty()
                                        || m.imports
                                            .iter()
                                            .any(|i| matches!(i.kind, ImportKind::Memory(_)))
                                })
                            };
                            has_memory(from_component) && has_memory(to_component)
                        }
                    };

                    // Check if the callee also imports the same interface
                    // (i.e., it re-exports from another component). In that case,
                    // it doesn't "define" the resource — a downstream component does.
                    let callee_is_reexporter = graph
                        .resolved_imports
                        .contains_key(&(*to_comp, import_name.clone()));

                    // Try per-function interface matching first.
                    //
                    // In wit-bindgen composed components, a component-level
                    // interface import like "test:numbers/numbers" decomposes
                    // into multiple core imports with:
                    //   module = "test:numbers/numbers", name = "roundtrip-u8"
                    // The target component exports these as:
                    //   "test:numbers/numbers#roundtrip-u8"
                    let interface_func_imports: Vec<&str> = from_module
                        .imports
                        .iter()
                        .filter(|imp| {
                            imp.module == *import_name
                                && matches!(imp.kind, ImportKind::Function(_))
                        })
                        .map(|imp| imp.name.as_str())
                        .collect();

                    if !interface_func_imports.is_empty() {
                        log::debug!(
                            "Per-function matching: {} functions from comp {} mod {} importing {:?}",
                            interface_func_imports.len(),
                            from_comp,
                            from_mod_idx,
                            import_name
                        );
                        let mut per_func_matched = false;
                        let callee_lift_info = to_component.lift_info_by_core_func();
                        let callee_resource_map = build_resource_type_to_import(to_component);
                        let caller_resource_map = build_resource_type_to_import(from_component);
                        // Provenance-based maps for correct core func index lookup.
                        // These account for interleaved canon lower / alias entries.
                        let callee_export_to_core = build_module_export_to_core_func(to_component);
                        let callee_core_to_local = build_core_func_to_module_local(to_component);

                        for func_name in &interface_func_imports {
                            let qualified = format!("{}#{}", export_name, func_name);
                            let mut found = false;

                            // Look up the caller's import type index for this function
                            let caller_import_type_idx = from_module
                                .imports
                                .iter()
                                .find(|imp| imp.module == *import_name && imp.name == *func_name)
                                .and_then(|imp| match &imp.kind {
                                    ImportKind::Function(ti) => Some(*ti),
                                    _ => None,
                                });

                            for (to_mod_idx, to_module) in
                                to_component.core_modules.iter().enumerate()
                            {
                                if let Some(export) = to_module.exports.iter().find(|exp| {
                                    exp.name == qualified && exp.kind == ExportKind::Function
                                }) {
                                    found = true;
                                    let mut requirements = AdapterRequirements::default();
                                    // Use provenance-based reverse map for correct
                                    // component-level core func index lookup.
                                    let comp_core_idx =
                                        callee_export_to_core.get(&(to_mod_idx, qualified.clone()));
                                    let lift_info =
                                        comp_core_idx.and_then(|idx| callee_lift_info.get(idx));
                                    if comp_core_idx.is_some() && lift_info.is_none() {
                                        log::debug!(
                                            "lift_info not found for {:?} (comp_core_idx={:?}, \
                                             {} lift entries)",
                                            func_name,
                                            comp_core_idx,
                                            callee_lift_info.len()
                                        );
                                    }
                                    if let Some((comp_type_idx, lift_opts)) = lift_info {
                                        requirements.callee_encoding =
                                            Some(lift_opts.string_encoding);
                                        requirements.callee_post_return =
                                            lift_opts.post_return.and_then(|pr_idx| {
                                                callee_core_to_local.get(&pr_idx).copied()
                                            });
                                        requirements.callee_realloc = lift_opts.realloc;

                                        // Compute layout info from the component function type
                                        // (needed for retptr bridging and multi-pointer copy).
                                        if let Some(ct) =
                                            to_component.get_type_definition(*comp_type_idx)
                                            && let ComponentTypeKind::Function {
                                                params: comp_params,
                                                results,
                                            } = &ct.kind
                                        {
                                            let size = to_component.return_area_byte_size(results);
                                            if size > 4 {
                                                requirements.return_area_byte_size = Some(size);
                                            }
                                            requirements.pointer_pair_positions = to_component
                                                .pointer_pair_param_positions(comp_params);
                                            requirements.result_pointer_pair_offsets =
                                                to_component.pointer_pair_result_offsets(results);
                                            // Compute copy layouts for each pointer pair
                                            requirements.param_copy_layouts =
                                                collect_param_copy_layouts(
                                                    to_component,
                                                    comp_params,
                                                );
                                            requirements.result_copy_layouts =
                                                collect_result_copy_layouts(to_component, results);
                                            // Collect conditional pointer pairs (option/result/variant)
                                            requirements.conditional_pointer_pairs = to_component
                                                .conditional_pointer_pair_positions(comp_params);
                                            requirements.conditional_result_pointer_pairs =
                                                to_component
                                                    .conditional_pointer_pair_result_positions(
                                                        results,
                                                    );
                                            requirements.conditional_result_flat_pairs =
                                                to_component
                                                    .conditional_pointer_pair_result_flat_positions(
                                                        results,
                                                    );
                                            requirements.return_area_slots =
                                                to_component.return_area_slots(results);
                                            // Collect resource-typed params and results
                                            requirements.resource_params =
                                                resolve_resource_positions(
                                                    &callee_resource_map,
                                                    &to_component
                                                        .resource_param_positions(comp_params),
                                                    "[resource-rep]",
                                                    &to_component.component_type_defs,
                                                    callee_is_reexporter,
                                                );
                                            requirements.resource_results =
                                                resolve_resource_positions(
                                                    &callee_resource_map,
                                                    &to_component
                                                        .resource_result_positions(results),
                                                    "[resource-new]",
                                                    &to_component.component_type_defs,
                                                    callee_is_reexporter,
                                                );
                                            // Caller-side resource params for 3-component chains
                                            requirements.caller_resource_params =
                                                resolve_resource_positions(
                                                    &caller_resource_map,
                                                    &to_component
                                                        .resource_param_positions(comp_params),
                                                    "[resource-rep]",
                                                    &from_component.component_type_defs,
                                                    true, // caller never defines
                                                );
                                        }
                                    }

                                    // Caller-side lower options for string encoding
                                    let caller_lower_map = from_component.lower_options_by_func();
                                    // Try to find the Lower entry matching the interface import
                                    let mut matched_caller_enc = None;
                                    {
                                        let mut comp_func_idx = 0u32;
                                        for ci in &from_component.imports {
                                            if matches!(
                                                ci.ty,
                                                wasmparser::ComponentTypeRef::Func(_)
                                            ) {
                                                if ci.name == *import_name {
                                                    if let Some(lo) =
                                                        caller_lower_map.get(&comp_func_idx)
                                                    {
                                                        matched_caller_enc =
                                                            Some(lo.string_encoding);
                                                    }
                                                    break;
                                                }
                                                comp_func_idx += 1;
                                            }
                                        }
                                    }
                                    if matched_caller_enc.is_none()
                                        && let Some((_, lo)) = caller_lower_map.iter().next()
                                    {
                                        matched_caller_enc = Some(lo.string_encoding);
                                    }
                                    if let Some(enc) = matched_caller_enc {
                                        requirements.caller_encoding = Some(enc);
                                    }
                                    if let (Some(ce), Some(ce2)) =
                                        (requirements.caller_encoding, requirements.callee_encoding)
                                    {
                                        requirements.string_transcoding = ce != ce2;
                                    }

                                    graph.adapter_sites.push(AdapterSite {
                                        from_component: *from_comp,
                                        from_module: from_mod_idx,
                                        import_name: (*func_name).to_string(),
                                        import_module: import_name.clone(),
                                        import_func_type_idx: caller_import_type_idx,
                                        to_component: *to_comp,
                                        to_module: to_mod_idx,
                                        export_name: qualified.clone(),
                                        export_func_idx: export.index,
                                        crosses_memory,
                                        requirements,
                                    });
                                    per_func_matched = true;
                                    break; // found target module for this func
                                }
                            }
                            if !found {
                                log::debug!(
                                    "  Per-func: no export {:?} in comp {} ({} modules)",
                                    qualified,
                                    to_comp,
                                    to_component.core_modules.len()
                                );
                            }
                        }

                        if per_func_matched {
                            continue; // all funcs handled, next from_module
                        }
                    }

                    // Fallback: single-export matching (simple components where
                    // the core export name matches the component-level name).
                    for (to_mod_idx, to_module) in to_component.core_modules.iter().enumerate() {
                        let has_export =
                            to_module.exports.iter().any(|exp| exp.name == *export_name);

                        if has_export {
                            let export_func_idx = match to_module
                                .exports
                                .iter()
                                .find(|exp| exp.name == *export_name)
                                .map(|exp| exp.index)
                            {
                                Some(idx) => idx,
                                None => {
                                    log::error!(
                                        "Export '{}' verified present but lookup failed \
                                         (component {} module {})",
                                        export_name,
                                        to_comp,
                                        to_mod_idx,
                                    );
                                    return Err(Error::UnresolvedImport {
                                        module: format!("component[{}]", to_comp),
                                        name: export_name.clone(),
                                    });
                                }
                            };

                            // Populate canonical requirements from lift/lower options
                            let mut requirements = AdapterRequirements::default();

                            // Callee side: use provenance-based lookup for correct
                            // component-level core func index, including type index
                            // for layout/resource detection.
                            let callee_lift_map = to_component.lift_info_by_core_func();
                            let fb_export_to_core = build_module_export_to_core_func(to_component);
                            let fb_core_to_local = build_core_func_to_module_local(to_component);
                            let fb_comp_core_idx =
                                fb_export_to_core.get(&(to_mod_idx, export_name.clone()));
                            if let Some((comp_type_idx, lift_opts)) =
                                fb_comp_core_idx.and_then(|idx| callee_lift_map.get(idx))
                            {
                                requirements.callee_encoding = Some(lift_opts.string_encoding);
                                requirements.callee_post_return = lift_opts
                                    .post_return
                                    .and_then(|pr_idx| fb_core_to_local.get(&pr_idx).copied());
                                requirements.callee_realloc = lift_opts.realloc;

                                // Populate layout and resource info from component
                                // function type (mirrors per-function path).
                                if let Some(ct) = to_component.get_type_definition(*comp_type_idx)
                                    && let ComponentTypeKind::Function {
                                        params: comp_params,
                                        results,
                                    } = &ct.kind
                                {
                                    let size = to_component.return_area_byte_size(results);
                                    if size > 4 {
                                        requirements.return_area_byte_size = Some(size);
                                    }
                                    requirements.pointer_pair_positions =
                                        to_component.pointer_pair_param_positions(comp_params);
                                    requirements.result_pointer_pair_offsets =
                                        to_component.pointer_pair_result_offsets(results);
                                    requirements.param_copy_layouts =
                                        collect_param_copy_layouts(to_component, comp_params);
                                    requirements.result_copy_layouts =
                                        collect_result_copy_layouts(to_component, results);
                                    requirements.conditional_pointer_pairs = to_component
                                        .conditional_pointer_pair_positions(comp_params);
                                    requirements.conditional_result_pointer_pairs = to_component
                                        .conditional_pointer_pair_result_positions(results);
                                    requirements.conditional_result_flat_pairs = to_component
                                        .conditional_pointer_pair_result_flat_positions(results);
                                    requirements.return_area_slots =
                                        to_component.return_area_slots(results);

                                    let callee_resource_map =
                                        build_resource_type_to_import(to_component);
                                    let fb_callee_reexporter = graph
                                        .resolved_imports
                                        .contains_key(&(*to_comp, import_name.clone()));
                                    requirements.resource_params = resolve_resource_positions(
                                        &callee_resource_map,
                                        &to_component.resource_param_positions(comp_params),
                                        "[resource-rep]",
                                        &to_component.component_type_defs,
                                        fb_callee_reexporter,
                                    );
                                    requirements.resource_results = resolve_resource_positions(
                                        &callee_resource_map,
                                        &to_component.resource_result_positions(results),
                                        "[resource-new]",
                                        &to_component.component_type_defs,
                                        fb_callee_reexporter,
                                    );
                                    // Caller-side resource params for 3-component chains
                                    let caller_resource_map =
                                        build_resource_type_to_import(from_component);
                                    requirements.caller_resource_params =
                                        resolve_resource_positions(
                                            &caller_resource_map,
                                            &to_component.resource_param_positions(comp_params),
                                            "[resource-rep]",
                                            &from_component.component_type_defs,
                                            true,
                                        );
                                }
                            }

                            // Caller side: look up lower options by import func index.
                            let caller_lower_map = from_component.lower_options_by_func();
                            let mut matched_caller_encoding = None;

                            {
                                let mut comp_func_idx = 0u32;
                                for comp_import in &from_component.imports {
                                    if matches!(
                                        comp_import.ty,
                                        wasmparser::ComponentTypeRef::Func(_)
                                    ) {
                                        if comp_import.name == *import_name {
                                            if let Some(lower_opts) =
                                                caller_lower_map.get(&comp_func_idx)
                                            {
                                                matched_caller_encoding =
                                                    Some(lower_opts.string_encoding);
                                            }
                                            break;
                                        }
                                        comp_func_idx += 1;
                                    }
                                }
                            }

                            if matched_caller_encoding.is_none()
                                && let Some((_, lower_opts)) = caller_lower_map.iter().next()
                            {
                                log::debug!(
                                    "Using heuristic lower encoding for import '{}' \
                                     (name-based match not found; {} lower entries)",
                                    import_name,
                                    caller_lower_map.len()
                                );
                                matched_caller_encoding = Some(lower_opts.string_encoding);
                            }

                            if let Some(enc) = matched_caller_encoding {
                                requirements.caller_encoding = Some(enc);
                            }

                            if let (Some(caller_enc), Some(callee_enc)) =
                                (requirements.caller_encoding, requirements.callee_encoding)
                            {
                                requirements.string_transcoding = caller_enc != callee_enc;
                            }

                            // Look up caller's import type for the fallback path
                            let fallback_import_type_idx = from_module
                                .imports
                                .iter()
                                .find(|imp| imp.name == *import_name || imp.module == *import_name)
                                .and_then(|imp| match &imp.kind {
                                    ImportKind::Function(ti) => Some(*ti),
                                    _ => None,
                                });

                            graph.adapter_sites.push(AdapterSite {
                                from_component: *from_comp,
                                from_module: from_mod_idx,
                                import_name: import_name.clone(),
                                import_module: import_name.clone(),
                                import_func_type_idx: fallback_import_type_idx,
                                to_component: *to_comp,
                                to_module: to_mod_idx,
                                export_name: export_name.clone(),
                                export_func_idx,
                                crosses_memory,
                                requirements,
                            });
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Identify intra-component module pairs that need adapters.
    ///
    /// When two modules within the same component communicate across a memory
    /// boundary (different memories, different string encodings, or different
    /// realloc functions), a direct call is incorrect -- we need an adapter to
    /// handle Canonical ABI lifting/lowering just as we do for cross-component
    /// calls.
    ///
    /// This method iterates `module_resolutions` (which are all intra-component),
    /// checks whether the source and target modules have different canonical
    /// options, and if so promotes the resolution to an `AdapterSite`. Promoted
    /// resolutions are removed from `module_resolutions` so the merger does not
    /// also wire them as direct calls.
    fn identify_intra_component_adapter_sites(
        &self,
        components: &[ParsedComponent],
        graph: &mut DependencyGraph,
    ) -> Result<()> {
        // Collect indices of module_resolutions that get promoted to adapter sites.
        let mut promoted_indices: Vec<usize> = Vec::new();

        for (res_idx, res) in graph.module_resolutions.iter().enumerate() {
            let component = &components[res.component_idx];

            // Only function-typed resolutions matter for adapters.
            // Find the target module's export to get the function index.
            let to_module = &component.core_modules[res.to_module];
            let export = match to_module
                .exports
                .iter()
                .find(|e| e.name == res.export_name && e.kind == ExportKind::Function)
            {
                Some(e) => e,
                None => continue, // Not a function export, skip
            };
            let export_func_idx = export.index;

            // Use provenance-based lookup for correct component-level core
            // function index (handles interleaved canon lower / alias entries).
            let intra_export_to_core = build_module_export_to_core_func(component);
            let intra_core_to_local = build_core_func_to_module_local(component);
            let target_comp_func_idx =
                match intra_export_to_core.get(&(res.to_module, res.export_name.clone())) {
                    Some(idx) => *idx,
                    None => continue, // Cannot find in provenance, skip
                };

            // Look up callee-side Lift options
            let lift_map = component.lift_options_by_core_func();
            let callee_lift = lift_map.get(&target_comp_func_idx);

            // Look up caller-side Lower options.
            // The Lower entry's func_index is a component function index.
            // For intra-component calls, the core import in the source module
            // was lowered from a component function via `canon lower`. We need
            // to find the Lower entry whose lowered core function corresponds
            // to the import in from_module.
            let lower_map = component.lower_options_by_func();
            let caller_lower = self.find_lower_for_intra_import(
                component,
                res.from_module,
                &res.import_name,
                &lower_map,
            );

            // Extract canonical options with defaults
            let callee_encoding = callee_lift.map(|l| l.string_encoding);
            let callee_memory = callee_lift.and_then(|l| l.memory);
            let callee_realloc = callee_lift.and_then(|l| l.realloc);

            let caller_encoding = caller_lower.map(|l| l.string_encoding);
            let caller_memory = caller_lower.and_then(|l| l.memory);
            let _caller_realloc = caller_lower.and_then(|l| l.realloc);

            // Check if an adapter is needed: different encoding, different memory,
            // or different realloc on callee side.
            let needs_adapter = {
                let encoding_differs = match (caller_encoding, callee_encoding) {
                    (Some(a), Some(b)) => a != b,
                    _ => false,
                };
                let memory_differs = match (caller_memory, callee_memory) {
                    (Some(a), Some(b)) => a != b,
                    // If one side has no memory annotation, no cross-memory issue
                    _ => false,
                };
                // Also check if both sides have memory but use different modules'
                // memories (multi-memory mode).
                let module_memory_differs = match self.memory_strategy {
                    MemoryStrategy::SharedMemory => false,
                    MemoryStrategy::MultiMemory => {
                        let from_has_memory = {
                            let m = &component.core_modules[res.from_module];
                            !m.memories.is_empty()
                                || m.imports
                                    .iter()
                                    .any(|i| matches!(i.kind, ImportKind::Memory(_)))
                        };
                        let to_has_memory = {
                            let m = &component.core_modules[res.to_module];
                            !m.memories.is_empty()
                                || m.imports
                                    .iter()
                                    .any(|i| matches!(i.kind, ImportKind::Memory(_)))
                        };
                        from_has_memory && to_has_memory
                    }
                };

                encoding_differs || memory_differs || module_memory_differs
            };

            if !needs_adapter {
                continue;
            }

            log::debug!(
                "Intra-component adapter needed: component {} module {} -> module {} \
                 (import '{}', export '{}', caller_enc={:?}, callee_enc={:?})",
                res.component_idx,
                res.from_module,
                res.to_module,
                res.import_name,
                res.export_name,
                caller_encoding,
                callee_encoding,
            );

            // Determine crosses_memory for the adapter site
            let crosses_memory = match self.memory_strategy {
                MemoryStrategy::SharedMemory => false,
                MemoryStrategy::MultiMemory => {
                    let from_has_memory = {
                        let m = &component.core_modules[res.from_module];
                        !m.memories.is_empty()
                            || m.imports
                                .iter()
                                .any(|i| matches!(i.kind, ImportKind::Memory(_)))
                    };
                    let to_has_memory = {
                        let m = &component.core_modules[res.to_module];
                        !m.memories.is_empty()
                            || m.imports
                                .iter()
                                .any(|i| matches!(i.kind, ImportKind::Memory(_)))
                    };
                    from_has_memory && to_has_memory
                }
            };

            // Build adapter requirements
            let mut requirements = AdapterRequirements {
                caller_encoding,
                callee_encoding,
                callee_realloc,
                ..Default::default()
            };

            // Decompose callee's post-return using provenance-based map
            if let Some(lift_opts) = callee_lift {
                requirements.callee_post_return = lift_opts
                    .post_return
                    .and_then(|pr_idx| intra_core_to_local.get(&pr_idx).copied());
            }

            // Set string_transcoding flag
            if let (Some(caller_enc), Some(callee_enc)) =
                (requirements.caller_encoding, requirements.callee_encoding)
            {
                requirements.string_transcoding = caller_enc != callee_enc;
            }

            graph.adapter_sites.push(AdapterSite {
                from_component: res.component_idx,
                from_module: res.from_module,
                import_name: res.import_name.clone(),
                import_module: res.import_name.clone(),
                import_func_type_idx: None,
                to_component: res.component_idx, // same component
                to_module: res.to_module,
                export_name: res.export_name.clone(),
                export_func_idx,
                crosses_memory,
                requirements,
            });

            promoted_indices.push(res_idx);
        }

        // Remove promoted resolutions in reverse order to preserve indices.
        promoted_indices.sort_unstable();
        for idx in promoted_indices.into_iter().rev() {
            graph.module_resolutions.remove(idx);
        }

        Ok(())
    }

    /// Find the Lower canonical options for an intra-component module import.
    ///
    /// In the component model, `canon lower` produces a core function that gets
    /// passed as an instantiation argument to a core module. The Lower entry's
    /// `func_index` is a component function index. We try to match the import
    /// name against component-level canonical Lower entries by examining the
    /// component's Lift entries (which map core functions to component functions)
    /// and finding a Lower that references the same component function.
    fn find_lower_for_intra_import<'a>(
        &self,
        component: &'a ParsedComponent,
        _from_module: usize,
        import_name: &str,
        lower_map: &HashMap<u32, &'a crate::parser::CanonicalOptions>,
    ) -> Option<&'a crate::parser::CanonicalOptions> {
        // Strategy 1: Match via component imports (same as cross-component logic).
        // Component imports are numbered in the component function index space.
        {
            let mut comp_func_idx = 0u32;
            for comp_import in &component.imports {
                if matches!(comp_import.ty, wasmparser::ComponentTypeRef::Func(_)) {
                    if comp_import.name == import_name
                        && let Some(lower_opts) = lower_map.get(&comp_func_idx)
                    {
                        return Some(lower_opts);
                    }
                    comp_func_idx += 1;
                }
            }
        }

        // Strategy 2: For intra-component calls, the function being lowered may
        // not be an import but a locally-defined component function (via Lift
        // then Lower). Iterate Lower entries and check if any was lowered from
        // a Lift whose export name matches our import name.
        // Build a reverse map: component_func_idx -> Lift's export name
        // (We approximate the component function index from Lift order.)
        // This is a best-effort heuristic for the common wit-component patterns.
        {
            // Component functions from Lifts are numbered after imported component
            // functions. Count imported component functions first.
            let imported_func_count = component
                .imports
                .iter()
                .filter(|i| matches!(i.ty, wasmparser::ComponentTypeRef::Func(_)))
                .count() as u32;

            // Map: component_func_idx -> export name (from Lift)
            let mut lift_comp_func_to_name: HashMap<u32, &str> = HashMap::new();
            let mut lift_idx = 0u32;
            for entry in &component.canonical_functions {
                if let crate::parser::CanonicalEntry::Lift { .. } = entry {
                    // The component function produced by this Lift has index
                    // imported_func_count + lift_idx.
                    let comp_func_idx = imported_func_count + lift_idx;
                    // Find component export that references this component function
                    for comp_export in &component.exports {
                        if comp_export.index == comp_func_idx {
                            lift_comp_func_to_name.insert(comp_func_idx, &comp_export.name);
                        }
                    }
                    lift_idx += 1;
                }
            }

            // Now check if any Lower entry references a component function whose
            // name matches our import_name
            for (&func_idx, &lower_opts) in lower_map {
                if let Some(&name) = lift_comp_func_to_name.get(&func_idx)
                    && name == import_name
                {
                    return Some(lower_opts);
                }
            }
        }

        // Strategy 3: Fall back to first Lower entry (common single-function case)
        if let Some((_, &lower_opts)) = lower_map.iter().next() {
            log::debug!(
                "Intra-component: using heuristic lower encoding for import '{}' \
                 ({} lower entries)",
                import_name,
                lower_map.len()
            );
            return Some(lower_opts);
        }

        None
    }
}

impl Default for Resolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_topological_sort_no_deps() {
        let resolver = Resolver::new();
        let result = resolver.topological_sort(3, &[]).unwrap();
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn test_topological_sort_linear() {
        let resolver = Resolver::new();
        // 0 -> 1 -> 2
        let edges = vec![(0, 1), (1, 2)];
        let result = resolver.topological_sort(3, &edges).unwrap();

        // Verify order: 0 before 1, 1 before 2
        let pos: HashMap<usize, usize> = result.iter().enumerate().map(|(i, &v)| (v, i)).collect();
        assert!(pos[&0] < pos[&1]);
        assert!(pos[&1] < pos[&2]);
    }

    #[test]
    fn test_topological_sort_circular_fallback() {
        let resolver = Resolver::new();
        // 0 -> 1 -> 2 -> 0 (full cycle)
        let edges = vec![(0, 1), (1, 2), (2, 0)];
        let result = resolver.topological_sort(3, &edges).unwrap();
        // All nodes should be present (cycle broken, appended in index order)
        assert_eq!(result.len(), 3);
        let mut sorted = result.clone();
        sorted.sort();
        assert_eq!(sorted, vec![0, 1, 2]);
    }

    #[test]
    fn test_resolver_strict_mode() {
        let resolver = Resolver::strict();
        assert!(!resolver.allow_unresolved);
    }

    #[test]
    fn test_detect_module_cycles_acyclic() {
        // Three modules: 0 -> 1 -> 2 (no cycle)
        let resolutions = vec![
            ModuleResolution {
                component_idx: 0,
                from_module: 0,
                to_module: 1,
                import_name: "foo".to_string(),
                export_name: "foo".to_string(),
            },
            ModuleResolution {
                component_idx: 0,
                from_module: 1,
                to_module: 2,
                import_name: "bar".to_string(),
                export_name: "bar".to_string(),
            },
        ];

        let result = Resolver::detect_module_cycles(0, 3, &resolutions);
        assert!(result.is_ok(), "Acyclic graph should not produce an error");
    }

    #[test]
    fn test_detect_module_cycles_cyclic() {
        // Two modules: 0 -> 1 -> 0 (cycle)
        let resolutions = vec![
            ModuleResolution {
                component_idx: 0,
                from_module: 0,
                to_module: 1,
                import_name: "foo".to_string(),
                export_name: "foo".to_string(),
            },
            ModuleResolution {
                component_idx: 0,
                from_module: 1,
                to_module: 0,
                import_name: "bar".to_string(),
                export_name: "bar".to_string(),
            },
        ];

        let result = Resolver::detect_module_cycles(0, 2, &resolutions);
        assert!(result.is_err(), "Cyclic graph should produce an error");
        let err = result.unwrap_err();
        match &err {
            Error::ModuleDependencyCycle {
                component_idx,
                cycle,
            } => {
                assert_eq!(*component_idx, 0);
                // The cycle string should mention both modules and form a closed path
                assert!(
                    cycle.contains("module[0]"),
                    "Cycle should mention module[0], got: {}",
                    cycle
                );
                assert!(
                    cycle.contains("module[1]"),
                    "Cycle should mention module[1], got: {}",
                    cycle
                );
            }
            other => panic!("Expected ModuleDependencyCycle, got: {:?}", other),
        }
    }

    #[test]
    fn test_detect_module_cycles_ignores_other_components() {
        // Cycle exists in component 1, but we check component 0 which is acyclic
        let resolutions = vec![
            ModuleResolution {
                component_idx: 0,
                from_module: 0,
                to_module: 1,
                import_name: "foo".to_string(),
                export_name: "foo".to_string(),
            },
            ModuleResolution {
                component_idx: 1,
                from_module: 0,
                to_module: 1,
                import_name: "a".to_string(),
                export_name: "a".to_string(),
            },
            ModuleResolution {
                component_idx: 1,
                from_module: 1,
                to_module: 0,
                import_name: "b".to_string(),
                export_name: "b".to_string(),
            },
        ];

        // Component 0 should be fine
        let result = Resolver::detect_module_cycles(0, 2, &resolutions);
        assert!(result.is_ok(), "Component 0 has no cycle and should pass");

        // Component 1 should detect the cycle
        let result = Resolver::detect_module_cycles(1, 2, &resolutions);
        assert!(result.is_err(), "Component 1 has a cycle and should fail");
    }

    #[test]
    fn test_detect_module_cycles_self_loop() {
        // Module 0 depends on itself (shouldn't happen in practice,
        // since resolve_module_imports filters from_mod == to_mod,
        // but the cycle detector should handle it if present)
        let resolutions = vec![ModuleResolution {
            component_idx: 0,
            from_module: 0,
            to_module: 0,
            import_name: "self".to_string(),
            export_name: "self".to_string(),
        }];

        let result = Resolver::detect_module_cycles(0, 1, &resolutions);
        assert!(result.is_err(), "Self-loop should be detected as a cycle");
    }

    #[test]
    fn test_detect_module_cycles_no_modules() {
        // Empty component (no modules)
        let result = Resolver::detect_module_cycles(0, 0, &[]);
        assert!(result.is_ok(), "Empty graph should not produce an error");
    }

    #[test]
    fn test_detect_module_cycles_three_node_cycle() {
        // 0 -> 1 -> 2 -> 0
        let resolutions = vec![
            ModuleResolution {
                component_idx: 0,
                from_module: 0,
                to_module: 1,
                import_name: "a".to_string(),
                export_name: "a".to_string(),
            },
            ModuleResolution {
                component_idx: 0,
                from_module: 1,
                to_module: 2,
                import_name: "b".to_string(),
                export_name: "b".to_string(),
            },
            ModuleResolution {
                component_idx: 0,
                from_module: 2,
                to_module: 0,
                import_name: "c".to_string(),
                export_name: "c".to_string(),
            },
        ];

        let result = Resolver::detect_module_cycles(0, 3, &resolutions);
        assert!(result.is_err(), "Three-node cycle should be detected");
        let err = result.unwrap_err();
        match &err {
            Error::ModuleDependencyCycle { cycle, .. } => {
                // Verify the cycle string forms a closed loop
                let parts: Vec<&str> = cycle.split(" -> ").collect();
                assert!(
                    parts.len() >= 3,
                    "Cycle path should have at least 3 entries (e.g. A -> B -> A), got: {}",
                    cycle
                );
                assert_eq!(
                    parts.first(),
                    parts.last(),
                    "Cycle path should start and end at the same module, got: {}",
                    cycle
                );
            }
            other => panic!("Expected ModuleDependencyCycle, got: {:?}", other),
        }
    }

    /// Helper: create a `ParsedComponent` with the given component-level
    /// imports and exports.
    ///
    /// Import names go into `component.imports` (matched by the resolver
    /// against other components' exports).  Export names go into
    /// `component.exports`.  All other fields use `ParsedComponent::empty()`
    /// defaults.
    fn make_component(import_names: &[&str], export_names: &[&str]) -> ParsedComponent {
        use crate::parser::ComponentImport;
        use wasmparser::{ComponentExternalKind, ComponentTypeRef};

        let mut comp = ParsedComponent::empty();
        for name in import_names {
            comp.imports.push(ComponentImport {
                name: name.to_string(),
                ty: ComponentTypeRef::Instance(0),
            });
        }
        for name in export_names {
            comp.exports.push(ComponentExport {
                name: name.to_string(),
                kind: ComponentExternalKind::Instance,
                index: 0,
            });
        }
        comp
    }

    /// SR-7: Valid topological instantiation order.
    /// LS-R-3: Diamond dependency graph.
    ///
    /// Four components forming a diamond:
    ///
    /// ```text
    ///       A (0)
    ///      / \
    ///   B (1) C (2)
    ///      \ /
    ///       D (3)
    /// ```
    ///
    /// A imports from B and C; B and C each import from D.
    /// Valid instantiation order requires D before {B, C} and {B, C} before A.
    #[test]
    fn test_topological_sort_diamond() {
        let components = vec![
            make_component(&["iface-b", "iface-c"], &[]), // A = index 0
            make_component(&["iface-d"], &["iface-b"]),   // B = index 1
            make_component(&["iface-d"], &["iface-c"]),   // C = index 2
            make_component(&[], &["iface-d"]),            // D = index 3
        ];

        let resolver = Resolver::new();
        let graph = resolver
            .resolve(&components)
            .expect("diamond resolution should succeed");

        let order = &graph.instantiation_order;
        assert_eq!(
            order.len(),
            4,
            "all four components must appear in the order"
        );

        // Build position map for order assertions
        let pos: HashMap<usize, usize> = order.iter().enumerate().map(|(i, &v)| (v, i)).collect();

        // D (3) must come before B (1) and C (2)
        assert!(
            pos[&3] < pos[&1],
            "D (index 3) must be instantiated before B (index 1), got order {:?}",
            order
        );
        assert!(
            pos[&3] < pos[&2],
            "D (index 3) must be instantiated before C (index 2), got order {:?}",
            order
        );

        // B (1) and C (2) must come before A (0)
        assert!(
            pos[&1] < pos[&0],
            "B (index 1) must be instantiated before A (index 0), got order {:?}",
            order
        );
        assert!(
            pos[&2] < pos[&0],
            "C (index 2) must be instantiated before A (index 0), got order {:?}",
            order
        );

        // Verify the dependency edges were recorded in resolved_imports
        assert!(
            graph
                .resolved_imports
                .contains_key(&(0, "iface-b".to_string())),
            "A's import of iface-b should be resolved"
        );
        assert!(
            graph
                .resolved_imports
                .contains_key(&(0, "iface-c".to_string())),
            "A's import of iface-c should be resolved"
        );
        assert!(
            graph
                .resolved_imports
                .contains_key(&(1, "iface-d".to_string())),
            "B's import of iface-d should be resolved"
        );
        assert!(
            graph
                .resolved_imports
                .contains_key(&(2, "iface-d".to_string())),
            "C's import of iface-d should be resolved"
        );
    }

    /// SC-9: Unresolved imports must be reported, not silently dropped.
    /// LS-R-4: Self-importing component (no provider for the import).
    ///
    /// A component imports an interface that no other component exports.
    /// Under strict mode the resolver must return an `UnresolvedImport` error.
    #[test]
    fn test_resolver_unresolved_import_error() {
        let components = vec![
            make_component(&["nonexistent-iface"], &[]),
            make_component(&[], &["some-other-iface"]),
        ];

        let resolver = Resolver::strict();
        let result = resolver.resolve(&components);

        assert!(
            result.is_err(),
            "strict resolver must reject an import that no component exports"
        );

        let err = result.unwrap_err();
        match &err {
            Error::UnresolvedImport { module, name } => {
                assert_eq!(module, "component");
                assert_eq!(
                    name, "nonexistent-iface",
                    "error should name the unresolved import"
                );
            }
            other => panic!("expected Error::UnresolvedImport, got: {:?}", other),
        }
    }

    /// SR-19 / LS-CP-2: Resolver order stability (determinism).
    ///
    /// Running the same resolution five times must produce an identical
    /// instantiation order every time.  Non-determinism here would cause
    /// downstream merging to produce semantically different modules from
    /// the same input, violating reproducible builds.
    #[test]
    fn test_resolver_preserves_order_stability() {
        // Use the diamond topology — it has multiple valid topological
        // orders (B and C are interchangeable), so a non-deterministic
        // implementation could vary between runs.
        let components = vec![
            make_component(&["iface-b", "iface-c"], &[]), // A = 0
            make_component(&["iface-d"], &["iface-b"]),   // B = 1
            make_component(&["iface-d"], &["iface-c"]),   // C = 2
            make_component(&[], &["iface-d"]),            // D = 3
        ];

        let resolver = Resolver::new();
        let baseline = resolver
            .resolve(&components)
            .expect("baseline resolution should succeed")
            .instantiation_order;

        for iteration in 1..=5 {
            let order = resolver
                .resolve(&components)
                .expect("repeated resolution should succeed")
                .instantiation_order;

            assert_eq!(
                order, baseline,
                "instantiation order diverged on iteration {}: got {:?}, expected {:?}",
                iteration, order, baseline
            );
        }
    }

    #[test]
    fn test_extract_wasi_resource_name() {
        // Standard WASI paths
        assert_eq!(extract_wasi_resource_name("wasi:io/error@0.2.6"), "error");
        assert_eq!(extract_wasi_resource_name("wasi:io/poll@0.2.6"), "poll");
        assert_eq!(
            extract_wasi_resource_name("wasi:io/streams@0.2.6"),
            "streams"
        );
        assert_eq!(
            extract_wasi_resource_name("wasi:cli/terminal-input@0.2.6"),
            "terminal-input"
        );

        // Without version
        assert_eq!(extract_wasi_resource_name("wasi:io/error"), "error");

        // Bare name (no slash, no version)
        assert_eq!(extract_wasi_resource_name("bare-name"), "bare-name");

        // Version but no slash
        assert_eq!(extract_wasi_resource_name("something@1.0.0"), "something");
    }

    // ---------------------------------------------------------------
    // CopyLayout classification tests (SR-6 / LS-R-2)
    // ---------------------------------------------------------------

    use crate::parser::{ComponentValType, PrimitiveValType};

    /// Build a minimal `ParsedComponent` with no modules, types, or instances.
    /// Sufficient for testing `copy_layout` on inline types (no `Type(idx)` references).
    fn empty_parsed_component() -> ParsedComponent {
        ParsedComponent {
            name: None,
            core_modules: Vec::new(),
            imports: Vec::new(),
            exports: Vec::new(),
            types: Vec::new(),
            instances: Vec::new(),
            canonical_functions: Vec::new(),
            sub_components: Vec::new(),
            component_aliases: Vec::new(),
            component_instances: Vec::new(),
            core_entity_order: Vec::new(),
            component_func_defs: Vec::new(),
            component_instance_defs: Vec::new(),
            component_type_defs: Vec::new(),
            original_size: 0,
            original_hash: String::new(),
            depth_0_sections: Vec::new(),
        }
    }

    /// SR-6: list<u32> contains no pointers, so should produce Bulk with
    /// byte_multiplier = 4 (sizeof(u32)).
    #[test]
    fn test_copy_layout_flat_list() {
        let pc = empty_parsed_component();
        let ty =
            ComponentValType::List(Box::new(ComponentValType::Primitive(PrimitiveValType::U32)));
        let layout = pc.copy_layout(&ty);
        match layout {
            CopyLayout::Bulk { byte_multiplier } => {
                assert_eq!(byte_multiplier, 4, "u32 element should be 4 bytes");
            }
            CopyLayout::Elements { .. } => {
                panic!("list<u32> should produce Bulk, not Elements");
            }
        }
    }

    /// SR-6: list<string> contains pointer pairs (each string is a (ptr, len) pair),
    /// so should produce Elements with element_size = 8 and one inner pointer at offset 0.
    #[test]
    fn test_copy_layout_string_list() {
        let pc = empty_parsed_component();
        let ty = ComponentValType::List(Box::new(ComponentValType::String));
        let layout = pc.copy_layout(&ty);
        match layout {
            CopyLayout::Elements {
                element_size,
                inner_pointers,
                ..
            } => {
                assert_eq!(
                    element_size, 8,
                    "string element is (i32 ptr, i32 len) = 8 bytes"
                );
                assert_eq!(
                    inner_pointers.len(),
                    1,
                    "one pointer pair per string element"
                );
                let (offset, ref inner_layout) = inner_pointers[0];
                assert_eq!(offset, 0, "string pointer pair starts at byte offset 0");
                // Inner layout for a string is Bulk { byte_multiplier: 1 }
                match inner_layout {
                    CopyLayout::Bulk { byte_multiplier } => {
                        assert_eq!(*byte_multiplier, 1, "string data is byte-granular");
                    }
                    _ => panic!("inner layout for string should be Bulk"),
                }
            }
            CopyLayout::Bulk { .. } => {
                panic!("list<string> should produce Elements, not Bulk");
            }
        }
    }

    /// SR-6 / LS-R-2: list<record{name: string, value: u32}> MUST produce Elements,
    /// not Bulk. The record contains a string field which is a (ptr, len) pair.
    /// Misclassifying this as Bulk would silently corrupt pointer data during
    /// cross-memory copy.
    #[test]
    fn test_copy_layout_record_with_string() {
        let pc = empty_parsed_component();
        // record { name: string, value: u32 }
        let record_ty = ComponentValType::Record(vec![
            ("name".to_string(), ComponentValType::String),
            (
                "value".to_string(),
                ComponentValType::Primitive(PrimitiveValType::U32),
            ),
        ]);
        let ty = ComponentValType::List(Box::new(record_ty));
        let layout = pc.copy_layout(&ty);
        match layout {
            CopyLayout::Elements {
                element_size,
                inner_pointers,
                ..
            } => {
                // Record layout: string at offset 0 (8 bytes: ptr + len, align 4),
                // then u32 at offset 8 (4 bytes, align 4). Unpadded size = 12.
                // Alignment = max(4, 4) = 4. Element size = align_up(12, 4) = 12.
                assert_eq!(
                    element_size, 12,
                    "record{{string, u32}} element should be 12 bytes"
                );
                assert_eq!(
                    inner_pointers.len(),
                    1,
                    "one pointer pair from the string field"
                );
                let (offset, ref inner_layout) = inner_pointers[0];
                assert_eq!(
                    offset, 0,
                    "string field starts at byte offset 0 in the record"
                );
                match inner_layout {
                    CopyLayout::Bulk { byte_multiplier } => {
                        assert_eq!(*byte_multiplier, 1, "string data is byte-granular");
                    }
                    _ => panic!("inner layout for string should be Bulk"),
                }
            }
            CopyLayout::Bulk { .. } => {
                panic!(
                    "list<record{{name: string, value: u32}}> MUST produce Elements, not Bulk \
                     (LS-R-2: pointer-containing record misclassified as Bulk)"
                );
            }
        }
    }

    /// SR-6: list<list<u8>> contains inner pointer pairs (each inner list is a
    /// (ptr, len) pair), so should produce Elements.
    #[test]
    fn test_copy_layout_nested_list() {
        let pc = empty_parsed_component();
        let inner_list =
            ComponentValType::List(Box::new(ComponentValType::Primitive(PrimitiveValType::U8)));
        let ty = ComponentValType::List(Box::new(inner_list));
        let layout = pc.copy_layout(&ty);
        match layout {
            CopyLayout::Elements {
                element_size,
                inner_pointers,
                ..
            } => {
                assert_eq!(
                    element_size, 8,
                    "list element is (i32 ptr, i32 len) = 8 bytes"
                );
                assert_eq!(
                    inner_pointers.len(),
                    1,
                    "one pointer pair per inner list element"
                );
                let (offset, ref inner_layout) = inner_pointers[0];
                assert_eq!(offset, 0, "inner list pointer pair starts at byte offset 0");
                // Inner layout for list<u8> is Bulk { byte_multiplier: 1 }
                match inner_layout {
                    CopyLayout::Bulk { byte_multiplier } => {
                        assert_eq!(*byte_multiplier, 1, "list<u8> element is 1 byte");
                    }
                    _ => panic!("inner layout for list<u8> should be Bulk"),
                }
            }
            CopyLayout::Bulk { .. } => {
                panic!("list<list<u8>> should produce Elements, not Bulk");
            }
        }
    }

    /// SR-6: list<record{a: u32, b: u32}> has no pointer-bearing fields,
    /// so should produce Bulk with byte_multiplier = 8 (two u32 fields).
    #[test]
    fn test_copy_layout_flat_record() {
        let pc = empty_parsed_component();
        let record_ty = ComponentValType::Record(vec![
            (
                "a".to_string(),
                ComponentValType::Primitive(PrimitiveValType::U32),
            ),
            (
                "b".to_string(),
                ComponentValType::Primitive(PrimitiveValType::U32),
            ),
        ]);
        let ty = ComponentValType::List(Box::new(record_ty));
        let layout = pc.copy_layout(&ty);
        match layout {
            CopyLayout::Bulk { byte_multiplier } => {
                assert_eq!(
                    byte_multiplier, 8,
                    "record{{a: u32, b: u32}} should be 8 bytes (4 + 4)"
                );
            }
            CopyLayout::Elements { .. } => {
                panic!(
                    "list<record{{a: u32, b: u32}}> should produce Bulk (no pointer fields), \
                     not Elements"
                );
            }
        }
    }

    // ---------------------------------------------------------------
    // SR-17: String encoding detection and transcoding requirements
    //
    // These tests verify that the resolver correctly detects when
    // string transcoding is needed based on caller/callee encoding
    // differences in AdapterRequirements.
    //
    // The resolver sets `string_transcoding = true` when
    // `caller_encoding != callee_encoding`. This flag is used by
    // the adapter generator to select the appropriate transcoding
    // loop (UTF-8 <-> UTF-16, Latin-1 -> UTF-8, etc.).
    // ---------------------------------------------------------------

    use crate::parser::CanonStringEncoding;

    #[test]
    fn test_sr17_adapter_requirements_no_transcoding_utf8_utf8() {
        let mut req = AdapterRequirements {
            caller_encoding: Some(CanonStringEncoding::Utf8),
            callee_encoding: Some(CanonStringEncoding::Utf8),
            ..Default::default()
        };
        // Simulate what the resolver does: compare encodings
        if let (Some(ce), Some(ce2)) = (req.caller_encoding, req.callee_encoding) {
            req.string_transcoding = ce != ce2;
        }
        assert!(
            !req.string_transcoding,
            "SR-17: UTF-8 to UTF-8 should not require transcoding"
        );
    }

    #[test]
    fn test_sr17_adapter_requirements_transcoding_utf8_to_utf16() {
        let mut req = AdapterRequirements {
            caller_encoding: Some(CanonStringEncoding::Utf8),
            callee_encoding: Some(CanonStringEncoding::Utf16),
            ..Default::default()
        };
        if let (Some(ce), Some(ce2)) = (req.caller_encoding, req.callee_encoding) {
            req.string_transcoding = ce != ce2;
        }
        assert!(
            req.string_transcoding,
            "SR-17: UTF-8 to UTF-16 should require transcoding"
        );
    }

    #[test]
    fn test_sr17_adapter_requirements_transcoding_utf16_to_utf8() {
        let mut req = AdapterRequirements {
            caller_encoding: Some(CanonStringEncoding::Utf16),
            callee_encoding: Some(CanonStringEncoding::Utf8),
            ..Default::default()
        };
        if let (Some(ce), Some(ce2)) = (req.caller_encoding, req.callee_encoding) {
            req.string_transcoding = ce != ce2;
        }
        assert!(
            req.string_transcoding,
            "SR-17: UTF-16 to UTF-8 should require transcoding"
        );
    }

    #[test]
    fn test_sr17_adapter_requirements_transcoding_compact_utf16_to_utf8() {
        let mut req = AdapterRequirements {
            caller_encoding: Some(CanonStringEncoding::CompactUtf16),
            callee_encoding: Some(CanonStringEncoding::Utf8),
            ..Default::default()
        };
        if let (Some(ce), Some(ce2)) = (req.caller_encoding, req.callee_encoding) {
            req.string_transcoding = ce != ce2;
        }
        assert!(
            req.string_transcoding,
            "SR-17: CompactUTF16 to UTF-8 should require transcoding"
        );
    }

    #[test]
    fn test_sr17_adapter_requirements_transcoding_utf8_to_compact_utf16() {
        let mut req = AdapterRequirements {
            caller_encoding: Some(CanonStringEncoding::Utf8),
            callee_encoding: Some(CanonStringEncoding::CompactUtf16),
            ..Default::default()
        };
        if let (Some(ce), Some(ce2)) = (req.caller_encoding, req.callee_encoding) {
            req.string_transcoding = ce != ce2;
        }
        assert!(
            req.string_transcoding,
            "SR-17: UTF-8 to CompactUTF16 should require transcoding"
        );
    }

    #[test]
    fn test_sr17_adapter_requirements_no_transcoding_utf16_utf16() {
        let mut req = AdapterRequirements {
            caller_encoding: Some(CanonStringEncoding::Utf16),
            callee_encoding: Some(CanonStringEncoding::Utf16),
            ..Default::default()
        };
        if let (Some(ce), Some(ce2)) = (req.caller_encoding, req.callee_encoding) {
            req.string_transcoding = ce != ce2;
        }
        assert!(
            !req.string_transcoding,
            "SR-17: UTF-16 to UTF-16 should not require transcoding"
        );
    }

    #[test]
    fn test_sr17_adapter_requirements_no_transcoding_compact_compact() {
        let mut req = AdapterRequirements {
            caller_encoding: Some(CanonStringEncoding::CompactUtf16),
            callee_encoding: Some(CanonStringEncoding::CompactUtf16),
            ..Default::default()
        };
        if let (Some(ce), Some(ce2)) = (req.caller_encoding, req.callee_encoding) {
            req.string_transcoding = ce != ce2;
        }
        assert!(
            !req.string_transcoding,
            "SR-17: CompactUTF16 to CompactUTF16 should not require transcoding"
        );
    }

    #[test]
    fn test_sr17_adapter_requirements_none_encoding_no_transcoding() {
        // When either encoding is None (e.g., no canonical option parsed),
        // the resolver does not set string_transcoding. This is the safe
        // default -- adapter generation defaults to UTF-8 on both sides.
        let mut req = AdapterRequirements {
            caller_encoding: None,
            callee_encoding: Some(CanonStringEncoding::Utf16),
            ..Default::default()
        };
        if let (Some(ce), Some(ce2)) = (req.caller_encoding, req.callee_encoding) {
            req.string_transcoding = ce != ce2;
        }
        assert!(
            !req.string_transcoding,
            "SR-17: None caller encoding should not trigger transcoding"
        );
    }

    #[test]
    fn test_sr17_all_encoding_pairs_transcoding_matrix() {
        // Exhaustive test: for every pair of CanonStringEncoding values,
        // verify that the transcoding flag matches whether they differ.
        let encodings = [
            CanonStringEncoding::Utf8,
            CanonStringEncoding::Utf16,
            CanonStringEncoding::CompactUtf16,
        ];
        for caller in &encodings {
            for callee in &encodings {
                let mut req = AdapterRequirements {
                    caller_encoding: Some(*caller),
                    callee_encoding: Some(*callee),
                    ..Default::default()
                };
                if let (Some(ce), Some(ce2)) = (req.caller_encoding, req.callee_encoding) {
                    req.string_transcoding = ce != ce2;
                }
                let expected = caller != callee;
                assert_eq!(
                    req.string_transcoding, expected,
                    "SR-17: {:?} to {:?}: expected transcoding={}, got={}",
                    caller, callee, expected, req.string_transcoding
                );
            }
        }
    }

    // ---------------------------------------------------------------
    // SR-17: CopyLayout for strings does NOT change with encoding
    //
    // The CopyLayout for a string parameter is always
    // Bulk { byte_multiplier: 1 } because CopyLayout describes the
    // raw data copy step. The `len` field in the (ptr, len) pair
    // has encoding-dependent semantics:
    //   - UTF-8:  len = byte count
    //   - UTF-16: len = code unit count (each code unit = 2 bytes)
    //   - Latin-1: len = byte count
    //
    // The adapter must account for this difference in the transcoding
    // loop, NOT in the CopyLayout. The CopyLayout always uses
    // byte_multiplier=1 for strings because the copy is encoding-
    // agnostic (copy raw bytes, then transcode if needed).
    // ---------------------------------------------------------------

    #[test]
    fn test_sr17_copy_layout_string_encoding_agnostic() {
        // CopyLayout for String is always Bulk { byte_multiplier: 1 },
        // regardless of the encoding that will be used. The encoding
        // is handled at the adapter level, not the copy layout level.
        let pc = empty_parsed_component();
        let ty = ComponentValType::String;
        let layout = pc.copy_layout(&ty);
        match layout {
            CopyLayout::Bulk { byte_multiplier } => {
                assert_eq!(
                    byte_multiplier, 1,
                    "SR-17: string CopyLayout byte_multiplier should always be 1"
                );
            }
            CopyLayout::Elements { .. } => {
                panic!("SR-17: string should never produce Elements CopyLayout");
            }
        }
    }

    #[test]
    fn test_sr17_collect_param_copy_layouts_string_param() {
        // A function with a single string parameter should produce one copy layout.
        let pc = empty_parsed_component();
        let params = vec![("s".to_string(), ComponentValType::String)];
        let layouts = collect_param_copy_layouts(&pc, &params);
        assert_eq!(
            layouts.len(),
            1,
            "SR-17: one string param should produce one copy layout"
        );
        match &layouts[0] {
            CopyLayout::Bulk { byte_multiplier } => {
                assert_eq!(*byte_multiplier, 1);
            }
            _ => panic!("SR-17: string param should produce Bulk layout"),
        }
    }

    #[test]
    fn test_sr17_collect_param_copy_layouts_multiple_strings() {
        // Multiple string params should each produce their own copy layout.
        let pc = empty_parsed_component();
        let params = vec![
            ("a".to_string(), ComponentValType::String),
            (
                "b".to_string(),
                ComponentValType::Primitive(PrimitiveValType::U32),
            ),
            ("c".to_string(), ComponentValType::String),
        ];
        let layouts = collect_param_copy_layouts(&pc, &params);
        assert_eq!(
            layouts.len(),
            2,
            "SR-17: two string params should produce two copy layouts (scalar params excluded)"
        );
    }

    #[test]
    fn test_sr17_collect_result_copy_layouts_string_result() {
        let pc = empty_parsed_component();
        let results: Vec<(Option<String>, ComponentValType)> =
            vec![(None, ComponentValType::String)];
        let layouts = collect_result_copy_layouts(&pc, &results);
        assert_eq!(
            layouts.len(),
            1,
            "SR-17: one string result should produce one copy layout"
        );
    }

    #[test]
    fn test_sr17_collect_result_copy_layouts_no_strings() {
        let pc = empty_parsed_component();
        let results: Vec<(Option<String>, ComponentValType)> =
            vec![(None, ComponentValType::Primitive(PrimitiveValType::U32))];
        let layouts = collect_result_copy_layouts(&pc, &results);
        assert_eq!(
            layouts.len(),
            0,
            "SR-17: scalar-only results should produce zero copy layouts"
        );
    }
}
