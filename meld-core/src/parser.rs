//! Component parsing using wasmparser
//!
//! This module handles parsing WebAssembly P2/P3 components and extracting
//! the core modules, types, imports, and exports needed for fusion.

use crate::attestation::compute_sha256;
use crate::{Error, Result};
use wasm_encoder::ValType;
use wasmparser::{
    ComponentExternalKind, ComponentTypeRef, ExternalKind, Parser, Payload, ValType as WasmValType,
};

/// A component-level instance created by `ComponentInstanceSection`.
///
/// These describe how sub-components are wired together at the component
/// level (as opposed to `ComponentInstance` / `InstanceKind` which describe
/// *core* module instantiation via the core `InstanceSection`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComponentLevelInstance {
    /// Instantiate a sub-component with the given arguments.
    Instantiate {
        component_index: u32,
        args: Vec<(String, ComponentExternalKind, u32)>,
    },
    /// Synthesized from inline exports.
    FromExports(Vec<(String, ComponentExternalKind, u32)>),
}

/// The kind of an outer alias, decoupled from wasmparser's internal type
/// for API stability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OuterAliasKind {
    /// A core module alias.
    CoreModule,
    /// A core type alias.
    CoreType,
    /// A component type alias.
    Type,
    /// A component alias.
    Component,
}

/// An entry from the `ComponentAliasSection`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComponentAliasEntry {
    /// Alias an export of a component instance.
    InstanceExport {
        kind: ComponentExternalKind,
        instance_index: u32,
        name: String,
    },
    /// Alias a core export of a core instance.
    CoreInstanceExport {
        kind: ExternalKind,
        instance_index: u32,
        name: String,
    },
    /// Outer alias (references parent component's index spaces).
    Outer {
        kind: OuterAliasKind,
        count: u32,
        index: u32,
    },
}

/// Records what created a core entity, preserving binary section ordering.
///
/// In the Component Model binary format, canonical function sections and
/// component alias sections can interleave arbitrarily. Both allocate from
/// per-kind entity counters (e.g., core funcs). This enum tracks the
/// creation order so the resolver can map entity indices back to their
/// source (a module export vs. a canonical function).
#[derive(Debug, Clone)]
pub enum CoreEntityDef {
    /// A canonical function (Lower, ResourceDrop, ResourceNew, ResourceRep)
    /// creates a core func. The usize is the index into `canonical_functions`.
    CanonicalFunction(usize),
    /// An alias of a core instance export creates a per-kind entity.
    /// The usize is the index into `component_aliases` (only CoreInstanceExport entries).
    CoreAlias(usize),
}

/// Records what created each component-level function index.
///
/// The component function index space is populated by imports (Func type),
/// `canon lift` entries, and `ComponentAlias::InstanceExport { kind: Func }`
/// entries. These sections interleave in the binary, so we track the
/// allocation order to reconstruct indices for canon-lower tracing.
#[derive(Debug, Clone)]
pub enum ComponentFuncDef {
    /// A component import with Func type. The usize is the index into `imports`.
    Import(usize),
    /// A `canon lift` creates a component function. Index into `canonical_functions`.
    Lift(usize),
    /// An `InstanceExport { kind: Func }` alias. Index into `component_aliases`.
    InstanceExportAlias(usize),
}

/// Records what created each component-level instance index.
///
/// The component instance index space is populated by imports (Instance type),
/// `ComponentInstanceSection` entries, and `ComponentAlias::InstanceExport { kind: Instance }`
/// entries. Tracked in binary section order.
#[derive(Debug, Clone)]
pub enum ComponentInstanceDef {
    /// A component import with Instance type. The usize is the index into `imports`.
    Import(usize),
    /// A `ComponentInstanceSection` entry. Index into `component_instances`.
    Instance(usize),
    /// An `InstanceExport { kind: Instance }` alias. Index into `component_aliases`.
    InstanceExportAlias(usize),
}

/// Records what created each component-level type index.
///
/// The component type index space is populated by `ComponentTypeSection` entries,
/// imports with `Type` type refs, and `ComponentAlias::InstanceExport { kind: Type }`
/// entries. Tracked in binary section order so the resolver can trace
/// `ResourceDrop { resource: T }` back to a WASI import name.
#[derive(Debug, Clone)]
pub enum ComponentTypeDef {
    /// A component import with Type type ref. The usize is the index into `imports`.
    Import(usize),
    /// A `ComponentTypeSection` entry (defined type, resource, etc.).
    Defined,
    /// An `InstanceExport { kind: Type }` alias. Index into `component_aliases`.
    InstanceExportAlias(usize),
    /// A type created by a component export with a type annotation `(type (eq N))`.
    /// The u32 is the target type index that this type equals.
    ExportAlias(u32),
}

/// A parsed WebAssembly component
#[derive(Debug, Clone)]
pub struct ParsedComponent {
    /// Optional name for this component
    pub name: Option<String>,

    /// Core modules extracted from the component
    pub core_modules: Vec<CoreModule>,

    /// Component-level imports
    pub imports: Vec<ComponentImport>,

    /// Component-level exports
    pub exports: Vec<ComponentExport>,

    /// Component type definitions
    pub types: Vec<ComponentType>,

    /// Instances defined in the component
    pub instances: Vec<ComponentInstance>,

    /// Canonical function entries (lift, lower, resource ops)
    pub canonical_functions: Vec<CanonicalEntry>,

    /// Nested sub-components (from `ComponentSection` payloads)
    pub sub_components: Vec<ParsedComponent>,

    /// Component-level aliases (from `ComponentAliasSection`)
    pub component_aliases: Vec<ComponentAliasEntry>,

    /// Component-level instances (from `ComponentInstanceSection`)
    pub component_instances: Vec<ComponentLevelInstance>,

    /// Ordered sequence of core entity-defining operations.
    /// Canonical functions create core funcs; core aliases create per-kind
    /// entities (func/memory/table/global). This preserves the interleaved
    /// section ordering from the binary, which is needed to map entity
    /// indices in `FromExports` instances back to source modules.
    pub core_entity_order: Vec<CoreEntityDef>,

    /// Ordered sequence of component function definitions.
    /// Tracks what created each component function index (imports, lifts,
    /// instance-export aliases) in binary section order.
    pub component_func_defs: Vec<ComponentFuncDef>,

    /// Ordered sequence of component instance definitions.
    /// Tracks what created each component instance index (imports,
    /// ComponentInstanceSection entries, instance-export aliases).
    pub component_instance_defs: Vec<ComponentInstanceDef>,

    /// Ordered sequence of component type definitions.
    /// Tracks what created each component type index (imports with Type refs,
    /// ComponentTypeSection entries, instance-export Type aliases).
    /// Used by the resolver to trace `ResourceDrop` back to WASI import names.
    pub component_type_defs: Vec<ComponentTypeDef>,

    /// Original size in bytes
    pub original_size: usize,

    /// SHA-256 hash of original component bytes (hex encoded)
    pub original_hash: String,

    /// Raw bytes of depth-0 component sections needed for P2 wrapping.
    /// Each entry is `(section_id, raw_bytes)` — specifically:
    /// - Section ID 6 (ComponentAlias) — type aliases from imported instances
    /// - Section ID 7 (ComponentType) — component-level type definitions
    /// - Section ID 10 (ComponentImport) — component-level import declarations
    ///   These are replayed verbatim into a wrapper component to preserve the
    ///   original WIT interface without full type reconstruction. The ordering
    ///   matters because Import sections reference types defined in preceding
    ///   Type and Alias sections.
    pub depth_0_sections: Vec<(u8, Vec<u8>)>,
}

/// A core WebAssembly module extracted from a component
#[derive(Debug, Clone)]
pub struct CoreModule {
    /// Module index within the component
    pub index: u32,

    /// Raw module bytes (the complete core module)
    pub bytes: Vec<u8>,

    /// Parsed type section
    pub types: Vec<FuncType>,

    /// Parsed import section
    pub imports: Vec<ModuleImport>,

    /// Parsed export section
    pub exports: Vec<ModuleExport>,

    /// Function section (type indices)
    pub functions: Vec<u32>,

    /// Memory definitions
    pub memories: Vec<MemoryType>,

    /// Table definitions
    pub tables: Vec<TableType>,

    /// Global definitions
    pub globals: Vec<GlobalType>,

    /// Start function index
    pub start: Option<u32>,

    /// Data segment count
    pub data_count: Option<u32>,

    /// Element segment count
    pub element_count: u32,

    /// Custom sections
    pub custom_sections: Vec<(String, Vec<u8>)>,

    /// Code section byte range (start, end) within module bytes
    pub code_section_range: Option<(usize, usize)>,

    /// Global section byte range for init expressions
    pub global_section_range: Option<(usize, usize)>,

    /// Element section byte range
    pub element_section_range: Option<(usize, usize)>,

    /// Data section byte range
    pub data_section_range: Option<(usize, usize)>,
}

/// Function type signature
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncType {
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
}

/// Module-level import
#[derive(Debug, Clone)]
pub struct ModuleImport {
    /// Import module name
    pub module: String,
    /// Import field name
    pub name: String,
    /// Import kind and type
    pub kind: ImportKind,
}

/// Import entity kind
#[derive(Debug, Clone)]
pub enum ImportKind {
    Function(u32), // Type index
    Table(TableType),
    Memory(MemoryType),
    Global(GlobalType),
}

/// Module-level export
#[derive(Debug, Clone)]
pub struct ModuleExport {
    /// Export name
    pub name: String,
    /// Export kind
    pub kind: ExportKind,
    /// Index of the exported entity
    pub index: u32,
}

/// Export entity kind
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExportKind {
    Function,
    Table,
    Memory,
    Global,
}

/// Memory type definition
#[derive(Debug, Clone)]
pub struct MemoryType {
    /// Whether the memory is 64-bit
    pub memory64: bool,
    /// Whether the memory is shared
    pub shared: bool,
    /// Initial memory size in pages
    pub initial: u64,
    /// Maximum memory size in pages
    pub maximum: Option<u64>,
}

/// Table type definition
#[derive(Debug, Clone)]
pub struct TableType {
    /// Element type
    pub element_type: ValType,
    /// Initial table size
    pub initial: u64,
    /// Maximum table size
    pub maximum: Option<u64>,
}

/// Global type definition
#[derive(Debug, Clone)]
pub struct GlobalType {
    /// Value type
    pub content_type: ValType,
    /// Whether the global is mutable
    pub mutable: bool,
    /// Raw init expression bytes (without trailing End opcode).
    /// Empty for imported globals which have no initializer.
    pub init_expr_bytes: Vec<u8>,
}

/// Component-level import
#[derive(Debug, Clone)]
pub struct ComponentImport {
    /// Import name (URL or kebab-case identifier)
    pub name: String,
    /// Type reference
    pub ty: ComponentTypeRef,
}

/// Component-level export
#[derive(Debug, Clone)]
pub struct ComponentExport {
    /// Export name
    pub name: String,
    /// Kind of export
    pub kind: ComponentExternalKind,
    /// Index of the exported entity
    pub index: u32,
}

/// Component type definition
#[derive(Debug, Clone)]
pub struct ComponentType {
    /// Type kind (function, instance, component, etc.)
    pub kind: ComponentTypeKind,
}

/// Component type kind
#[derive(Debug, Clone)]
pub enum ComponentTypeKind {
    /// Component function type
    Function {
        params: Vec<(String, ComponentValType)>,
        results: Vec<(Option<String>, ComponentValType)>,
    },
    /// Instance type
    Instance {
        exports: Vec<(String, ComponentTypeRef)>,
    },
    /// Defined value type (result, list, option, etc.)
    Defined(ComponentValType),
    /// Other type (resource, component, etc.)
    Other,
}

/// Component value type
#[derive(Debug, Clone)]
pub enum ComponentValType {
    Primitive(PrimitiveValType),
    String,
    List(Box<ComponentValType>),
    Record(Vec<(String, ComponentValType)>),
    Variant(Vec<(String, Option<ComponentValType>)>),
    Tuple(Vec<ComponentValType>),
    Option(Box<ComponentValType>),
    Result {
        ok: Option<Box<ComponentValType>>,
        err: Option<Box<ComponentValType>>,
    },
    Own(u32),
    Borrow(u32),
    Type(u32),
}

/// Primitive value types in the Component Model
#[derive(Debug, Clone, Copy)]
pub enum PrimitiveValType {
    Bool,
    S8,
    U8,
    S16,
    U16,
    S32,
    U32,
    S64,
    U64,
    F32,
    F64,
    Char,
}

/// String encoding declared in canonical options
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CanonStringEncoding {
    Utf8,
    Utf16,
    CompactUtf16,
}

/// Canonical ABI options attached to a lift or lower
#[derive(Debug, Clone)]
pub struct CanonicalOptions {
    pub string_encoding: CanonStringEncoding,
    pub memory: Option<u32>,
    pub realloc: Option<u32>,
    pub post_return: Option<u32>,
}

impl Default for CanonicalOptions {
    fn default() -> Self {
        Self {
            string_encoding: CanonStringEncoding::Utf8,
            memory: None,
            realloc: None,
            post_return: None,
        }
    }
}

/// A canonical function entry from the ComponentCanonicalSection
#[derive(Debug, Clone)]
pub enum CanonicalEntry {
    /// Lift a core function to a component function
    Lift {
        core_func_index: u32,
        type_index: u32,
        options: CanonicalOptions,
    },
    /// Lower a component function to a core function
    Lower {
        func_index: u32,
        options: CanonicalOptions,
    },
    /// Create a new resource handle
    ResourceNew { resource: u32 },
    /// Drop a resource handle
    ResourceDrop { resource: u32 },
    /// Get representation of a resource handle
    ResourceRep { resource: u32 },
    /// Spawn a new thread
    ThreadSpawn { func_ty_index: u32 },
    /// Query hardware thread concurrency
    ThreadHwConcurrency,
}

/// Component instance
#[derive(Debug, Clone)]
pub struct ComponentInstance {
    /// Instance index
    pub index: u32,
    /// How the instance was created
    pub kind: InstanceKind,
}

/// How a component instance was created
#[derive(Debug, Clone)]
pub enum InstanceKind {
    /// Instantiated from a module
    Instantiate {
        module_idx: u32,
        args: Vec<(String, InstanceArg)>,
    },
    /// Created from exports (core module exports)
    FromExports(Vec<(String, ExternalKind, u32)>),
}

/// Argument to an instance instantiation
#[derive(Debug, Clone)]
pub enum InstanceArg {
    Instance(u32),
    Function(u32),
    Value(u32),
}

/// Parser for WebAssembly components
pub struct ComponentParser {
    /// Whether to validate during parsing
    validate: bool,
}

/// Check if any sub-component in the tree contains core modules.
fn has_modules_recursive(component: &ParsedComponent) -> bool {
    component
        .sub_components
        .iter()
        .any(|sub| !sub.core_modules.is_empty() || has_modules_recursive(sub))
}

impl ComponentParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self { validate: true }
    }

    /// Create a parser without validation (faster but less safe)
    pub fn without_validation() -> Self {
        Self { validate: false }
    }

    /// Parse component bytes into a ParsedComponent
    pub fn parse(&self, bytes: &[u8]) -> Result<ParsedComponent> {
        // Check for WASM magic number
        if bytes.len() < 8 {
            return Err(Error::InvalidWasm("file too small".to_string()));
        }

        if &bytes[0..4] != b"\0asm" {
            return Err(Error::InvalidWasm("invalid magic number".to_string()));
        }

        // Check version - component format has version 0x0d (13)
        let version = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
        let is_component = version == 0x0001_000d;

        if !is_component {
            // This is a core module, not a component
            return Err(Error::NotAComponent);
        }

        if self.validate {
            let mut validator = wasmparser::Validator::new();
            validator.validate_all(bytes)?;
        }

        let mut component = ParsedComponent {
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
            original_size: bytes.len(),
            original_hash: compute_sha256(bytes),
            depth_0_sections: Vec::new(),
        };

        let parser = Parser::new(0);

        // Depth-aware parsing: track nesting level so that payloads inside
        // nested ComponentSection are routed to the correct sub-component.
        let mut depth = 0usize;
        let mut sub_stack: Vec<ParsedComponent> = Vec::new();
        // Track non-component nesting (ModuleSection) so that their End
        // payloads don't prematurely pop the component sub_stack.
        let mut module_nesting = 0usize;
        // Stop capturing depth_0_sections once we hit the first core module,
        // so we only replay interface-definition sections (Type, Import, Alias)
        // and not the wiring sections that reference core instances.
        let mut seen_core_module = false;

        for payload in parser.parse_all(bytes) {
            let payload = payload?;
            // Track when we first encounter a core module or sub-component at
            // depth 0.  After this point, sections are wiring (instances,
            // aliases referencing sub-components) rather than interface
            // definitions, so we stop capturing depth_0_sections.
            if depth == 0
                && matches!(
                    &payload,
                    Payload::ModuleSection { .. } | Payload::ComponentSection { .. }
                )
            {
                seen_core_module = true;
            }
            let is_module_section = matches!(&payload, Payload::ModuleSection { .. });
            match &payload {
                Payload::ComponentSection { .. } => {
                    depth += 1;
                    sub_stack.push(ParsedComponent::empty());
                    continue; // don't pass ComponentSection to handle_payload
                }
                Payload::End(_) if module_nesting > 0 => {
                    // End of a nested core module — NOT a component.
                    module_nesting -= 1;
                    continue;
                }
                Payload::End(_) if depth > 0 => {
                    depth -= 1;
                    let sub = sub_stack.pop().unwrap();
                    let parent = if depth > 0 {
                        sub_stack.last_mut().unwrap()
                    } else {
                        &mut component
                    };
                    parent.sub_components.push(sub);
                    continue;
                }
                _ => {}
            }
            // Skip payloads from nested core modules (TypeSection,
            // FunctionSection, etc.) — they're handled by parse_core_module.
            if module_nesting > 0 {
                continue;
            }
            let target = if depth > 0 {
                sub_stack.last_mut().unwrap()
            } else {
                &mut component
            };
            let capture_sections = depth == 0 && !seen_core_module;
            self.handle_payload(payload, target, bytes, capture_sections)?;
            // After handle_payload processes a ModuleSection (calling
            // parse_core_module which independently parses the module from
            // its binary range), start skipping the module's inner payloads
            // that parse_all will yield next.
            if is_module_section {
                module_nesting += 1;
            }
        }

        if component.core_modules.is_empty() && !has_modules_recursive(&component) {
            return Err(Error::NoCoreModules);
        }

        Ok(component)
    }

    /// Handle a single payload from the parser.
    ///
    /// `capture_sections`: if true, raw section bytes for Type/Import/Alias
    /// sections are appended to `depth_0_sections` for P2 component wrapping.
    fn handle_payload(
        &self,
        payload: Payload<'_>,
        component: &mut ParsedComponent,
        _full_bytes: &[u8],
        capture_sections: bool,
    ) -> Result<()> {
        match payload {
            Payload::Version { .. } => {
                // Already handled
            }

            Payload::ModuleSection {
                parser,
                unchecked_range,
            } => {
                // Found an embedded core module
                let module_bytes = &_full_bytes[unchecked_range.start..unchecked_range.end];
                let core_module = self.parse_core_module(
                    component.core_modules.len() as u32,
                    module_bytes,
                    parser,
                )?;
                component.core_modules.push(core_module);
            }

            Payload::ComponentImportSection(reader) => {
                // Capture raw section bytes at depth 0 for P2 wrapping.
                // Section ID 10 = ComponentImport in the component binary format.
                if capture_sections {
                    let range = reader.range();
                    component
                        .depth_0_sections
                        .push((10, _full_bytes[range.start..range.end].to_vec()));
                }
                for import in reader {
                    let import = import?;
                    let import_idx = component.imports.len();
                    // Track component-level index allocations from imports
                    match &import.ty {
                        wasmparser::ComponentTypeRef::Func(_) => {
                            component
                                .component_func_defs
                                .push(ComponentFuncDef::Import(import_idx));
                        }
                        wasmparser::ComponentTypeRef::Instance(_) => {
                            component
                                .component_instance_defs
                                .push(ComponentInstanceDef::Import(import_idx));
                        }
                        wasmparser::ComponentTypeRef::Type(..) => {
                            component
                                .component_type_defs
                                .push(ComponentTypeDef::Import(import_idx));
                        }
                        _ => {}
                    }
                    component.imports.push(ComponentImport {
                        name: import.name.0.to_string(),
                        ty: import.ty,
                    });
                }
            }

            Payload::ComponentExportSection(reader) => {
                for export in reader {
                    let export = export?;
                    // Component exports with type annotations create new type indices
                    // when the export kind is Type. Track these in component_type_defs.
                    if export.kind == ComponentExternalKind::Type {
                        if let Some(wasmparser::ComponentTypeRef::Type(
                            wasmparser::TypeBounds::Eq(target_idx),
                        )) = export.ty
                        {
                            component
                                .component_type_defs
                                .push(ComponentTypeDef::ExportAlias(target_idx));
                        } else {
                            // SubResource or no type annotation — still allocates a type index
                            component
                                .component_type_defs
                                .push(ComponentTypeDef::ExportAlias(export.index));
                        }
                    }
                    component.exports.push(ComponentExport {
                        name: export.name.0.to_string(),
                        kind: export.kind,
                        index: export.index,
                    });
                }
            }

            Payload::InstanceSection(reader) => {
                for instance in reader {
                    let instance = instance?;
                    let global_idx = component.instances.len() as u32;
                    let kind = match instance {
                        wasmparser::Instance::Instantiate { module_index, args } => {
                            let parsed_args: Vec<_> = args
                                .iter()
                                .map(|arg| {
                                    let inst_arg = match arg.kind {
                                        wasmparser::InstantiationArgKind::Instance => {
                                            InstanceArg::Instance(arg.index)
                                        }
                                    };
                                    (arg.name.to_string(), inst_arg)
                                })
                                .collect();
                            InstanceKind::Instantiate {
                                module_idx: module_index,
                                args: parsed_args,
                            }
                        }
                        wasmparser::Instance::FromExports(exports) => {
                            let parsed: Vec<_> = exports
                                .iter()
                                .map(|export| (export.name.to_string(), export.kind, export.index))
                                .collect();
                            InstanceKind::FromExports(parsed)
                        }
                    };
                    component.instances.push(ComponentInstance {
                        index: global_idx,
                        kind,
                    });
                }
            }

            Payload::ComponentTypeSection(reader) => {
                // Capture raw section bytes at depth 0 for P2 wrapping.
                // Section ID 7 = ComponentType in the component binary format.
                if capture_sections {
                    let range = reader.range();
                    component
                        .depth_0_sections
                        .push((7, _full_bytes[range.start..range.end].to_vec()));
                }
                for ty in reader {
                    let ty = ty?;
                    let kind = match ty {
                        wasmparser::ComponentType::Func(func_type) => {
                            let params = func_type
                                .params
                                .iter()
                                .map(|(name, ty)| {
                                    (name.to_string(), convert_wp_component_val_type(ty))
                                })
                                .collect();
                            let results = func_type
                                .results
                                .iter()
                                .map(|(name, ty)| {
                                    (name.map(String::from), convert_wp_component_val_type(ty))
                                })
                                .collect();
                            ComponentTypeKind::Function { params, results }
                        }
                        wasmparser::ComponentType::Defined(dt) => convert_wp_defined_type(&dt),
                        wasmparser::ComponentType::Component(_) => ComponentTypeKind::Other,
                        wasmparser::ComponentType::Instance(_) => ComponentTypeKind::Other,
                        wasmparser::ComponentType::Resource { .. } => ComponentTypeKind::Other,
                    };
                    component.types.push(ComponentType { kind });
                    component
                        .component_type_defs
                        .push(ComponentTypeDef::Defined);
                }
            }

            Payload::ComponentCanonicalSection(reader) => {
                for canon in reader {
                    let canon = canon?;
                    let creates_core_func = matches!(
                        &canon,
                        wasmparser::CanonicalFunction::Lower { .. }
                            | wasmparser::CanonicalFunction::ResourceNew { .. }
                            | wasmparser::CanonicalFunction::ResourceDrop { .. }
                            | wasmparser::CanonicalFunction::ResourceRep { .. }
                    );
                    let is_lift = matches!(&canon, wasmparser::CanonicalFunction::Lift { .. });
                    let canon_idx = component.canonical_functions.len();
                    component
                        .canonical_functions
                        .push(convert_canonical_function(canon));
                    if creates_core_func {
                        component
                            .core_entity_order
                            .push(CoreEntityDef::CanonicalFunction(canon_idx));
                    }
                    if is_lift {
                        component
                            .component_func_defs
                            .push(ComponentFuncDef::Lift(canon_idx));
                    }
                }
            }
            Payload::CoreTypeSection(_) => {}
            Payload::ComponentAliasSection(reader) => {
                // Capture raw section bytes at depth 0 for P2 wrapping.
                // Section ID 6 = ComponentAlias. These define type aliases
                // from imported instances that subsequent Type/Import sections
                // reference.
                if capture_sections {
                    let range = reader.range();
                    component
                        .depth_0_sections
                        .push((6, _full_bytes[range.start..range.end].to_vec()));
                }
                for alias in reader {
                    let alias = alias?;
                    let entry = convert_component_alias(alias);
                    if let Some(entry) = entry {
                        let alias_idx = component.component_aliases.len();
                        let is_core_instance_export =
                            matches!(&entry, ComponentAliasEntry::CoreInstanceExport { .. });
                        // Track component-level index allocations from aliases
                        match &entry {
                            ComponentAliasEntry::InstanceExport {
                                kind: ComponentExternalKind::Func,
                                ..
                            } => {
                                component
                                    .component_func_defs
                                    .push(ComponentFuncDef::InstanceExportAlias(alias_idx));
                            }
                            ComponentAliasEntry::InstanceExport {
                                kind: ComponentExternalKind::Instance,
                                ..
                            } => {
                                component
                                    .component_instance_defs
                                    .push(ComponentInstanceDef::InstanceExportAlias(alias_idx));
                            }
                            ComponentAliasEntry::InstanceExport {
                                kind: ComponentExternalKind::Type,
                                ..
                            } => {
                                component
                                    .component_type_defs
                                    .push(ComponentTypeDef::InstanceExportAlias(alias_idx));
                            }
                            _ => {}
                        }
                        component.component_aliases.push(entry);
                        if is_core_instance_export {
                            component
                                .core_entity_order
                                .push(CoreEntityDef::CoreAlias(alias_idx));
                        }
                    }
                }
            }
            Payload::ComponentSection { .. } => {
                // Handled by depth tracking in parse(); should not reach here.
            }
            Payload::ComponentInstanceSection(reader) => {
                for instance in reader {
                    let instance = instance?;
                    let inst_idx = component.component_instances.len();
                    let entry = convert_component_instance(instance);
                    component
                        .component_instance_defs
                        .push(ComponentInstanceDef::Instance(inst_idx));
                    component.component_instances.push(entry);
                }
            }
            Payload::ComponentStartSection { .. } => {}

            // Custom sections
            Payload::CustomSection(reader) => {
                // Store component-level custom sections
                // These might contain important metadata
                let name = reader.name().to_string();
                let data = reader.data().to_vec();
                log::debug!("Found component custom section: {}", name);
                // For now we don't store component-level custom sections
                // They're typically component metadata, not module data
                let _ = (name, data);
            }

            // Skip other payloads
            _ => {}
        }

        Ok(())
    }

    /// Parse an embedded core module
    fn parse_core_module(
        &self,
        index: u32,
        bytes: &[u8],
        _parser: wasmparser::Parser,
    ) -> Result<CoreModule> {
        let mut module = CoreModule {
            index,
            bytes: bytes.to_vec(),
            types: Vec::new(),
            imports: Vec::new(),
            exports: Vec::new(),
            functions: Vec::new(),
            memories: Vec::new(),
            tables: Vec::new(),
            globals: Vec::new(),
            start: None,
            data_count: None,
            element_count: 0,
            custom_sections: Vec::new(),
            code_section_range: None,
            global_section_range: None,
            element_section_range: None,
            data_section_range: None,
        };

        // Parse the core module
        let parser = Parser::new(0);
        for payload in parser.parse_all(bytes) {
            let payload = payload?;
            match payload {
                Payload::TypeSection(reader) => {
                    for rec_group in reader {
                        let rec_group = rec_group?;
                        for subtype in rec_group.into_types() {
                            if let wasmparser::CompositeInnerType::Func(ft) =
                                &subtype.composite_type.inner
                            {
                                module.types.push(FuncType {
                                    params: ft
                                        .params()
                                        .iter()
                                        .map(|t| convert_val_type(*t))
                                        .collect(),
                                    results: ft
                                        .results()
                                        .iter()
                                        .map(|t| convert_val_type(*t))
                                        .collect(),
                                });
                            }
                        }
                    }
                }

                Payload::ImportSection(reader) => {
                    for import in reader {
                        let import = import?;
                        let kind = match import.ty {
                            wasmparser::TypeRef::Func(idx) => ImportKind::Function(idx),
                            wasmparser::TypeRef::Table(t) => ImportKind::Table(TableType {
                                element_type: convert_ref_type(t.element_type),
                                initial: t.initial,
                                maximum: t.maximum,
                            }),
                            wasmparser::TypeRef::Memory(m) => ImportKind::Memory(MemoryType {
                                memory64: m.memory64,
                                shared: m.shared,
                                initial: m.initial,
                                maximum: m.maximum,
                            }),
                            wasmparser::TypeRef::Global(g) => ImportKind::Global(GlobalType {
                                content_type: convert_val_type(g.content_type),
                                mutable: g.mutable,
                                init_expr_bytes: vec![],
                            }),
                            wasmparser::TypeRef::Tag(_) => {
                                return Err(Error::UnsupportedFeature(
                                    "exception handling tags".to_string(),
                                ));
                            }
                        };
                        module.imports.push(ModuleImport {
                            module: import.module.to_string(),
                            name: import.name.to_string(),
                            kind,
                        });
                    }
                }

                Payload::FunctionSection(reader) => {
                    for func in reader {
                        module.functions.push(func?);
                    }
                }

                Payload::TableSection(reader) => {
                    for table in reader {
                        let table = table?;
                        module.tables.push(TableType {
                            element_type: convert_ref_type(table.ty.element_type),
                            initial: table.ty.initial,
                            maximum: table.ty.maximum,
                        });
                    }
                }

                Payload::MemorySection(reader) => {
                    for mem in reader {
                        let mem = mem?;
                        module.memories.push(MemoryType {
                            memory64: mem.memory64,
                            shared: mem.shared,
                            initial: mem.initial,
                            maximum: mem.maximum,
                        });
                    }
                }

                Payload::GlobalSection(reader) => {
                    for global in reader {
                        let global = global?;
                        let mut bin = global.init_expr.get_binary_reader();
                        let len = bin.bytes_remaining();
                        let raw = bin.read_bytes(len)?;
                        // Strip trailing End opcode (0x0B)
                        let init_bytes = if raw.last() == Some(&0x0B) {
                            raw[..raw.len() - 1].to_vec()
                        } else {
                            raw.to_vec()
                        };
                        module.globals.push(GlobalType {
                            content_type: convert_val_type(global.ty.content_type),
                            mutable: global.ty.mutable,
                            init_expr_bytes: init_bytes,
                        });
                    }
                }

                Payload::ExportSection(reader) => {
                    for export in reader {
                        let export = export?;
                        let kind = match export.kind {
                            wasmparser::ExternalKind::Func => ExportKind::Function,
                            wasmparser::ExternalKind::Table => ExportKind::Table,
                            wasmparser::ExternalKind::Memory => ExportKind::Memory,
                            wasmparser::ExternalKind::Global => ExportKind::Global,
                            wasmparser::ExternalKind::Tag => {
                                return Err(Error::UnsupportedFeature(
                                    "exception handling tags".to_string(),
                                ));
                            }
                        };
                        module.exports.push(ModuleExport {
                            name: export.name.to_string(),
                            kind,
                            index: export.index,
                        });
                    }
                }

                Payload::StartSection { func, .. } => {
                    module.start = Some(func);
                }

                Payload::DataCountSection { count, .. } => {
                    module.data_count = Some(count);
                }

                Payload::ElementSection(reader) => {
                    module.element_count = reader.count();
                    module.element_section_range = Some((reader.range().start, reader.range().end));
                }

                Payload::CodeSectionStart { range, .. } => {
                    module.code_section_range = Some((range.start, range.end));
                }

                Payload::DataSection(reader) => {
                    module.data_section_range = Some((reader.range().start, reader.range().end));
                }

                Payload::CustomSection(reader) => {
                    module
                        .custom_sections
                        .push((reader.name().to_string(), reader.data().to_vec()));
                }

                _ => {}
            }
        }

        Ok(module)
    }
}

impl Default for ComponentParser {
    fn default() -> Self {
        Self::new()
    }
}

impl ParsedComponent {
    /// Create an empty `ParsedComponent` with no modules, no imports, etc.
    /// Used as a placeholder when pushing onto the sub-component stack.
    pub fn empty() -> Self {
        Self {
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

    /// Build a map from core function index → canonical options for Lift entries.
    /// Use this to look up the callee-side encoding, realloc, and post-return
    /// for an exported core function.
    pub fn lift_options_by_core_func(&self) -> std::collections::HashMap<u32, &CanonicalOptions> {
        let mut map = std::collections::HashMap::new();
        for entry in &self.canonical_functions {
            if let CanonicalEntry::Lift {
                core_func_index,
                options,
                ..
            } = entry
            {
                map.insert(*core_func_index, options);
            }
        }
        map
    }

    /// Build a map from component function index → canonical options for Lower entries.
    /// Use this to look up the caller-side encoding and realloc for a lowered import.
    pub fn lower_options_by_func(&self) -> std::collections::HashMap<u32, &CanonicalOptions> {
        let mut map = std::collections::HashMap::new();
        for entry in &self.canonical_functions {
            if let CanonicalEntry::Lower {
                func_index,
                options,
            } = entry
            {
                map.insert(*func_index, options);
            }
        }
        map
    }

    /// Look up the type definition at a given component type index.
    ///
    /// Follows `ExportAlias` chains to resolve type aliases created by
    /// component exports with `(type (eq N))` annotations. Returns `None`
    /// for import-defined or instance-export-alias types that cannot be
    /// resolved locally.
    pub fn get_type_definition(&self, type_idx: u32) -> Option<&ComponentType> {
        let mut idx = type_idx;
        // Follow ExportAlias chains (bounded to prevent infinite loops)
        for _ in 0..self.component_type_defs.len() {
            let def = self.component_type_defs.get(idx as usize)?;
            match def {
                ComponentTypeDef::Defined => {
                    // The Nth Defined entry in component_type_defs corresponds to types[N]
                    let def_offset = self.component_type_defs[..idx as usize]
                        .iter()
                        .filter(|d| matches!(d, ComponentTypeDef::Defined))
                        .count();
                    return self.types.get(def_offset);
                }
                ComponentTypeDef::ExportAlias(target) => {
                    idx = *target;
                }
                _ => return None,
            }
        }
        None
    }

    /// Build a map from core function index → (component type index, canonical options)
    /// for Lift entries. The type index refers to the component function type that
    /// describes the high-level params/results (needed for computing return area size).
    pub fn lift_info_by_core_func(
        &self,
    ) -> std::collections::HashMap<u32, (u32, &CanonicalOptions)> {
        let mut map = std::collections::HashMap::new();
        for entry in &self.canonical_functions {
            if let CanonicalEntry::Lift {
                core_func_index,
                type_index,
                options,
            } = entry
            {
                map.insert(*core_func_index, (*type_index, options));
            }
        }
        map
    }

    /// Compute the flat byte size of a component value type's canonical ABI representation.
    ///
    /// In the canonical ABI, complex types are "flattened" to sequences of core wasm values.
    /// This returns the total byte size of that flat representation, used for sizing
    /// return area buffers in the retptr calling convention.
    pub fn flat_byte_size(&self, ty: &ComponentValType) -> u32 {
        match ty {
            ComponentValType::Primitive(p) => match p {
                PrimitiveValType::S64 | PrimitiveValType::U64 | PrimitiveValType::F64 => 8,
                _ => 4,
            },
            ComponentValType::String => 8,  // (ptr: i32, len: i32)
            ComponentValType::List(_) => 8, // (ptr: i32, len: i32)
            ComponentValType::Record(fields) => {
                fields.iter().map(|(_, ty)| self.flat_byte_size(ty)).sum()
            }
            ComponentValType::Tuple(elems) => elems.iter().map(|ty| self.flat_byte_size(ty)).sum(),
            ComponentValType::Option(inner) => 4 + self.flat_byte_size(inner),
            ComponentValType::Result { ok, err } => {
                let ok_size = ok.as_ref().map(|t| self.flat_byte_size(t)).unwrap_or(0);
                let err_size = err.as_ref().map(|t| self.flat_byte_size(t)).unwrap_or(0);
                4 + ok_size.max(err_size)
            }
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx) {
                    if let ComponentTypeKind::Defined(inner) = &ct.kind {
                        self.flat_byte_size(inner)
                    } else {
                        4
                    }
                } else {
                    4
                }
            }
            ComponentValType::Variant(cases) => {
                // discriminant + max case payload
                let max_payload = cases
                    .iter()
                    .filter_map(|(_, ty)| ty.as_ref().map(|t| self.flat_byte_size(t)))
                    .max()
                    .unwrap_or(0);
                4 + max_payload
            }
            ComponentValType::Own(_) | ComponentValType::Borrow(_) => 4,
        }
    }

    /// Compute the byte size of the return area for a component function's results.
    ///
    /// The return area uses the canonical ABI memory layout (with alignment),
    /// not the flat (stack) representation. Results are stored as a tuple.
    pub fn return_area_byte_size(&self, results: &[(Option<String>, ComponentValType)]) -> u32 {
        let mut size = 0u32;
        for (_, ty) in results {
            let align = self.canonical_abi_align(ty);
            size = align_up(size, align);
            size += self.canonical_abi_size_unpadded(ty);
        }
        // Align final size to the max alignment of the tuple
        let max_align = results
            .iter()
            .map(|(_, ty)| self.canonical_abi_align(ty))
            .max()
            .unwrap_or(1);
        align_up(size, max_align)
    }

    /// Compute the layout of all slots in the return area.
    ///
    /// Each slot describes a contiguous value in the canonical ABI memory layout
    /// with its byte offset, byte size, and whether it is a pointer pair.
    /// The adapter uses this to emit correctly-sized load/store instructions
    /// (e.g., `i64.load`/`i64.store` for 8-byte f64/i64 values).
    pub fn return_area_slots(
        &self,
        results: &[(Option<String>, ComponentValType)],
    ) -> Vec<crate::resolver::ReturnAreaSlot> {
        let mut slots = Vec::new();
        let mut byte_offset = 0u32;
        for (_, ty) in results {
            let align = self.canonical_abi_align(ty);
            byte_offset = align_up(byte_offset, align);
            self.collect_return_area_type_slots(ty, byte_offset, &mut slots);
            byte_offset += self.canonical_abi_size_unpadded(ty);
        }
        slots
    }

    /// Recursively collect return area slots for a single type at a given base offset.
    fn collect_return_area_type_slots(
        &self,
        ty: &ComponentValType,
        base: u32,
        out: &mut Vec<crate::resolver::ReturnAreaSlot>,
    ) {
        use crate::resolver::ReturnAreaSlot;
        match ty {
            ComponentValType::Primitive(p) => {
                let size = match p {
                    PrimitiveValType::Bool | PrimitiveValType::S8 | PrimitiveValType::U8 => 1,
                    PrimitiveValType::S16 | PrimitiveValType::U16 => 2,
                    PrimitiveValType::S32
                    | PrimitiveValType::U32
                    | PrimitiveValType::F32
                    | PrimitiveValType::Char => 4,
                    PrimitiveValType::S64 | PrimitiveValType::U64 | PrimitiveValType::F64 => 8,
                };
                out.push(ReturnAreaSlot {
                    byte_offset: base,
                    byte_size: size,
                    is_pointer_pair: false,
                });
            }
            ComponentValType::String | ComponentValType::List(_) => {
                // Pointer pair: (ptr: i32, len: i32) = 8 bytes
                out.push(ReturnAreaSlot {
                    byte_offset: base,
                    byte_size: 8,
                    is_pointer_pair: true,
                });
            }
            ComponentValType::Record(fields) => {
                let mut offset = base;
                for (_, field_ty) in fields {
                    let align = self.canonical_abi_align(field_ty);
                    offset = align_up(offset, align);
                    self.collect_return_area_type_slots(field_ty, offset, out);
                    offset += self.canonical_abi_size_unpadded(field_ty);
                }
            }
            ComponentValType::Tuple(elems) => {
                let mut offset = base;
                for elem_ty in elems {
                    let align = self.canonical_abi_align(elem_ty);
                    offset = align_up(offset, align);
                    self.collect_return_area_type_slots(elem_ty, offset, out);
                    offset += self.canonical_abi_size_unpadded(elem_ty);
                }
            }
            ComponentValType::Variant(cases) => {
                // Discriminant
                let ds = disc_size(cases.len());
                out.push(ReturnAreaSlot {
                    byte_offset: base,
                    byte_size: ds,
                    is_pointer_pair: false,
                });
                // Payload: union of all case payloads at aligned offset.
                // We emit the max-size payload as a single opaque slot.
                let max_case_align = cases
                    .iter()
                    .filter_map(|(_, t)| t.as_ref().map(|t| self.canonical_abi_align(t)))
                    .max()
                    .unwrap_or(1);
                let payload_offset = align_up(ds, max_case_align);
                let max_payload = cases
                    .iter()
                    .filter_map(|(_, t)| t.as_ref().map(|t| self.canonical_abi_element_size(t)))
                    .max()
                    .unwrap_or(0);
                if max_payload > 0 {
                    // Emit payload as 4-byte or 8-byte aligned chunks.
                    // Since variant payloads are a union, we can't know the exact
                    // type at this point. Copy as the widest natural chunks.
                    let chunk_size = if max_case_align >= 8 { 8 } else { 4 };
                    let mut off = 0u32;
                    while off < max_payload {
                        let remaining = max_payload - off;
                        let sz = if remaining >= chunk_size {
                            chunk_size
                        } else if remaining >= 4 {
                            4
                        } else if remaining >= 2 {
                            2
                        } else {
                            1
                        };
                        out.push(ReturnAreaSlot {
                            byte_offset: base + payload_offset + off,
                            byte_size: sz,
                            is_pointer_pair: false,
                        });
                        off += sz;
                    }
                }
            }
            ComponentValType::Option(inner) => {
                // Discriminant (1 byte for 2 cases)
                let ds = disc_size(2);
                out.push(ReturnAreaSlot {
                    byte_offset: base,
                    byte_size: ds,
                    is_pointer_pair: false,
                });
                // Payload at aligned offset
                let payload_align = self.canonical_abi_align(inner);
                let payload_offset = align_up(ds, payload_align);
                let payload_size = self.canonical_abi_element_size(inner);
                if payload_size > 0 {
                    let chunk_size = if payload_align >= 8 { 8 } else { 4 };
                    let mut off = 0u32;
                    while off < payload_size {
                        let remaining = payload_size - off;
                        let sz = if remaining >= chunk_size {
                            chunk_size
                        } else if remaining >= 4 {
                            4
                        } else if remaining >= 2 {
                            2
                        } else {
                            1
                        };
                        out.push(ReturnAreaSlot {
                            byte_offset: base + payload_offset + off,
                            byte_size: sz,
                            is_pointer_pair: false,
                        });
                        off += sz;
                    }
                }
            }
            ComponentValType::Result { ok, err } => {
                // Discriminant (1 byte for 2 cases)
                let ds = disc_size(2);
                out.push(ReturnAreaSlot {
                    byte_offset: base,
                    byte_size: ds,
                    is_pointer_pair: false,
                });
                // Payload: union of ok/err at aligned offset
                let ok_align = ok
                    .as_ref()
                    .map(|t| self.canonical_abi_align(t))
                    .unwrap_or(1);
                let err_align = err
                    .as_ref()
                    .map(|t| self.canonical_abi_align(t))
                    .unwrap_or(1);
                let max_case_align = ok_align.max(err_align);
                let payload_offset = align_up(ds, max_case_align);
                let ok_s = ok
                    .as_ref()
                    .map(|t| self.canonical_abi_element_size(t))
                    .unwrap_or(0);
                let err_s = err
                    .as_ref()
                    .map(|t| self.canonical_abi_element_size(t))
                    .unwrap_or(0);
                let max_payload = ok_s.max(err_s);
                if max_payload > 0 {
                    let chunk_size = if max_case_align >= 8 { 8 } else { 4 };
                    let mut off = 0u32;
                    while off < max_payload {
                        let remaining = max_payload - off;
                        let sz = if remaining >= chunk_size {
                            chunk_size
                        } else if remaining >= 4 {
                            4
                        } else if remaining >= 2 {
                            2
                        } else {
                            1
                        };
                        out.push(ReturnAreaSlot {
                            byte_offset: base + payload_offset + off,
                            byte_size: sz,
                            is_pointer_pair: false,
                        });
                        off += sz;
                    }
                }
            }
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx)
                    && let ComponentTypeKind::Defined(inner) = &ct.kind
                {
                    self.collect_return_area_type_slots(inner, base, out);
                } else {
                    // Fallback: treat as i32
                    out.push(ReturnAreaSlot {
                        byte_offset: base,
                        byte_size: 4,
                        is_pointer_pair: false,
                    });
                }
            }
            ComponentValType::Own(_) | ComponentValType::Borrow(_) => {
                out.push(ReturnAreaSlot {
                    byte_offset: base,
                    byte_size: 4,
                    is_pointer_pair: false,
                });
            }
        }
    }

    /// Compute flat core param indices where (ptr, len) pairs start.
    ///
    /// In the canonical ABI, `string` and `list<T>` params flatten to
    /// two consecutive i32 values (pointer, length). This method walks the
    /// component function type's params and returns the 0-based flat index
    /// where each such pair begins.
    pub fn pointer_pair_param_positions(&self, params: &[(String, ComponentValType)]) -> Vec<u32> {
        let mut positions = Vec::new();
        let mut flat_idx = 0u32;
        for (_, ty) in params {
            self.collect_pointer_positions(ty, flat_idx, &mut positions);
            flat_idx += self.flat_count(ty);
        }
        positions
    }

    /// Compute return-area byte offsets where (ptr, len) pairs start.
    ///
    /// Uses canonical ABI memory layout offsets (with alignment), matching
    /// how the callee stores results in the return area.
    pub fn pointer_pair_result_offsets(
        &self,
        results: &[(Option<String>, ComponentValType)],
    ) -> Vec<u32> {
        let mut offsets = Vec::new();
        let mut byte_offset = 0u32;
        for (_, ty) in results {
            let align = self.canonical_abi_align(ty);
            byte_offset = align_up(byte_offset, align);
            self.collect_pointer_byte_offsets(ty, byte_offset, &mut offsets);
            byte_offset += self.canonical_abi_size_unpadded(ty);
        }
        offsets
    }

    /// Collect flat param indices where pointer pairs start within a type.
    fn collect_pointer_positions(&self, ty: &ComponentValType, base: u32, out: &mut Vec<u32>) {
        match ty {
            ComponentValType::String | ComponentValType::List(_) => {
                out.push(base);
            }
            ComponentValType::Record(fields) => {
                let mut offset = base;
                for (_, field_ty) in fields {
                    self.collect_pointer_positions(field_ty, offset, out);
                    offset += self.flat_count(field_ty);
                }
            }
            ComponentValType::Tuple(elems) => {
                let mut offset = base;
                for elem_ty in elems {
                    self.collect_pointer_positions(elem_ty, offset, out);
                    offset += self.flat_count(elem_ty);
                }
            }
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx)
                    && let ComponentTypeKind::Defined(inner) = &ct.kind
                {
                    self.collect_pointer_positions(inner, base, out);
                }
            }
            // Scalars, options, results, resources — no pointer pairs at param level
            _ => {}
        }
    }

    /// Collect byte offsets in the return area where pointer pairs start.
    /// Uses canonical ABI memory layout offsets (with alignment).
    fn collect_pointer_byte_offsets(&self, ty: &ComponentValType, base: u32, out: &mut Vec<u32>) {
        match ty {
            ComponentValType::String | ComponentValType::List(_) => {
                out.push(base);
            }
            ComponentValType::Record(fields) => {
                let mut offset = base;
                for (_, field_ty) in fields {
                    let align = self.canonical_abi_align(field_ty);
                    offset = align_up(offset, align);
                    self.collect_pointer_byte_offsets(field_ty, offset, out);
                    offset += self.canonical_abi_size_unpadded(field_ty);
                }
            }
            ComponentValType::Tuple(elems) => {
                let mut offset = base;
                for elem_ty in elems {
                    let align = self.canonical_abi_align(elem_ty);
                    offset = align_up(offset, align);
                    self.collect_pointer_byte_offsets(elem_ty, offset, out);
                    offset += self.canonical_abi_size_unpadded(elem_ty);
                }
            }
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx)
                    && let ComponentTypeKind::Defined(inner) = &ct.kind
                {
                    self.collect_pointer_byte_offsets(inner, base, out);
                }
            }
            _ => {}
        }
    }

    /// Collect conditional pointer pairs from params that contain option/result/variant
    /// types with pointer payloads.
    pub fn conditional_pointer_pair_positions(
        &self,
        params: &[(String, ComponentValType)],
    ) -> Vec<crate::resolver::ConditionalPointerPair> {
        let mut out = Vec::new();
        let mut flat_idx = 0u32;
        for (_, ty) in params {
            self.collect_conditional_pointers(ty, flat_idx, &mut out);
            flat_idx += self.flat_count(ty);
        }
        out
    }

    /// Collect conditional pointer pairs from results using flat indices (non-retptr path).
    pub fn conditional_pointer_pair_result_flat_positions(
        &self,
        results: &[(Option<String>, ComponentValType)],
    ) -> Vec<crate::resolver::ConditionalPointerPair> {
        let mut out = Vec::new();
        let mut flat_idx = 0u32;
        for (_, ty) in results {
            self.collect_conditional_pointers(ty, flat_idx, &mut out);
            flat_idx += self.flat_count(ty);
        }
        out
    }

    /// Collect conditional pointer pairs from results (byte-offset based, for retptr path).
    /// Uses canonical ABI memory layout offsets.
    pub fn conditional_pointer_pair_result_positions(
        &self,
        results: &[(Option<String>, ComponentValType)],
    ) -> Vec<crate::resolver::ConditionalPointerPair> {
        let mut out = Vec::new();
        let mut byte_offset = 0u32;
        for (_, ty) in results {
            let align = self.canonical_abi_align(ty);
            byte_offset = align_up(byte_offset, align);
            self.collect_conditional_result_pointers(ty, byte_offset, &mut out);
            byte_offset += self.canonical_abi_size_unpadded(ty);
        }
        out
    }

    /// Collect conditional pointer pairs for flat params.
    /// For option<T> where T contains pointers: disc at base, payload at base+1.
    fn collect_conditional_pointers(
        &self,
        ty: &ComponentValType,
        base: u32,
        out: &mut Vec<crate::resolver::ConditionalPointerPair>,
    ) {
        match ty {
            ComponentValType::Option(inner) if self.type_contains_pointers(inner) => {
                // option<T> flattens to [disc, ...T_flat]
                // disc=1 means Some, payload starts at base+1
                // In flat representation, discriminant is always i32 (4 bytes)
                let payload_base = base + 1;
                let mut inner_positions = Vec::new();
                self.collect_pointer_positions(inner, payload_base, &mut inner_positions);
                for ptr_pos in inner_positions {
                    let layout = self.copy_layout_for_string_or_list_at(inner);
                    out.push(crate::resolver::ConditionalPointerPair {
                        discriminant_position: base,
                        discriminant_value: 1,
                        ptr_position: ptr_pos,
                        copy_layout: layout,
                        discriminant_byte_size: 4,
                    });
                }
                self.collect_conditional_pointers(inner, payload_base, out);
            }
            ComponentValType::Result { ok, err } => {
                // result<T,E> flattens to [disc, ...max(T_flat, E_flat)]
                // disc=0 means Ok(T), disc=1 means Err(E)
                let payload_base = base + 1;
                if let Some(ok_ty) = ok
                    && self.type_contains_pointers(ok_ty)
                {
                    let mut inner_positions = Vec::new();
                    self.collect_pointer_positions(ok_ty, payload_base, &mut inner_positions);
                    for ptr_pos in inner_positions {
                        let layout = self.copy_layout_for_string_or_list_at(ok_ty);
                        out.push(crate::resolver::ConditionalPointerPair {
                            discriminant_position: base,
                            discriminant_value: 0,
                            ptr_position: ptr_pos,
                            copy_layout: layout,
                            discriminant_byte_size: 4,
                        });
                    }
                    self.collect_conditional_pointers(ok_ty, payload_base, out);
                }
                if let Some(err_ty) = err
                    && self.type_contains_pointers(err_ty)
                {
                    let mut inner_positions = Vec::new();
                    self.collect_pointer_positions(err_ty, payload_base, &mut inner_positions);
                    for ptr_pos in inner_positions {
                        let layout = self.copy_layout_for_string_or_list_at(err_ty);
                        out.push(crate::resolver::ConditionalPointerPair {
                            discriminant_position: base,
                            discriminant_value: 1,
                            ptr_position: ptr_pos,
                            copy_layout: layout,
                            discriminant_byte_size: 4,
                        });
                    }
                    self.collect_conditional_pointers(err_ty, payload_base, out);
                }
            }
            ComponentValType::Variant(cases) => {
                // variant flattens to [disc, ...max(case_payloads)]
                let payload_base = base + 1;
                for (case_idx, (_, case_ty)) in cases.iter().enumerate() {
                    if let Some(ty) = case_ty
                        && self.type_contains_pointers(ty)
                    {
                        let mut inner_positions = Vec::new();
                        self.collect_pointer_positions(ty, payload_base, &mut inner_positions);
                        for ptr_pos in inner_positions {
                            let layout = self.copy_layout_for_string_or_list_at(ty);
                            out.push(crate::resolver::ConditionalPointerPair {
                                discriminant_position: base,
                                discriminant_value: case_idx as u32,
                                ptr_position: ptr_pos,
                                copy_layout: layout,
                                discriminant_byte_size: 4,
                            });
                        }
                        self.collect_conditional_pointers(ty, payload_base, out);
                    }
                }
            }
            ComponentValType::Record(fields) => {
                let mut offset = base;
                for (_, field_ty) in fields {
                    self.collect_conditional_pointers(field_ty, offset, out);
                    offset += self.flat_count(field_ty);
                }
            }
            ComponentValType::Tuple(elems) => {
                let mut offset = base;
                for elem_ty in elems {
                    self.collect_conditional_pointers(elem_ty, offset, out);
                    offset += self.flat_count(elem_ty);
                }
            }
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx)
                    && let ComponentTypeKind::Defined(inner) = &ct.kind
                {
                    self.collect_conditional_pointers(inner, base, out);
                }
            }
            _ => {}
        }
    }

    /// Collect conditional pointer pairs for result byte offsets.
    fn collect_conditional_result_pointers(
        &self,
        ty: &ComponentValType,
        base: u32,
        out: &mut Vec<crate::resolver::ConditionalPointerPair>,
    ) {
        match ty {
            ComponentValType::Option(inner) if self.type_contains_pointers(inner) => {
                // In memory layout: disc (disc_size bytes), aligned gap, then payload
                let disc_offset = base;
                let ds = disc_size(2);
                let payload_align = self.canonical_abi_align(inner);
                let payload_offset = base + align_up(ds, payload_align);
                let mut inner_offsets = Vec::new();
                self.collect_pointer_byte_offsets(inner, payload_offset, &mut inner_offsets);
                for ptr_off in inner_offsets {
                    let layout = self.copy_layout_for_string_or_list_at(inner);
                    out.push(crate::resolver::ConditionalPointerPair {
                        discriminant_position: disc_offset,
                        discriminant_value: 1,
                        ptr_position: ptr_off,
                        copy_layout: layout,
                        discriminant_byte_size: ds,
                    });
                }
                self.collect_conditional_result_pointers(inner, payload_offset, out);
            }
            ComponentValType::Result { ok, err } => {
                let disc_offset = base;
                let ds = disc_size(2);
                let ok_align = ok
                    .as_ref()
                    .map(|t| self.canonical_abi_align(t))
                    .unwrap_or(1);
                let err_align = err
                    .as_ref()
                    .map(|t| self.canonical_abi_align(t))
                    .unwrap_or(1);
                let max_case_align = ok_align.max(err_align);
                let payload_offset = base + align_up(ds, max_case_align);
                if let Some(ok_ty) = ok
                    && self.type_contains_pointers(ok_ty)
                {
                    let mut inner_offsets = Vec::new();
                    self.collect_pointer_byte_offsets(ok_ty, payload_offset, &mut inner_offsets);
                    for ptr_off in inner_offsets {
                        let layout = self.copy_layout_for_string_or_list_at(ok_ty);
                        out.push(crate::resolver::ConditionalPointerPair {
                            discriminant_position: disc_offset,
                            discriminant_value: 0,
                            ptr_position: ptr_off,
                            copy_layout: layout,
                            discriminant_byte_size: ds,
                        });
                    }
                    self.collect_conditional_result_pointers(ok_ty, payload_offset, out);
                }
                if let Some(err_ty) = err
                    && self.type_contains_pointers(err_ty)
                {
                    let mut inner_offsets = Vec::new();
                    self.collect_pointer_byte_offsets(err_ty, payload_offset, &mut inner_offsets);
                    for ptr_off in inner_offsets {
                        let layout = self.copy_layout_for_string_or_list_at(err_ty);
                        out.push(crate::resolver::ConditionalPointerPair {
                            discriminant_position: disc_offset,
                            discriminant_value: 1,
                            ptr_position: ptr_off,
                            copy_layout: layout,
                            discriminant_byte_size: ds,
                        });
                    }
                    self.collect_conditional_result_pointers(err_ty, payload_offset, out);
                }
            }
            ComponentValType::Variant(cases) => {
                let disc_offset = base;
                let ds = disc_size(cases.len());
                let max_case_align = cases
                    .iter()
                    .filter_map(|(_, t)| t.as_ref().map(|t| self.canonical_abi_align(t)))
                    .max()
                    .unwrap_or(1);
                let payload_offset = base + align_up(ds, max_case_align);
                for (case_idx, (_, case_ty)) in cases.iter().enumerate() {
                    if let Some(ty) = case_ty
                        && self.type_contains_pointers(ty)
                    {
                        let mut inner_offsets = Vec::new();
                        self.collect_pointer_byte_offsets(ty, payload_offset, &mut inner_offsets);
                        for ptr_off in inner_offsets {
                            let layout = self.copy_layout_for_string_or_list_at(ty);
                            out.push(crate::resolver::ConditionalPointerPair {
                                discriminant_position: disc_offset,
                                discriminant_value: case_idx as u32,
                                ptr_position: ptr_off,
                                copy_layout: layout,
                                discriminant_byte_size: ds,
                            });
                        }
                        self.collect_conditional_result_pointers(ty, payload_offset, out);
                    }
                }
            }
            ComponentValType::Record(fields) => {
                let mut offset = base;
                for (_, field_ty) in fields {
                    let align = self.canonical_abi_align(field_ty);
                    offset = align_up(offset, align);
                    self.collect_conditional_result_pointers(field_ty, offset, out);
                    offset += self.canonical_abi_size_unpadded(field_ty);
                }
            }
            ComponentValType::Tuple(elems) => {
                let mut offset = base;
                for elem_ty in elems {
                    let align = self.canonical_abi_align(elem_ty);
                    offset = align_up(offset, align);
                    self.collect_conditional_result_pointers(elem_ty, offset, out);
                    offset += self.canonical_abi_size_unpadded(elem_ty);
                }
            }
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx)
                    && let ComponentTypeKind::Defined(inner) = &ct.kind
                {
                    self.collect_conditional_result_pointers(inner, base, out);
                }
            }
            _ => {}
        }
    }

    /// Check if a type contains any pointer data (strings, lists).
    pub fn type_contains_pointers(&self, ty: &ComponentValType) -> bool {
        match ty {
            ComponentValType::String | ComponentValType::List(_) => true,
            ComponentValType::Option(inner) => self.type_contains_pointers(inner),
            ComponentValType::Result { ok, err } => {
                ok.as_ref().is_some_and(|t| self.type_contains_pointers(t))
                    || err.as_ref().is_some_and(|t| self.type_contains_pointers(t))
            }
            ComponentValType::Record(fields) => {
                fields.iter().any(|(_, t)| self.type_contains_pointers(t))
            }
            ComponentValType::Tuple(elems) => elems.iter().any(|t| self.type_contains_pointers(t)),
            ComponentValType::Variant(cases) => cases
                .iter()
                .any(|(_, t)| t.as_ref().is_some_and(|t| self.type_contains_pointers(t))),
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx)
                    && let ComponentTypeKind::Defined(inner) = &ct.kind
                {
                    self.type_contains_pointers(inner)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Get the copy layout for a type that is either a string or a list.
    fn copy_layout_for_string_or_list_at(
        &self,
        ty: &ComponentValType,
    ) -> crate::resolver::CopyLayout {
        self.copy_layout(ty)
    }

    /// Count the number of flat core wasm values a component type flattens to.
    pub fn flat_count(&self, ty: &ComponentValType) -> u32 {
        match ty {
            ComponentValType::Primitive(_) => 1, // always 1 core value (i32/i64/f32/f64)
            ComponentValType::String | ComponentValType::List(_) => 2, // (ptr, len)
            ComponentValType::Record(fields) => {
                fields.iter().map(|(_, t)| self.flat_count(t)).sum()
            }
            ComponentValType::Tuple(elems) => elems.iter().map(|t| self.flat_count(t)).sum(),
            ComponentValType::Option(inner) => 1 + self.flat_count(inner),
            ComponentValType::Result { ok, err } => {
                let ok_c = ok.as_ref().map(|t| self.flat_count(t)).unwrap_or(0);
                let err_c = err.as_ref().map(|t| self.flat_count(t)).unwrap_or(0);
                1 + ok_c.max(err_c)
            }
            ComponentValType::Variant(cases) => {
                let max_c = cases
                    .iter()
                    .filter_map(|(_, t)| t.as_ref().map(|t| self.flat_count(t)))
                    .max()
                    .unwrap_or(0);
                1 + max_c
            }
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx) {
                    if let ComponentTypeKind::Defined(inner) = &ct.kind {
                        self.flat_count(inner)
                    } else {
                        1
                    }
                } else {
                    1
                }
            }
            ComponentValType::Own(_) | ComponentValType::Borrow(_) => 1,
        }
    }

    /// Canonical ABI alignment of a value type in linear memory.
    pub fn canonical_abi_align(&self, ty: &ComponentValType) -> u32 {
        match ty {
            ComponentValType::Primitive(p) => match p {
                PrimitiveValType::Bool | PrimitiveValType::S8 | PrimitiveValType::U8 => 1,
                PrimitiveValType::S16 | PrimitiveValType::U16 => 2,
                PrimitiveValType::S32
                | PrimitiveValType::U32
                | PrimitiveValType::F32
                | PrimitiveValType::Char => 4,
                PrimitiveValType::S64 | PrimitiveValType::U64 | PrimitiveValType::F64 => 8,
            },
            ComponentValType::String | ComponentValType::List(_) => 4, // ptr alignment
            ComponentValType::Record(fields) => fields
                .iter()
                .map(|(_, t)| self.canonical_abi_align(t))
                .max()
                .unwrap_or(1),
            ComponentValType::Tuple(elems) => elems
                .iter()
                .map(|t| self.canonical_abi_align(t))
                .max()
                .unwrap_or(1),
            ComponentValType::Variant(cases) => {
                let ds = disc_size(cases.len());
                let max_case_align = cases
                    .iter()
                    .filter_map(|(_, t)| t.as_ref().map(|t| self.canonical_abi_align(t)))
                    .max()
                    .unwrap_or(1);
                ds.max(max_case_align)
            }
            ComponentValType::Option(inner) => {
                // option has 2 cases → disc_size = 1
                disc_size(2).max(self.canonical_abi_align(inner))
            }
            ComponentValType::Result { ok, err } => {
                // result has 2 cases → disc_size = 1
                let oa = ok
                    .as_ref()
                    .map(|t| self.canonical_abi_align(t))
                    .unwrap_or(1);
                let ea = err
                    .as_ref()
                    .map(|t| self.canonical_abi_align(t))
                    .unwrap_or(1);
                disc_size(2).max(oa).max(ea)
            }
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx)
                    && let ComponentTypeKind::Defined(inner) = &ct.kind
                {
                    return self.canonical_abi_align(inner);
                }
                4
            }
            ComponentValType::Own(_) | ComponentValType::Borrow(_) => 4,
        }
    }

    /// Canonical ABI byte size of a value type in linear memory (NOT flat size).
    ///
    /// This is the size of one element when stored in a list's backing buffer.
    /// Includes alignment padding between fields but NOT trailing padding
    /// (that's handled by `canonical_abi_element_size`).
    fn canonical_abi_size_unpadded(&self, ty: &ComponentValType) -> u32 {
        match ty {
            ComponentValType::Primitive(p) => match p {
                PrimitiveValType::Bool | PrimitiveValType::S8 | PrimitiveValType::U8 => 1,
                PrimitiveValType::S16 | PrimitiveValType::U16 => 2,
                PrimitiveValType::S32
                | PrimitiveValType::U32
                | PrimitiveValType::F32
                | PrimitiveValType::Char => 4,
                PrimitiveValType::S64 | PrimitiveValType::U64 | PrimitiveValType::F64 => 8,
            },
            ComponentValType::String | ComponentValType::List(_) => 8, // (ptr: i32, len: i32)
            ComponentValType::Record(fields) => {
                let mut size = 0u32;
                for (_, field_ty) in fields {
                    let align = self.canonical_abi_align(field_ty);
                    size = align_up(size, align);
                    size += self.canonical_abi_size_unpadded(field_ty);
                }
                size
            }
            ComponentValType::Tuple(elems) => {
                let mut size = 0u32;
                for elem_ty in elems {
                    let align = self.canonical_abi_align(elem_ty);
                    size = align_up(size, align);
                    size += self.canonical_abi_size_unpadded(elem_ty);
                }
                size
            }
            ComponentValType::Variant(cases) => {
                let ds = disc_size(cases.len());
                let max_case_align = cases
                    .iter()
                    .filter_map(|(_, t)| t.as_ref().map(|t| self.canonical_abi_align(t)))
                    .max()
                    .unwrap_or(1);
                let max_payload = cases
                    .iter()
                    .filter_map(|(_, t)| t.as_ref().map(|t| self.canonical_abi_element_size(t)))
                    .max()
                    .unwrap_or(0);
                align_up(ds, max_case_align) + max_payload
            }
            ComponentValType::Option(inner) => {
                let ds = disc_size(2);
                let payload_align = self.canonical_abi_align(inner);
                align_up(ds, payload_align) + self.canonical_abi_element_size(inner)
            }
            ComponentValType::Result { ok, err } => {
                let ds = disc_size(2);
                let ok_align = ok
                    .as_ref()
                    .map(|t| self.canonical_abi_align(t))
                    .unwrap_or(1);
                let err_align = err
                    .as_ref()
                    .map(|t| self.canonical_abi_align(t))
                    .unwrap_or(1);
                let max_case_align = ok_align.max(err_align);
                let ok_s = ok
                    .as_ref()
                    .map(|t| self.canonical_abi_element_size(t))
                    .unwrap_or(0);
                let err_s = err
                    .as_ref()
                    .map(|t| self.canonical_abi_element_size(t))
                    .unwrap_or(0);
                align_up(ds, max_case_align) + ok_s.max(err_s)
            }
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx)
                    && let ComponentTypeKind::Defined(inner) = &ct.kind
                {
                    return self.canonical_abi_size_unpadded(inner);
                }
                4
            }
            ComponentValType::Own(_) | ComponentValType::Borrow(_) => 4,
        }
    }

    /// Canonical ABI element size — the stride when stored in a list.
    /// This is `align_up(size, align)`.
    pub fn canonical_abi_element_size(&self, ty: &ComponentValType) -> u32 {
        let size = self.canonical_abi_size_unpadded(ty);
        let align = self.canonical_abi_align(ty);
        align_up(size, align)
    }

    /// Build a `CopyLayout` describing how to copy a (ptr, len) value
    /// of the given type across memories.
    pub fn copy_layout(&self, ty: &ComponentValType) -> crate::resolver::CopyLayout {
        use crate::resolver::CopyLayout;
        match ty {
            ComponentValType::String => CopyLayout::Bulk { byte_multiplier: 1 },
            ComponentValType::List(inner) => {
                let element_size = self.canonical_abi_element_size(inner);
                let inner_ptrs = self.element_inner_pointers(inner, 0);
                if inner_ptrs.is_empty() {
                    CopyLayout::Bulk {
                        byte_multiplier: element_size,
                    }
                } else {
                    CopyLayout::Elements {
                        element_size,
                        inner_pointers: inner_ptrs,
                    }
                }
            }
            // For non-list/string types, treat as bulk with 1x multiplier
            _ => CopyLayout::Bulk { byte_multiplier: 1 },
        }
    }

    /// Find inner (ptr, len) pairs within an element type at the given base offset.
    /// Returns Vec<(byte_offset, CopyLayout)> for each pointer pair found.
    fn element_inner_pointers(
        &self,
        ty: &ComponentValType,
        base: u32,
    ) -> Vec<(u32, crate::resolver::CopyLayout)> {
        let mut result = Vec::new();
        match ty {
            ComponentValType::String => {
                result.push((
                    base,
                    crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 },
                ));
            }
            ComponentValType::List(inner) => {
                result.push((base, self.copy_layout(ty)));
                // The list itself is a pointer pair — don't recurse further here
                let _ = inner;
            }
            ComponentValType::Record(fields) => {
                let mut offset = base;
                for (_, field_ty) in fields {
                    let align = self.canonical_abi_align(field_ty);
                    offset = align_up(offset, align);
                    result.extend(self.element_inner_pointers(field_ty, offset));
                    offset += self.canonical_abi_size_unpadded(field_ty);
                }
            }
            ComponentValType::Tuple(elems) => {
                let mut offset = base;
                for elem_ty in elems {
                    let align = self.canonical_abi_align(elem_ty);
                    offset = align_up(offset, align);
                    result.extend(self.element_inner_pointers(elem_ty, offset));
                    offset += self.canonical_abi_size_unpadded(elem_ty);
                }
            }
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx)
                    && let ComponentTypeKind::Defined(inner) = &ct.kind
                {
                    return self.element_inner_pointers(inner, base);
                }
            }
            _ => {} // scalars, options, results — no pointer pairs
        }
        result
    }
}

fn align_up(size: u32, align: u32) -> u32 {
    (size + align - 1) & !(align - 1)
}

/// Canonical ABI discriminant byte size for a variant-like type with `num_cases` cases.
///
/// Per the Component Model spec:
/// - ≤ 2^8 cases → 1 byte (u8)
/// - ≤ 2^16 cases → 2 bytes (u16)
/// - otherwise → 4 bytes (u32)
fn disc_size(num_cases: usize) -> u32 {
    if num_cases <= 0x100 {
        1
    } else if num_cases <= 0x1_0000 {
        2
    } else {
        4
    }
}

/// Convert wasmparser's `ComponentValType` to our owned representation.
fn convert_wp_component_val_type(ty: &wasmparser::ComponentValType) -> ComponentValType {
    match ty {
        wasmparser::ComponentValType::Primitive(p) => match p {
            wasmparser::PrimitiveValType::String => ComponentValType::String,
            wasmparser::PrimitiveValType::Bool => {
                ComponentValType::Primitive(PrimitiveValType::Bool)
            }
            wasmparser::PrimitiveValType::S8 => ComponentValType::Primitive(PrimitiveValType::S8),
            wasmparser::PrimitiveValType::U8 => ComponentValType::Primitive(PrimitiveValType::U8),
            wasmparser::PrimitiveValType::S16 => ComponentValType::Primitive(PrimitiveValType::S16),
            wasmparser::PrimitiveValType::U16 => ComponentValType::Primitive(PrimitiveValType::U16),
            wasmparser::PrimitiveValType::S32 => ComponentValType::Primitive(PrimitiveValType::S32),
            wasmparser::PrimitiveValType::U32 => ComponentValType::Primitive(PrimitiveValType::U32),
            wasmparser::PrimitiveValType::S64 => ComponentValType::Primitive(PrimitiveValType::S64),
            wasmparser::PrimitiveValType::U64 => ComponentValType::Primitive(PrimitiveValType::U64),
            wasmparser::PrimitiveValType::F32 => ComponentValType::Primitive(PrimitiveValType::F32),
            wasmparser::PrimitiveValType::F64 => ComponentValType::Primitive(PrimitiveValType::F64),
            wasmparser::PrimitiveValType::Char => {
                ComponentValType::Primitive(PrimitiveValType::Char)
            }
        },
        wasmparser::ComponentValType::Type(idx) => ComponentValType::Type(*idx),
    }
}

/// Convert wasmparser's `ComponentDefinedType` to our `ComponentTypeKind`.
fn convert_wp_defined_type(dt: &wasmparser::ComponentDefinedType) -> ComponentTypeKind {
    match dt {
        wasmparser::ComponentDefinedType::Result { ok, err } => {
            ComponentTypeKind::Defined(ComponentValType::Result {
                ok: ok
                    .as_ref()
                    .map(|t| Box::new(convert_wp_component_val_type(t))),
                err: err
                    .as_ref()
                    .map(|t| Box::new(convert_wp_component_val_type(t))),
            })
        }
        wasmparser::ComponentDefinedType::List(ty) => ComponentTypeKind::Defined(
            ComponentValType::List(Box::new(convert_wp_component_val_type(ty))),
        ),
        wasmparser::ComponentDefinedType::Option(ty) => ComponentTypeKind::Defined(
            ComponentValType::Option(Box::new(convert_wp_component_val_type(ty))),
        ),
        wasmparser::ComponentDefinedType::Tuple(types) => ComponentTypeKind::Defined(
            ComponentValType::Tuple(types.iter().map(convert_wp_component_val_type).collect()),
        ),
        wasmparser::ComponentDefinedType::Record(fields) => {
            ComponentTypeKind::Defined(ComponentValType::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (name.to_string(), convert_wp_component_val_type(ty)))
                    .collect(),
            ))
        }
        wasmparser::ComponentDefinedType::Variant(cases) => {
            ComponentTypeKind::Defined(ComponentValType::Variant(
                cases
                    .iter()
                    .map(|c| {
                        (
                            c.name.to_string(),
                            c.ty.as_ref().map(convert_wp_component_val_type),
                        )
                    })
                    .collect(),
            ))
        }
        wasmparser::ComponentDefinedType::Own(id) => {
            ComponentTypeKind::Defined(ComponentValType::Own(*id))
        }
        wasmparser::ComponentDefinedType::Borrow(id) => {
            ComponentTypeKind::Defined(ComponentValType::Borrow(*id))
        }
        wasmparser::ComponentDefinedType::Primitive(p) => {
            // A defined type that aliases a primitive (e.g., `type list-typedef = string`)
            ComponentTypeKind::Defined(convert_wp_component_val_type(
                &wasmparser::ComponentValType::Primitive(*p),
            ))
        }
        wasmparser::ComponentDefinedType::Enum(cases) => {
            // An enum is a variant where all cases have no payload
            ComponentTypeKind::Defined(ComponentValType::Variant(
                cases.iter().map(|name| (name.to_string(), None)).collect(),
            ))
        }
        wasmparser::ComponentDefinedType::Flags(names) => {
            // Flags are represented as a record of bools in the canonical ABI.
            // For flat counting and pointer analysis, we use a record representation.
            ComponentTypeKind::Defined(ComponentValType::Record(
                names
                    .iter()
                    .map(|name| {
                        (
                            name.to_string(),
                            ComponentValType::Primitive(PrimitiveValType::Bool),
                        )
                    })
                    .collect(),
            ))
        }
    }
}

/// Convert wasmparser CanonicalOption list into our CanonicalOptions
fn convert_canonical_options(options: &[wasmparser::CanonicalOption]) -> CanonicalOptions {
    let mut result = CanonicalOptions::default();
    for opt in options {
        match opt {
            wasmparser::CanonicalOption::UTF8 => {
                result.string_encoding = CanonStringEncoding::Utf8;
            }
            wasmparser::CanonicalOption::UTF16 => {
                result.string_encoding = CanonStringEncoding::Utf16;
            }
            wasmparser::CanonicalOption::CompactUTF16 => {
                result.string_encoding = CanonStringEncoding::CompactUtf16;
            }
            wasmparser::CanonicalOption::Memory(idx) => {
                result.memory = Some(*idx);
            }
            wasmparser::CanonicalOption::Realloc(idx) => {
                result.realloc = Some(*idx);
            }
            wasmparser::CanonicalOption::PostReturn(idx) => {
                result.post_return = Some(*idx);
            }
        }
    }
    result
}

/// Convert a wasmparser CanonicalFunction into our CanonicalEntry
fn convert_canonical_function(canon: wasmparser::CanonicalFunction) -> CanonicalEntry {
    match canon {
        wasmparser::CanonicalFunction::Lift {
            core_func_index,
            type_index,
            options,
        } => CanonicalEntry::Lift {
            core_func_index,
            type_index,
            options: convert_canonical_options(&options),
        },
        wasmparser::CanonicalFunction::Lower {
            func_index,
            options,
        } => CanonicalEntry::Lower {
            func_index,
            options: convert_canonical_options(&options),
        },
        wasmparser::CanonicalFunction::ResourceNew { resource } => {
            CanonicalEntry::ResourceNew { resource }
        }
        wasmparser::CanonicalFunction::ResourceDrop { resource } => {
            CanonicalEntry::ResourceDrop { resource }
        }
        wasmparser::CanonicalFunction::ResourceRep { resource } => {
            CanonicalEntry::ResourceRep { resource }
        }
        wasmparser::CanonicalFunction::ThreadSpawn { func_ty_index } => {
            CanonicalEntry::ThreadSpawn { func_ty_index }
        }
        wasmparser::CanonicalFunction::ThreadHwConcurrency => CanonicalEntry::ThreadHwConcurrency,
    }
}

/// Convert a `wasmparser::ComponentAlias` into our `ComponentAliasEntry`.
fn convert_component_alias(alias: wasmparser::ComponentAlias<'_>) -> Option<ComponentAliasEntry> {
    match alias {
        wasmparser::ComponentAlias::InstanceExport {
            kind,
            instance_index,
            name,
        } => Some(ComponentAliasEntry::InstanceExport {
            kind,
            instance_index,
            name: name.to_string(),
        }),
        wasmparser::ComponentAlias::CoreInstanceExport {
            kind,
            instance_index,
            name,
        } => Some(ComponentAliasEntry::CoreInstanceExport {
            kind,
            instance_index,
            name: name.to_string(),
        }),
        wasmparser::ComponentAlias::Outer { kind, count, index } => {
            let our_kind = match kind {
                wasmparser::ComponentOuterAliasKind::CoreModule => OuterAliasKind::CoreModule,
                wasmparser::ComponentOuterAliasKind::CoreType => OuterAliasKind::CoreType,
                wasmparser::ComponentOuterAliasKind::Type => OuterAliasKind::Type,
                wasmparser::ComponentOuterAliasKind::Component => OuterAliasKind::Component,
            };
            Some(ComponentAliasEntry::Outer {
                kind: our_kind,
                count,
                index,
            })
        }
    }
}

/// Convert a `wasmparser::ComponentInstance` into our `ComponentLevelInstance`.
fn convert_component_instance(
    instance: wasmparser::ComponentInstance<'_>,
) -> ComponentLevelInstance {
    match instance {
        wasmparser::ComponentInstance::Instantiate {
            component_index,
            args,
        } => {
            let parsed_args: Vec<_> = args
                .iter()
                .map(|arg| (arg.name.to_string(), arg.kind, arg.index))
                .collect();
            ComponentLevelInstance::Instantiate {
                component_index,
                args: parsed_args,
            }
        }
        wasmparser::ComponentInstance::FromExports(exports) => {
            let parsed: Vec<_> = exports
                .iter()
                .map(|e| (e.name.0.to_string(), e.kind, e.index))
                .collect();
            ComponentLevelInstance::FromExports(parsed)
        }
    }
}

/// Convert wasmparser ValType to wasm-encoder ValType
fn convert_val_type(ty: WasmValType) -> ValType {
    match ty {
        WasmValType::I32 => ValType::I32,
        WasmValType::I64 => ValType::I64,
        WasmValType::F32 => ValType::F32,
        WasmValType::F64 => ValType::F64,
        WasmValType::V128 => ValType::V128,
        WasmValType::Ref(rt) => convert_ref_type(rt),
    }
}

/// Convert wasmparser RefType to wasm-encoder ValType
fn convert_ref_type(rt: wasmparser::RefType) -> ValType {
    if rt.is_func_ref() {
        ValType::Ref(wasm_encoder::RefType::FUNCREF)
    } else if rt.is_extern_ref() {
        ValType::Ref(wasm_encoder::RefType::EXTERNREF)
    } else {
        // For other reference types, default to funcref
        // This is a simplification - real implementation would handle all ref types
        ValType::Ref(wasm_encoder::RefType::FUNCREF)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parser_rejects_core_module() {
        // Minimal valid core module
        let core_module = wat::parse_str("(module)").unwrap();
        let parser = ComponentParser::new();
        let result = parser.parse(&core_module);
        assert!(matches!(result, Err(Error::NotAComponent)));
    }

    #[test]
    fn test_parser_rejects_invalid_wasm() {
        let parser = ComponentParser::new();

        // Too small
        let result = parser.parse(&[0, 1, 2]);
        assert!(matches!(result, Err(Error::InvalidWasm(_))));

        // Invalid magic
        let result = parser.parse(&[1, 2, 3, 4, 5, 6, 7, 8]);
        assert!(matches!(result, Err(Error::InvalidWasm(_))));
    }

    #[test]
    fn test_convert_canonical_options_default() {
        // Empty options list should produce defaults
        let opts = convert_canonical_options(&[]);
        assert_eq!(opts.string_encoding, CanonStringEncoding::Utf8);
        assert_eq!(opts.memory, None);
        assert_eq!(opts.realloc, None);
        assert_eq!(opts.post_return, None);
    }

    #[test]
    fn test_convert_canonical_options_full() {
        let opts = convert_canonical_options(&[
            wasmparser::CanonicalOption::UTF16,
            wasmparser::CanonicalOption::Memory(3),
            wasmparser::CanonicalOption::Realloc(7),
            wasmparser::CanonicalOption::PostReturn(12),
        ]);
        assert_eq!(opts.string_encoding, CanonStringEncoding::Utf16);
        assert_eq!(opts.memory, Some(3));
        assert_eq!(opts.realloc, Some(7));
        assert_eq!(opts.post_return, Some(12));
    }

    #[test]
    fn test_convert_canonical_function_lift() {
        let canon = wasmparser::CanonicalFunction::Lift {
            core_func_index: 5,
            type_index: 2,
            options: vec![
                wasmparser::CanonicalOption::UTF8,
                wasmparser::CanonicalOption::Memory(0),
                wasmparser::CanonicalOption::Realloc(1),
            ]
            .into_boxed_slice(),
        };
        let entry = convert_canonical_function(canon);
        match entry {
            CanonicalEntry::Lift {
                core_func_index,
                type_index,
                options,
            } => {
                assert_eq!(core_func_index, 5);
                assert_eq!(type_index, 2);
                assert_eq!(options.string_encoding, CanonStringEncoding::Utf8);
                assert_eq!(options.memory, Some(0));
                assert_eq!(options.realloc, Some(1));
                assert_eq!(options.post_return, None);
            }
            _ => panic!("Expected CanonicalEntry::Lift"),
        }
    }

    #[test]
    fn test_convert_canonical_function_lower() {
        let canon = wasmparser::CanonicalFunction::Lower {
            func_index: 3,
            options: vec![wasmparser::CanonicalOption::CompactUTF16].into_boxed_slice(),
        };
        let entry = convert_canonical_function(canon);
        match entry {
            CanonicalEntry::Lower {
                func_index,
                options,
            } => {
                assert_eq!(func_index, 3);
                assert_eq!(options.string_encoding, CanonStringEncoding::CompactUtf16);
            }
            _ => panic!("Expected CanonicalEntry::Lower"),
        }
    }

    #[test]
    fn test_convert_val_types() {
        assert_eq!(convert_val_type(WasmValType::I32), ValType::I32);
        assert_eq!(convert_val_type(WasmValType::I64), ValType::I64);
        assert_eq!(convert_val_type(WasmValType::F32), ValType::F32);
        assert_eq!(convert_val_type(WasmValType::F64), ValType::F64);
    }

    // ---------------------------------------------------------------
    // Canonical ABI sizing tests (SR-3: Correct Canonical ABI element
    // size computation)
    // ---------------------------------------------------------------

    /// Build a minimal `ParsedComponent` with no types/modules/imports.
    /// Sufficient for exercising the sizing functions on inline types.
    fn empty_parsed_component() -> ParsedComponent {
        ParsedComponent {
            name: None,
            core_modules: vec![],
            imports: vec![],
            exports: vec![],
            types: vec![],
            instances: vec![],
            canonical_functions: vec![],
            sub_components: vec![],
            component_aliases: vec![],
            component_instances: vec![],
            core_entity_order: vec![],
            component_func_defs: vec![],
            component_instance_defs: vec![],
            component_type_defs: vec![],
            original_size: 0,
            original_hash: String::new(),
            depth_0_sections: vec![],
        }
    }

    /// SR-3: Verify element_size for every primitive type matches the
    /// Canonical ABI specification (Core Spec 3.0 / Component Model).
    #[test]
    fn test_canonical_abi_element_size_primitive_types() {
        let pc = empty_parsed_component();

        let cases: &[(PrimitiveValType, u32)] = &[
            (PrimitiveValType::U8, 1),
            (PrimitiveValType::U16, 2),
            (PrimitiveValType::U32, 4),
            (PrimitiveValType::U64, 8),
            (PrimitiveValType::S8, 1),
            (PrimitiveValType::S16, 2),
            (PrimitiveValType::S32, 4),
            (PrimitiveValType::S64, 8),
            (PrimitiveValType::F32, 4),
            (PrimitiveValType::F64, 8),
            (PrimitiveValType::Bool, 1),
        ];

        for (prim, expected) in cases {
            let ty = ComponentValType::Primitive(*prim);
            assert_eq!(
                pc.canonical_abi_element_size(&ty),
                *expected,
                "element_size mismatch for {:?}",
                prim,
            );
        }
    }

    /// SR-3: String is a (ptr: i32, len: i32) pair = 8 bytes, align 4.
    #[test]
    fn test_canonical_abi_element_size_string() {
        let pc = empty_parsed_component();
        let ty = ComponentValType::String;
        assert_eq!(pc.canonical_abi_element_size(&ty), 8);
    }

    /// SR-3 / LS-P-2: A record {u8, string} must include alignment
    /// padding.  Naive sum would give 1 + 8 = 9, but the string field
    /// requires align-4, so the layout is:
    ///   offset 0: u8      (1 byte)
    ///   offset 1: padding  (3 bytes to reach align 4)
    ///   offset 4: string   (8 bytes: ptr + len)
    /// Unpadded size = 12.  Record align = max(1, 4) = 4.
    /// element_size = align_up(12, 4) = 12.
    #[test]
    fn test_canonical_abi_element_size_record_with_padding() {
        let pc = empty_parsed_component();
        let ty = ComponentValType::Record(vec![
            (
                "a".into(),
                ComponentValType::Primitive(PrimitiveValType::U8),
            ),
            ("b".into(), ComponentValType::String),
        ]);
        assert_eq!(
            pc.canonical_abi_element_size(&ty),
            12,
            "record {{u8, string}} should be 12 (with alignment padding), not 9",
        );
    }

    /// SR-3: A homogeneous record {u32, u32} needs no inter-field
    /// padding — both fields are align-4 and the first already ends on
    /// an aligned boundary.  element_size = 8.
    #[test]
    fn test_canonical_abi_element_size_record_homogeneous() {
        let pc = empty_parsed_component();
        let ty = ComponentValType::Record(vec![
            (
                "x".into(),
                ComponentValType::Primitive(PrimitiveValType::U32),
            ),
            (
                "y".into(),
                ComponentValType::Primitive(PrimitiveValType::U32),
            ),
        ]);
        assert_eq!(pc.canonical_abi_element_size(&ty), 8);
    }

    /// SR-3: Verify canonical_abi_align returns the correct power-of-two
    /// alignment for each primitive and for compound types.
    #[test]
    fn test_canonical_abi_align_values() {
        let pc = empty_parsed_component();

        // Primitives
        let prim_cases: &[(PrimitiveValType, u32)] = &[
            (PrimitiveValType::Bool, 1),
            (PrimitiveValType::U8, 1),
            (PrimitiveValType::S8, 1),
            (PrimitiveValType::U16, 2),
            (PrimitiveValType::S16, 2),
            (PrimitiveValType::U32, 4),
            (PrimitiveValType::S32, 4),
            (PrimitiveValType::F32, 4),
            (PrimitiveValType::Char, 4),
            (PrimitiveValType::U64, 8),
            (PrimitiveValType::S64, 8),
            (PrimitiveValType::F64, 8),
        ];
        for (prim, expected) in prim_cases {
            let ty = ComponentValType::Primitive(*prim);
            assert_eq!(
                pc.canonical_abi_align(&ty),
                *expected,
                "align mismatch for {:?}",
                prim,
            );
        }

        // String — pointer alignment = 4
        assert_eq!(pc.canonical_abi_align(&ComponentValType::String), 4);

        // List — pointer alignment = 4
        let list_ty =
            ComponentValType::List(Box::new(ComponentValType::Primitive(PrimitiveValType::U8)));
        assert_eq!(pc.canonical_abi_align(&list_ty), 4);

        // Record inherits max alignment of its fields
        let record_ty = ComponentValType::Record(vec![
            (
                "a".into(),
                ComponentValType::Primitive(PrimitiveValType::U8),
            ),
            (
                "b".into(),
                ComponentValType::Primitive(PrimitiveValType::U64),
            ),
        ]);
        assert_eq!(
            pc.canonical_abi_align(&record_ty),
            8,
            "record {{u8, u64}} align should be max(1, 8) = 8",
        );

        // Empty record defaults to align 1
        let empty_record = ComponentValType::Record(vec![]);
        assert_eq!(pc.canonical_abi_align(&empty_record), 1);
    }

    #[test]
    fn test_disc_size_values() {
        // ≤ 256 cases → 1 byte
        assert_eq!(disc_size(0), 1);
        assert_eq!(disc_size(1), 1);
        assert_eq!(disc_size(2), 1); // option, result
        assert_eq!(disc_size(256), 1);
        // 257..65536 → 2 bytes
        assert_eq!(disc_size(257), 2);
        assert_eq!(disc_size(65536), 2);
        // > 65536 → 4 bytes
        assert_eq!(disc_size(65537), 4);
    }

    #[test]
    fn test_canonical_abi_variant_layout() {
        let pc = empty_parsed_component();

        // option<bool>: disc_size=1, max_case_align=1, payload_offset=1
        // size_unpadded = align_up(1,1) + element_size(bool) = 1 + 1 = 2
        // align = max(1,1) = 1
        // element_size = align_up(2,1) = 2
        let opt_bool = ComponentValType::Option(Box::new(ComponentValType::Primitive(
            PrimitiveValType::Bool,
        )));
        assert_eq!(pc.canonical_abi_align(&opt_bool), 1);
        assert_eq!(pc.canonical_abi_element_size(&opt_bool), 2);

        // option<u32>: disc_size=1, max_case_align=4, payload_offset=4
        // size_unpadded = align_up(1,4) + element_size(u32) = 4 + 4 = 8
        // align = max(1,4) = 4
        // element_size = align_up(8,4) = 8
        let opt_u32 =
            ComponentValType::Option(Box::new(ComponentValType::Primitive(PrimitiveValType::U32)));
        assert_eq!(pc.canonical_abi_align(&opt_u32), 4);
        assert_eq!(pc.canonical_abi_element_size(&opt_u32), 8);

        // option<f64>: disc_size=1, max_case_align=8, payload_offset=8
        // size_unpadded = align_up(1,8) + element_size(f64) = 8 + 8 = 16
        // align = max(1,8) = 8
        // element_size = align_up(16,8) = 16
        let opt_f64 =
            ComponentValType::Option(Box::new(ComponentValType::Primitive(PrimitiveValType::F64)));
        assert_eq!(pc.canonical_abi_align(&opt_f64), 8);
        assert_eq!(pc.canonical_abi_element_size(&opt_f64), 16);

        // option<string>: disc_size=1, max_case_align=4, payload_offset=4
        // size_unpadded = align_up(1,4) + element_size(string) = 4 + 8 = 12
        // align = max(1,4) = 4
        // element_size = align_up(12,4) = 12
        let opt_string = ComponentValType::Option(Box::new(ComponentValType::String));
        assert_eq!(pc.canonical_abi_align(&opt_string), 4);
        assert_eq!(pc.canonical_abi_element_size(&opt_string), 12);

        // result<string, u32>: disc_size=1, max_case_align=4, payload_offset=4
        // size_unpadded = align_up(1,4) + max(element_size(string)=8, element_size(u32)=4) = 4+8 = 12
        // align = max(1,4,4) = 4
        // element_size = align_up(12,4) = 12
        let res_str_u32 = ComponentValType::Result {
            ok: Some(Box::new(ComponentValType::String)),
            err: Some(Box::new(ComponentValType::Primitive(PrimitiveValType::U32))),
        };
        assert_eq!(pc.canonical_abi_align(&res_str_u32), 4);
        assert_eq!(pc.canonical_abi_element_size(&res_str_u32), 12);

        // variant { a: u8, b: f64 } (2 cases): disc_size=1, max_case_align=8
        // payload_offset = align_up(1,8) = 8
        // size_unpadded = 8 + max(element_size(u8)=1, element_size(f64)=8) = 8+8 = 16
        // align = max(1,8) = 8
        // element_size = align_up(16,8) = 16
        let variant_f64 = ComponentValType::Variant(vec![
            (
                "a".into(),
                Some(ComponentValType::Primitive(PrimitiveValType::U8)),
            ),
            (
                "b".into(),
                Some(ComponentValType::Primitive(PrimitiveValType::F64)),
            ),
        ]);
        assert_eq!(pc.canonical_abi_align(&variant_f64), 8);
        assert_eq!(pc.canonical_abi_element_size(&variant_f64), 16);

        // variant { a: u8, b: u16 } (2 cases): disc_size=1, max_case_align=2
        // payload_offset = align_up(1,2) = 2
        // size_unpadded = 2 + max(element_size(u8)=1, element_size(u16)=2) = 2+2 = 4
        // align = max(1,2) = 2
        // element_size = align_up(4,2) = 4
        let variant_small = ComponentValType::Variant(vec![
            (
                "a".into(),
                Some(ComponentValType::Primitive(PrimitiveValType::U8)),
            ),
            (
                "b".into(),
                Some(ComponentValType::Primitive(PrimitiveValType::U16)),
            ),
        ]);
        assert_eq!(pc.canonical_abi_align(&variant_small), 2);
        assert_eq!(pc.canonical_abi_element_size(&variant_small), 4);

        // result<(), ()>: disc_size=1, no payloads
        // size_unpadded = align_up(1,1) + 0 = 1
        // align = max(1,1,1) = 1
        // element_size = align_up(1,1) = 1
        let res_unit = ComponentValType::Result {
            ok: None,
            err: None,
        };
        assert_eq!(pc.canonical_abi_align(&res_unit), 1);
        assert_eq!(pc.canonical_abi_element_size(&res_unit), 1);
    }

    #[test]
    fn test_conditional_result_pointer_offsets_variant_f64() {
        let pc = empty_parsed_component();

        // variant { none, some: string } (like option<string> but explicit)
        // disc_size=1, max_case_align=4 (string align), payload_offset=align_up(1,4)=4
        // The pointer pair for string should be at byte offset 4 (not hardcoded 4)
        let results: Vec<(Option<String>, ComponentValType)> = vec![(
            None,
            ComponentValType::Variant(vec![
                ("none".into(), None),
                ("some".into(), Some(ComponentValType::String)),
            ]),
        )];
        let pairs = pc.conditional_pointer_pair_result_positions(&results);
        assert_eq!(pairs.len(), 1, "should find 1 conditional pointer pair");
        assert_eq!(pairs[0].discriminant_position, 0);
        assert_eq!(pairs[0].discriminant_value, 1); // case "some" = index 1
        assert_eq!(
            pairs[0].ptr_position, 4,
            "pointer should be at offset 4 (align_up(1,4))"
        );

        // variant { a: f64, b: string } — max_case_align = max(8, 4) = 8
        // disc_size=1, payload_offset = align_up(1, 8) = 8
        let results_f64: Vec<(Option<String>, ComponentValType)> = vec![(
            None,
            ComponentValType::Variant(vec![
                (
                    "a".into(),
                    Some(ComponentValType::Primitive(PrimitiveValType::F64)),
                ),
                ("b".into(), Some(ComponentValType::String)),
            ]),
        )];
        let pairs_f64 = pc.conditional_pointer_pair_result_positions(&results_f64);
        assert_eq!(
            pairs_f64.len(),
            1,
            "should find 1 conditional pointer pair for string case"
        );
        assert_eq!(pairs_f64[0].discriminant_position, 0);
        assert_eq!(pairs_f64[0].discriminant_value, 1); // case "b" = index 1
        assert_eq!(
            pairs_f64[0].ptr_position, 8,
            "pointer should be at offset 8 (align_up(1,8)) not 4"
        );
    }
}
