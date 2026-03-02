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
        // Stop capturing depth_0_sections once we hit the first core module,
        // so we only replay interface-definition sections (Type, Import, Alias)
        // and not the wiring sections that reference core instances.
        let mut seen_core_module = false;

        for payload in parser.parse_all(bytes) {
            let payload = payload?;
            // Track when we first encounter a core module at depth 0
            if depth == 0 && matches!(&payload, Payload::ModuleSection { .. }) {
                seen_core_module = true;
            }
            match &payload {
                Payload::ComponentSection { .. } => {
                    depth += 1;
                    sub_stack.push(ParsedComponent::empty());
                    continue; // don't pass ComponentSection to handle_payload
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
            let target = if depth > 0 {
                sub_stack.last_mut().unwrap()
            } else {
                &mut component
            };
            let capture_sections = depth == 0 && !seen_core_module;
            self.handle_payload(payload, target, bytes, capture_sections)?;
        }

        if component.core_modules.is_empty() {
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
    /// Returns `Some` only for types defined via `ComponentTypeSection` (i.e.,
    /// `ComponentTypeDef::Defined`). Returns `None` for import-defined or
    /// alias-defined types.
    pub fn get_type_definition(&self, type_idx: u32) -> Option<&ComponentType> {
        let def = self.component_type_defs.get(type_idx as usize)?;
        if !matches!(def, ComponentTypeDef::Defined) {
            return None;
        }
        // The Nth Defined entry in component_type_defs corresponds to types[N]
        let def_offset = self.component_type_defs[..type_idx as usize]
            .iter()
            .filter(|d| matches!(d, ComponentTypeDef::Defined))
            .count();
        self.types.get(def_offset)
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
        _ => ComponentTypeKind::Other,
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
}
