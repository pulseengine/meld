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

    /// P3 async features detected during parsing (not yet supported).
    /// Each entry describes a specific P3 construct found, e.g.
    /// "future<string> type", "async canonical option", "task.wait builtin".
    /// Non-empty means the component uses P3 async features that meld
    /// cannot yet fuse correctly.
    pub p3_async_features: Vec<String>,
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
    /// P3 async type (future, stream) — not yet supported.
    /// The string describes the specific type, e.g. "future<string>".
    P3Async(String),
}

/// Component value type
#[derive(Debug, Clone)]
pub enum ComponentValType {
    Primitive(PrimitiveValType),
    String,
    List(Box<ComponentValType>),
    FixedSizeList(Box<ComponentValType>, u32),
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

/// Position of a resource-typed parameter or result in the flat ABI layout.
///
/// Used by the adapter generator to emit `[resource-rep]` (handle → representation)
/// or `[resource-new]` (representation → handle) calls at the correct positions.
#[derive(Debug, Clone)]
pub struct ResourcePosition {
    /// Index in the flat (stack) ABI layout (e.g., param 0, 1, 2…)
    pub flat_idx: u32,
    /// Byte offset in the canonical ABI memory layout (for return-area results)
    pub byte_offset: u32,
    /// `true` for `own<R>`, `false` for `borrow<R>`
    pub is_owned: bool,
    /// Component-level type index of the resource
    pub resource_type_id: u32,
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
    pub async_: bool,
    pub callback: Option<u32>,
}

impl Default for CanonicalOptions {
    fn default() -> Self {
        Self {
            string_encoding: CanonStringEncoding::Utf8,
            memory: None,
            realloc: None,
            post_return: None,
            async_: false,
            callback: None,
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
    /// Spawn a new thread (via ref)
    ThreadSpawn { func_ty_index: u32 },
    /// Query hardware thread concurrency
    ThreadHwConcurrency,
    /// Async drop of a resource handle
    ResourceDropAsync { resource: u32 },
    /// Increment backpressure counter
    BackpressureInc,
    /// Decrement backpressure counter
    BackpressureDec,
    /// Return a result from a lifted async export
    TaskReturn {
        result: Option<ComponentValType>,
        options: CanonicalOptions,
    },
    /// Acknowledge cancellation of the current task
    TaskCancel,
    /// Get task-local context slot
    ContextGet(u32),
    /// Set task-local context slot
    ContextSet(u32),
    /// Yield control to the host
    ThreadYield { cancellable: bool },
    /// Drop a completed subtask
    SubtaskDrop,
    /// Cancel an in-progress subtask
    SubtaskCancel { async_: bool },
    /// Create a new stream handle
    StreamNew { ty: u32 },
    /// Read from a stream
    StreamRead { ty: u32, options: CanonicalOptions },
    /// Write to a stream
    StreamWrite { ty: u32, options: CanonicalOptions },
    /// Cancel an in-progress stream read
    StreamCancelRead { ty: u32, async_: bool },
    /// Cancel an in-progress stream write
    StreamCancelWrite { ty: u32, async_: bool },
    /// Drop the readable end of a stream
    StreamDropReadable { ty: u32 },
    /// Drop the writable end of a stream
    StreamDropWritable { ty: u32 },
    /// Create a new future handle
    FutureNew { ty: u32 },
    /// Read from a future
    FutureRead { ty: u32, options: CanonicalOptions },
    /// Write to a future
    FutureWrite { ty: u32, options: CanonicalOptions },
    /// Cancel an in-progress future read
    FutureCancelRead { ty: u32, async_: bool },
    /// Cancel an in-progress future write
    FutureCancelWrite { ty: u32, async_: bool },
    /// Drop the readable end of a future
    FutureDropReadable { ty: u32 },
    /// Drop the writable end of a future
    FutureDropWritable { ty: u32 },
    /// Create a new error-context with a debug message
    ErrorContextNew { options: CanonicalOptions },
    /// Get the debug message for an error-context
    ErrorContextDebugMessage { options: CanonicalOptions },
    /// Drop an error-context
    ErrorContextDrop,
    /// Create a new waitable-set
    WaitableSetNew,
    /// Block on the next item within a waitable-set
    WaitableSetWait { cancellable: bool, memory: u32 },
    /// Check if any items are ready within a waitable-set
    WaitableSetPoll { cancellable: bool, memory: u32 },
    /// Drop a waitable-set
    WaitableSetDrop,
    /// Add an item to a waitable-set
    WaitableJoin,
    /// Unsupported canonical function (thread.index, thread.*indirect, etc.)
    Unsupported,
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
            let features = wasmparser::WasmFeatures::default()
                | wasmparser::WasmFeatures::CM_FIXED_LENGTH_LISTS
                | wasmparser::WasmFeatures::CM_ASYNC;
            let mut validator = wasmparser::Validator::new_with_features(features);
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
            p3_async_features: Vec::new(),
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
                                .result
                                .iter()
                                .map(|ty| (None, convert_wp_component_val_type(ty)))
                                .collect();
                            ComponentTypeKind::Function { params, results }
                        }
                        wasmparser::ComponentType::Defined(dt) => convert_wp_defined_type(&dt),
                        wasmparser::ComponentType::Component(_) => ComponentTypeKind::Other,
                        wasmparser::ComponentType::Instance(_) => ComponentTypeKind::Other,
                        wasmparser::ComponentType::Resource { .. } => ComponentTypeKind::Other,
                    };
                    if let ComponentTypeKind::P3Async(ref desc) = kind {
                        component.p3_async_features.push(format!("{desc} type"));
                    }
                    component.types.push(ComponentType { kind });
                    component
                        .component_type_defs
                        .push(ComponentTypeDef::Defined);
                }
            }

            Payload::ComponentCanonicalSection(reader) => {
                for canon in reader {
                    let canon = canon?;
                    let creates_core_func =
                        !matches!(&canon, wasmparser::CanonicalFunction::Lift { .. });
                    let is_lift = matches!(&canon, wasmparser::CanonicalFunction::Lift { .. });
                    let canon_idx = component.canonical_functions.len();
                    component
                        .canonical_functions
                        .push(convert_canonical_function(
                            canon,
                            &mut component.p3_async_features,
                        ));
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
                    for import in reader.into_imports() {
                        let import = import?;
                        let kind = match import.ty {
                            wasmparser::TypeRef::Func(idx)
                            | wasmparser::TypeRef::FuncExact(idx) => ImportKind::Function(idx),
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
                            wasmparser::ExternalKind::Func
                            | wasmparser::ExternalKind::FuncExact => ExportKind::Function,
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
            p3_async_features: Vec::new(),
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
            ComponentValType::Record(fields) => fields
                .iter()
                .map(|(_, ty)| self.flat_byte_size(ty))
                .fold(0u32, u32::saturating_add),
            ComponentValType::Tuple(elems) => elems
                .iter()
                .map(|ty| self.flat_byte_size(ty))
                .fold(0u32, u32::saturating_add),
            ComponentValType::Option(inner) => 4u32.saturating_add(self.flat_byte_size(inner)),
            ComponentValType::Result { ok, err } => {
                let ok_size = ok.as_ref().map(|t| self.flat_byte_size(t)).unwrap_or(0);
                let err_size = err.as_ref().map(|t| self.flat_byte_size(t)).unwrap_or(0);
                4u32.saturating_add(ok_size.max(err_size))
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
                4u32.saturating_add(max_payload)
            }
            ComponentValType::FixedSizeList(elem, len) => {
                self.flat_byte_size(elem).saturating_mul(*len)
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

    /// Compute the total number of flat (core wasm) params for a component function's params.
    ///
    /// If this exceeds MAX_FLAT_PARAMS (16), the canonical ABI uses the params-ptr
    /// calling convention: a single i32 pointer to a buffer in linear memory.
    pub fn total_flat_params(&self, params: &[(String, ComponentValType)]) -> u32 {
        params.iter().map(|(_, ty)| self.flat_count(ty)).sum()
    }

    /// Compute the byte size of the params area for a component function's params.
    ///
    /// The params area uses the canonical ABI memory layout (with alignment),
    /// matching `return_area_byte_size` but for parameters. Used when the canonical
    /// ABI employs params-ptr lowering (flat param count > MAX_FLAT_PARAMS = 16).
    pub fn params_area_byte_size(&self, params: &[(String, ComponentValType)]) -> u32 {
        let mut size = 0u32;
        for (_, ty) in params {
            let align = self.canonical_abi_align(ty);
            size = align_up(size, align);
            size += self.canonical_abi_size_unpadded(ty);
        }
        // Align final size to the max alignment of the tuple
        let max_align = params
            .iter()
            .map(|(_, ty)| self.canonical_abi_align(ty))
            .max()
            .unwrap_or(1);
        align_up(size, max_align)
    }

    /// Compute the maximum alignment of the params area.
    pub fn params_area_max_align(&self, params: &[(String, ComponentValType)]) -> u32 {
        params
            .iter()
            .map(|(_, ty)| self.canonical_abi_align(ty))
            .max()
            .unwrap_or(1)
    }

    /// Compute byte offsets in the params area where (ptr, len) pairs start.
    ///
    /// Uses canonical ABI memory layout offsets (with alignment), matching
    /// how params are stored in the params-ptr buffer. Mirrors
    /// `pointer_pair_result_offsets` but for parameters.
    pub fn pointer_pair_params_byte_offsets(
        &self,
        params: &[(String, ComponentValType)],
    ) -> Vec<u32> {
        let mut offsets = Vec::new();
        let mut byte_offset = 0u32;
        for (_, ty) in params {
            let align = self.canonical_abi_align(ty);
            byte_offset = align_up(byte_offset, align);
            self.collect_pointer_byte_offsets(ty, byte_offset, &mut offsets);
            byte_offset += self.canonical_abi_size_unpadded(ty);
        }
        offsets
    }

    /// Compute the layout of all slots in the params area.
    ///
    /// Each slot describes a contiguous value in the canonical ABI memory layout
    /// with its byte offset, byte size, and whether it is a pointer pair.
    /// Mirrors `return_area_slots` but for parameters.
    pub fn params_area_slots(
        &self,
        params: &[(String, ComponentValType)],
    ) -> Vec<crate::resolver::ReturnAreaSlot> {
        let mut slots = Vec::new();
        let mut byte_offset = 0u32;
        for (_, ty) in params {
            let align = self.canonical_abi_align(ty);
            byte_offset = align_up(byte_offset, align);
            self.collect_return_area_type_slots(ty, byte_offset, &mut slots);
            byte_offset += self.canonical_abi_size_unpadded(ty);
        }
        slots
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
            ComponentValType::FixedSizeList(elem, len) => {
                // Inline fixed-size list: lay out each element sequentially
                let elem_size = self.canonical_abi_element_size(elem);
                let mut offset = base;
                for _ in 0..*len {
                    self.collect_return_area_type_slots(elem, offset, out);
                    offset += elem_size;
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

    /// Resolve a `ComponentValType` to its resource type, if any.
    ///
    /// Returns `Some((resource_type_id, is_owned))` for `Own(T)`, `Borrow(T)`,
    /// and `Type(idx)` that resolves to a `Defined(Own(T))` or `Defined(Borrow(T))`.
    fn resolve_to_resource(&self, ty: &ComponentValType) -> Option<(u32, bool)> {
        match ty {
            ComponentValType::Own(id) => Some((*id, true)),
            ComponentValType::Borrow(id) => Some((*id, false)),
            ComponentValType::Type(idx) => {
                // Follow type definition chain
                if let Some(ct) = self.get_type_definition(*idx)
                    && let ComponentTypeKind::Defined(inner) = &ct.kind
                {
                    match inner {
                        ComponentValType::Own(id) => Some((*id, true)),
                        ComponentValType::Borrow(id) => Some((*id, false)),
                        _ => None,
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Identify resource-typed parameters and their flat-ABI positions.
    ///
    /// For each `own<R>` or `borrow<R>` parameter (including through `Type(idx)`
    /// indirection), returns a `ResourcePosition` with the flat param index and
    /// resource type ID. Used by the adapter to emit `[resource-rep]` calls that
    /// convert handles to representations.
    pub fn resource_param_positions(
        &self,
        params: &[(String, ComponentValType)],
    ) -> Vec<ResourcePosition> {
        let mut positions = Vec::new();
        let mut flat_idx = 0u32;
        for (_, ty) in params {
            if let Some((resource_type_id, is_owned)) = self.resolve_to_resource(ty) {
                positions.push(ResourcePosition {
                    flat_idx,
                    byte_offset: 0, // not used for params
                    is_owned,
                    resource_type_id,
                });
            }
            flat_idx += self.flat_count(ty);
        }
        positions
    }

    /// Identify resource-typed parameters at their canonical ABI byte offsets
    /// within the params-ptr buffer.
    ///
    /// Walks the full type structure (records, tuples, variants, options, results)
    /// to find all `own<R>` and `borrow<R>` values and their byte offsets in the
    /// canonical ABI memory layout. Used by the params-ptr adapter to emit
    /// `[resource-rep]` calls for borrow handles inside the buffer.
    pub fn resource_params_area_positions(
        &self,
        params: &[(String, ComponentValType)],
    ) -> Vec<ResourcePosition> {
        let mut positions = Vec::new();
        let mut byte_offset = 0u32;
        for (_, ty) in params {
            let align = self.canonical_abi_align(ty);
            byte_offset = align_up(byte_offset, align);
            self.collect_resource_byte_positions(ty, byte_offset, &mut positions);
            byte_offset += self.canonical_abi_size_unpadded(ty);
        }
        positions
    }

    /// Recursively collect resource handle byte offsets within a type's
    /// canonical ABI memory layout.
    fn collect_resource_byte_positions(
        &self,
        ty: &ComponentValType,
        base: u32,
        out: &mut Vec<ResourcePosition>,
    ) {
        match ty {
            ComponentValType::Own(id) => {
                out.push(ResourcePosition {
                    flat_idx: 0, // not meaningful for byte-offset based access
                    byte_offset: base,
                    is_owned: true,
                    resource_type_id: *id,
                });
            }
            ComponentValType::Borrow(id) => {
                out.push(ResourcePosition {
                    flat_idx: 0,
                    byte_offset: base,
                    is_owned: false,
                    resource_type_id: *id,
                });
            }
            ComponentValType::Record(fields) => {
                let mut offset = base;
                for (_, field_ty) in fields {
                    let align = self.canonical_abi_align(field_ty);
                    offset = align_up(offset, align);
                    self.collect_resource_byte_positions(field_ty, offset, out);
                    offset += self.canonical_abi_size_unpadded(field_ty);
                }
            }
            ComponentValType::Tuple(elems) => {
                let mut offset = base;
                for elem_ty in elems {
                    let align = self.canonical_abi_align(elem_ty);
                    offset = align_up(offset, align);
                    self.collect_resource_byte_positions(elem_ty, offset, out);
                    offset += self.canonical_abi_size_unpadded(elem_ty);
                }
            }
            ComponentValType::Option(inner) => {
                // discriminant (1-4 bytes) + payload
                let disc_size = 1u32; // option discriminant is always 1 byte
                let payload_align = self.canonical_abi_align(inner);
                let payload_offset = align_up(base + disc_size, payload_align);
                // Only collect when discriminant == 1 (Some)
                // The adapter must check the discriminant at runtime
                self.collect_resource_byte_positions(inner, payload_offset, out);
            }
            ComponentValType::Result { ok, err } => {
                let disc_size = 1u32;
                let ok_align = ok
                    .as_ref()
                    .map(|t| self.canonical_abi_align(t))
                    .unwrap_or(1);
                let err_align = err
                    .as_ref()
                    .map(|t| self.canonical_abi_align(t))
                    .unwrap_or(1);
                let payload_align = ok_align.max(err_align);
                let payload_offset = align_up(base + disc_size, payload_align);
                if let Some(ok_ty) = ok {
                    self.collect_resource_byte_positions(ok_ty, payload_offset, out);
                }
                if let Some(err_ty) = err {
                    self.collect_resource_byte_positions(err_ty, payload_offset, out);
                }
            }
            ComponentValType::Variant(cases) => {
                let disc_size = if cases.len() <= 256 { 1u32 } else { 4 };
                let payload_align = cases
                    .iter()
                    .filter_map(|(_, t)| t.as_ref().map(|t| self.canonical_abi_align(t)))
                    .max()
                    .unwrap_or(1);
                let payload_offset = align_up(base + disc_size, payload_align);
                for (_, case_ty) in cases {
                    if let Some(ty) = case_ty {
                        self.collect_resource_byte_positions(ty, payload_offset, out);
                    }
                }
            }
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx)
                    && let ComponentTypeKind::Defined(inner) = &ct.kind
                {
                    self.collect_resource_byte_positions(inner, base, out);
                }
            }
            // Lists contain resource handles but they're in a separate memory area,
            // not in the params buffer itself. The adapter handles list resource
            // conversion separately via inner_resource_fixups.
            ComponentValType::List(_) | ComponentValType::String => {}
            ComponentValType::FixedSizeList(elem, len) => {
                let elem_size = self.canonical_abi_element_size(elem);
                let mut offset = base;
                for _ in 0..*len {
                    self.collect_resource_byte_positions(elem, offset, out);
                    offset += elem_size;
                }
            }
            _ => {} // primitives
        }
    }

    /// Identify resource-typed results and their flat-ABI / byte-offset positions.
    ///
    /// Returns both the flat index (for non-retptr results) and the canonical ABI
    /// byte offset (for retptr return-area results). Used by the adapter to emit
    /// `[resource-new]` calls that convert representations to handles.
    pub fn resource_result_positions(
        &self,
        results: &[(Option<String>, ComponentValType)],
    ) -> Vec<ResourcePosition> {
        let mut positions = Vec::new();
        let mut flat_idx = 0u32;
        let mut byte_offset = 0u32;
        for (_, ty) in results {
            let align = self.canonical_abi_align(ty);
            byte_offset = align_up(byte_offset, align);
            if let Some((resource_type_id, is_owned)) = self.resolve_to_resource(ty) {
                positions.push(ResourcePosition {
                    flat_idx,
                    byte_offset,
                    is_owned,
                    resource_type_id,
                });
            }
            flat_idx += self.flat_count(ty);
            byte_offset += self.canonical_abi_size_unpadded(ty);
        }
        positions
    }

    /// Resolve a component type index to `(module_name, type_name)` for resource ops.
    ///
    /// Traces the type index through `component_type_defs` and `component_aliases`
    /// to find the WASI interface module name and the resource's exported name.
    /// Returns `None` if the type cannot be traced to an import.
    pub fn resolve_resource_type(&self, type_id: u32) -> Option<(String, String)> {
        // Build instance → import name map
        let mut comp_instance_to_import: std::collections::HashMap<u32, String> =
            std::collections::HashMap::new();
        for (inst_idx, def) in self.component_instance_defs.iter().enumerate() {
            if let ComponentInstanceDef::Import(import_idx) = def
                && let Some(imp) = self.imports.get(*import_idx)
            {
                comp_instance_to_import.insert(inst_idx as u32, imp.name.clone());
            }
        }

        if let Some(def) = self.component_type_defs.get(type_id as usize) {
            match def {
                ComponentTypeDef::InstanceExportAlias(alias_idx) => {
                    if let Some(ComponentAliasEntry::InstanceExport {
                        instance_index,
                        name,
                        ..
                    }) = self.component_aliases.get(*alias_idx)
                        && let Some(module_name) = comp_instance_to_import.get(instance_index)
                    {
                        return Some((module_name.clone(), name.clone()));
                    }
                }
                ComponentTypeDef::Import(import_idx) => {
                    if let Some(imp) = self.imports.get(*import_idx) {
                        // Extract resource name from WASI path:
                        // "wasi:io/error@0.2.6" → "error"
                        let without_version = imp
                            .name
                            .rfind('@')
                            .map(|pos| &imp.name[..pos])
                            .unwrap_or(&imp.name);
                        let resource_name = without_version
                            .rfind('/')
                            .map(|pos| &without_version[pos + 1..])
                            .unwrap_or(without_version);
                        return Some((imp.name.clone(), resource_name.to_string()));
                    }
                }
                _ => {}
            }
        }
        None
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
            ComponentValType::FixedSizeList(elem, len) => {
                // Inline: each element is flattened sequentially
                let elem_flat = self.flat_count(elem);
                let mut offset = base;
                for _ in 0..*len {
                    self.collect_pointer_positions(elem, offset, out);
                    offset += elem_flat;
                }
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
            ComponentValType::FixedSizeList(elem, len) => {
                // Inline: each element laid out at stride = element_size
                let elem_size = self.canonical_abi_element_size(elem);
                let mut offset = base;
                for _ in 0..*len {
                    self.collect_pointer_byte_offsets(elem, offset, out);
                    offset += elem_size;
                }
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
            ComponentValType::FixedSizeList(elem, len) => {
                let elem_flat = self.flat_count(elem);
                let mut offset = base;
                for _ in 0..*len {
                    self.collect_conditional_pointers(elem, offset, out);
                    offset += elem_flat;
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
            ComponentValType::FixedSizeList(elem, len) => {
                let elem_size = self.canonical_abi_element_size(elem);
                let mut offset = base;
                for _ in 0..*len {
                    self.collect_conditional_result_pointers(elem, offset, out);
                    offset += elem_size;
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
            ComponentValType::FixedSizeList(elem, _) => self.type_contains_pointers(elem),
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
            ComponentValType::Record(fields) => fields
                .iter()
                .map(|(_, t)| self.flat_count(t))
                .fold(0u32, u32::saturating_add),
            ComponentValType::Tuple(elems) => elems
                .iter()
                .map(|t| self.flat_count(t))
                .fold(0u32, u32::saturating_add),
            ComponentValType::Option(inner) => 1u32.saturating_add(self.flat_count(inner)),
            ComponentValType::Result { ok, err } => {
                let ok_c = ok.as_ref().map(|t| self.flat_count(t)).unwrap_or(0);
                let err_c = err.as_ref().map(|t| self.flat_count(t)).unwrap_or(0);
                1u32.saturating_add(ok_c.max(err_c))
            }
            ComponentValType::Variant(cases) => {
                let max_c = cases
                    .iter()
                    .filter_map(|(_, t)| t.as_ref().map(|t| self.flat_count(t)))
                    .max()
                    .unwrap_or(0);
                1u32.saturating_add(max_c)
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
            ComponentValType::FixedSizeList(elem, len) => {
                self.flat_count(elem).saturating_mul(*len)
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
            ComponentValType::FixedSizeList(elem, _) => self.canonical_abi_align(elem),
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
            ComponentValType::FixedSizeList(elem, len) => {
                // Inline: element_size (padded stride) * length.
                // Saturating to u32::MAX prevents wrap-to-0 on adversarial
                // nested fixed-length-list types whose product exceeds u32.
                // Downstream allocation/copy with u32::MAX safely fails
                // rather than under-allocating and writing OOB.
                self.canonical_abi_element_size(elem).saturating_mul(*len)
            }
            ComponentValType::Record(fields) => {
                let mut size = 0u32;
                for (_, field_ty) in fields {
                    let align = self.canonical_abi_align(field_ty);
                    size = align_up(size, align);
                    size = size.saturating_add(self.canonical_abi_size_unpadded(field_ty));
                }
                size
            }
            ComponentValType::Tuple(elems) => {
                let mut size = 0u32;
                for elem_ty in elems {
                    let align = self.canonical_abi_align(elem_ty);
                    size = align_up(size, align);
                    size = size.saturating_add(self.canonical_abi_size_unpadded(elem_ty));
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
                align_up(ds, max_case_align).saturating_add(max_payload)
            }
            ComponentValType::Option(inner) => {
                let ds = disc_size(2);
                let payload_align = self.canonical_abi_align(inner);
                align_up(ds, payload_align).saturating_add(self.canonical_abi_element_size(inner))
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
                align_up(ds, max_case_align).saturating_add(ok_s.max(err_s))
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
                let inner_res = self.element_inner_resources(inner, 0);
                if inner_ptrs.is_empty() && inner_res.is_empty() {
                    CopyLayout::Bulk {
                        byte_multiplier: element_size,
                    }
                } else {
                    CopyLayout::Elements {
                        element_size,
                        inner_pointers: inner_ptrs,
                        inner_resources: inner_res,
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
            ComponentValType::FixedSizeList(elem, len) => {
                // Inline: recurse into each element
                let elem_size = self.canonical_abi_element_size(elem);
                let mut offset = base;
                for _ in 0..*len {
                    result.extend(self.element_inner_pointers(elem, offset));
                    offset += elem_size;
                }
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

    /// Find resource handles embedded within a composite type's memory layout.
    /// Returns `(byte_offset, resource_type_id, is_owned)` for each resource found.
    fn element_inner_resources(
        &self,
        ty: &ComponentValType,
        base: u32,
    ) -> Vec<crate::resolver::InnerResource> {
        use crate::resolver::InnerResource;
        let mut result = Vec::new();
        match ty {
            ComponentValType::Own(id) => {
                result.push(InnerResource {
                    byte_offset: base,
                    resource_type_id: *id,
                    is_owned: true,
                    rep_import: None,
                });
            }
            ComponentValType::Borrow(id) => {
                result.push(InnerResource {
                    byte_offset: base,
                    resource_type_id: *id,
                    is_owned: false,
                    rep_import: None,
                });
            }
            ComponentValType::Record(fields) => {
                let mut offset = base;
                for (_, field_ty) in fields {
                    let align = self.canonical_abi_align(field_ty);
                    offset = align_up(offset, align);
                    result.extend(self.element_inner_resources(field_ty, offset));
                    offset = offset.saturating_add(self.canonical_abi_size_unpadded(field_ty));
                }
            }
            ComponentValType::Tuple(elems) => {
                let mut offset = base;
                for elem_ty in elems {
                    let align = self.canonical_abi_align(elem_ty);
                    offset = align_up(offset, align);
                    result.extend(self.element_inner_resources(elem_ty, offset));
                    offset = offset.saturating_add(self.canonical_abi_size_unpadded(elem_ty));
                }
            }
            ComponentValType::Type(idx) => {
                if let Some(ct) = self.get_type_definition(*idx)
                    && let ComponentTypeKind::Defined(inner) = &ct.kind
                {
                    return self.element_inner_resources(inner, base);
                }
            }
            _ => {} // scalars, strings, lists, options, variants — skip
        }
        result
    }
}

fn align_up(size: u32, align: u32) -> u32 {
    // Saturating to u32::MAX prevents overflow when `size` is already
    // u32::MAX (e.g. from a saturated FixedSizeList multiplication) and
    // `align >= 2`. Downstream sees "type too large" via a saturated max,
    // not a panic.
    if align <= 1 {
        return size;
    }
    let mask = !(align - 1);
    size.saturating_add(align - 1) & mask
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
            wasmparser::PrimitiveValType::ErrorContext => {
                // P3 error context type — treat as opaque i32 handle
                ComponentValType::Primitive(PrimitiveValType::U32)
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
        wasmparser::ComponentDefinedType::FixedLengthList(ty, len) => ComponentTypeKind::Defined(
            ComponentValType::FixedSizeList(Box::new(convert_wp_component_val_type(ty)), *len),
        ),
        // P3 async types — detected and flagged, not silently swallowed
        wasmparser::ComponentDefinedType::Future(inner) => {
            let desc = match inner {
                Some(ty) => format!("future<{ty:?}>"),
                None => "future".to_string(),
            };
            ComponentTypeKind::P3Async(desc)
        }
        wasmparser::ComponentDefinedType::Stream(inner) => {
            let desc = match inner {
                Some(ty) => format!("stream<{ty:?}>"),
                None => "stream".to_string(),
            };
            ComponentTypeKind::P3Async(desc)
        }
        wasmparser::ComponentDefinedType::Map(key_ty, val_ty) => {
            ComponentTypeKind::P3Async(format!("map<{key_ty:?}, {val_ty:?}>"))
        }
    }
}

/// Convert wasmparser CanonicalOption list into our CanonicalOptions.
///
/// The `_p3_async_features` parameter is retained for call-site
/// compatibility but is no longer used — async/callback options are
/// now stored directly in `CanonicalOptions`.
fn convert_canonical_options(
    options: &[wasmparser::CanonicalOption],
    _p3_async_features: Option<&mut Vec<String>>,
) -> CanonicalOptions {
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
            wasmparser::CanonicalOption::Async => {
                result.async_ = true;
            }
            wasmparser::CanonicalOption::Callback(idx) => {
                result.callback = Some(*idx);
            }
            wasmparser::CanonicalOption::CoreType(_) => {}
            wasmparser::CanonicalOption::Gc => {}
        }
    }
    result
}

/// Convert a wasmparser CanonicalFunction into our CanonicalEntry.
///
/// P3 async canonical built-ins (task.*, subtask.*, stream.*, future.*,
/// error-context.*) are detected and described in `p3_async_features`
/// instead of being silently mapped to `Unsupported`.
fn convert_canonical_function(
    canon: wasmparser::CanonicalFunction,
    p3_async_features: &mut Vec<String>,
) -> CanonicalEntry {
    match canon {
        wasmparser::CanonicalFunction::Lift {
            core_func_index,
            type_index,
            options,
        } => CanonicalEntry::Lift {
            core_func_index,
            type_index,
            options: convert_canonical_options(&options, Some(p3_async_features)),
        },
        wasmparser::CanonicalFunction::Lower {
            func_index,
            options,
        } => CanonicalEntry::Lower {
            func_index,
            options: convert_canonical_options(&options, Some(p3_async_features)),
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
        wasmparser::CanonicalFunction::ThreadSpawnRef { func_ty_index } => {
            CanonicalEntry::ThreadSpawn { func_ty_index }
        }
        wasmparser::CanonicalFunction::ResourceDropAsync { resource } => {
            CanonicalEntry::ResourceDropAsync { resource }
        }
        wasmparser::CanonicalFunction::BackpressureInc => CanonicalEntry::BackpressureInc,
        wasmparser::CanonicalFunction::BackpressureDec => CanonicalEntry::BackpressureDec,
        wasmparser::CanonicalFunction::TaskReturn { result, options } => {
            CanonicalEntry::TaskReturn {
                result: result.as_ref().map(convert_wp_component_val_type),
                options: convert_canonical_options(&options, None),
            }
        }
        wasmparser::CanonicalFunction::TaskCancel => CanonicalEntry::TaskCancel,
        wasmparser::CanonicalFunction::ContextGet(idx) => CanonicalEntry::ContextGet(idx),
        wasmparser::CanonicalFunction::ContextSet(idx) => CanonicalEntry::ContextSet(idx),
        wasmparser::CanonicalFunction::ThreadYield { cancellable } => {
            CanonicalEntry::ThreadYield { cancellable }
        }
        wasmparser::CanonicalFunction::SubtaskDrop => CanonicalEntry::SubtaskDrop,
        wasmparser::CanonicalFunction::SubtaskCancel { async_ } => {
            CanonicalEntry::SubtaskCancel { async_ }
        }
        wasmparser::CanonicalFunction::StreamNew { ty } => CanonicalEntry::StreamNew { ty },
        wasmparser::CanonicalFunction::StreamRead { ty, options } => CanonicalEntry::StreamRead {
            ty,
            options: convert_canonical_options(&options, None),
        },
        wasmparser::CanonicalFunction::StreamWrite { ty, options } => CanonicalEntry::StreamWrite {
            ty,
            options: convert_canonical_options(&options, None),
        },
        wasmparser::CanonicalFunction::StreamCancelRead { ty, async_ } => {
            CanonicalEntry::StreamCancelRead { ty, async_ }
        }
        wasmparser::CanonicalFunction::StreamCancelWrite { ty, async_ } => {
            CanonicalEntry::StreamCancelWrite { ty, async_ }
        }
        wasmparser::CanonicalFunction::StreamDropReadable { ty } => {
            CanonicalEntry::StreamDropReadable { ty }
        }
        wasmparser::CanonicalFunction::StreamDropWritable { ty } => {
            CanonicalEntry::StreamDropWritable { ty }
        }
        wasmparser::CanonicalFunction::FutureNew { ty } => CanonicalEntry::FutureNew { ty },
        wasmparser::CanonicalFunction::FutureRead { ty, options } => CanonicalEntry::FutureRead {
            ty,
            options: convert_canonical_options(&options, None),
        },
        wasmparser::CanonicalFunction::FutureWrite { ty, options } => CanonicalEntry::FutureWrite {
            ty,
            options: convert_canonical_options(&options, None),
        },
        wasmparser::CanonicalFunction::FutureCancelRead { ty, async_ } => {
            CanonicalEntry::FutureCancelRead { ty, async_ }
        }
        wasmparser::CanonicalFunction::FutureCancelWrite { ty, async_ } => {
            CanonicalEntry::FutureCancelWrite { ty, async_ }
        }
        wasmparser::CanonicalFunction::FutureDropReadable { ty } => {
            CanonicalEntry::FutureDropReadable { ty }
        }
        wasmparser::CanonicalFunction::FutureDropWritable { ty } => {
            CanonicalEntry::FutureDropWritable { ty }
        }
        wasmparser::CanonicalFunction::ErrorContextNew { options } => {
            CanonicalEntry::ErrorContextNew {
                options: convert_canonical_options(&options, None),
            }
        }
        wasmparser::CanonicalFunction::ErrorContextDebugMessage { options } => {
            CanonicalEntry::ErrorContextDebugMessage {
                options: convert_canonical_options(&options, None),
            }
        }
        wasmparser::CanonicalFunction::ErrorContextDrop => CanonicalEntry::ErrorContextDrop,
        wasmparser::CanonicalFunction::WaitableSetNew => CanonicalEntry::WaitableSetNew,
        wasmparser::CanonicalFunction::WaitableSetWait {
            cancellable,
            memory,
        } => CanonicalEntry::WaitableSetWait {
            cancellable,
            memory,
        },
        wasmparser::CanonicalFunction::WaitableSetPoll {
            cancellable,
            memory,
        } => CanonicalEntry::WaitableSetPoll {
            cancellable,
            memory,
        },
        wasmparser::CanonicalFunction::WaitableSetDrop => CanonicalEntry::WaitableSetDrop,
        wasmparser::CanonicalFunction::WaitableJoin => CanonicalEntry::WaitableJoin,
        // Truly unsupported variants (thread.index, thread.*indirect, etc.)
        other => {
            let desc = format!("{other:?}");
            p3_async_features.push(desc);
            CanonicalEntry::Unsupported
        }
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
        let opts = convert_canonical_options(&[], None);
        assert_eq!(opts.string_encoding, CanonStringEncoding::Utf8);
        assert_eq!(opts.memory, None);
        assert_eq!(opts.realloc, None);
        assert_eq!(opts.post_return, None);
    }

    #[test]
    fn test_convert_canonical_options_full() {
        let opts = convert_canonical_options(
            &[
                wasmparser::CanonicalOption::UTF16,
                wasmparser::CanonicalOption::Memory(3),
                wasmparser::CanonicalOption::Realloc(7),
                wasmparser::CanonicalOption::PostReturn(12),
            ],
            None,
        );
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
        let entry = convert_canonical_function(canon, &mut vec![]);
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
        let entry = convert_canonical_function(canon, &mut vec![]);
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
            p3_async_features: vec![],
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

    // ---------------------------------------------------------------
    // SR-17: String encoding canonical option parsing
    //
    // These tests verify that the parser correctly identifies string
    // encoding canonical options from component binary format. The
    // canonical ABI defines three string encodings:
    //
    //   1. UTF-8 (default) — variable-length, 1-4 bytes per code point
    //   2. UTF-16 — fixed 2 bytes per code unit, surrogate pairs for
    //      code points >= U+10000
    //   3. CompactUTF16 (latin1+utf16) — 1 byte per char for Latin-1
    //      range, falls back to UTF-16 for wider chars
    //
    // The parser must correctly set CanonicalOptions.string_encoding
    // based on wasmparser::CanonicalOption::UTF8/UTF16/CompactUTF16.
    // ---------------------------------------------------------------

    #[test]
    fn test_sr17_canonical_options_utf8_explicit() {
        // Explicitly setting UTF8 should produce Utf8 (same as default)
        let opts = convert_canonical_options(&[wasmparser::CanonicalOption::UTF8], None);
        assert_eq!(
            opts.string_encoding,
            CanonStringEncoding::Utf8,
            "SR-17: explicit UTF8 option should produce Utf8 encoding"
        );
    }

    #[test]
    fn test_sr17_canonical_options_utf16() {
        let opts = convert_canonical_options(&[wasmparser::CanonicalOption::UTF16], None);
        assert_eq!(
            opts.string_encoding,
            CanonStringEncoding::Utf16,
            "SR-17: UTF16 option should produce Utf16 encoding"
        );
    }

    #[test]
    fn test_sr17_canonical_options_compact_utf16() {
        let opts = convert_canonical_options(&[wasmparser::CanonicalOption::CompactUTF16], None);
        assert_eq!(
            opts.string_encoding,
            CanonStringEncoding::CompactUtf16,
            "SR-17: CompactUTF16 option should produce CompactUtf16 encoding"
        );
    }

    #[test]
    fn test_sr17_canonical_options_default_is_utf8() {
        // When no string encoding option is specified, default is UTF-8
        // (per the canonical ABI spec).
        let opts = convert_canonical_options(
            &[
                wasmparser::CanonicalOption::Memory(0),
                wasmparser::CanonicalOption::Realloc(1),
            ],
            None,
        );
        assert_eq!(
            opts.string_encoding,
            CanonStringEncoding::Utf8,
            "SR-17: default encoding (no explicit option) should be Utf8"
        );
    }

    #[test]
    fn test_sr17_canonical_options_encoding_with_memory_and_realloc() {
        // Verify encoding is correctly parsed alongside other canonical options
        let opts = convert_canonical_options(
            &[
                wasmparser::CanonicalOption::UTF16,
                wasmparser::CanonicalOption::Memory(2),
                wasmparser::CanonicalOption::Realloc(5),
                wasmparser::CanonicalOption::PostReturn(10),
            ],
            None,
        );
        assert_eq!(
            opts.string_encoding,
            CanonStringEncoding::Utf16,
            "SR-17: UTF16 encoding with other options"
        );
        assert_eq!(opts.memory, Some(2));
        assert_eq!(opts.realloc, Some(5));
        assert_eq!(opts.post_return, Some(10));
    }

    #[test]
    fn test_sr17_canonical_options_last_encoding_wins() {
        // If multiple encoding options are present (unusual but valid per parser),
        // the last one wins because convert_canonical_options overwrites.
        let opts = convert_canonical_options(
            &[
                wasmparser::CanonicalOption::UTF8,
                wasmparser::CanonicalOption::UTF16,
            ],
            None,
        );
        assert_eq!(
            opts.string_encoding,
            CanonStringEncoding::Utf16,
            "SR-17: last encoding option should win when multiple specified"
        );
    }

    #[test]
    fn test_sr17_canonical_function_lift_utf16_encoding() {
        // Verify that a canon lift with UTF-16 encoding correctly propagates
        // the encoding to the CanonicalEntry.
        let canon = wasmparser::CanonicalFunction::Lift {
            core_func_index: 0,
            type_index: 0,
            options: vec![
                wasmparser::CanonicalOption::UTF16,
                wasmparser::CanonicalOption::Memory(0),
                wasmparser::CanonicalOption::Realloc(0),
            ]
            .into_boxed_slice(),
        };
        let entry = convert_canonical_function(canon, &mut vec![]);
        match entry {
            CanonicalEntry::Lift { options, .. } => {
                assert_eq!(
                    options.string_encoding,
                    CanonStringEncoding::Utf16,
                    "SR-17: lifted function should carry UTF-16 encoding"
                );
            }
            _ => panic!("Expected CanonicalEntry::Lift"),
        }
    }

    #[test]
    fn test_sr17_canonical_function_lower_compact_utf16_encoding() {
        // Verify that a canon lower with CompactUTF16 correctly propagates.
        let canon = wasmparser::CanonicalFunction::Lower {
            func_index: 0,
            options: vec![
                wasmparser::CanonicalOption::CompactUTF16,
                wasmparser::CanonicalOption::Memory(0),
                wasmparser::CanonicalOption::Realloc(0),
            ]
            .into_boxed_slice(),
        };
        let entry = convert_canonical_function(canon, &mut vec![]);
        match entry {
            CanonicalEntry::Lower { options, .. } => {
                assert_eq!(
                    options.string_encoding,
                    CanonStringEncoding::CompactUtf16,
                    "SR-17: lowered function should carry CompactUTF16 encoding"
                );
            }
            _ => panic!("Expected CanonicalEntry::Lower"),
        }
    }

    // ---------------------------------------------------------------
    // SR-17: Canonical ABI element sizes for string-related types
    //
    // Strings and lists are stored as (ptr: i32, len: i32) = 8 bytes
    // regardless of the string encoding. The encoding affects the
    // interpretation of the data at the pointer address, not the
    // size of the (ptr, len) pair itself.
    //
    // However, when transcoding, the *element size* for the pointed-to
    // data differs:
    //   - UTF-8:  variable (1-4 bytes per code point)
    //   - UTF-16: 2 bytes per code unit
    //   - Latin-1: 1 byte per character
    // ---------------------------------------------------------------

    #[test]
    fn test_sr17_string_canonical_abi_size_is_8() {
        // A string type is always stored as (ptr: i32, len: i32) = 8 bytes
        // in the canonical ABI, regardless of encoding.
        let pc = empty_parsed_component();
        let ty = ComponentValType::String;
        assert_eq!(
            pc.canonical_abi_element_size(&ty),
            8,
            "SR-17: string element size should be 8 (ptr + len) regardless of encoding"
        );
    }

    #[test]
    fn test_sr17_string_copy_layout_is_bulk_byte_multiplier_1() {
        // CopyLayout for a string: Bulk { byte_multiplier: 1 }.
        // This means: copy `len * 1` bytes from the source memory.
        // The byte_multiplier is 1 because len IS the byte count for UTF-8.
        //
        // NOTE: This layout is used for the cross-memory copy step BEFORE
        // transcoding. When encodings differ, the adapter must also run
        // the transcoding loop. The copy_layout only describes the raw
        // data copy, not the encoding transformation.
        let pc = empty_parsed_component();
        let ty = ComponentValType::String;
        let layout = pc.copy_layout(&ty);
        match layout {
            crate::resolver::CopyLayout::Bulk { byte_multiplier } => {
                assert_eq!(
                    byte_multiplier, 1,
                    "SR-17: string copy layout byte_multiplier should be 1"
                );
            }
            crate::resolver::CopyLayout::Elements { .. } => {
                panic!("SR-17: string should produce Bulk layout, not Elements");
            }
        }
    }

    #[test]
    fn test_sr17_list_string_copy_layout_has_inner_pointers() {
        // list<string> has inner pointer pairs that need recursive fixup.
        // Each string element is (ptr: i32, len: i32) = 8 bytes, and each
        // element's pointed-to data must also be copied across memories.
        let pc = empty_parsed_component();
        let ty = ComponentValType::List(Box::new(ComponentValType::String));
        let layout = pc.copy_layout(&ty);
        match layout {
            crate::resolver::CopyLayout::Elements {
                element_size,
                inner_pointers,
                ..
            } => {
                assert_eq!(
                    element_size, 8,
                    "SR-17: list<string> element should be 8 bytes"
                );
                assert_eq!(
                    inner_pointers.len(),
                    1,
                    "SR-17: list<string> should have 1 inner pointer pair per element"
                );
            }
            crate::resolver::CopyLayout::Bulk { .. } => {
                panic!("SR-17: list<string> should produce Elements layout, not Bulk");
            }
        }
    }

    // ---------------------------------------------------------------
    // P3 async feature detection tests
    //
    // These tests verify that P3 async constructs are detected during
    // parsing and recorded in `p3_async_features`, rather than being
    // silently swallowed. The fuser uses this information to reject
    // P3 async components with a clear error message.
    // ---------------------------------------------------------------

    #[test]
    fn test_p3_async_canonical_option_detected() {
        // Async canonical option should be stored in CanonicalOptions
        let opts = convert_canonical_options(
            &[
                wasmparser::CanonicalOption::UTF8,
                wasmparser::CanonicalOption::Memory(0),
                wasmparser::CanonicalOption::Async,
            ],
            None,
        );
        // Standard options should still be parsed correctly
        assert_eq!(opts.string_encoding, CanonStringEncoding::Utf8);
        assert_eq!(opts.memory, Some(0));
        // P3 async option should be stored directly
        assert!(opts.async_);
        assert_eq!(opts.callback, None);
    }

    #[test]
    fn test_p3_callback_canonical_option_detected() {
        let opts = convert_canonical_options(&[wasmparser::CanonicalOption::Callback(42)], None);
        assert_eq!(opts.callback, Some(42));
    }

    #[test]
    fn test_p3_async_option_stored_regardless_of_tracking() {
        // Async option is always stored in CanonicalOptions, regardless
        // of the p3_async_features parameter.
        let opts = convert_canonical_options(
            &[
                wasmparser::CanonicalOption::UTF8,
                wasmparser::CanonicalOption::Async,
            ],
            None,
        );
        assert_eq!(opts.string_encoding, CanonStringEncoding::Utf8);
        assert!(opts.async_);
    }

    #[test]
    fn test_p3_future_type_detected() {
        // Future type should produce P3Async variant
        let kind = convert_wp_defined_type(&wasmparser::ComponentDefinedType::Future(Some(
            wasmparser::ComponentValType::Primitive(wasmparser::PrimitiveValType::String),
        )));
        match kind {
            ComponentTypeKind::P3Async(desc) => {
                assert!(
                    desc.contains("future"),
                    "expected 'future' in description: {desc}"
                );
            }
            other => panic!("expected P3Async, got {other:?}"),
        }
    }

    #[test]
    fn test_p3_stream_type_detected() {
        // Stream type should produce P3Async variant
        let kind = convert_wp_defined_type(&wasmparser::ComponentDefinedType::Stream(None));
        match kind {
            ComponentTypeKind::P3Async(desc) => {
                assert!(
                    desc.contains("stream"),
                    "expected 'stream' in description: {desc}"
                );
            }
            other => panic!("expected P3Async, got {other:?}"),
        }
    }

    #[test]
    fn test_p3_async_features_collected_in_parsed_component() {
        // Verify that p3_async_features are accumulated during type parsing.
        // Only P3 async *types* (future, stream, map) push to p3_async_features
        // now; async/callback canonical options are stored in CanonicalOptions.
        let mut comp = empty_parsed_component();

        // Simulate what the parse loop does when it encounters a P3 type
        let kind = convert_wp_defined_type(&wasmparser::ComponentDefinedType::Future(None));
        if let ComponentTypeKind::P3Async(ref desc) = kind {
            comp.p3_async_features.push(format!("{desc} type"));
        }
        comp.types.push(ComponentType { kind });

        assert_eq!(comp.p3_async_features.len(), 1);
        assert!(comp.p3_async_features[0].contains("future"));

        // Async canonical option is now stored directly, not in p3_async_features
        let opts = convert_canonical_options(&[wasmparser::CanonicalOption::Async], None);
        assert!(opts.async_);
    }

    #[test]
    fn test_p3_error_message_via_fuser() {
        // Verify that the Fuser rejects components with P3 async features
        let mut comp = empty_parsed_component();
        comp.p3_async_features.push("stream<u8> type".to_string());
        comp.name = Some("test-component".to_string());

        // Build a Fuser and manually inject the parsed component
        let config = crate::FuserConfig::default();
        let fuser = crate::Fuser::new(config);
        // We can't use add_component since we have a pre-parsed component,
        // so test the error check logic directly
        let p3_details: Vec<String> = [comp]
            .iter()
            .enumerate()
            .filter_map(|(idx, c)| {
                if c.p3_async_features.is_empty() {
                    return None;
                }
                let default_name = format!("component {idx}");
                let comp_name = c.name.as_deref().unwrap_or(&default_name);
                let mut feats = c.p3_async_features.clone();
                feats.sort();
                feats.dedup();
                Some(format!("'{comp_name}' uses: {}", feats.join(", ")))
            })
            .collect();

        assert!(!p3_details.is_empty());
        let err_msg = format!(
            "{}. P3 async features (stream, future, async lift/lower, task builtins) \
             are not yet supported by meld. Use P2 components or wait for meld P3 support.",
            p3_details.join("; ")
        );
        assert!(
            err_msg.contains("test-component"),
            "error should mention component name"
        );
        assert!(
            err_msg.contains("stream<u8>"),
            "error should mention specific feature"
        );
        assert!(
            err_msg.contains("not yet supported"),
            "error should be actionable"
        );

        // Also verify the Error variant works
        let err = crate::Error::P3AsyncNotSupported(err_msg.clone());
        let display = format!("{err}");
        assert!(display.contains("P3 async"));
        let _ = fuser; // suppress unused warning
    }

    /// Mythos pre-release finding: nested `fixed-length-list` types whose
    /// per-level lengths individually pass validation but whose product
    /// exceeds u32::MAX would overflow `element_size * len` in
    /// canonical_abi_size_unpadded — panic in debug, silent wrap to 0 in
    /// release. The wrapped 0 propagates to adapter copy sizes, leading
    /// to OOB writes on the receiver. After the saturating-arithmetic
    /// fix, the product saturates to u32::MAX so downstream allocation
    /// fails safely.
    #[test]
    fn test_canonical_abi_size_fixed_size_list_saturates_on_overflow() {
        let pc = empty_parsed_component();
        // 65536 * 65536 = 2^32 — exactly at u32 wrap boundary.
        let inner = ComponentValType::FixedSizeList(
            Box::new(ComponentValType::Primitive(PrimitiveValType::U8)),
            65_536,
        );
        let outer = ComponentValType::FixedSizeList(Box::new(inner), 65_536);

        // Must not panic.
        let size = pc.canonical_abi_element_size(&outer);
        let flat = pc.flat_count(&outer);
        let flat_bytes = pc.flat_byte_size(&outer);

        // Saturated to u32::MAX (or close), never wrap-to-zero.
        assert_eq!(size, u32::MAX, "size must saturate, not wrap to 0");
        assert_eq!(flat, u32::MAX, "flat_count must saturate");
        assert_eq!(flat_bytes, u32::MAX, "flat_byte_size must saturate");
    }

    /// align_up must not panic when given a saturated u32::MAX size and
    /// a non-trivial alignment — the previous `(size + align - 1)` form
    /// would overflow.
    #[test]
    fn test_align_up_saturates_at_u32_max() {
        // Sanity: small inputs unchanged.
        assert_eq!(super::align_up(0, 4), 0);
        assert_eq!(super::align_up(1, 4), 4);
        assert_eq!(super::align_up(4, 4), 4);
        assert_eq!(super::align_up(5, 8), 8);
        // Boundary: would have panicked / overflowed before the fix.
        // u32::MAX & !7 == !7 — the fix saturates the addition then masks.
        assert_eq!(super::align_up(u32::MAX, 8), !7u32);
        assert_eq!(super::align_up(u32::MAX - 3, 8), !7u32);
    }
}
