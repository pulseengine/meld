//! Component parsing using wasmparser
//!
//! This module handles parsing WebAssembly P2/P3 components and extracting
//! the core modules, types, imports, and exports needed for fusion.

use crate::{Error, Result};
use wasmparser::{
    ComponentExternalKind, ComponentTypeRef, ExternalKind, Parser, Payload,
    ValType as WasmValType,
};
use wasm_encoder::ValType;

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

    /// Original size in bytes
    pub original_size: usize,
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
    /// Other type (resource, etc.)
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

        let mut component = ParsedComponent {
            name: None,
            core_modules: Vec::new(),
            imports: Vec::new(),
            exports: Vec::new(),
            types: Vec::new(),
            instances: Vec::new(),
            original_size: bytes.len(),
        };

        let parser = Parser::new(0);

        for payload in parser.parse_all(bytes) {
            let payload = payload?;
            self.handle_payload(payload, &mut component, bytes)?;
        }

        if component.core_modules.is_empty() {
            return Err(Error::NoCoreModules);
        }

        Ok(component)
    }

    /// Handle a single payload from the parser
    fn handle_payload(
        &self,
        payload: Payload<'_>,
        component: &mut ParsedComponent,
        _full_bytes: &[u8],
    ) -> Result<()> {
        match payload {
            Payload::Version { .. } => {
                // Already handled
            }

            Payload::ModuleSection { parser, unchecked_range } => {
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
                for import in reader {
                    let import = import?;
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
                for (idx, instance) in reader.into_iter().enumerate() {
                    let instance = instance?;
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
                                .map(|export| {
                                    (export.name.to_string(), export.kind, export.index)
                                })
                                .collect();
                            InstanceKind::FromExports(parsed)
                        }
                    };
                    component.instances.push(ComponentInstance {
                        index: idx as u32,
                        kind,
                    });
                }
            }

            Payload::ComponentTypeSection(reader) => {
                for ty in reader {
                    let ty = ty?;
                    let kind = match ty {
                        wasmparser::ComponentType::Defined(_) => ComponentTypeKind::Other,
                        wasmparser::ComponentType::Func(_) => ComponentTypeKind::Other,
                        wasmparser::ComponentType::Component(_) => ComponentTypeKind::Other,
                        wasmparser::ComponentType::Instance(_) => ComponentTypeKind::Other,
                        wasmparser::ComponentType::Resource { .. } => ComponentTypeKind::Other,
                    };
                    component.types.push(ComponentType { kind });
                }
            }

            // Component sections we don't need to parse in detail
            Payload::ComponentCanonicalSection(_) => {}
            Payload::CoreTypeSection(_) => {}
            Payload::ComponentAliasSection(_) => {}
            Payload::ComponentSection { .. } => {}
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
                            if let wasmparser::CompositeInnerType::Func(ft) = &subtype.composite_type.inner {
                                module.types.push(FuncType {
                                    params: ft.params().iter().map(|t| convert_val_type(*t)).collect(),
                                    results: ft.results().iter().map(|t| convert_val_type(*t)).collect(),
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
                                initial: t.initial.into(),
                                maximum: t.maximum.map(|m| m.into()),
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
                            }),
                            wasmparser::TypeRef::Tag(_) => {
                                return Err(Error::UnsupportedFeature("exception handling tags".to_string()));
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
                            initial: table.ty.initial.into(),
                            maximum: table.ty.maximum.map(|m| m.into()),
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
                        module.globals.push(GlobalType {
                            content_type: convert_val_type(global.ty.content_type),
                            mutable: global.ty.mutable,
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
                                return Err(Error::UnsupportedFeature("exception handling tags".to_string()));
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
                    module.custom_sections.push((
                        reader.name().to_string(),
                        reader.data().to_vec(),
                    ));
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
    fn test_convert_val_types() {
        assert_eq!(convert_val_type(WasmValType::I32), ValType::I32);
        assert_eq!(convert_val_type(WasmValType::I64), ValType::I64);
        assert_eq!(convert_val_type(WasmValType::F32), ValType::F32);
        assert_eq!(convert_val_type(WasmValType::F64), ValType::F64);
    }
}
