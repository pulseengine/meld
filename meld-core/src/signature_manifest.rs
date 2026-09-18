//! Signature manifest (#400) — what a host needs to invoke a fused export.
//!
//! Fusing a component to a core module drops the WIT type information, so a
//! runtime that does not know the component's shape at build time cannot
//! invoke its exports. bytecodealliance/rfcs#46 names that case ("the shape of
//! the component is not known ahead of time") and leaves it open; its primary
//! path, `host-wit-bindgen`, generates bindings from the WIT world at host
//! build time and does not serve a generic invoker like kiln. This manifest
//! fills that gap: the dynamic-case complement, not meld's type story in
//! general.
//!
//! ## The property that makes it worth carrying
//!
//! Each entry states the WIT signature **and** the core signature meld
//! actually emitted, so a consumer can cross-check its own lowering instead of
//! trusting ours. That only holds if the two come from different places:
//!
//! - [`ExportSignature::wit`] is computed from the component's WIT types.
//! - [`ExportSignature::core`] is **read back from the emitted module bytes**.
//!
//! If `core` were derived from the same WIT tree, the two would agree by
//! construction, the cross-check would always pass, and the field would be
//! decoration. kiln fails loud on disagreement rather than preferring one.
//!
//! ## Why the shape cannot be read from `core` alone
//!
//! `f(x: u32) -> u32` and a function taking 18 flattened `f32` both lower to
//! `(i32) -> i32`: in the first the `i32` is a value, in the second a pointer
//! to an argument area. Only the WIT says which. That is why
//! [`ExportSignature::flat_param_count`] and [`ExportSignature::needs`] are
//! here — without them a host cannot tell the two apart, and the Canonical ABI
//! passes garbage rather than erroring (kiln 0.5.0 accepted an arbitrary
//! integer for a pointer parameter and reported success).
//!
//! Field names follow component-model#378 (`BuildTargets.md`), which defines
//! an export's core type as `flatten_functype(ft, 'lift')` and derives
//! `needs.memory` / `needs.realloc` — it has no "calling shape" vocabulary, so
//! this manifest invents none.
//!
//! ## Never guess
//!
//! An export whose WIT types do not fully resolve is **omitted**, with the
//! reason recorded in [`SignatureManifest::omitted`]. A sized-by-fallback
//! entry is what #393 shipped as "4 bytes" and got wrong answers from; an
//! absent entry makes a host refuse rather than invoke on a guess.

use crate::merger::MergedModule;
use crate::parser::{ComponentTypeKind, ComponentValType, ParsedComponent, PrimitiveValType};
use serde::{Deserialize, Serialize};

/// Custom-section name carrying the JSON manifest.
pub const SECTION_NAME: &str = "meld.signature-manifest";

/// Manifest format version. A consumer that does not know this major version
/// refuses the manifest rather than best-effort parsing it (kiln's stated
/// reader behaviour).
pub const VERSION: u32 = 1;

/// `MAX_FLAT_PARAMS` from the Canonical ABI: above this, arguments are passed
/// through a pointer to an area the **callee's** `realloc` allocates.
pub const MAX_FLAT_PARAMS: u32 = 16;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SignatureManifest {
    pub version: u32,
    pub exports: Vec<ExportSignature>,
    /// Exports deliberately left out, with the reason. Never silently dropped:
    /// a host that finds its export here knows meld could not describe it.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub omitted: Vec<OmittedExport>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct OmittedExport {
    pub export: String,
    pub reason: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExportSignature {
    /// The name the fused module exports, exactly as emitted.
    pub export: String,
    pub wit: WitSignature,
    /// Read back from the emitted function type — never derived from `wit`.
    pub core: CoreSignature,
    /// Flattened parameter count per the Canonical ABI. Above
    /// [`MAX_FLAT_PARAMS`] the single core `i32` parameter is a pointer.
    pub flat_param_count: u32,
    pub needs: Needs,
    /// Exported name of the memory the lift uses, when one is needed.
    pub memory: Option<String>,
    /// Exported name of the allocator **this export's lift names**, resolved
    /// through fusion rather than matched by name. `None` when that function
    /// is not exported by the fused module: with `needs.realloc = true` that
    /// pair states a contradiction a host must refuse rather than paper over
    /// by calling some other exported allocator.
    pub realloc: Option<String>,
    pub post_return: Option<String>,
    pub return_area: Option<ReturnArea>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct WitSignature {
    /// `(name, rendered type)` per parameter, in order.
    pub params: Vec<(String, String)>,
    pub result: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CoreSignature {
    pub params: Vec<String>,
    pub results: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Needs {
    pub memory: bool,
    pub realloc: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ReturnArea {
    pub size: u32,
    pub align: u32,
    /// Top-level layout only. Nested layouts are deliberately absent rather
    /// than emitted from the spec alone: a consumer refuses to decode below
    /// the level described instead of inferring it.
    pub layout: Vec<LayoutEntry>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LayoutEntry {
    pub offset: u32,
    pub field: String,
    pub size: u32,
}

/// Render a WIT type structurally. `None` when a type reference does not
/// resolve — the caller omits the export rather than guessing (#393).
pub fn render_wit(component: &ParsedComponent, ty: &ComponentValType) -> Option<String> {
    Some(match ty {
        ComponentValType::Primitive(p) => render_primitive(p).to_string(),
        ComponentValType::String => "string".to_string(),
        ComponentValType::List(inner) => format!("list<{}>", render_wit(component, inner)?),
        ComponentValType::FixedSizeList(inner, n) => {
            format!("list<{}, {n}>", render_wit(component, inner)?)
        }
        ComponentValType::Record(fields) => {
            let mut out = Vec::with_capacity(fields.len());
            for (name, ty) in fields {
                out.push(format!("{name}: {}", render_wit(component, ty)?));
            }
            format!("record {{ {} }}", out.join(", "))
        }
        ComponentValType::Flags(names) => format!("flags {{ {} }}", names.join(", ")),
        ComponentValType::Variant(cases) => {
            let mut out = Vec::with_capacity(cases.len());
            for (name, payload) in cases {
                out.push(match payload {
                    Some(ty) => format!("{name}({})", render_wit(component, ty)?),
                    None => name.clone(),
                });
            }
            format!("variant {{ {} }}", out.join(", "))
        }
        ComponentValType::Tuple(types) => {
            let mut out = Vec::with_capacity(types.len());
            for ty in types {
                out.push(render_wit(component, ty)?);
            }
            format!("tuple<{}>", out.join(", "))
        }
        ComponentValType::Option(inner) => format!("option<{}>", render_wit(component, inner)?),
        ComponentValType::Result { ok, err } => {
            let ok = match ok {
                Some(t) => render_wit(component, t)?,
                None => "_".to_string(),
            };
            let err = match err {
                Some(t) => render_wit(component, t)?,
                None => "_".to_string(),
            };
            format!("result<{ok}, {err}>")
        }
        ComponentValType::Own(_) => "own<resource>".to_string(),
        ComponentValType::Borrow(_) => "borrow<resource>".to_string(),
        ComponentValType::Type(idx) => {
            // The #393 seam: a `use`d type that does not resolve was silently
            // sized at 4 bytes and produced wrong answers. Here it produces no
            // entry at all.
            // #393's resolver: follows ExportAlias AND InstanceExportAlias
            // hops, which is what a WIT `use types.{torque}` compiles to. Its
            // contract is that `None` means unknown, never a default size.
            let inner = component.resolve_defined_val_type(*idx)?;
            render_wit(component, &inner)?
        }
    })
}

fn render_primitive(p: &PrimitiveValType) -> &'static str {
    match p {
        PrimitiveValType::Bool => "bool",
        PrimitiveValType::S8 => "s8",
        PrimitiveValType::U8 => "u8",
        PrimitiveValType::S16 => "s16",
        PrimitiveValType::U16 => "u16",
        PrimitiveValType::S32 => "s32",
        PrimitiveValType::U32 => "u32",
        PrimitiveValType::S64 => "s64",
        PrimitiveValType::U64 => "u64",
        PrimitiveValType::F32 => "f32",
        PrimitiveValType::F64 => "f64",
        PrimitiveValType::Char => "char",
    }
}

/// Does lowering a value of this type into the guest require the guest's
/// allocator? Strings and lists do, wherever they appear (component-model#378
/// sets `needs.realloc` for them on the lift side).
pub fn needs_guest_allocation(component: &ParsedComponent, ty: &ComponentValType) -> bool {
    match ty {
        ComponentValType::String => true,
        ComponentValType::List(_) => true,
        ComponentValType::FixedSizeList(inner, _) => needs_guest_allocation(component, inner),
        ComponentValType::Record(fields) => fields
            .iter()
            .any(|(_, t)| needs_guest_allocation(component, t)),
        ComponentValType::Tuple(types) => {
            types.iter().any(|t| needs_guest_allocation(component, t))
        }
        ComponentValType::Variant(cases) => cases.iter().any(|(_, t)| {
            t.as_ref()
                .is_some_and(|t| needs_guest_allocation(component, t))
        }),
        ComponentValType::Option(inner) => needs_guest_allocation(component, inner),
        ComponentValType::Result { ok, err } => {
            ok.as_ref()
                .is_some_and(|t| needs_guest_allocation(component, t))
                || err
                    .as_ref()
                    .is_some_and(|t| needs_guest_allocation(component, t))
        }
        ComponentValType::Type(idx) => component
            .resolve_defined_val_type(*idx)
            .map(|inner| needs_guest_allocation(component, &inner))
            // Unresolvable: the export is omitted before this matters.
            .unwrap_or(false),
        _ => false,
    }
}

/// The exported names and core signatures of a fused module, read from its
/// bytes. This is the half of the manifest that must not come from the WIT.
#[derive(Debug, Default)]
pub struct EmittedExports {
    /// export name -> core signature
    pub funcs: std::collections::BTreeMap<String, CoreSignature>,
    /// export name -> function index
    pub func_indices: std::collections::BTreeMap<String, u32>,
    /// the first exported memory, if any
    pub memory: Option<String>,
}

/// Read every exported function's emitted type out of a core module.
pub fn emitted_exports(module_bytes: &[u8]) -> EmittedExports {
    use wasmparser::{Parser, Payload, TypeRef};

    let mut sigs: Vec<CoreSignature> = Vec::new();
    let mut func_type_idx: Vec<u32> = Vec::new();
    let mut imported_func_types: Vec<u32> = Vec::new();
    let mut out = EmittedExports::default();

    for payload in Parser::new(0).parse_all(module_bytes) {
        match payload {
            Ok(Payload::TypeSection(reader)) => {
                for rec_group in reader.into_iter().flatten() {
                    for sub_type in rec_group.into_types() {
                        if let wasmparser::CompositeInnerType::Func(ft) =
                            &sub_type.composite_type.inner
                        {
                            sigs.push(CoreSignature {
                                params: ft.params().iter().map(val_type_name).collect(),
                                results: ft.results().iter().map(val_type_name).collect(),
                            });
                        } else {
                            sigs.push(CoreSignature {
                                params: Vec::new(),
                                results: Vec::new(),
                            });
                        }
                    }
                }
            }
            Ok(Payload::ImportSection(reader)) => {
                for import in reader.into_imports().flatten() {
                    match import.ty {
                        TypeRef::Func(ti) | TypeRef::FuncExact(ti) => imported_func_types.push(ti),
                        _ => {}
                    }
                }
            }
            Ok(Payload::FunctionSection(reader)) => {
                func_type_idx.extend(reader.into_iter().flatten());
            }
            Ok(Payload::ExportSection(reader)) => {
                for export in reader.into_iter().flatten() {
                    match export.kind {
                        wasmparser::ExternalKind::Func => {
                            out.func_indices
                                .insert(export.name.to_string(), export.index);
                        }
                        wasmparser::ExternalKind::Memory => {
                            out.memory.get_or_insert_with(|| export.name.to_string());
                        }
                        _ => {}
                    }
                }
            }
            Ok(_) => {}
            Err(_) => break,
        }
    }

    let imported = imported_func_types.len();
    for (name, index) in &out.func_indices {
        let type_idx = if (*index as usize) < imported {
            imported_func_types.get(*index as usize).copied()
        } else {
            func_type_idx.get(*index as usize - imported).copied()
        };
        if let Some(sig) = type_idx.and_then(|t| sigs.get(t as usize)) {
            out.funcs.insert(name.clone(), sig.clone());
        }
    }
    out
}

fn val_type_name(t: &wasmparser::ValType) -> String {
    match t {
        wasmparser::ValType::I32 => "i32",
        wasmparser::ValType::I64 => "i64",
        wasmparser::ValType::F32 => "f32",
        wasmparser::ValType::F64 => "f64",
        wasmparser::ValType::V128 => "v128",
        wasmparser::ValType::Ref(_) => "ref",
    }
    .to_string()
}

/// Which fused function index a component-local function ended up at, or
/// `None` when it was not merged into the output.
fn fused_index_of(merged: &MergedModule, origin: (usize, usize, u32)) -> Option<u32> {
    merged
        .functions
        .iter()
        .position(|f| f.origin == origin)
        .map(|defined_idx| merged.import_counts.func + defined_idx as u32)
}

/// Build the manifest for a fused module.
///
/// `components` is the flattened component list (the one the merger worked
/// from), `merged` gives origin → fused index, and `output_bytes` is the
/// module as emitted — the only source for `core`.
pub fn build(
    components: &[ParsedComponent],
    merged: &MergedModule,
    output_bytes: &[u8],
) -> SignatureManifest {
    let emitted = emitted_exports(output_bytes);
    let mut exports = Vec::new();
    let mut omitted = Vec::new();

    for (comp_idx, component) in components.iter().enumerate() {
        let lifts = component.lift_info_by_core_func();
        for (core_func_index, (type_index, options)) in lifts {
            let Some((export_name, mod_idx, local_idx)) =
                locate_core_func(component, core_func_index)
            else {
                continue;
            };
            // The fused module keeps the lifted export's name.
            let Some(core) = emitted.funcs.get(&export_name).cloned() else {
                continue;
            };
            let Some(def) = component.get_type_definition(type_index) else {
                omitted.push(OmittedExport {
                    export: export_name,
                    reason: "the lift's function type does not resolve".to_string(),
                });
                continue;
            };
            let ComponentTypeKind::Function { params, results } = &def.kind else {
                continue;
            };

            let mut wit_params = Vec::with_capacity(params.len());
            let mut unresolved = None;
            for (name, ty) in params {
                match render_wit(component, ty) {
                    Some(rendered) => wit_params.push((name.clone(), rendered)),
                    None => {
                        unresolved = Some(format!("parameter `{name}` has an unresolvable type"));
                        break;
                    }
                }
            }
            if let Some(reason) = unresolved {
                omitted.push(OmittedExport {
                    export: export_name,
                    reason,
                });
                continue;
            }

            let result_ty = results.first().map(|(_, ty)| ty.clone());
            let wit_result = match &result_ty {
                Some(ty) => match render_wit(component, ty) {
                    Some(rendered) => Some(rendered),
                    None => {
                        omitted.push(OmittedExport {
                            export: export_name,
                            reason: "the result type does not resolve".to_string(),
                        });
                        continue;
                    }
                },
                None => None,
            };

            let flat_param_count = component.total_flat_params(params);
            let return_area = result_ty.as_ref().and_then(|ty| {
                // One flat result is returned directly; more go through the
                // return area the callee owns.
                (component.flat_count(ty) > 1).then(|| ReturnArea {
                    size: component.canonical_abi_element_size(ty),
                    align: component.canonical_abi_align(ty),
                    layout: top_level_layout(component, ty),
                })
            });

            let needs = Needs {
                realloc: flat_param_count > MAX_FLAT_PARAMS
                    || params
                        .iter()
                        .any(|(_, ty)| needs_guest_allocation(component, ty)),
                memory: return_area.is_some()
                    || flat_param_count > MAX_FLAT_PARAMS
                    || params
                        .iter()
                        .any(|(_, ty)| needs_guest_allocation(component, ty)),
            };

            let realloc = options
                .realloc
                .and_then(|r| exported_name_of_core_func(component, comp_idx, merged, &emitted, r));
            let post_return = options
                .post_return
                .and_then(|p| exported_name_of_core_func(component, comp_idx, merged, &emitted, p));

            let _ = (mod_idx, local_idx);
            exports.push(ExportSignature {
                export: export_name,
                wit: WitSignature {
                    params: wit_params,
                    result: wit_result,
                },
                core,
                flat_param_count,
                needs,
                memory: needs.memory.then(|| emitted.memory.clone()).flatten(),
                realloc,
                post_return,
                return_area,
            });
        }
    }

    exports.sort_by(|a, b| a.export.cmp(&b.export));
    omitted.sort_by(|a, b| a.export.cmp(&b.export));
    SignatureManifest {
        version: VERSION,
        exports,
        omitted,
    }
}

/// The module export name, module index and module-local index of a
/// component-level core function.
fn locate_core_func(
    component: &ParsedComponent,
    core_func_index: u32,
) -> Option<(String, usize, u32)> {
    let sources = crate::resolver::core_func_sources(component);
    let (mod_idx, export_name) = sources.get(&core_func_index)?.clone();
    let local_idx = component
        .core_modules
        .get(mod_idx)?
        .exports
        .iter()
        .find(|e| e.name == export_name)
        .map(|e| e.index)?;
    Some((export_name, mod_idx, local_idx))
}

/// Resolve a component-level core function to the name the fused module
/// exports it under, **through fusion** — never by matching a likely name.
fn exported_name_of_core_func(
    component: &ParsedComponent,
    comp_idx: usize,
    merged: &MergedModule,
    emitted: &EmittedExports,
    core_func_index: u32,
) -> Option<String> {
    let (_, mod_idx, local_idx) = locate_core_func(component, core_func_index)?;
    let _ = component;
    let fused_idx = fused_index_of(merged, (comp_idx, mod_idx, local_idx))?;
    emitted
        .func_indices
        .iter()
        .find(|(_, idx)| **idx == fused_idx)
        .map(|(name, _)| name.clone())
}

/// Top-level `(offset, field, size)` of a value stored in memory.
fn top_level_layout(component: &ParsedComponent, ty: &ComponentValType) -> Vec<LayoutEntry> {
    let resolved = resolve_alias(component, ty);
    match resolved.as_ref().unwrap_or(ty) {
        ComponentValType::Record(fields) => {
            let mut out = Vec::with_capacity(fields.len());
            let mut offset = 0u32;
            for (name, field_ty) in fields {
                let align = component.canonical_abi_align(field_ty);
                offset = align_to(offset, align);
                let size = component.canonical_abi_element_size(field_ty);
                out.push(LayoutEntry {
                    offset,
                    field: name.clone(),
                    size,
                });
                offset = offset.saturating_add(size);
            }
            out
        }
        other => vec![LayoutEntry {
            offset: 0,
            field: "value".to_string(),
            size: component.canonical_abi_element_size(other),
        }],
    }
}

fn resolve_alias(component: &ParsedComponent, ty: &ComponentValType) -> Option<ComponentValType> {
    match ty {
        ComponentValType::Type(idx) => {
            let inner = component.resolve_defined_val_type(*idx)?;
            Some(resolve_alias(component, &inner).unwrap_or(inner))
        }
        _ => None,
    }
}

fn align_to(offset: u32, align: u32) -> u32 {
    if align <= 1 {
        return offset;
    }
    offset.div_ceil(align) * align
}
