//! Per-import host contract for `meld fuse --emit-import-map` (#513).
//!
//! A host that implements the fused module's function imports needs, for every
//! import, the memory its pointer arguments index, the `cabi_realloc` it must
//! allocate results with, and the string encoding of its string arguments.
//! Since #484/#490 meld resolves exactly those three from each import's OWN
//! source `canon lower` (`MergedModule::import_lower_sites`), not from a
//! per-component default. This module reports that resolution, so the host is
//! told what the component wrapper would have used.
//!
//! # Null versus unknown
//!
//! * [`LowerOption::Absent`] (JSON `null`) means a lower was traced and it has
//!   NO such option, so the import cannot touch a memory / allocate.
//! * [`LowerOption::Unknown`] (JSON `{"unknown": "<reason>"}`) means meld could
//!   not establish the lower's options at all. This is deliberately NOT
//!   `null`: a host reading `null` as "no memory" would silently mis-read
//!   pointers, which is the failure class `--memory multi` refuses to ship (the
//!   component wrapper errors on the same input). A consumer that indexes
//!   `["index"]` into an `unknown` object fails loudly instead.
//!
//! No index is ever guessed: `index` / `func` come only from the lower's own
//! option, resolved through the merger's index maps.

use crate::merger::MergedModule;
use crate::parser::{CanonStringEncoding, ParsedComponent};

/// One lower-derived option of an import.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LowerOption<T> {
    /// The lower was traced and names no such option (JSON `null`).
    Absent,
    /// The lower's option, resolved.
    Present(T),
    /// The lower could not be traced or resolved; the reason says why.
    Unknown(String),
}

/// A fused memory an import's pointers refer to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryRef {
    /// Fused memory index (the module's memory index space).
    pub index: u32,
    /// A memory export of the fused module with that index, if any.
    pub export: Option<String>,
}

/// A fused `cabi_realloc` an import allocates with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReallocRef {
    /// Fused function index of the allocator.
    pub func: u32,
    /// A function export of the fused module with that index, if any.
    pub export: Option<String>,
}

/// A resource intrinsic left as an import.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResourceInfo {
    /// `new`, `rep` or `drop`.
    pub operation: &'static str,
    /// Resource type name, without any `$N` dedup suffix.
    pub resource: String,
    /// Interface the resource lives in (the module name, `[export]` stripped).
    pub interface: String,
    /// The importer defines the resource (module carried an `[export]` prefix).
    pub definer: bool,
    /// The `<interface>#[dtor]<resource>` export, when exactly one candidate
    /// is identifiable.
    pub dtor_export: Option<String>,
    /// All `[dtor]` exports that could be this resource's, when `dtor_export`
    /// is `None` because there are several.
    pub dtor_candidates: Vec<String>,
}

/// Everything a host needs to know about one fused function import.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportMapEntry {
    /// Function index within the fused module's function index space.
    pub index: u32,
    pub module: String,
    pub name: String,
    /// Flattened component that owns the import (the `N` of a `$N` suffix).
    pub component: Option<usize>,
    /// Other components whose identical lowers were merged into this import
    /// (shared-memory dedup). Empty under `--memory multi`.
    pub also_components: Vec<usize>,
    pub memory: LowerOption<MemoryRef>,
    pub realloc: LowerOption<ReallocRef>,
    /// `utf8`, `utf16` or `latin1+utf16`.
    pub encoding: LowerOption<&'static str>,
    pub resource: Option<ResourceInfo>,
}

/// What the final core module exposes, parsed from its own bytes so the names
/// are the ones a host will really see.
#[derive(Default)]
struct CoreView {
    func_imports: Vec<(String, String)>,
    memory_count: usize,
    memory_exports: Vec<(String, u32)>,
    func_exports: Vec<(String, u32)>,
}

fn core_view(core: &[u8]) -> CoreView {
    use wasmparser::{ExternalKind, Parser, Payload, TypeRef};
    let mut v = CoreView::default();
    for payload in Parser::new(0).parse_all(core).flatten() {
        match payload {
            Payload::ImportSection(r) => {
                for imp in r.into_imports().flatten() {
                    match imp.ty {
                        TypeRef::Func(_) | TypeRef::FuncExact(_) => {
                            v.func_imports
                                .push((imp.module.to_string(), imp.name.to_string()));
                        }
                        TypeRef::Memory(_) => v.memory_count += 1,
                        _ => {}
                    }
                }
            }
            Payload::MemorySection(r) => v.memory_count += r.count() as usize,
            Payload::ExportSection(r) => {
                for e in r.into_iter().flatten() {
                    match e.kind {
                        ExternalKind::Memory => {
                            v.memory_exports.push((e.name.to_string(), e.index))
                        }
                        ExternalKind::Func | ExternalKind::FuncExact => {
                            v.func_exports.push((e.name.to_string(), e.index))
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
    v
}

fn encoding_name(e: CanonStringEncoding) -> &'static str {
    match e {
        CanonStringEncoding::Utf8 => "utf8",
        CanonStringEncoding::Utf16 => "utf16",
        CanonStringEncoding::CompactUtf16 => "latin1+utf16",
    }
}

/// `[resource-new]` / `[resource-rep]` / `[resource-drop]` intrinsic parts.
fn resource_op(name: &str) -> Option<(&'static str, &str)> {
    [
        ("new", "[resource-new]"),
        ("rep", "[resource-rep]"),
        ("drop", "[resource-drop]"),
    ]
    .into_iter()
    .find_map(|(op, p)| name.strip_prefix(p).map(|rest| (op, rest)))
}

fn resource_info(
    view: &CoreView,
    module: &str,
    name: &str,
    component: Option<usize>,
) -> Option<ResourceInfo> {
    let (operation, rest) = resource_op(name)?;
    let resource = crate::merger::strip_dollar_suffix(rest).to_string();
    let (interface, definer) = match module.strip_prefix("[export]") {
        Some(i) => (i.to_string(), true),
        None => (module.to_string(), false),
    };
    let exact = format!("{interface}#[dtor]{resource}");
    let dollar = format!("{exact}$");
    let mut cands: Vec<String> = view
        .func_exports
        .iter()
        .filter(|(n, _)| {
            *n == exact
                || n.strip_prefix(&dollar)
                    .is_some_and(|s| !s.is_empty() && s.chars().all(|c| c.is_ascii_digit()))
        })
        .map(|(n, _)| n.clone())
        .collect();
    cands.sort();
    cands.dedup();
    // The definer's own dtor carries the definer's `$N` when dtors were
    // deduplicated per component.
    let dtor_export = match (cands.len(), definer, component) {
        (1, _, _) => Some(cands[0].clone()),
        (_, true, Some(c)) => {
            let want = format!("{exact}${c}");
            cands.iter().find(|n| **n == want).cloned()
        }
        _ => None,
    };
    let dtor_candidates = if dtor_export.is_none() {
        cands
    } else {
        Vec::new()
    };
    Some(ResourceInfo {
        operation,
        resource,
        interface,
        definer,
        dtor_export,
        dtor_candidates,
    })
}

/// Build the per-import map for the fused core module `core`.
///
/// `components` is the flattened component list the merger numbered.
pub fn build_import_map(
    components: &[ParsedComponent],
    merged: &MergedModule,
    core: &[u8],
) -> Vec<ImportMapEntry> {
    let view = core_view(core);
    let func_imports: Vec<&crate::merger::MergedImport> = merged
        .imports
        .iter()
        .filter(|i| matches!(i.entity_type, wasm_encoder::EntityType::Function(_)))
        .collect();
    let aligned = func_imports.len() == view.func_imports.len()
        && func_imports
            .iter()
            .zip(&view.func_imports)
            .all(|(m, (module, name))| m.module == *module && m.name == *name);

    let mem_export = |index: u32| {
        view.memory_exports
            .iter()
            .find(|(_, i)| *i == index)
            .map(|(n, _)| n.clone())
    };
    // Prefer a `cabi_realloc*` name when several exports carry the function.
    let func_export = |index: u32| {
        view.func_exports
            .iter()
            .find(|(n, i)| *i == index && n.starts_with("cabi_realloc"))
            .or_else(|| view.func_exports.iter().find(|(_, i)| *i == index))
            .map(|(n, _)| n.clone())
    };

    view.func_imports
        .iter()
        .enumerate()
        .map(|(i, (module, name))| {
            let mut entry = ImportMapEntry {
                index: i as u32,
                module: module.clone(),
                name: name.clone(),
                component: None,
                also_components: Vec::new(),
                memory: LowerOption::Absent,
                realloc: LowerOption::Absent,
                encoding: LowerOption::Absent,
                resource: None,
            };
            let unknown = |entry: &mut ImportMapEntry, why: String| {
                entry.memory = LowerOption::Unknown(why.clone());
                entry.realloc = LowerOption::Unknown(why.clone());
                entry.encoding = LowerOption::Unknown(why);
            };
            if !aligned {
                unknown(
                    &mut entry,
                    "the merger's import list does not line up with the emitted module".into(),
                );
                return entry;
            }
            let own = func_imports[i];
            entry.component = own.component_idx;
            entry.resource = resource_info(&view, module, name, own.component_idx);
            // A resource intrinsic is a canonical builtin, not a lower: it has
            // no memory, realloc or string option to report.
            if entry.resource.is_some() {
                return entry;
            }
            let Some(slot) = merged.import_lower_sites.get(i) else {
                unknown(&mut entry, "no lower was recorded for this import".into());
                return entry;
            };
            for &(c, _) in &slot.sites {
                if Some(c) != entry.component && !entry.also_components.contains(&c) {
                    entry.also_components.push(c);
                }
            }
            entry.also_components.sort_unstable();
            if slot.sites.is_empty() {
                let why = match slot.untraced.first() {
                    Some(who) => format!("the canon lower of {who} could not be traced"),
                    None => "not a canon lower (a synthesized builtin); its options are not \
                             recorded"
                        .to_string(),
                };
                unknown(&mut entry, why);
                return entry;
            }
            if slot.members > 1
                && let Some(who) = slot.untraced.first()
            {
                unknown(
                    &mut entry,
                    format!(
                        "this import merges {} imports and the canon lower of {who} could not \
                         be traced",
                        slot.members
                    ),
                );
                return entry;
            }
            match crate::component_wrap::resolve_lower_spec(
                components,
                merged,
                view.memory_count,
                &slot.sites,
            ) {
                Ok(Some(spec)) => {
                    entry.memory = match spec.memory {
                        Some(index) => LowerOption::Present(MemoryRef {
                            index,
                            export: mem_export(index),
                        }),
                        None => LowerOption::Absent,
                    };
                    entry.realloc = match spec.realloc {
                        Some(func) => LowerOption::Present(ReallocRef {
                            func,
                            export: func_export(func),
                        }),
                        None => LowerOption::Absent,
                    };
                    entry.encoding = LowerOption::Present(encoding_name(spec.encoding));
                }
                Ok(None) => unknown(&mut entry, "no canon lower could be traced".into()),
                Err(e) => unknown(&mut entry, e.to_string()),
            }
            entry
        })
        .collect()
}
