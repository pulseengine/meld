//! P3 cooperative-thread built-ins: the producer ABI (#547, ADR-9).
//!
//! meld does not lower these. Each of the nine built-ins becomes a plain core
//! import of the fused module, under exactly the module/field name and core
//! type the producers (`wit-bindgen c --generate-threading-helpers`,
//! `wit-component`) emit, and the host runtime (kiln, pulseengine/kiln#620)
//! owns the semantics.
//!
//! The names and types below were read off real producer output (the clang C
//! thread components), not guessed; `tests/coop_threads_547.rs` re-derives
//! them from the fused modules.

use crate::parser::CanonicalEntry;
use wasm_encoder::ValType;

/// Import module every producer files the cooperative built-ins under.
pub const MODULE: &str = "$root";

/// Export name of the fused funcref table that `thread.new-indirect`'s
/// `fn_idx` indexes. The host reads it to find the start function.
pub const THREAD_TABLE_EXPORT: &str = "__meld_thread_table";

/// Field name of `thread.new-indirect` (producers append `-v0`).
pub const NEW_INDIRECT: &str = "[thread-new-indirect-v0]";

/// `(field, params, results)` of every cooperative built-in, in the order of
/// the canonical-ABI proposal. `thread.yield` is included: it is the same
/// pass-through as the other eight (it predates #547).
pub const BUILTINS: [(&str, &[ValType], &[ValType]); 9] = [
    (NEW_INDIRECT, &[ValType::I32, ValType::I32], &[ValType::I32]),
    ("[thread-index]", &[], &[ValType::I32]),
    ("[thread-yield]", &[], &[ValType::I32]),
    ("[thread-suspend]", &[], &[ValType::I32]),
    ("[thread-resume-later]", &[ValType::I32], &[]),
    (
        "[thread-suspend-then-resume]",
        &[ValType::I32],
        &[ValType::I32],
    ),
    (
        "[thread-yield-then-resume]",
        &[ValType::I32],
        &[ValType::I32],
    ),
    (
        "[thread-suspend-then-promote]",
        &[ValType::I32],
        &[ValType::I32],
    ),
    (
        "[thread-yield-then-promote]",
        &[ValType::I32],
        &[ValType::I32],
    ),
];

/// The producer field name for a cooperative-thread canonical entry.
pub fn producer_name(entry: &CanonicalEntry) -> Option<&'static str> {
    Some(match entry {
        CanonicalEntry::ThreadNewIndirect { .. } => NEW_INDIRECT,
        CanonicalEntry::ThreadIndex => "[thread-index]",
        CanonicalEntry::ThreadYield { .. } => "[thread-yield]",
        CanonicalEntry::ThreadSuspend => "[thread-suspend]",
        CanonicalEntry::ThreadResumeLater => "[thread-resume-later]",
        CanonicalEntry::ThreadSuspendThenResume => "[thread-suspend-then-resume]",
        CanonicalEntry::ThreadYieldThenResume => "[thread-yield-then-resume]",
        CanonicalEntry::ThreadSuspendThenPromote => "[thread-suspend-then-promote]",
        CanonicalEntry::ThreadYieldThenPromote => "[thread-yield-then-promote]",
        _ => return None,
    })
}

/// `true` if `(module, field)` names one of the nine cooperative built-ins.
///
/// Under `--memory multi` the merger gives the same `(module, field)` from a
/// second component a `$<component>` suffix so the pairs stay unique in the
/// binary (`[thread-index]$1`), exactly as it does for every other pass-through
/// built-in. The suffix is stripped before matching: it names the component
/// the call belongs to, not a different built-in.
pub fn is_builtin_import(module: &str, field: &str) -> bool {
    let base = crate::merger::strip_dollar_suffix(field);
    module == MODULE && BUILTINS.iter().any(|(name, _, _)| *name == base)
}

/// `true` if `(module, field)` is `thread.new-indirect` (any `$N` suffix).
pub fn is_new_indirect_import(module: &str, field: &str) -> bool {
    module == MODULE && crate::merger::strip_dollar_suffix(field) == NEW_INDIRECT
}

/// The fused funcref table `thread.new-indirect`'s `fn_idx` indexes (#547).
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ThreadTable {
    /// Table index in the fused module's table index space.
    pub index: u32,
    /// Export name the fused module carries it under
    /// ([`THREAD_TABLE_EXPORT`]).
    pub export: String,
}

/// Resolve the table every `thread.new-indirect` canon in `components` names
/// to its fused table index.
///
/// Returns `Ok(None)` when no component uses `thread.new-indirect`. Refuses
/// (never guesses) when a canon's table cannot be traced to a merged table, or
/// when two canons name two DIFFERENT fused tables: the host gets one
/// `__meld_thread_table` export, so it could not tell which table a given
/// `fn_idx` belongs to.
pub fn resolve_thread_table(
    components: &[crate::parser::ParsedComponent],
    merged: &crate::merger::MergedModule,
) -> crate::Result<Option<u32>> {
    use crate::Error;
    use crate::parser::ExportKind;

    // fused table index -> first component that named it
    let mut found: std::collections::BTreeMap<u32, usize> = std::collections::BTreeMap::new();
    for (comp_idx, comp) in components.iter().enumerate() {
        let mut sources = None;
        for entry in &comp.canonical_functions {
            let CanonicalEntry::ThreadNewIndirect { table_index, .. } = entry else {
                continue;
            };
            let sources = sources.get_or_insert_with(|| crate::resolver::core_table_sources(comp));
            let untraced = |why: &str| {
                Error::UnsupportedFeature(format!(
                    "thread.new-indirect in component {comp_idx} names core table \
                     {table_index}, which cannot be traced to a fused table ({why}); \
                     the host would not know which table its fn_idx indexes (ADR-9)"
                ))
            };
            let (mod_idx, export_name) = sources
                .get(table_index)
                .ok_or_else(|| untraced("not an alias of a core module's table export"))?;
            let module = comp
                .core_modules
                .get(*mod_idx)
                .ok_or_else(|| untraced("its module is not in the component"))?;
            let export = module
                .exports
                .iter()
                .find(|e| e.name == *export_name && e.kind == ExportKind::Table)
                .ok_or_else(|| untraced("the module has no such table export"))?;
            let fused = merged
                .table_index_map
                .get(&(comp_idx, *mod_idx, export.index))
                .ok_or_else(|| untraced("the merger did not map the table"))?;
            found.entry(*fused).or_insert(comp_idx);
        }
    }
    let mut it = found.iter();
    match (it.next(), it.next()) {
        (None, _) => Ok(None),
        (Some((&idx, _)), None) => Ok(Some(idx)),
        (Some((&a, &ca)), Some((&b, &cb))) => Err(Error::UnsupportedFeature(format!(
            "thread.new-indirect uses two different funcref tables (fused table {a} from \
             component {ca}, fused table {b} from component {cb}); the fused module exports one \
             `{THREAD_TABLE_EXPORT}`, so the host could not tell which table a start function \
             index belongs to (ADR-9)"
        ))),
    }
}

/// Indices of the components that declare any cooperative-thread built-in
/// other than `thread.yield`.
///
/// `thread.yield` is left out on purpose: it is also the plain P3 async yield,
/// predates #547, and components that use only it have always fused.
pub fn components_using_cooperative_threads(
    components: &[crate::parser::ParsedComponent],
) -> Vec<usize> {
    components
        .iter()
        .enumerate()
        .filter(|(_, c)| {
            c.canonical_functions.iter().any(|e| {
                producer_name(e).is_some() && !matches!(e, CanonicalEntry::ThreadYield { .. })
            })
        })
        .map(|(i, _)| i)
        .collect()
}
