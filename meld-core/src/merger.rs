//! Module merging for component fusion
//!
//! This module handles combining multiple core modules into a single module,
//! reindexing all references (functions, tables, memories, globals).
//!
//! # Proof-implementation gap
//!
//! The proof model in `merge_defs.v` assumes flat concatenation: every
//! module's imports are preserved verbatim and index spaces grow by the
//! full `import_count + defined_count` of each preceding module.
//!
//! This code, by contrast, *resolves* cross-component imports against
//! other modules' exports and only emits genuinely unresolved imports.
//! [`ImportCounts`] records how many unresolved imports remain so that
//! `function_index_map` values (and the other index maps) are absolute
//! wasm indices (`import_count + array_position`), not 0-based offsets.
//!
//! `proofs/transformations/merge/merge_resolution.v` bridges the gap by
//! showing that import resolution is a refinement of flat concatenation
//! that preserves the remap properties proved in `merge_defs.v`.

// Allow nested ifs for Bazel compatibility (rules_rust doesn't support if-let chains yet)
#![allow(clippy::collapsible_if)]

use crate::parser::{
    CoreModule, ExportKind, GlobalType, ImportKind, MemoryType, ParsedComponent, TableType,
};
use crate::resolver::DependencyGraph;
use crate::rewriter::{IndexMaps, convert_abstract_heap_type, rewrite_function_body};
use crate::{Error, MemoryStrategy, Result};
use std::collections::{HashMap, HashSet};
use wasm_encoder::{
    ConstExpr, EntityType, ExportKind as EncoderExportKind, Function,
    GlobalType as EncoderGlobalType, Instruction, MemoryType as EncoderMemoryType, RefType,
    TableType as EncoderTableType, ValType,
};

const WASM_PAGE_SIZE: u64 = 65536;

/// Pre-computed counts of unresolved imports by entity kind.
///
/// In the wasm binary, each index space is partitioned as
/// `[imports | defined entities]`.  These counts record how many
/// unresolved imports occupy the beginning of each index space so
/// that all index-map values can be absolute wasm indices rather
/// than 0-based array positions.
#[derive(Debug, Clone, Copy, Default)]
pub struct ImportCounts {
    pub func: u32,
    pub table: u32,
    pub memory: u32,
    pub global: u32,
}

/// A merged WebAssembly module ready for encoding
#[derive(Debug, Clone)]
pub struct MergedModule {
    /// Merged type section
    pub types: Vec<MergedFuncType>,

    /// Remaining imports (unresolved)
    pub imports: Vec<MergedImport>,

    /// Merged functions
    pub functions: Vec<MergedFunction>,

    /// Merged tables
    pub tables: Vec<EncoderTableType>,

    /// Merged memories
    pub memories: Vec<EncoderMemoryType>,

    /// Merged globals
    pub globals: Vec<MergedGlobal>,

    /// Merged exports
    pub exports: Vec<MergedExport>,

    /// Start function index (if any)
    pub start_function: Option<u32>,

    /// Element segments (parsed and reindexed)
    pub elements: Vec<crate::segments::ReindexedElementSegment>,

    /// Data segments (parsed and reindexed)
    pub data_segments: Vec<crate::segments::ReindexedDataSegment>,

    /// Custom sections
    pub custom_sections: Vec<(String, Vec<u8>)>,

    /// #328: fused function names accumulated from every input module's
    /// `name` section, with each function index already remapped into the
    /// fused function-index space (`function_index_map`). Emitted as ONE
    /// coalesced `name` section under `preserve_names` — replacing the old
    /// verbatim per-module copies (duplicate sections + stale indices).
    /// `BTreeMap` keeps the fused indices ascending (the order the
    /// name-section function-name subsection expects).
    pub fused_function_names: std::collections::BTreeMap<u32, String>,

    /// Index mapping for function references
    pub function_index_map: HashMap<(usize, usize, u32), u32>,

    /// Index mapping for memory references
    pub memory_index_map: HashMap<(usize, usize, u32), u32>,

    /// Index mapping for table references
    pub table_index_map: HashMap<(usize, usize, u32), u32>,

    /// Index mapping for global references
    pub global_index_map: HashMap<(usize, usize, u32), u32>,

    /// Index mapping for type references
    pub type_index_map: HashMap<(usize, usize, u32), u32>,

    /// Merged index of each module's cabi_realloc function, if exported
    /// Maps (component_idx, module_idx) -> merged function index
    pub realloc_map: HashMap<(usize, usize), u32>,

    /// Pre-computed counts of unresolved imports for each index space.
    /// All index-map values are offset by these counts so they represent
    /// absolute wasm indices rather than 0-based array positions.
    pub import_counts: ImportCounts,

    /// For each emitted function import (by position), the merged memory index
    /// that the importing component uses. Used by component_wrap to select the
    /// correct CanonicalOption::Memory(N) per import.
    pub import_memory_indices: Vec<u32>,

    /// For each emitted function import (by position), the merged function index
    /// of the component's cabi_realloc. Used by component_wrap to select the
    /// correct CanonicalOption::Realloc(N) per import.
    pub import_realloc_indices: Vec<Option<u32>>,

    /// Maps (component_idx, resource_name) → merged function index for [resource-rep].
    /// Used by adapter generation to find the correct component's [resource-rep]
    /// in multi-component chains where multiple components have the same resource.
    pub resource_rep_by_component: HashMap<(usize, String), u32>,

    /// Maps (component_idx, resource_name) → merged function index for [resource-new].
    pub resource_new_by_component: HashMap<(usize, String), u32>,

    /// Per-resource handle table info for re-exporters.
    /// Key is (owning_component_idx, interface, resource_name) — a single
    /// re-exporter component may have multiple entries when it re-exports
    /// multiple resources, and routing must discriminate per-resource so the
    /// re-exporter's own export resource gets a handle table while imports
    /// it passes through do not.
    pub handle_tables: HashMap<(usize, String, String), HandleTableInfo>,

    /// Task.return shim info: maps merged import index of [task-return]N
    /// to the global indices where the shim stores result values.
    /// Used by the callback-driving adapter to read results after EXIT.
    pub task_return_shims: HashMap<u32, TaskReturnShimInfo>,

    /// Maps (component_idx, func_name) → shim globals for async result delivery.
    /// Built after element segment patching. Used by the callback-driving adapter.
    pub async_result_globals: HashMap<(usize, String), Vec<(u32, ValType)>>,

    /// Per-module base offsets into the concatenated `data_segments` / `elements`
    /// vectors: maps (component_idx, module_idx) → (data_segment_base, elem_base).
    ///
    /// Recorded in `merge_core_module` at the point the module's `IndexMaps` is
    /// built — i.e. BEFORE this module's own segments are appended — so the base
    /// equals the count of segments contributed by all PRIOR modules, which is
    /// exactly where this module's local segment indices land in the fused
    /// section. Re-rewrite passes that run after the full merge (when `.len()`
    /// no longer equals the base) look the base up here.
    pub segment_bases: HashMap<(usize, usize), (u32, u32)>,
}

/// Info about a generated task.return shim function.
#[derive(Debug, Clone)]
pub struct TaskReturnShimInfo {
    /// Merged function index of the shim
    pub shim_func: u32,
    /// Global indices for each result value (in param order)
    pub result_globals: Vec<(u32, ValType)>,
    /// Source component index
    pub component_idx: usize,
    /// Fused import name (e.g., "[task-return]0")
    pub import_name: String,
    /// Original function name (e.g., "fibonacci") — extracted from the
    /// original component's core module import before renumbering.
    pub original_func_name: String,
    /// Lifted (WIT-level) result type. When present, the adapter uses this
    /// to compute element-aware byte counts and walk nested indirections
    /// (strings inside records inside lists) during cross-memory copy.
    /// `None` means we couldn't recover the type and the adapter falls
    /// back to treating the result as opaque bytes.
    pub result_type: Option<crate::parser::ComponentValType>,
}

/// Per-component resource handle table allocated in a re-exporter's linear memory.
///
/// Handles are 4-byte-aligned memory addresses into an i32 array, satisfying
/// wit-bindgen's `ResourceTable` alignment check (`value & 3 == 0`).
#[derive(Debug, Clone)]
pub struct HandleTableInfo {
    /// Merged memory index for this component
    pub memory_idx: u32,
    /// Merged global index for the next-allocation pointer
    pub next_ptr_global: u32,
    /// Base address in linear memory where the table starts
    pub table_base_addr: u32,
    /// Number of entry slots
    pub capacity: u32,
    /// Merged function index of ht_new (store rep, return handle)
    pub new_func: u32,
    /// Merged function index of ht_rep (load rep from handle)
    pub rep_func: u32,
    /// Merged function index of ht_drop (zero out entry)
    pub drop_func: u32,
}

/// Function type in merged module
#[derive(Debug, Clone)]
pub struct MergedFuncType {
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
}

/// Import in merged module
#[derive(Debug, Clone)]
pub struct MergedImport {
    pub module: String,
    pub name: String,
    pub entity_type: EntityType,
    /// Source component index (for routing resource imports to handle tables)
    pub component_idx: Option<usize>,
}

/// Function in merged module
#[derive(Debug, Clone)]
pub struct MergedFunction {
    /// Type index in merged type section
    pub type_idx: u32,
    /// Function body
    pub body: Function,
    /// Original location (component_idx, module_idx, function_idx)
    pub origin: (usize, usize, u32),
    /// What kind of meld-generated helper this is, when the function is
    /// synthetic (`origin` carries a sentinel). `None` for functions
    /// copied from input modules. Consumed by `dwarf::adapter_spans`
    /// for per-class `<meld-adapter>` attribution (#144 inc 4).
    pub synthetic_kind: Option<SyntheticKind>,
}

/// Kind of merger-emitted synthetic function (#144 inc 4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntheticKind {
    /// Per-resource handle-table helper (`ht_new` / `ht_rep` / `ht_drop`).
    HandleTable,
    /// Wrapper calling every input module's `start` function in order.
    StartWrapper,
    /// Type-coercion shim wrapping a call to a FACT adapter (i32/i64
    /// widening glue between the caller's import type and the adapter).
    AdapterShim,
    /// P3 async `task.return` shim storing results into result globals.
    TaskReturnShim,
    /// Cross-component stream-bridge shim (#141): per-component
    /// `stream_*` dispatch function emitted by `crate::p3_bridge` that
    /// routes locally-minted (bit-31-tagged) handles to the in-module
    /// bridge ring memory and forwards host handles to the retained
    /// `pulseengine:async` imports.
    StreamBridge,
}

/// Global in merged module
#[derive(Debug, Clone)]
pub struct MergedGlobal {
    pub ty: EncoderGlobalType,
    pub init_expr: ConstExpr,
}

/// Export in merged module
#[derive(Debug, Clone)]
pub struct MergedExport {
    pub name: String,
    pub kind: EncoderExportKind,
    pub index: u32,
}

impl MergedModule {
    /// Look up a defined function by its absolute wasm index.
    /// Returns `None` if the index refers to an imported function.
    pub fn defined_func(&self, wasm_idx: u32) -> Option<&MergedFunction> {
        if wasm_idx < self.import_counts.func {
            None
        } else {
            self.functions
                .get((wasm_idx - self.import_counts.func) as usize)
        }
    }
}

/// Pre-computed mapping from unresolved import identity to its
/// position in the merged import index space (per entity kind).
struct UnresolvedImportAssignments {
    func: HashMap<(usize, usize, String, String), u32>,
    global: HashMap<(usize, usize, String, String), u32>,
    table: HashMap<(usize, usize, String, String), u32>,
}

/// Dedup key type for unresolved imports.
///
/// In multi-memory mode, each component gets its own import slot even for
/// the same `(module, field)`, because each needs a different canon lower
/// with Memory(N) and Realloc(N). The optional `usize` is the component
/// index — `Some(comp_idx)` in multi-memory mode, `None` in shared-memory
/// mode (preserving existing dedup behavior).
type DedupKey = (String, String, Option<usize>);

/// Deduplication metadata for unresolved imports.
///
/// Tracks which effective `(module, field)` pairs have already been assigned
/// an import position and which WASI version string to use for each dedup key.
struct ImportDedupInfo {
    /// For each dedup key, the full module name with the highest WASI version
    /// seen across all occurrences.
    best_module_version: HashMap<DedupKey, String>,
    /// Entries where dedup was skipped because the function type didn't match
    /// the first occurrence with the same effective (module, field) key.
    /// Keyed by (component_idx, module_idx, module_name, field_name).
    type_mismatch_entries: HashSet<(usize, usize, String, String)>,
}

/// Strip `@major.minor.patch` version suffix from a WASI module name.
///
/// `"wasi:io/error@0.2.0"` → `"wasi:io/error"`; `"env"` → `"env"`
/// Build a unique export-name suffix for a per-resource handle table.
///
/// Combines component index, sanitised interface, and resource name into
/// one identifier. The interface sanitisation replaces ':', '/', '@', '.'
/// (illegal in WASM export names? all are legal but conventionally avoided)
/// with '_'.
/// Strip a trailing `$N` dedup suffix from a resource name. Meld appends
/// these when multiple components import the same `[resource-*]X` helper —
/// the canonical resource name (used for handle-table lookup and the
/// canonical-ABI) doesn't include the suffix.
pub(crate) fn strip_dollar_suffix(s: &str) -> &str {
    if let Some(dollar_pos) = s.rfind('$') {
        let suffix = &s[dollar_pos + 1..];
        if !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()) {
            return &s[..dollar_pos];
        }
    }
    s
}

pub(crate) fn ht_export_suffix(comp_idx: usize, interface: &str, resource_name: &str) -> String {
    let safe_iface: String = interface
        .chars()
        .map(|c| match c {
            ':' | '/' | '@' | '.' | '-' => '_',
            other => other,
        })
        .collect();
    format!("{}_{}_{}", comp_idx, safe_iface, resource_name)
}

fn normalize_wasi_module_name(name: &str) -> &str {
    match name.rfind('@') {
        Some(pos) if name[..pos].contains(':') => &name[..pos],
        _ => name,
    }
}

/// Compare two semver-like version strings.
///
/// Implements a small subset of [semver 2.0.0] precedence rules sufficient
/// for the WASI version strings meld encounters:
///
/// * Build metadata (`+...`) is ignored.
/// * The main `MAJOR.MINOR.PATCH` triple is compared numerically; missing
///   trailing segments default to `0` (so `"0.2"` == `"0.2.0"`).
/// * A version *with* a pre-release suffix sorts BEFORE the same version
///   without one (`0.2.0-rc1 < 0.2.0`).
/// * Pre-release identifiers are compared dot-segment-wise: numeric
///   identifiers numerically, alphanumeric identifiers lexically, and
///   numeric identifiers always sort below alphanumeric ones.
/// * Non-numeric main segments fall back to a lexical comparison of that
///   segment (covers exotic inputs like `"0.2.x"`).
///
/// [semver 2.0.0]: https://semver.org/spec/v2.0.0.html
fn compare_version(a: &str, b: &str) -> std::cmp::Ordering {
    use std::cmp::Ordering;

    // Strip build metadata: it does not affect precedence.
    fn strip_build(s: &str) -> &str {
        match s.find('+') {
            Some(i) => &s[..i],
            None => s,
        }
    }
    // Split off pre-release suffix on the first '-'.
    fn split_pre(s: &str) -> (&str, Option<&str>) {
        match s.find('-') {
            Some(i) => (&s[..i], Some(&s[i + 1..])),
            None => (s, None),
        }
    }

    let (main_a, pre_a) = split_pre(strip_build(a));
    let (main_b, pre_b) = split_pre(strip_build(b));

    // Compare the MAJOR.MINOR.PATCH... segments. Treat missing trailing
    // segments as 0 so "0.2" == "0.2.0".
    let segs_a: Vec<&str> = main_a.split('.').collect();
    let segs_b: Vec<&str> = main_b.split('.').collect();
    let max_len = segs_a.len().max(segs_b.len());
    for i in 0..max_len {
        let sa = segs_a.get(i).copied().unwrap_or("0");
        let sb = segs_b.get(i).copied().unwrap_or("0");
        let cmp = match (sa.parse::<u64>(), sb.parse::<u64>()) {
            (Ok(na), Ok(nb)) => na.cmp(&nb),
            // Fall back to lexical compare for non-numeric main segments.
            _ => sa.cmp(sb),
        };
        if cmp != Ordering::Equal {
            return cmp;
        }
    }

    // Main triples are equal — compare pre-release suffixes per semver.
    match (pre_a, pre_b) {
        (None, None) => Ordering::Equal,
        // No-prerelease > has-prerelease.
        (None, Some(_)) => Ordering::Greater,
        (Some(_), None) => Ordering::Less,
        (Some(pa), Some(pb)) => compare_prerelease(pa, pb),
    }
}

/// Compare two semver pre-release strings dot-segment-wise.
///
/// Numeric identifiers compare numerically and sort below alphanumeric
/// identifiers; alphanumerics compare lexically; if all shared segments
/// are equal, the longer suffix wins.
fn compare_prerelease(a: &str, b: &str) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let mut ia = a.split('.');
    let mut ib = b.split('.');
    loop {
        match (ia.next(), ib.next()) {
            (None, None) => return Ordering::Equal,
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (Some(sa), Some(sb)) => {
                let cmp = match (sa.parse::<u64>(), sb.parse::<u64>()) {
                    (Ok(na), Ok(nb)) => na.cmp(&nb),
                    // Numeric < alphanumeric per semver §11.4.3.
                    (Ok(_), Err(_)) => Ordering::Less,
                    (Err(_), Ok(_)) => Ordering::Greater,
                    (Err(_), Err(_)) => sa.cmp(sb),
                };
                if cmp != Ordering::Equal {
                    return cmp;
                }
            }
        }
    }
}

/// Extract the version suffix from a WASI module name, if any.
///
/// `"wasi:io/error@0.2.6"` → `Some("0.2.6")`; `"env"` → `None`
fn extract_version(name: &str) -> Option<&str> {
    match name.rfind('@') {
        Some(pos) if name[..pos].contains(':') => Some(&name[pos + 1..]),
        _ => None,
    }
}

/// Compute the effective `(module, field)` dedup key for an unresolved import.
///
/// Uses display names (from canon-lower WASI tracing) when available, falls
/// back to original core module import names. The module name is then
/// version-normalized so that `wasi:io/error@0.2.0` and `@0.2.6` map to
/// the same key.
fn effective_import_key(unresolved: &crate::resolver::UnresolvedImport) -> (String, String) {
    let module = unresolved
        .display_module
        .as_ref()
        .unwrap_or(&unresolved.module_name);
    let field = unresolved
        .display_field
        .as_ref()
        .unwrap_or(&unresolved.field_name);
    (
        normalize_wasi_module_name(module).to_string(),
        field.clone(),
    )
}

/// Return the effective module name (with display override) for an unresolved import.
fn effective_module_name(unresolved: &crate::resolver::UnresolvedImport) -> &str {
    unresolved
        .display_module
        .as_ref()
        .unwrap_or(&unresolved.module_name)
}

/// Resolve the imports-vector index whose name exactly matches
/// `expected_name` by scanning the values of a per-component
/// resource-tracking map. Exact match (not `ends_with`) — the prior
/// `imp.name.ends_with(rn)` form silently conflated two resources
/// whose names shared a suffix (e.g. `float` matched both
/// `[resource-rep]float` and `[resource-rep]bigfloat`), letting the
/// dedup-skip path register the wrong import for the wrong-suffix
/// component. See LS-A-19 for the regression.
fn find_exact_resource_import_idx(
    tracking: &HashMap<(usize, String), u32>,
    imports: &[MergedImport],
    expected_name: &str,
) -> Option<u32> {
    tracking.values().copied().find(|&idx| {
        imports
            .get(idx as usize)
            .is_some_and(|imp| imp.name == expected_name)
    })
}

/// Module merger
pub struct Merger {
    memory_strategy: MemoryStrategy,
    address_rebasing: bool,
    /// (interface, resource_name) tuples marked opaque-rep — skip handle
    /// table allocation for these resources because their reps are already
    /// valid integer handles (no Box dereferencing in user code).
    opaque_resources: Vec<(String, String)>,
}

#[derive(Debug, Clone)]
struct SharedMemoryPlan {
    memory: EncoderMemoryType,
    import: Option<(String, String)>,
    bases: HashMap<(usize, usize), u64>,
}

impl Merger {
    /// Create a new merger with the specified memory strategy
    pub fn new(memory_strategy: MemoryStrategy, address_rebasing: bool) -> Self {
        // `Auto` is resolved to a concrete strategy by
        // `Fuser::fuse_with_stats` before the merger is constructed. If an
        // unresolved `Auto` arrives via direct API use, normalize it to
        // `MultiMemory` (the always-sound strategy) HERE — the strategy
        // comparisons throughout this file are a mix of `== SharedMemory`
        // and `== MultiMemory`, and an un-normalized third variant would
        // satisfy neither consistently (Mythos finding B, PR #220: multi
        // memory layout with shared-style export dedup silently drops the
        // second component's memory export).
        let memory_strategy = match memory_strategy {
            MemoryStrategy::Auto => MemoryStrategy::MultiMemory,
            concrete => concrete,
        };
        Self {
            memory_strategy,
            address_rebasing,
            opaque_resources: Vec::new(),
        }
    }

    /// Mark resources as opaque-rep so handle table allocation skips them.
    pub fn with_opaque_resources(mut self, opaque: Vec<(String, String)>) -> Self {
        self.opaque_resources = opaque;
        self
    }

    fn compute_shared_memory_plan(
        &self,
        components: &[ParsedComponent],
    ) -> Result<Option<SharedMemoryPlan>> {
        let mut memory_types = Vec::new();
        let mut import_names: Vec<(String, String)> = Vec::new();
        let mut has_defined = false;
        let mut module_memories: Vec<((usize, usize), MemoryType)> = Vec::new();

        for (comp_idx, component) in components.iter().enumerate() {
            for (mod_idx, module) in component.core_modules.iter().enumerate() {
                for import in &module.imports {
                    if let ImportKind::Memory(mem) = &import.kind {
                        memory_types.push(mem.clone());
                        import_names.push((import.module.clone(), import.name.clone()));
                    }
                }

                if !module.memories.is_empty() {
                    has_defined = true;
                    memory_types.extend(module.memories.iter().cloned());
                }

                if self.address_rebasing {
                    if let Some(module_memory) = module_memory_type(module)? {
                        module_memories.push(((comp_idx, mod_idx), module_memory));
                    }
                }
            }
        }

        if memory_types.is_empty() {
            return Ok(None);
        }

        let combined = if self.address_rebasing {
            combine_memory_types_rebased(&memory_types)?
        } else {
            combine_memory_types_shared(&memory_types)?
        };

        let import = if has_defined {
            None
        } else {
            let Some((module, name)) = import_names.first().cloned() else {
                return Ok(None);
            };
            if import_names.iter().any(|(m, n)| *m != module || *n != name) {
                return Err(Error::MemoryStrategyUnsupported(
                    "shared memory requires a single import module/name".to_string(),
                ));
            }
            Some((module, name))
        };

        let mut bases = HashMap::new();
        if self.address_rebasing {
            let mut next_base_pages: u64 = 0;
            for (key, module_memory) in module_memories {
                let base_pages = next_base_pages;
                let base_bytes = base_pages.checked_mul(WASM_PAGE_SIZE).ok_or_else(|| {
                    Error::MemoryStrategyUnsupported(
                        "shared memory base offset overflow".to_string(),
                    )
                })?;
                if !combined.memory64 && base_bytes > u64::from(u32::MAX) {
                    return Err(Error::MemoryStrategyUnsupported(
                        "shared memory base offset exceeds 32-bit address space".to_string(),
                    ));
                }
                bases.insert(key, base_bytes);
                next_base_pages = next_base_pages
                    .checked_add(module_memory.initial)
                    .ok_or_else(|| {
                        Error::MemoryStrategyUnsupported("shared memory size overflow".to_string())
                    })?;
            }
        }

        Ok(Some(SharedMemoryPlan {
            memory: convert_memory_type(&combined),
            import,
            bases,
        }))
    }

    /// Check that no component instantiates the same core module more than once.
    ///
    /// The merger's index-space merging model assumes each module index appears
    /// at most once in the instantiation order. Multiply-instantiated modules
    /// would produce duplicate function/memory/table entries with conflicting
    /// index offsets, causing silent data corruption (LS-M-5, SR-31).
    fn check_no_duplicate_instantiations(components: &[ParsedComponent]) -> Result<()> {
        for (comp_idx, component) in components.iter().enumerate() {
            let mut seen_modules = std::collections::HashSet::new();
            for instance in &component.instances {
                if let crate::parser::InstanceKind::Instantiate { module_idx, .. } = &instance.kind
                {
                    if !seen_modules.insert(*module_idx) {
                        return Err(Error::DuplicateModuleInstantiation {
                            component_idx: comp_idx,
                            module_idx: *module_idx,
                        });
                    }
                }
            }
        }
        Ok(())
    }

    /// Allocate per-component handle tables for re-exporter components.
    ///
    /// For each re-exporter, grows its memory by 1 page and places a handle
    /// table at the start of the new page. Adds a mutable global for the
    /// next-allocation pointer and generates ht_new/ht_rep/ht_drop functions.
    #[allow(dead_code)]
    fn allocate_handle_tables(
        graph: &DependencyGraph,
        merged: &mut MergedModule,
        opaque_resources: &[(String, String)],
    ) -> Result<()> {
        // Handle table capacity: 256 entries = 1024 bytes (fits in 1 page)
        const HT_CAPACITY: u32 = 256;
        const ENTRY_SIZE: u32 = 4; // i32

        for (comp_idx, iface, rn) in &graph.reexporter_resources {
            let comp_idx = *comp_idx;
            // Opaque-rep resources still get ht_* slots in handle_tables, but
            // the function bodies are pure identity (no memory storage):
            //   ht_new(rep)  → rep   (the rep IS the handle)
            //   ht_rep(h)    → h     (the handle IS the rep)
            //   ht_drop(h)   → ()    (no cleanup needed)
            // Path B's redirect routes [resource-*] imports through these
            // same ht_* functions whether opaque or not, so opaque imports
            // bypass wasmtime's canonical resource layer entirely (which
            // would otherwise reject cross-component handle passing for
            // per-component-typed resources).
            // Opaque-rep gets the same memory-backed ht_* as standard
            // resources — the rep storage semantics are the same (ht_new
            // allocates a fresh handle and stores the rep, ht_rep reads
            // it back). The DIFFERENCE with --opaque-rep is in the wrapper:
            // opaque resources use a separate-typed local_resource_types
            // entry so wasmtime's canonical resource layer doesn't conflate
            // them with standard Box-pattern reps.
            let _is_opaque = opaque_resources.iter().any(|(i, r)| i == iface && r == rn);

            // Find merged memory index for this component's memory 0
            let memory_idx = match merged.memory_index_map.get(&(comp_idx, 0, 0)) {
                Some(&idx) => idx,
                None => continue, // No memory — skip (shouldn't happen for real components)
            };

            // Determine table base: grow memory by 1 page, place table at start
            // of new page. Each (component, resource) gets its own page so the
            // tables don't collide.
            let mem_slot = (memory_idx - merged.import_counts.memory) as usize;
            let current_pages = if mem_slot < merged.memories.len() {
                merged.memories[mem_slot].minimum
            } else {
                continue;
            };
            let table_base_addr = (current_pages * WASM_PAGE_SIZE) as u32;

            // Grow memory by 1 page to accommodate the handle table
            merged.memories[mem_slot].minimum += 1;
            if let Some(max) = merged.memories[mem_slot].maximum {
                if max < merged.memories[mem_slot].minimum {
                    merged.memories[mem_slot].maximum = Some(merged.memories[mem_slot].minimum);
                }
            }

            // Add mutable i32 global for next-allocation pointer.
            // Start at base+4 to skip slot 0 (handle=0 means "no handle").
            let next_ptr_global = merged.import_counts.global + merged.globals.len() as u32;
            merged.globals.push(MergedGlobal {
                ty: EncoderGlobalType {
                    val_type: ValType::I32,
                    mutable: true,
                    shared: false,
                },
                init_expr: ConstExpr::i32_const((table_base_addr + ENTRY_SIZE) as i32),
            });

            // Register or reuse the function types we need:
            //   ht_new:  (i32) -> (i32)
            //   ht_rep:  (i32) -> (i32)
            //   ht_drop: (i32) -> ()
            let type_i32_to_i32 =
                Self::find_or_add_type(&mut merged.types, &[ValType::I32], &[ValType::I32]);
            let type_i32_to_void = Self::find_or_add_type(&mut merged.types, &[ValType::I32], &[]);

            let mem_arg = wasm_encoder::MemArg {
                offset: 0,
                align: 2, // 4-byte aligned
                memory_index: memory_idx,
            };

            // Generate ht_new: store rep at next_ptr, return next_ptr, advance by 4
            let new_func_idx = merged.import_counts.func + merged.functions.len() as u32;
            {
                let mut body = Function::new([(1, ValType::I32)]); // local $handle
                body.instruction(&Instruction::GlobalGet(next_ptr_global));
                body.instruction(&Instruction::LocalSet(1)); // handle = next_ptr
                body.instruction(&Instruction::LocalGet(1)); // [handle]
                body.instruction(&Instruction::LocalGet(0)); // [handle, rep]
                body.instruction(&Instruction::I32Store(mem_arg)); // mem[handle] = rep
                body.instruction(&Instruction::LocalGet(1)); // [handle]
                body.instruction(&Instruction::I32Const(ENTRY_SIZE as i32));
                body.instruction(&Instruction::I32Add);
                body.instruction(&Instruction::GlobalSet(next_ptr_global)); // next_ptr += 4
                body.instruction(&Instruction::LocalGet(1)); // return handle
                body.instruction(&Instruction::End);
                merged.functions.push(MergedFunction {
                    type_idx: type_i32_to_i32,
                    body,
                    origin: (comp_idx, 0, u32::MAX), // synthetic
                    synthetic_kind: Some(SyntheticKind::HandleTable),
                });
            }

            // Generate ht_rep: return mem[handle]
            let rep_func_idx = merged.import_counts.func + merged.functions.len() as u32;
            {
                let mut body = Function::new([]);
                body.instruction(&Instruction::LocalGet(0)); // [handle]
                body.instruction(&Instruction::I32Load(mem_arg)); // mem[handle] -> rep
                body.instruction(&Instruction::End);
                merged.functions.push(MergedFunction {
                    type_idx: type_i32_to_i32,
                    body,
                    origin: (comp_idx, 0, u32::MAX),
                    synthetic_kind: Some(SyntheticKind::HandleTable),
                });
            }

            // Find the resource's dtor function (if any) so ht_drop can
            // invoke it before zeroing the slot. wit-bindgen-rust emits
            // `<iface>#[dtor]<rn>` as a core export for each component that
            // owns a Box-backed rep.
            //
            // Match by EXACT `<iface>#[dtor]<rn>` (with optional `$N` dedup
            // suffix tolerance). A previous version used `name.contains(...)`
            // which collided when one component defines the same resource
            // name across multiple interfaces (e.g. `resource_floats` has
            // dtors for `exports#[dtor]float`, `imports#[dtor]float`, and
            // `test:resource-floats/test#[dtor]float` — the contains-match
            // picked the first regardless of iface). Exact match plus the
            // origin-comp filter selects the right dtor unambiguously.
            let exact_dtor_export = format!("{}#[dtor]{}", iface, rn);
            let exact_dtor_dollar = format!("{}#[dtor]{}$", iface, rn);
            let dtor_func_idx: Option<u32> = merged
                .exports
                .iter()
                .filter(|e| {
                    matches!(e.kind, EncoderExportKind::Func)
                        && (e.name == exact_dtor_export || e.name.starts_with(&exact_dtor_dollar))
                })
                .find_map(|e| {
                    let import_count = merged.import_counts.func;
                    if e.index < import_count {
                        return None;
                    }
                    let local_idx = (e.index - import_count) as usize;
                    let func = merged.functions.get(local_idx)?;
                    if func.origin.0 == comp_idx {
                        Some(e.index)
                    } else {
                        None
                    }
                });
            if let Some(idx) = dtor_func_idx {
                log::info!(
                    "ht_drop for {}/{} in component {} will invoke dtor func {}",
                    iface,
                    rn,
                    comp_idx,
                    idx,
                );
            }

            // Generate ht_drop: load rep, optionally call dtor(rep), zero slot.
            // Skip the dtor invocation when ht_drop is called with handle=0
            // (used as a sentinel by the canonical ABI). Using if-then to
            // avoid double-free if the same handle is dropped twice.
            //
            // For re-exporters whose ht stores foreign reps (placed there by
            // the own bridge), invoking the local dtor on a foreign rep is
            // undefined behavior — the dtor casts the rep as `*mut
            // _ThingRep<LocalT>` and Box::from_raw drops what it thinks is a
            // local box. When the foreign rep is actually a leaf-allocated
            // box, this misinterprets memory and leads to recursion through
            // the import drop chain. Suppress the dtor for re-exporter
            // components whose ht is also fed via own bridges (the standard
            // Box-pattern wit-bindgen design assumes the rep is always
            // owned by the component whose ht stores it, but Phase 1's
            // per-component-ht-for-definers broke that invariant).
            let invoke_dtor =
                dtor_func_idx.filter(|_| !graph.reexporter_components.contains(&comp_idx));
            let drop_func_idx = merged.import_counts.func + merged.functions.len() as u32;
            {
                let mut body = Function::new([]);
                body.instruction(&Instruction::LocalGet(0)); // [handle]
                body.instruction(&Instruction::I32Eqz); // [handle == 0]
                body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                body.instruction(&Instruction::Else);
                if let Some(dtor_idx) = invoke_dtor {
                    // Load the rep stored at this handle slot, then call dtor(rep).
                    body.instruction(&Instruction::LocalGet(0));
                    body.instruction(&Instruction::I32Load(mem_arg));
                    body.instruction(&Instruction::Call(dtor_idx));
                }
                // Zero the slot regardless of whether a dtor was called.
                body.instruction(&Instruction::LocalGet(0));
                body.instruction(&Instruction::I32Const(0));
                body.instruction(&Instruction::I32Store(mem_arg));
                body.instruction(&Instruction::End); // end if
                body.instruction(&Instruction::End); // end function
                merged.functions.push(MergedFunction {
                    type_idx: type_i32_to_void,
                    body,
                    origin: (comp_idx, 0, u32::MAX),
                    synthetic_kind: Some(SyntheticKind::HandleTable),
                });
            }

            merged.handle_tables.insert(
                (comp_idx, iface.clone(), rn.clone()),
                HandleTableInfo {
                    memory_idx,
                    next_ptr_global,
                    table_base_addr,
                    capacity: HT_CAPACITY,
                    new_func: new_func_idx,
                    rep_func: rep_func_idx,
                    drop_func: drop_func_idx,
                },
            );

            // Export handle table functions so the P2 wrapper can alias them.
            // Naming: $ht_new_{comp}_{iface_safe}_{rn} so multiple resources
            // per component don't collide.
            let suffix = ht_export_suffix(comp_idx, iface, rn);
            merged.exports.push(MergedExport {
                name: format!("$ht_new_{}", suffix),
                kind: EncoderExportKind::Func,
                index: new_func_idx,
            });
            merged.exports.push(MergedExport {
                name: format!("$ht_rep_{}", suffix),
                kind: EncoderExportKind::Func,
                index: rep_func_idx,
            });
            merged.exports.push(MergedExport {
                name: format!("$ht_drop_{}", suffix),
                kind: EncoderExportKind::Func,
                index: drop_func_idx,
            });

            log::info!(
                "handle table for component {} resource {}/{}: memory={}, base=0x{:x}, global={}, funcs=({},{},{})",
                comp_idx,
                iface,
                rn,
                memory_idx,
                table_base_addr,
                next_ptr_global,
                new_func_idx,
                rep_func_idx,
                drop_func_idx,
            );
        }

        Ok(())
    }

    /// Find an existing function type or add a new one, returning its index.
    #[allow(dead_code)]
    pub(crate) fn find_or_add_type(
        types: &mut Vec<MergedFuncType>,
        params: &[ValType],
        results: &[ValType],
    ) -> u32 {
        for (i, ty) in types.iter().enumerate() {
            if ty.params == params && ty.results == results {
                return i as u32;
            }
        }
        let idx = types.len() as u32;
        types.push(MergedFuncType {
            params: params.to_vec(),
            results: results.to_vec(),
        });
        idx
    }

    /// Merge components into a single module
    pub fn merge(
        &self,
        components: &[ParsedComponent],
        graph: &DependencyGraph,
    ) -> Result<MergedModule> {
        Self::check_no_duplicate_instantiations(components)?;

        let shared_memory_plan = if self.memory_strategy == MemoryStrategy::SharedMemory {
            self.compute_shared_memory_plan(components)?
        } else {
            None
        };

        // Pre-compute unresolved import counts and assignments so that all
        // index-map values produced during merging are absolute wasm indices
        // (offset by the number of unresolved imports in each index space).
        let (import_counts, unresolved_assignments, dedup_info) =
            compute_unresolved_import_assignments(
                graph,
                shared_memory_plan.as_ref(),
                components,
                self.memory_strategy,
            );

        let mut merged = MergedModule {
            types: Vec::new(),
            imports: Vec::new(),
            functions: Vec::new(),
            tables: Vec::new(),
            memories: Vec::new(),
            globals: Vec::new(),
            exports: Vec::new(),
            start_function: None,
            elements: Vec::new(),
            data_segments: Vec::new(),
            custom_sections: Vec::new(),
            fused_function_names: std::collections::BTreeMap::new(),
            function_index_map: HashMap::new(),
            memory_index_map: HashMap::new(),
            table_index_map: HashMap::new(),
            global_index_map: HashMap::new(),
            type_index_map: HashMap::new(),
            realloc_map: HashMap::new(),
            import_counts,
            import_memory_indices: Vec::new(),
            import_realloc_indices: Vec::new(),
            resource_rep_by_component: HashMap::new(),
            resource_new_by_component: HashMap::new(),
            handle_tables: HashMap::new(),
            task_return_shims: HashMap::new(),
            async_result_globals: HashMap::new(),
            segment_bases: HashMap::new(),
        };

        // Process components in topological order
        for &comp_idx in &graph.instantiation_order {
            let component = &components[comp_idx];
            self.merge_component(
                comp_idx,
                component,
                components,
                graph,
                &mut merged,
                shared_memory_plan.as_ref(),
                &unresolved_assignments,
            )?;
        }

        // Handle unresolved imports
        self.add_unresolved_imports(graph, &mut merged, shared_memory_plan.as_ref(), &dedup_info)?;

        // Handle start functions
        self.resolve_start_functions(components, &mut merged)?;

        // Allocate per-component handle tables for re-exporter components.
        // These are needed for 3-component resource chains where the
        // re-exporter's wit-bindgen code expects 4-byte-aligned memory
        // pointers as handles, not sequential canonical ABI handles.
        if !graph.reexporter_resources.is_empty() {
            Self::allocate_handle_tables(graph, &mut merged, &self.opaque_resources)?;

            // Remap [resource-*] imports to handle-table functions, with
            // per-resource discrimination. For each component that owns a
            // handle table, walk its core modules' imports and redirect only
            // those imports whose (interface, resource_name) matches a
            // registered handle table for this component as owner.
            //
            // The owner of `[export]<iface>.[resource-*]<rn>` is the
            // importing component itself (it's the component's own export
            // resource). The owner of `<iface>.[resource-*]<rn>` (no
            // [export] prefix) is whatever component DEFINES the resource —
            // that's resource_graph.resource_definer(iface, rn). Imports
            // routed at the leaf-definer's helpers should NOT be rewritten
            // through any other component's handle table; they must call
            // the natural canonical-ABI handler in their owning component.
            let mut affected_modules: Vec<(usize, usize)> = Vec::new();
            // Iterate ALL components, not just those with handle tables.
            // A pure consumer (e.g. the runner in a 3-component chain) holds
            // handles allocated by the re-exporter's ht_new and must drop
            // them through the same handle table — its [resource-drop]
            // imports also need redirection.
            for (comp_idx, _component) in components.iter().enumerate() {
                let component = &components[comp_idx];
                for (mod_idx, module) in component.core_modules.iter().enumerate() {
                    let mut import_func_idx = 0u32;
                    let mut changed = false;
                    for imp in &module.imports {
                        if !matches!(imp.kind, crate::parser::ImportKind::Function(_)) {
                            continue;
                        }
                        // Parse: which (iface, resource_name) and which op?
                        // Strip optional `$N` dedup suffix that meld appends
                        // when multiple components import the same resource
                        // helper — the canonical resource name is the same.
                        let (op_kind, rn_raw) =
                            if let Some(rn) = imp.name.strip_prefix("[resource-rep]") {
                                (Some("rep"), rn)
                            } else if let Some(rn) = imp.name.strip_prefix("[resource-new]") {
                                (Some("new"), rn)
                            } else if let Some(rn) = imp.name.strip_prefix("[resource-drop]") {
                                (Some("drop"), rn)
                            } else {
                                (None, "")
                            };
                        if op_kind.is_none() {
                            import_func_idx += 1;
                            continue;
                        }
                        let rn = strip_dollar_suffix(rn_raw);
                        // Strip [export] prefix from the import module name.
                        // If present (importer's own export resource), the
                        // owner is self. Otherwise the importer is consuming
                        // a resource from elsewhere — find ANY component that
                        // has a handle table for (iface, rn). That's the
                        // re-exporter that allocated the handles being passed
                        // around; consumers must route their [resource-*]
                        // calls through that same table to stay consistent.
                        let iface_with_prefix = imp.module.as_str();
                        let iface = iface_with_prefix
                            .strip_prefix("[export]")
                            .unwrap_or(iface_with_prefix);
                        let key_target = if iface_with_prefix.starts_with("[export]") {
                            // Importer's own export — look up by self first.
                            let key = (comp_idx, iface.to_string(), rn.to_string());
                            merged.handle_tables.get(&key).or_else(|| {
                                // Resource-alias fallback: when a different
                                // component re-exports THIS resource via
                                // `use` (e.g., intermediate has `use
                                // test.{float}` re-exporting leaf's
                                // test.float as exports.float), wasmtime
                                // unifies them into one canonical type. The
                                // re-exporter's handle table is the only
                                // storage that knows the memory-pointer
                                // handles minted by ht_new — definer-side
                                // [resource-*] must route there too, or
                                // peers will hand it pointers it can't
                                // dereference. Match by resource_name only
                                // since the iface differs across the alias.
                                // Sort keys for deterministic tie-breaking
                                // (LS-A-15).
                                let mut keys: Vec<&(
                                    usize,
                                    String,
                                    String,
                                )> = merged
                                    .handle_tables
                                    .keys()
                                    .filter(|(_, _, r)| r == rn)
                                    .collect();
                                keys.sort();
                                let found = keys
                                    .first()
                                    .and_then(|k| merged.handle_tables.get(*k));
                                if found.is_some() {
                                    log::info!(
                                        "alias-fallback: comp {} mod {} import {}/{} → ht for resource '{}'",
                                        comp_idx,
                                        mod_idx,
                                        iface,
                                        imp.name,
                                        rn,
                                    );
                                }
                                found
                            })
                        } else {
                            // Consumer-side import. If THIS component itself
                            // re-exports (iface, rn) — has its own handle
                            // table for the same resource — then this import
                            // is the inner-component (definer) view, NOT the
                            // re-exporter view. Use canonical resource ops
                            // (don't redirect). Otherwise the importer is a
                            // pure consumer and the handle was minted by the
                            // re-exporter's ht_new — route through that table.
                            //
                            // Same alias-fallback as the definer branch: when
                            // strict `(i, r)` matches no handle table, fall
                            // back to matching by resource_name only. This
                            // catches consumer imports of resources unified
                            // via `use other-iface.{rn}` (e.g. runner's
                            // `test:resource-floats/test [resource-drop]float`
                            // when only `(3, "exports", "float")` ht exists).
                            //
                            // Self-owns check: this component owns a handle
                            // table for the SPECIFIC (iface, rn) pair. We do
                            // NOT block when the iface differs but the
                            // resource name is the same — those are
                            // `use`-aliased resources unified at canon-type
                            // level, and they SHOULD route through the
                            // re-exporter's ht.
                            let self_owns_specific = merged.handle_tables.contains_key(&(
                                comp_idx,
                                iface.to_string(),
                                rn.to_string(),
                            ));
                            if self_owns_specific {
                                None
                            } else {
                                // Look up (any-owner, iface, rn) first, then
                                // fall back to (any-owner, any-iface, rn).
                                // Iterate in sorted-key order so ties are
                                // broken deterministically (LS-A-15).
                                let mut iface_keys: Vec<&(usize, String, String)> = merged
                                    .handle_tables
                                    .keys()
                                    .filter(|(_, i, r)| i == iface && r == rn)
                                    .collect();
                                iface_keys.sort();
                                iface_keys
                                    .first()
                                    .and_then(|k| merged.handle_tables.get(*k))
                                    .or_else(|| {
                                        let mut any_keys: Vec<&(usize, String, String)> = merged
                                            .handle_tables
                                            .keys()
                                            .filter(|(_, _, r)| r == rn)
                                            .collect();
                                        any_keys.sort();
                                        any_keys.first().and_then(|k| merged.handle_tables.get(*k))
                                    })
                            }
                        };
                        if let Some(ht) = key_target {
                            let target = match op_kind.unwrap() {
                                "rep" => ht.rep_func,
                                "new" => ht.new_func,
                                "drop" => ht.drop_func,
                                _ => unreachable!(),
                            };
                            merged
                                .function_index_map
                                .insert((comp_idx, mod_idx, import_func_idx), target);
                            changed = true;
                        }
                        import_func_idx += 1;
                    }
                    if changed {
                        affected_modules.push((comp_idx, mod_idx));
                    }
                }
            }

            // Re-rewrite function bodies for modules that had resource imports
            // redirected to handle table functions.
            for &(comp_idx, mod_idx) in &affected_modules {
                let module = &components[comp_idx].core_modules[mod_idx];
                // This pass runs AFTER the full merge, so `merged.*.len()` is
                // the total segment count, not this module's base. Recover the
                // correct per-module base recorded during the main merge loop.
                let (data_segment_base, elem_segment_base) = merged
                    .segment_bases
                    .get(&(comp_idx, mod_idx))
                    .copied()
                    .unwrap_or((0, 0));
                let index_maps = build_index_maps_for_module(
                    comp_idx,
                    mod_idx,
                    module,
                    &merged,
                    self.memory_strategy,
                    false, // address_rebasing
                    0u64,  // memory_base_offset
                    false, // memory64
                    None,  // memory_initial_pages
                    data_segment_base,
                    elem_segment_base,
                    None, // code_addr_relocs (rebasing off in this re-rewrite pass)
                );
                let import_func_count = module
                    .imports
                    .iter()
                    .filter(|i| matches!(i.kind, ImportKind::Function(_)))
                    .count() as u32;

                for (old_idx, &type_idx) in module.functions.iter().enumerate() {
                    let old_func_idx = import_func_count + old_idx as u32;
                    let param_count = module
                        .types
                        .get(type_idx as usize)
                        .map(|ty| ty.params.len() as u32)
                        .unwrap_or(0);

                    let body = extract_function_body(module, old_idx, param_count, &index_maps)?;

                    if let Some(mf) = merged
                        .functions
                        .iter_mut()
                        .find(|f| f.origin == (comp_idx, mod_idx, old_func_idx))
                    {
                        mf.body = body;
                    }
                }
                log::info!(
                    "re-rewrote {} functions in component {} module {} for handle table routing",
                    module.functions.len(),
                    comp_idx,
                    mod_idx,
                );
            }
        }

        if let Some(plan) = shared_memory_plan {
            if plan.import.is_none() {
                merged.memories.clear();
                merged.memories.push(plan.memory);
            } else {
                merged.memories.clear();
            }
        }

        Ok(merged)
    }

    /// Merge a single component into the merged module.
    ///
    /// Modules within a component are merged in dependency order so that
    /// target modules (from `module_resolutions`) are processed before the
    /// modules that import from them.  This ensures `function_index_map`
    /// entries exist when resolving intra-component imports.
    #[allow(clippy::too_many_arguments)]
    fn merge_component(
        &self,
        comp_idx: usize,
        component: &ParsedComponent,
        components: &[ParsedComponent],
        graph: &DependencyGraph,
        merged: &mut MergedModule,
        shared_memory_plan: Option<&SharedMemoryPlan>,
        unresolved_assignments: &UnresolvedImportAssignments,
    ) -> Result<()> {
        let module_count = component.core_modules.len();
        let merge_order = Self::compute_module_merge_order(comp_idx, module_count, graph);

        for mod_idx in merge_order {
            let module = &component.core_modules[mod_idx];
            self.merge_core_module(
                comp_idx,
                mod_idx,
                module,
                components,
                graph,
                merged,
                shared_memory_plan,
                unresolved_assignments,
            )?;
        }

        Ok(())
    }

    /// Compute the merge order for modules within a component using
    /// topological sort on `module_resolutions`.
    ///
    /// Target modules (those that provide exports) are processed before
    /// source modules (those that import from them).  When no dependencies
    /// exist, modules are processed in their original order.
    fn compute_module_merge_order(
        comp_idx: usize,
        module_count: usize,
        graph: &DependencyGraph,
    ) -> Vec<usize> {
        // Build adjacency list: from_module depends on to_module
        let mut in_degree = vec![0usize; module_count];
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); module_count];

        for res in &graph.module_resolutions {
            if res.component_idx == comp_idx && res.from_module != res.to_module {
                // to_module must be processed before from_module
                // Edge: to_module → from_module (to_module comes first)
                if res.to_module < module_count && res.from_module < module_count {
                    adj[res.to_module].push(res.from_module);
                    in_degree[res.from_module] += 1;
                }
            }
        }

        // Deduplicate edges and recount in-degrees
        let mut in_degree = vec![0usize; module_count];
        for edges in adj.iter_mut().take(module_count) {
            edges.sort_unstable();
            edges.dedup();
            for &neighbor in edges.iter() {
                in_degree[neighbor] += 1;
            }
        }

        // Kahn's algorithm — use original index as tiebreaker
        let mut queue: std::collections::BinaryHeap<std::cmp::Reverse<usize>> =
            std::collections::BinaryHeap::new();
        for (i, &deg) in in_degree.iter().enumerate().take(module_count) {
            if deg == 0 {
                queue.push(std::cmp::Reverse(i));
            }
        }

        let mut order = Vec::with_capacity(module_count);
        while let Some(std::cmp::Reverse(node)) = queue.pop() {
            order.push(node);
            for &neighbor in &adj[node] {
                in_degree[neighbor] -= 1;
                if in_degree[neighbor] == 0 {
                    queue.push(std::cmp::Reverse(neighbor));
                }
            }
        }

        // If there's a cycle (shouldn't happen — resolver checks this),
        // fall back to sequential order for any remaining modules.
        if order.len() < module_count {
            for i in 0..module_count {
                if !order.contains(&i) {
                    order.push(i);
                }
            }
        }

        order
    }

    /// Merge a single core module
    #[allow(clippy::too_many_arguments)]
    fn merge_core_module(
        &self,
        comp_idx: usize,
        mod_idx: usize,
        module: &CoreModule,
        components: &[ParsedComponent],
        graph: &DependencyGraph,
        merged: &mut MergedModule,
        shared_memory_plan: Option<&SharedMemoryPlan>,
        unresolved_assignments: &UnresolvedImportAssignments,
    ) -> Result<()> {
        // Merge types.
        //
        // Two passes: first record every type's old->merged index mapping, then
        // build the merged types. The split is required because a func type's
        // param/result may be a concrete typed-ref `(ref $t)` whose index `t`
        // can forward-reference another type in this same module; remapping it
        // needs the *complete* mapping for the module to already be in place.
        let type_offset = merged.types.len() as u32;
        for (old_idx, _ty) in module.types.iter().enumerate() {
            merged.type_index_map.insert(
                (comp_idx, mod_idx, old_idx as u32),
                type_offset + old_idx as u32,
            );
        }
        for ty in module.types.iter() {
            merged.types.push(MergedFuncType {
                params: ty
                    .params
                    .iter()
                    .map(|&p| remap_concrete_val_type(p, comp_idx, mod_idx, merged))
                    .collect(),
                results: ty
                    .results
                    .iter()
                    .map(|&r| remap_concrete_val_type(r, comp_idx, mod_idx, merged))
                    .collect(),
            });
        }

        // Track import counts for index calculations
        let mut import_func_count = 0u32;
        let mut import_table_count = 0u32;
        let mut import_mem_count = 0u32;
        let mut import_global_count = 0u32;

        // Count imports (they contribute to index space)
        for import in &module.imports {
            match &import.kind {
                ImportKind::Function(_) => import_func_count += 1,
                ImportKind::Table(_) => import_table_count += 1,
                ImportKind::Memory(_) => import_mem_count += 1,
                ImportKind::Global(_) => import_global_count += 1,
            }
        }

        // Merge memories
        if self.memory_strategy == MemoryStrategy::SharedMemory {
            let total_memories = import_mem_count + module.memories.len() as u32;
            for idx in 0..total_memories {
                merged.memory_index_map.insert((comp_idx, mod_idx, idx), 0);
            }
        } else {
            // Multi-memory: each component keeps its own memory.
            // Both imported and defined memories get unique indices.
            let mem_offset = merged.memories.len() as u32;
            let mut next_idx = 0u32;

            // Track which imported memory indices get resolved via module_resolutions
            // so we can skip creating standalone memories for them.
            let mut resolved_import_mem_indices: HashSet<u32> = HashSet::new();

            // Pre-scan: identify imported memories that are resolved via
            // module_resolutions (e.g., Module 1 imports memory from Module 0).
            {
                let mut scan_mem_idx = 0u32;
                for imp in &module.imports {
                    if !matches!(imp.kind, ImportKind::Memory(_)) {
                        continue;
                    }
                    let intra = graph.module_resolutions.iter().find(|res| {
                        res.component_idx == comp_idx
                            && res.from_module == mod_idx
                            && imp.name == res.import_name
                            && (res.from_import_module.is_empty()
                                || res.from_import_module == imp.module)
                    });
                    if let Some(res) = intra {
                        let target_module =
                            &components[res.component_idx].core_modules[res.to_module];
                        if let Some(export) = target_module
                            .exports
                            .iter()
                            .find(|e| e.name == res.export_name && e.kind == ExportKind::Memory)
                        {
                            if let Some(&target_idx) = merged.memory_index_map.get(&(
                                res.component_idx,
                                res.to_module,
                                export.index,
                            )) {
                                // Map this imported memory to the target module's memory
                                merged
                                    .memory_index_map
                                    .insert((comp_idx, mod_idx, scan_mem_idx), target_idx);
                                resolved_import_mem_indices.insert(scan_mem_idx);
                            }
                        }
                    }
                    scan_mem_idx += 1;
                }
            }

            // Imported memories — only create new memories for unresolved ones
            let mut import_mem_local_idx = 0u32;
            for import in &module.imports {
                if let ImportKind::Memory(mem) = &import.kind {
                    if !resolved_import_mem_indices.contains(&import_mem_local_idx) {
                        let new_idx = mem_offset + next_idx;
                        merged
                            .memory_index_map
                            .insert((comp_idx, mod_idx, import_mem_local_idx), new_idx);
                        merged.memories.push(convert_memory_type(mem));
                        next_idx += 1;
                    }
                    import_mem_local_idx += 1;
                }
            }

            // Defined memories
            for (old_idx, mem) in module.memories.iter().enumerate() {
                let new_idx = mem_offset + next_idx + old_idx as u32;
                merged.memory_index_map.insert(
                    (comp_idx, mod_idx, import_mem_count + old_idx as u32),
                    new_idx,
                );
                merged.memories.push(convert_memory_type(mem));
            }
        }

        // Merge tables (defined tables only; imported tables handled below)
        let table_offset = merged.tables.len() as u32;
        for (old_idx, table) in module.tables.iter().enumerate() {
            let old_table_idx = import_table_count + old_idx as u32;
            let new_idx = merged.import_counts.table + table_offset + old_idx as u32;
            log::debug!(
                "table defined: ({},{},{}) → {} (offset={}, import_count={})",
                comp_idx,
                mod_idx,
                old_table_idx,
                new_idx,
                table_offset,
                merged.import_counts.table,
            );
            merged
                .table_index_map
                .insert((comp_idx, mod_idx, old_table_idx), new_idx);
            merged
                .tables
                .push(convert_table_type(table, comp_idx, mod_idx, merged));
        }

        // Merge globals (defined globals only; imported globals handled below)
        let global_offset = merged.globals.len() as u32;
        for (old_idx, global) in module.globals.iter().enumerate() {
            let new_idx = merged.import_counts.global + global_offset + old_idx as u32;
            merged.global_index_map.insert(
                (comp_idx, mod_idx, import_global_count + old_idx as u32),
                new_idx,
            );
            let init_expr = convert_init_expr(
                &global.init_expr_bytes,
                comp_idx,
                mod_idx,
                merged,
                &global.content_type,
            );
            let ty = convert_global_type(global, comp_idx, mod_idx, merged);
            merged.globals.push(MergedGlobal { ty, init_expr });
        }

        // Resolve imported global indices via intra-component module_resolutions.
        // This mirrors how function imports are resolved below: if module A
        // imports a global that module B exports, map A's imported global index
        // to B's defined global's merged index.
        {
            let mut import_global_idx = 0u32;
            for imp in &module.imports {
                if !matches!(imp.kind, ImportKind::Global(_)) {
                    continue;
                }

                // Intra-component: check module_resolutions
                let intra = graph.module_resolutions.iter().find(|res| {
                    res.component_idx == comp_idx
                        && res.from_module == mod_idx
                        && imp.name == res.import_name
                        && (res.from_import_module.is_empty()
                            || res.from_import_module == imp.module)
                });
                if let Some(res) = intra {
                    let target_module = &components[res.component_idx].core_modules[res.to_module];
                    if let Some(export) = target_module
                        .exports
                        .iter()
                        .find(|e| e.name == res.export_name && e.kind == ExportKind::Global)
                    {
                        if let Some(&target_idx) = merged.global_index_map.get(&(
                            res.component_idx,
                            res.to_module,
                            export.index,
                        )) {
                            merged
                                .global_index_map
                                .insert((comp_idx, mod_idx, import_global_idx), target_idx);
                        }
                    }
                }

                // Map unresolved global imports to their merged import index
                if let std::collections::hash_map::Entry::Vacant(e) = merged
                    .global_index_map
                    .entry((comp_idx, mod_idx, import_global_idx))
                {
                    if let Some(&import_index) = unresolved_assignments.global.get(&(
                        comp_idx,
                        mod_idx,
                        imp.module.clone(),
                        imp.name.clone(),
                    )) {
                        e.insert(import_index);
                    }
                }

                import_global_idx += 1;
            }
        }

        // Resolve imported table indices via intra-component module_resolutions.
        // Same pattern as global import resolution above.
        {
            let mut import_table_idx = 0u32;
            for imp in &module.imports {
                if !matches!(imp.kind, ImportKind::Table(_)) {
                    continue;
                }

                // Intra-component: check module_resolutions
                let intra = graph.module_resolutions.iter().find(|res| {
                    res.component_idx == comp_idx
                        && res.from_module == mod_idx
                        && imp.name == res.import_name
                        && (res.from_import_module.is_empty()
                            || res.from_import_module == imp.module)
                });
                if let Some(res) = intra {
                    let target_module = &components[res.component_idx].core_modules[res.to_module];
                    if let Some(export) = target_module
                        .exports
                        .iter()
                        .find(|e| e.name == res.export_name && e.kind == ExportKind::Table)
                    {
                        if let Some(&target_idx) = merged.table_index_map.get(&(
                            res.component_idx,
                            res.to_module,
                            export.index,
                        )) {
                            merged
                                .table_index_map
                                .insert((comp_idx, mod_idx, import_table_idx), target_idx);
                        }
                    }
                }

                // Map unresolved table imports to their merged import index
                if let std::collections::hash_map::Entry::Vacant(e) = merged
                    .table_index_map
                    .entry((comp_idx, mod_idx, import_table_idx))
                {
                    if let Some(&import_index) = unresolved_assignments.table.get(&(
                        comp_idx,
                        mod_idx,
                        imp.module.clone(),
                        imp.name.clone(),
                    )) {
                        e.insert(import_index);
                    }
                }

                import_table_idx += 1;
            }
        }

        // Resolve function imports that have been matched to exports in other
        // modules (cross-component and intra-component via adapter_sites,
        // remaining intra-component direct calls via module_resolutions).
        // adapter_sites is checked first because it includes both cross-component
        // adapters AND intra-component adapters (for module pairs with different
        // canonical options). module_resolutions is the fallback for
        // intra-component calls that don't need adapters.
        // This populates function_index_map for imported function indices so the
        // body rewriter can replace call targets.
        {
            let mut import_func_idx = 0u32;
            for imp in &module.imports {
                if !matches!(imp.kind, ImportKind::Function(_)) {
                    continue;
                }

                // Check adapter_sites first (cross-component + intra-component adapters).
                let resolved = graph.adapter_sites.iter().find(|site| {
                    site.from_component == comp_idx
                        && site.from_module == mod_idx
                        && (imp.name == site.import_name || imp.module == site.import_name)
                        && (imp.module == site.import_module || imp.name == site.import_module)
                });
                if let Some(site) = resolved {
                    if let Some(&target_idx) = merged.function_index_map.get(&(
                        site.to_component,
                        site.to_module,
                        site.export_func_idx,
                    )) {
                        log::debug!(
                            "Adapter site resolved: comp {} mod {} import {:?} -> func {}",
                            comp_idx,
                            mod_idx,
                            imp.name,
                            target_idx
                        );
                        merged
                            .function_index_map
                            .insert((comp_idx, mod_idx, import_func_idx), target_idx);
                    } else {
                        log::debug!(
                            "Adapter site MISS: comp {} mod {} import {:?} -> \
                             target comp {} mod {} func {} NOT in function_index_map",
                            comp_idx,
                            mod_idx,
                            imp.name,
                            site.to_component,
                            site.to_module,
                            site.export_func_idx
                        );
                    }
                } else if imp.module.contains("test:numbers") {
                    log::debug!(
                        "NO adapter site for: comp {} mod {} module={:?} name={:?} \
                         (total sites: {})",
                        comp_idx,
                        mod_idx,
                        imp.module,
                        imp.name,
                        graph.adapter_sites.len()
                    );
                }

                // Intra-component fallback: check module_resolutions for direct
                // calls that don't need adapters (adapter-needing ones were
                // already promoted to adapter_sites by the resolver).
                if !merged
                    .function_index_map
                    .contains_key(&(comp_idx, mod_idx, import_func_idx))
                {
                    let intra = graph.module_resolutions.iter().find(|res| {
                        res.component_idx == comp_idx
                            && res.from_module == mod_idx
                            && imp.name == res.import_name
                            && (res.from_import_module.is_empty()
                                || res.from_import_module == imp.module)
                    });
                    if let Some(res) = intra {
                        // Look up the target module's export to find its function index
                        let target_module =
                            &components[res.component_idx].core_modules[res.to_module];
                        if let Some(export) = target_module
                            .exports
                            .iter()
                            .find(|e| e.name == res.export_name && e.kind == ExportKind::Function)
                        {
                            if let Some(&target_idx) = merged.function_index_map.get(&(
                                res.component_idx,
                                res.to_module,
                                export.index,
                            )) {
                                log::debug!(
                                    "intra-comp func resolve: comp {} mod {} import {}({}) -> comp {} mod {} export {}[{}] = merged {}",
                                    comp_idx,
                                    mod_idx,
                                    imp.name,
                                    import_func_idx,
                                    res.component_idx,
                                    res.to_module,
                                    res.export_name,
                                    export.index,
                                    target_idx,
                                );
                                merged
                                    .function_index_map
                                    .insert((comp_idx, mod_idx, import_func_idx), target_idx);
                            } else {
                                log::warn!(
                                    "intra-comp func resolve MISS: comp {} mod {} import {}({}) -> comp {} mod {} export {}[{}] NOT IN function_index_map",
                                    comp_idx,
                                    mod_idx,
                                    imp.name,
                                    import_func_idx,
                                    res.component_idx,
                                    res.to_module,
                                    res.export_name,
                                    export.index,
                                );
                            }
                        }
                    }
                }

                // Map unresolved function imports to their merged import index
                if let std::collections::hash_map::Entry::Vacant(e) = merged
                    .function_index_map
                    .entry((comp_idx, mod_idx, import_func_idx))
                {
                    if let Some(&import_index) = unresolved_assignments.func.get(&(
                        comp_idx,
                        mod_idx,
                        imp.module.clone(),
                        imp.name.clone(),
                    )) {
                        log::debug!(
                            "unresolved func assign: comp {} mod {} import {}::{}({}) = merged import {}",
                            comp_idx,
                            mod_idx,
                            imp.module,
                            imp.name,
                            import_func_idx,
                            import_index,
                        );
                        e.insert(import_index);
                    } else {
                        log::debug!(
                            "UNMAPPED func import: comp {} mod {} import {}::{}({})",
                            comp_idx,
                            mod_idx,
                            imp.module,
                            imp.name,
                            import_func_idx,
                        );
                    }
                }

                import_func_idx += 1;
            }
        }

        // First pass: build all function index mappings.
        // Values are absolute wasm indices: import_count + array position.
        let func_offset = merged.functions.len() as u32;
        let mut func_type_indices = Vec::new();

        for (old_idx, &type_idx) in module.functions.iter().enumerate() {
            let new_func_idx = merged.import_counts.func + func_offset + old_idx as u32;
            let old_func_idx = import_func_count + old_idx as u32;

            merged
                .function_index_map
                .insert((comp_idx, mod_idx, old_func_idx), new_func_idx);

            // Get the remapped type index
            let new_type_idx = *merged
                .type_index_map
                .get(&(comp_idx, mod_idx, type_idx))
                .ok_or(Error::IndexOutOfBounds {
                    kind: "type",
                    index: type_idx,
                    max: module.types.len() as u32,
                })?;

            func_type_indices.push((old_idx, old_func_idx, new_type_idx, type_idx));
        }

        // Build IndexMaps for this module's function bodies
        let memory_base_offset = shared_memory_plan
            .and_then(|plan| plan.bases.get(&(comp_idx, mod_idx)).copied())
            .unwrap_or(0);

        // #326: relocation-driven address rebasing. A module placed at a
        // non-zero shared-memory base has its absolute addresses shifted by
        // that base; the `reloc.CODE` MEMORY_ADDR sites name exactly which
        // `i32.const`/`memarg` immediates encode those addresses.
        //
        // Path-F (ADR-6): if such a module carries NO reloc metadata we cannot
        // find its absolute addresses, so emitting it unchanged would collide
        // it with a prior module and silently corrupt memory. Hard-fail —
        // BUT only when the module actually performs *direct* (non-bulk)
        // memory access. A module whose every memory touch is a bulk-memory op
        // (`memory.copy/fill/init`) is safe without relocs: the rewriter
        // rebases those ops' runtime address operands dynamically
        // (`append_rebased_address`), so no baked-in absolute address can hide.
        let mut data_addr_relocs: Vec<crate::reloc::RelocEntry> = Vec::new();
        let code_addr_relocs = if self.address_rebasing {
            let has_reloc = crate::reloc::has_reloc_metadata(&module.custom_sections);
            if memory_base_offset != 0 && !has_reloc && module_has_direct_memory_access(module)? {
                return Err(Error::MissingRelocMetadata {
                    component: component_display_name(components, comp_idx),
                    module: mod_idx.to_string(),
                });
            }
            if has_reloc {
                let info = crate::reloc::parse_reloc_info(&module.custom_sections)?;
                // #326 Finding B: a memory64 module emits 8-byte inline data
                // pointers (`R_WASM_MEMORY_ADDR_I64`) we cannot rebase; the
                // segment placement would move while the pointers stay stale —
                // silent corruption. Reject rather than emit a wrong module.
                if info.has_unhandled_data_addr_relocs() {
                    return Err(Error::UnsupportedFeature(format!(
                        "component '{}' module {mod_idx}: shared-memory rebasing of \
                         non-32-bit inline data pointers (memory64 reloc.DATA) is not \
                         supported (#326)",
                        component_display_name(components, comp_idx),
                    )));
                }
                data_addr_relocs = info.data_memory_addr_entries();
                Some(info.code_memory_addr_offsets())
            } else {
                None
            }
        } else {
            None
        };

        let module_memory = if self.address_rebasing {
            module_memory_type(module)?
        } else {
            None
        };
        let memory64 = module_memory
            .as_ref()
            .map(|mem| mem.memory64)
            .unwrap_or(false);
        let memory_initial_pages = module_memory.as_ref().map(|mem| mem.initial);

        // Segment base offsets: this module's local segment indices land in
        // the concatenated section at `base + local`. Capture the bases NOW,
        // before this module's own segments are appended (lines below), so
        // they count only PRIOR modules' segments — exactly mirroring how
        // `func_offset = merged.functions.len()` is captured before this
        // module's functions are pushed. Record them on `merged` so the
        // post-merge re-rewrite pass (resource-import redirect) can recover
        // the correct base after `.len()` no longer equals it.
        let data_segment_base = merged.data_segments.len() as u32;
        let elem_segment_base = merged.elements.len() as u32;
        merged
            .segment_bases
            .insert((comp_idx, mod_idx), (data_segment_base, elem_segment_base));

        let index_maps = build_index_maps_for_module(
            comp_idx,
            mod_idx,
            module,
            merged,
            self.memory_strategy,
            self.address_rebasing,
            memory_base_offset,
            memory64,
            memory_initial_pages,
            data_segment_base,
            elem_segment_base,
            code_addr_relocs,
        );

        // Second pass: extract and rewrite function bodies
        for (old_idx, old_func_idx, new_type_idx, type_idx) in func_type_indices {
            let param_count = module
                .types
                .get(type_idx as usize)
                .map(|ty| ty.params.len() as u32)
                .unwrap_or(0);
            let body = extract_function_body(module, old_idx, param_count, &index_maps)?;

            merged.functions.push(MergedFunction {
                type_idx: new_type_idx,
                body,
                origin: (comp_idx, mod_idx, old_func_idx),
                synthetic_kind: None,
            });
        }

        // Merge exports (with component prefix if multiple components)
        for export in &module.exports {
            let (kind, old_idx) = match export.kind {
                ExportKind::Function => {
                    let new_idx = *merged
                        .function_index_map
                        .get(&(comp_idx, mod_idx, export.index))
                        .unwrap_or(&export.index);
                    (EncoderExportKind::Func, new_idx)
                }
                ExportKind::Table => {
                    let new_idx = *merged
                        .table_index_map
                        .get(&(comp_idx, mod_idx, export.index))
                        .unwrap_or(&export.index);
                    (EncoderExportKind::Table, new_idx)
                }
                ExportKind::Memory => {
                    let new_idx = *merged
                        .memory_index_map
                        .get(&(comp_idx, mod_idx, export.index))
                        .unwrap_or(&export.index);
                    (EncoderExportKind::Memory, new_idx)
                }
                ExportKind::Global => {
                    let new_idx = *merged
                        .global_index_map
                        .get(&(comp_idx, mod_idx, export.index))
                        .unwrap_or(&export.index);
                    (EncoderExportKind::Global, new_idx)
                }
            };

            // Export deduplication: in multi-memory mode, suffix duplicate
            // export names with the component index. Each component's shim
            // module exports numeric function names ("0", "1", ...) and a
            // "$imports" table that must remain distinct — deduplication
            // would wire the fixup module to the wrong component's indirect
            // table. In shared-memory mode, first-wins dedup is correct
            // since all components share one memory.
            // #245: `cabi_realloc` is named by the per-memory path below
            // (`cabi_realloc$<mem_idx>`), which is the convention the P2
            // wrapper consumes (component_wrap.rs looks reallocs up by
            // memory index). The generic comp_idx-suffixed dedup here must
            // NOT also mint into that namespace: when a colliding export's
            // comp_idx coincides with another realloc's mem_idx the two
            // schemes emit the same `cabi_realloc$N` twice and the output
            // fails validation ("duplicate export name"). A colliding
            // `cabi_realloc` is always comp_idx >= 1 with its own mem_idx
            // >= 1, so the per-memory path is guaranteed to publish it;
            // skip the redundant generic copy here. (Component 0's realloc
            // is the non-colliding first occurrence and still flows through
            // the else branch as plain `cabi_realloc`.)
            if self.memory_strategy == MemoryStrategy::MultiMemory
                && export.name == "cabi_realloc"
                && merged.exports.iter().any(|e| e.name == export.name)
            {
                continue;
            }
            let export_name = if self.memory_strategy == MemoryStrategy::MultiMemory
                && merged.exports.iter().any(|e| e.name == export.name)
            {
                format!("{}${}", export.name, comp_idx)
            } else if self.memory_strategy != MemoryStrategy::MultiMemory
                && merged.exports.iter().any(|e| e.name == export.name)
            {
                continue; // first-wins dedup in shared-memory mode
            } else {
                export.name.clone()
            };

            merged.exports.push(MergedExport {
                name: export_name,
                kind,
                index: old_idx,
            });
        }

        // Detect cabi_realloc for adapter generation.
        // 1. Check canonical section Realloc options (takes priority)
        //
        // The canonical section's Realloc(idx) refers to the *component-level*
        // core function index space, which spans all modules in the component
        // (and includes core functions from canon lower / aliases). For
        // single-module components the component-level index equals the
        // module-local index. For multi-module components, we decompose the
        // component-level index by accumulating per-module function counts.
        let mut realloc_from_canonical = false;

        // Helper: check if a merged function has the cabi_realloc signature
        // (i32, i32, i32, i32) -> i32.
        let is_realloc_sig = |merged: &MergedModule, merged_idx: u32| -> bool {
            if let Some(func) = merged.defined_func(merged_idx) {
                if let Some(ty) = merged.types.get(func.type_idx as usize) {
                    return ty.params.len() == 4
                        && ty.results.len() == 1
                        && ty.params.iter().all(|p| *p == wasm_encoder::ValType::I32)
                        && ty.results[0] == wasm_encoder::ValType::I32;
                }
            }
            // Import functions — accept if we can't verify
            (merged_idx as usize) < merged.import_counts.func as usize
        };

        for entry in &components[comp_idx].canonical_functions {
            let realloc_idx = match entry {
                crate::parser::CanonicalEntry::Lift { options, .. } => options.realloc,
                crate::parser::CanonicalEntry::Lower { options, .. } => options.realloc,
                _ => None,
            };
            if let Some(core_func_idx) = realloc_idx {
                // Decompose component-level core function index to
                // (target_module_idx, module_local_func_idx).
                if let Some((target_mod_idx, local_func_idx)) =
                    decompose_component_core_func_index(&components[comp_idx], core_func_idx)
                {
                    // Only store the realloc for the module currently being
                    // merged (mod_idx).
                    if target_mod_idx == mod_idx {
                        if let Some(&merged_idx) = merged.function_index_map.get(&(
                            comp_idx,
                            target_mod_idx,
                            local_func_idx,
                        )) {
                            // Validate signature: decompose_component_core_func_index
                            // can produce incorrect mappings for multi-module components
                            // because the component core function space includes canon
                            // lower entries that aren't in any module's function space.
                            if is_realloc_sig(merged, merged_idx) {
                                merged.realloc_map.insert((comp_idx, mod_idx), merged_idx);
                                realloc_from_canonical = true;
                                log::debug!(
                                    "Found canonical realloc in component {} module {}: \
                                     component core func {} -> module-local {} -> merged idx {}",
                                    comp_idx,
                                    mod_idx,
                                    core_func_idx,
                                    local_func_idx,
                                    merged_idx
                                );
                                break;
                            } else {
                                log::debug!(
                                    "Canonical realloc candidate in component {} module {} \
                                     (core func {} -> local {} -> merged {}) has wrong signature, skipping",
                                    comp_idx,
                                    mod_idx,
                                    core_func_idx,
                                    local_func_idx,
                                    merged_idx
                                );
                            }
                        }
                    }
                } else {
                    // Decomposition failed -- the index may refer to a core
                    // function created by canon lower or an alias, which lives
                    // outside any module's function space. Try a direct lookup
                    // as a fallback (works for single-module components where
                    // component-level == module-local).
                    if let Some(&merged_idx) =
                        merged
                            .function_index_map
                            .get(&(comp_idx, mod_idx, core_func_idx))
                    {
                        if is_realloc_sig(merged, merged_idx) {
                            merged.realloc_map.insert((comp_idx, mod_idx), merged_idx);
                            realloc_from_canonical = true;
                            log::debug!(
                                "Found canonical realloc (direct fallback) in component {} module {}: \
                                 core func {} -> merged idx {}",
                                comp_idx,
                                mod_idx,
                                core_func_idx,
                                merged_idx
                            );
                            break;
                        }
                    }
                }
            }
        }

        // 2. Fall back to name-based detection if canonical section didn't provide one
        if !realloc_from_canonical {
            for export in &module.exports {
                if export.name == "cabi_realloc" && export.kind == ExportKind::Function {
                    if let Some(&merged_idx) =
                        merged
                            .function_index_map
                            .get(&(comp_idx, mod_idx, export.index))
                    {
                        merged.realloc_map.insert((comp_idx, mod_idx), merged_idx);
                        log::debug!(
                            "Found cabi_realloc by name in component {} module {}: merged idx {}",
                            comp_idx,
                            mod_idx,
                            merged_idx
                        );
                    }
                }
            }
        }

        // In multi-memory mode, export per-component cabi_realloc and memories
        // so the P2 wrapper can reference the correct allocator and memory per import.
        if self.memory_strategy == MemoryStrategy::MultiMemory {
            // Export cabi_realloc$N using the MEMORY INDEX as suffix (not comp_idx).
            // The P2 wrapper looks up cabi_realloc$N by memory index, so these must match.
            let mem_idx = merged
                .memory_index_map
                .get(&(comp_idx, mod_idx, 0))
                .copied();
            if let (Some(mem_idx), Some(&realloc_idx)) =
                (mem_idx, merged.realloc_map.get(&(comp_idx, mod_idx)))
            {
                if mem_idx > 0 {
                    let export_name = format!("cabi_realloc${}", mem_idx);
                    if !merged.exports.iter().any(|e| e.name == export_name) {
                        merged.exports.push(MergedExport {
                            name: export_name,
                            kind: EncoderExportKind::Func,
                            index: realloc_idx,
                        });
                    }
                }
            }

            // Note: memory$N exports are NOT needed on the fused module.
            // The P2 wrapper's stubs module provides all memories with
            // the $N naming convention. The fused module imports them.
        }

        // Merge custom sections
        for (name, data) in &module.custom_sections {
            // #328: the `name` section carries function indices in THIS
            // module's index space. Copying it verbatim produces duplicate
            // `name` sections (llvm-dwarfdump rejects the module) whose
            // indices point at the wrong fused functions. Instead, remap its
            // function-name entries into the fused index space and accumulate
            // them; a single coalesced `name` section is emitted at encode
            // time under `preserve_names`. Function merge above has already
            // populated `function_index_map` for this module.
            if name == "name" {
                accumulate_remapped_function_names(
                    data,
                    comp_idx,
                    mod_idx,
                    &merged.function_index_map,
                    &mut merged.fused_function_names,
                );
                continue;
            }
            merged.custom_sections.push((name.clone(), data.clone()));
        }

        // Parse and merge element segments with reindexing
        let element_segments = crate::segments::parse_element_segments(module)?;
        for segment in element_segments {
            let reindexed = crate::segments::reindex_element_segment(&segment, &index_maps);
            merged.elements.push(reindexed);
        }

        // Parse and merge data segments with reindexing.
        let data_segments = crate::segments::parse_data_segments(module)?;
        for mut segment in data_segments {
            // #326 Part C: rebase absolute pointers baked into a data segment's
            // payload. `reloc.DATA` MEMORY_ADDR_I32 sites name the 4-byte LE
            // pointers; each segment's `content_offset` places its bytes in the
            // same data-section-content coordinate space as those sites.
            if memory_base_offset != 0 && !data_addr_relocs.is_empty() {
                let base = u32::try_from(memory_base_offset).map_err(|_| {
                    Error::MemoryStrategyUnsupported(
                        "shared memory base offset exceeds 32-bit address space".to_string(),
                    )
                })?;
                crate::reloc::rebase_data_segment_pointers(
                    &mut segment.data,
                    segment.content_offset,
                    &data_addr_relocs,
                    base,
                );
            }
            let reindexed = crate::segments::reindex_data_segment(&segment, &index_maps)?;
            merged.data_segments.push(reindexed);
        }

        Ok(())
    }

    /// Add remaining unresolved imports to the merged module.
    ///
    /// **Invariant**: This function MUST iterate `graph.unresolved_imports` in
    /// exactly the same order as [`compute_unresolved_import_assignments`], and
    /// must produce the same per-entity-kind position for each import. If these
    /// two functions diverge, import indices will be silently misaligned,
    /// producing incorrect wasm output. Debug assertions below verify this
    /// invariant at development/test time.
    ///
    /// **Deduplication**: When multiple unresolved imports share the same
    /// effective `(module, field)` after WASI version normalization, only the
    /// first occurrence is emitted. Subsequent duplicates are skipped but their
    /// assignments (from `compute_unresolved_import_assignments`) already point
    /// to the same position, so `function_index_map` etc. remain correct.
    fn add_unresolved_imports(
        &self,
        graph: &DependencyGraph,
        merged: &mut MergedModule,
        shared_memory_plan: Option<&SharedMemoryPlan>,
        dedup_info: &ImportDedupInfo,
    ) -> Result<()> {
        let mut shared_memory_import_added = false;

        // Track per-kind positions so we can assert alignment with
        // compute_unresolved_import_assignments.
        let mut func_position: u32 = 0;
        let mut table_position: u32 = 0;
        let mut memory_position: u32 = 0;
        let mut global_position: u32 = 0;

        // Track already-emitted dedup keys per entity kind (includes component
        // dimension in multi-memory mode so each component gets its own slot).
        let mut emitted_func: HashSet<DedupKey> = HashSet::new();
        let mut emitted_table: HashSet<DedupKey> = HashSet::new();
        let mut emitted_global: HashSet<DedupKey> = HashSet::new();

        // Track base (module, field) names already emitted for function imports
        // so we can suffix duplicates in multi-memory mode.
        let mut emitted_base_func: HashSet<(String, String)> = HashSet::new();
        // Same for tables/globals: type-mismatched same-named imports need a
        // unique (module, field) in multi-memory mode.
        let mut emitted_base_table: HashSet<(String, String)> = HashSet::new();
        let mut emitted_base_global: HashSet<(String, String)> = HashSet::new();

        for unresolved in &graph.unresolved_imports {
            // Skip imports resolved by adapter sites (must match the
            // filter in compute_unresolved_import_assignments).
            let resolved_by_adapter = graph.adapter_sites.iter().any(|site| {
                if site.from_component != unresolved.component_idx {
                    return false;
                }
                let direct = site.from_module == unresolved.module_idx
                    && site.import_name == unresolved.field_name;
                let display = unresolved.display_field.as_deref() == Some(&site.import_name);
                direct || display
            });
            if resolved_by_adapter {
                continue;
            }

            if let (Some(plan), ImportKind::Memory(_)) = (shared_memory_plan, &unresolved.kind) {
                if let Some((module, name)) = &plan.import {
                    if !shared_memory_import_added {
                        merged.imports.push(MergedImport {
                            module: module.clone(),
                            name: name.clone(),
                            entity_type: EntityType::Memory(plan.memory),
                            component_idx: None,
                        });
                        shared_memory_import_added = true;
                        memory_position += 1;
                    }
                }
                continue;
            }

            let (eff_module_norm, eff_field) = effective_import_key(unresolved);
            let comp_dim = if self.memory_strategy == MemoryStrategy::MultiMemory {
                Some(unresolved.component_idx)
            } else {
                None
            };
            let dedup_key: DedupKey = (eff_module_norm, eff_field, comp_dim);

            match &unresolved.kind {
                ImportKind::Function(type_idx) => {
                    // Check if this entry was marked as type-mismatched (not safe
                    // to dedup). If so, always emit even if the dedup_key was seen.
                    let is_type_mismatch = dedup_info.type_mismatch_entries.contains(&(
                        unresolved.component_idx,
                        unresolved.module_idx,
                        unresolved.module_name.clone(),
                        unresolved.field_name.clone(),
                    ));
                    if !is_type_mismatch && !emitted_func.insert(dedup_key.clone()) {
                        // Duplicate with matching type — skip emitting.
                        // Still record per-component resource tracking: find the
                        // func index already assigned to this resource name.
                        let eff_field = &dedup_key.1;
                        // Exact-match the full `[resource-{rep,new}]<name>`
                        // import name. The prior `ends_with(rn)` matched any
                        // resource whose name had `rn` as a suffix (e.g.
                        // `rn = "float"` collided with both
                        // `[resource-rep]float` and `[resource-rep]bigfloat`),
                        // letting `resource_rep_by_component` track the
                        // wrong import for the wrong-suffix collision — silent
                        // cross-resource confusion (LS-A-19).
                        if let Some(rn) = eff_field.strip_prefix("[resource-rep]") {
                            let expected = format!("[resource-rep]{rn}");
                            if let Some(idx) = find_exact_resource_import_idx(
                                &merged.resource_rep_by_component,
                                &merged.imports,
                                &expected,
                            ) {
                                merged
                                    .resource_rep_by_component
                                    .insert((unresolved.component_idx, rn.to_string()), idx);
                            }
                        } else if let Some(rn) = eff_field.strip_prefix("[resource-new]") {
                            let expected = format!("[resource-new]{rn}");
                            if let Some(idx) = find_exact_resource_import_idx(
                                &merged.resource_new_by_component,
                                &merged.imports,
                                &expected,
                            ) {
                                merged
                                    .resource_new_by_component
                                    .insert((unresolved.component_idx, rn.to_string()), idx);
                            }
                        }
                        continue;
                    }

                    debug_assert!(
                        func_position < merged.import_counts.func,
                        "add_unresolved_imports: func import position {} exceeds \
                         pre-computed count {} — iteration order has diverged from \
                         compute_unresolved_import_assignments",
                        func_position,
                        merged.import_counts.func,
                    );
                    func_position += 1;

                    // Remap type index
                    let new_type_idx = *merged
                        .type_index_map
                        .get(&(unresolved.component_idx, unresolved.module_idx, *type_idx))
                        .unwrap_or(type_idx);

                    // Use best version module name from dedup_info
                    let module = dedup_info
                        .best_module_version
                        .get(&dedup_key)
                        .cloned()
                        .unwrap_or_else(|| {
                            unresolved
                                .display_module
                                .as_ref()
                                .unwrap_or(&unresolved.module_name)
                                .clone()
                        });

                    // In multi-memory mode, suffix the field name with $comp_idx
                    // when a different component already emitted the same base name.
                    // This ensures unique (module, field) pairs in the wasm binary.
                    let base_key = (dedup_key.0.clone(), dedup_key.1.clone());
                    let needs_suffix = self.memory_strategy == MemoryStrategy::MultiMemory
                        && !emitted_base_func.insert(base_key);
                    let name = if needs_suffix {
                        format!("{}${}", dedup_key.1, unresolved.component_idx)
                    } else {
                        dedup_key.1.clone()
                    };

                    // Populate per-import metadata for component_wrap
                    let mem_idx = component_memory_index(merged, unresolved.component_idx);
                    let realloc_idx = component_realloc_index(merged, unresolved.component_idx);
                    merged.import_memory_indices.push(mem_idx);
                    merged.import_realloc_indices.push(realloc_idx);

                    merged.imports.push(MergedImport {
                        module,
                        name,
                        entity_type: EntityType::Function(new_type_idx),
                        component_idx: Some(unresolved.component_idx),
                    });

                    // Track per-component resource import indices.
                    // Strip $N suffix (multi-memory dedup) from the resource name
                    // so the adapter can look up by bare name (e.g., "float" not "float$5").
                    let merged_func_idx = func_position - 1;
                    let eff_field = &dedup_key.1;
                    if let Some(rn) = eff_field.strip_prefix("[resource-rep]") {
                        let bare_rn = rn.rsplit_once('$').map_or(rn, |(base, _)| base);
                        merged
                            .resource_rep_by_component
                            .entry((unresolved.component_idx, bare_rn.to_string()))
                            .or_insert(merged_func_idx);
                    } else if let Some(rn) = eff_field.strip_prefix("[resource-new]") {
                        let bare_rn = rn.rsplit_once('$').map_or(rn, |(base, _)| base);
                        merged
                            .resource_new_by_component
                            .entry((unresolved.component_idx, bare_rn.to_string()))
                            .or_insert(merged_func_idx);
                    }
                }
                ImportKind::Table(t) => {
                    // Type-mismatched entries must emit a separate import even
                    // when the dedup key was already seen (mirrors the function
                    // arm). Same-typed duplicates still collapse to one slot.
                    let is_type_mismatch = dedup_info.type_mismatch_entries.contains(&(
                        unresolved.component_idx,
                        unresolved.module_idx,
                        unresolved.module_name.clone(),
                        unresolved.field_name.clone(),
                    ));
                    if !is_type_mismatch && !emitted_table.insert(dedup_key.clone()) {
                        continue;
                    }

                    debug_assert!(
                        table_position < merged.import_counts.table,
                        "add_unresolved_imports: table import position {} exceeds \
                         pre-computed count {} — iteration order has diverged from \
                         compute_unresolved_import_assignments",
                        table_position,
                        merged.import_counts.table,
                    );
                    table_position += 1;

                    let module = dedup_info
                        .best_module_version
                        .get(&dedup_key)
                        .cloned()
                        .unwrap_or_else(|| {
                            unresolved
                                .display_module
                                .as_ref()
                                .unwrap_or(&unresolved.module_name)
                                .clone()
                        });
                    // In multi-memory mode, suffix the field with $comp_idx when
                    // a different component already emitted the same base name,
                    // keeping (module, field) pairs unique (mirrors func arm).
                    let base_key = (dedup_key.0.clone(), dedup_key.1.clone());
                    let needs_suffix = self.memory_strategy == MemoryStrategy::MultiMemory
                        && !emitted_base_table.insert(base_key);
                    let name = if needs_suffix {
                        format!("{}${}", dedup_key.1, unresolved.component_idx)
                    } else {
                        dedup_key.1.clone()
                    };

                    merged.imports.push(MergedImport {
                        module,
                        name,
                        entity_type: EntityType::Table(convert_table_type(
                            t,
                            unresolved.component_idx,
                            unresolved.module_idx,
                            merged,
                        )),
                        component_idx: Some(unresolved.component_idx),
                    });
                }
                ImportKind::Memory(m) => {
                    memory_position += 1;

                    let module = unresolved
                        .display_module
                        .as_ref()
                        .unwrap_or(&unresolved.module_name)
                        .clone();
                    let name = unresolved
                        .display_field
                        .as_ref()
                        .unwrap_or(&unresolved.field_name)
                        .clone();
                    merged.imports.push(MergedImport {
                        module,
                        name,
                        entity_type: EntityType::Memory(convert_memory_type(m)),
                        component_idx: Some(unresolved.component_idx),
                    });
                }
                ImportKind::Global(g) => {
                    // Type-mismatched entries must emit a separate import even
                    // when the dedup key was already seen (mirrors the function
                    // arm). Same-typed duplicates still collapse to one slot.
                    let is_type_mismatch = dedup_info.type_mismatch_entries.contains(&(
                        unresolved.component_idx,
                        unresolved.module_idx,
                        unresolved.module_name.clone(),
                        unresolved.field_name.clone(),
                    ));
                    if !is_type_mismatch && !emitted_global.insert(dedup_key.clone()) {
                        continue;
                    }

                    debug_assert!(
                        global_position < merged.import_counts.global,
                        "add_unresolved_imports: global import position {} exceeds \
                         pre-computed count {} — iteration order has diverged from \
                         compute_unresolved_import_assignments",
                        global_position,
                        merged.import_counts.global,
                    );
                    global_position += 1;

                    let module = dedup_info
                        .best_module_version
                        .get(&dedup_key)
                        .cloned()
                        .unwrap_or_else(|| {
                            unresolved
                                .display_module
                                .as_ref()
                                .unwrap_or(&unresolved.module_name)
                                .clone()
                        });
                    // In multi-memory mode, suffix the field with $comp_idx when
                    // a different component already emitted the same base name,
                    // keeping (module, field) pairs unique (mirrors func arm).
                    let base_key = (dedup_key.0.clone(), dedup_key.1.clone());
                    let needs_suffix = self.memory_strategy == MemoryStrategy::MultiMemory
                        && !emitted_base_global.insert(base_key);
                    let name = if needs_suffix {
                        format!("{}${}", dedup_key.1, unresolved.component_idx)
                    } else {
                        dedup_key.1.clone()
                    };

                    merged.imports.push(MergedImport {
                        module,
                        name,
                        entity_type: EntityType::Global(convert_global_type(
                            g,
                            unresolved.component_idx,
                            unresolved.module_idx,
                            merged,
                        )),
                        component_idx: Some(unresolved.component_idx),
                    });
                }
            };
        }

        if let Some(plan) = shared_memory_plan {
            if let Some((module, name)) = &plan.import {
                if !shared_memory_import_added {
                    merged.imports.push(MergedImport {
                        module: module.clone(),
                        name: name.clone(),
                        entity_type: EntityType::Memory(plan.memory),
                        component_idx: None,
                    });
                    memory_position += 1;
                }
            }
        }

        // Final totals must match what compute_unresolved_import_assignments produced.
        debug_assert_eq!(
            func_position, merged.import_counts.func,
            "add_unresolved_imports: final func count ({}) != pre-computed ({}). \
             The iteration order has diverged from compute_unresolved_import_assignments.",
            func_position, merged.import_counts.func,
        );
        debug_assert_eq!(
            table_position, merged.import_counts.table,
            "add_unresolved_imports: final table count ({}) != pre-computed ({}). \
             The iteration order has diverged from compute_unresolved_import_assignments.",
            table_position, merged.import_counts.table,
        );
        debug_assert_eq!(
            memory_position, merged.import_counts.memory,
            "add_unresolved_imports: final memory count ({}) != pre-computed ({}). \
             The iteration order has diverged from compute_unresolved_import_assignments.",
            memory_position, merged.import_counts.memory,
        );
        debug_assert_eq!(
            global_position, merged.import_counts.global,
            "add_unresolved_imports: final global count ({}) != pre-computed ({}). \
             The iteration order has diverged from compute_unresolved_import_assignments.",
            global_position, merged.import_counts.global,
        );

        Ok(())
    }

    /// Resolve start functions from multiple components
    fn resolve_start_functions(
        &self,
        components: &[ParsedComponent],
        merged: &mut MergedModule,
    ) -> Result<()> {
        // Collect all start functions
        let mut start_funcs = Vec::new();
        for (comp_idx, component) in components.iter().enumerate() {
            for (mod_idx, module) in component.core_modules.iter().enumerate() {
                if let Some(start_idx) = module.start {
                    if let Some(&new_idx) = merged
                        .function_index_map
                        .get(&(comp_idx, mod_idx, start_idx))
                    {
                        start_funcs.push(new_idx);
                    }
                }
            }
        }

        if start_funcs.len() == 1 {
            merged.start_function = Some(start_funcs[0]);
        } else if start_funcs.len() > 1 {
            // Generate a wrapper function that calls all start functions in order.
            // Start functions have type [] -> [], so the wrapper is also [] -> [].

            // Find or create the [] -> [] type
            let empty_type_idx = merged
                .types
                .iter()
                .position(|t| t.params.is_empty() && t.results.is_empty())
                .unwrap_or_else(|| {
                    let idx = merged.types.len();
                    merged.types.push(MergedFuncType {
                        params: vec![],
                        results: vec![],
                    });
                    idx
                }) as u32;

            let mut wrapper = Function::new(vec![]);
            for &func_idx in &start_funcs {
                wrapper.instruction(&wasm_encoder::Instruction::Call(func_idx));
            }
            wrapper.instruction(&wasm_encoder::Instruction::End);

            // The wrapper's function index = import_func_count + functions.len()
            let wrapper_idx = merged.import_counts.func + merged.functions.len() as u32;

            merged.functions.push(MergedFunction {
                type_idx: empty_type_idx,
                body: wrapper,
                origin: (usize::MAX, usize::MAX, 0), // synthetic function
                synthetic_kind: Some(SyntheticKind::StartWrapper),
            });

            log::info!(
                "Generated start wrapper (func {}) calling {} start functions",
                wrapper_idx,
                start_funcs.len()
            );
            merged.start_function = Some(wrapper_idx);
        }

        Ok(())
    }
}

/// Decompose a component-level core function index into (module_idx, module_local_func_idx).
///
/// The component-level core function index space is formed by concatenating
/// each core module's function space (imports + defined functions) in module
/// order. This function finds which module the given index falls in and
/// returns the module index and the module-local function index.
///
/// Returns `None` if `core_func_idx` exceeds the total number of functions
/// across all modules (it may refer to a core function created by `canon lower`
/// or an alias, which lives outside any module's function space).
pub(crate) fn decompose_component_core_func_index(
    component: &ParsedComponent,
    core_func_idx: u32,
) -> Option<(usize, u32)> {
    let mut running: u32 = 0;
    for (mod_idx, module) in component.core_modules.iter().enumerate() {
        let import_func_count = module
            .imports
            .iter()
            .filter(|i| matches!(i.kind, ImportKind::Function(_)))
            .count() as u32;
        let module_func_count = import_func_count + module.functions.len() as u32;
        if core_func_idx < running.saturating_add(module_func_count) {
            return Some((mod_idx, core_func_idx - running));
        }
        running = running.saturating_add(module_func_count);
    }
    None
}

pub(crate) fn module_memory_type(module: &CoreModule) -> Result<Option<MemoryType>> {
    let mut memory_type: Option<MemoryType> = None;

    for import in &module.imports {
        if let ImportKind::Memory(mem) = &import.kind {
            if memory_type.is_some() {
                return Err(Error::MemoryStrategyUnsupported(
                    "shared memory rebasing supports a single memory per module".to_string(),
                ));
            }
            memory_type = Some(mem.clone());
        }
    }

    for mem in &module.memories {
        if memory_type.is_some() {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory rebasing supports a single memory per module".to_string(),
            ));
        }
        memory_type = Some(mem.clone());
    }

    Ok(memory_type)
}

fn combine_memory_types_shared(memories: &[MemoryType]) -> Result<MemoryType> {
    let Some(first) = memories.first() else {
        return Err(Error::MemoryStrategyUnsupported(
            "shared memory requires at least one memory".to_string(),
        ));
    };

    let mut minimum = first.initial;
    let mut maximum = first.maximum;

    for mem in memories.iter().skip(1) {
        if mem.memory64 != first.memory64 {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory requires matching memory64 settings".to_string(),
            ));
        }
        if mem.shared != first.shared {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory requires matching shared settings".to_string(),
            ));
        }

        minimum = minimum.max(mem.initial);
        maximum = match (maximum, mem.maximum) {
            (Some(a), Some(b)) => Some(a.min(b)),
            _ => None,
        };
    }

    if let Some(max) = maximum {
        if minimum > max {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory minimum exceeds maximum".to_string(),
            ));
        }
    }

    Ok(MemoryType {
        memory64: first.memory64,
        shared: first.shared,
        initial: minimum,
        maximum,
    })
}

fn combine_memory_types_rebased(memories: &[MemoryType]) -> Result<MemoryType> {
    let Some(first) = memories.first() else {
        return Err(Error::MemoryStrategyUnsupported(
            "shared memory requires at least one memory".to_string(),
        ));
    };

    let mut minimum = 0u64;
    let mut maximum: Option<u64> = Some(0);

    for mem in memories {
        if mem.memory64 != first.memory64 {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory requires matching memory64 settings".to_string(),
            ));
        }
        if mem.shared != first.shared {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory requires matching shared settings".to_string(),
            ));
        }

        minimum = minimum
            .checked_add(mem.initial)
            .ok_or_else(|| Error::MemoryStrategyUnsupported("memory size overflow".to_string()))?;

        maximum = match (maximum, mem.maximum) {
            (Some(a), Some(b)) => a.checked_add(b),
            _ => None,
        };
    }

    if !first.memory64 {
        let max_pages = u64::from(u32::MAX) / WASM_PAGE_SIZE;
        if minimum > max_pages {
            return Err(Error::MemoryStrategyUnsupported(
                "shared memory exceeds 32-bit address space".to_string(),
            ));
        }
        if let Some(max) = maximum {
            if max > max_pages {
                return Err(Error::MemoryStrategyUnsupported(
                    "shared memory maximum exceeds 32-bit address space".to_string(),
                ));
            }
        }
    }

    Ok(MemoryType {
        memory64: first.memory64,
        shared: first.shared,
        initial: minimum,
        maximum,
    })
}

/// Convert parser MemoryType to encoder MemoryType
fn convert_memory_type(mem: &MemoryType) -> EncoderMemoryType {
    EncoderMemoryType {
        minimum: mem.initial,
        maximum: mem.maximum,
        memory64: mem.memory64,
        shared: mem.shared,
        page_size_log2: None,
    }
}

/// Remap a concrete heap-type index embedded in a `RefType` through the
/// per-module type index map, so it points at the correct merged type.
///
/// Concrete indices on `RefType`s produced by the parser are *module-level*
/// (see `parser.rs::convert_ref_type`). When the merger renumbers types it
/// records `(comp_idx, mod_idx, old_idx) -> merged_idx` in
/// `merged.type_index_map` (built at the top of `merge_module`). This applies
/// that same mapping. Abstract heap types carry no index and are returned
/// unchanged.
///
/// This mirrors the concrete-heap-type remap already done for `ref.null` const
/// expressions (the `RefNull` arm in `convert_const_expr`); that path remaps
/// indices in *const-expression operands*, whereas this remaps the indices in
/// *type/table/global section declarations*. The two cover disjoint structures,
/// so applying this does not double-remap anything that path already handles.
fn remap_concrete_ref_type(
    rt: RefType,
    comp_idx: usize,
    mod_idx: usize,
    merged: &MergedModule,
) -> RefType {
    let heap_type = match rt.heap_type {
        wasm_encoder::HeapType::Concrete(old_idx) => {
            let new_idx = merged
                .type_index_map
                .get(&(comp_idx, mod_idx, old_idx))
                .copied()
                .unwrap_or(old_idx);
            wasm_encoder::HeapType::Concrete(new_idx)
        }
        other => other,
    };
    RefType { heap_type, ..rt }
}

/// Remap a concrete heap-type index embedded in a `ValType` (no-op for
/// non-reference value types). Used for func-signature params/results and
/// global content types. See [`remap_concrete_ref_type`].
fn remap_concrete_val_type(
    ty: ValType,
    comp_idx: usize,
    mod_idx: usize,
    merged: &MergedModule,
) -> ValType {
    match ty {
        ValType::Ref(rt) => ValType::Ref(remap_concrete_ref_type(rt, comp_idx, mod_idx, merged)),
        other => other,
    }
}

/// Convert parser TableType to encoder TableType.
///
/// `element_type` may be a concrete typed-ref (`(ref null $t)`); its
/// module-level type index is remapped to the merged-module index via
/// [`remap_concrete_ref_type`].
fn convert_table_type(
    table: &TableType,
    comp_idx: usize,
    mod_idx: usize,
    merged: &MergedModule,
) -> EncoderTableType {
    EncoderTableType {
        element_type: match table.element_type {
            ValType::Ref(rt) => remap_concrete_ref_type(rt, comp_idx, mod_idx, merged),
            _ => RefType::FUNCREF,
        },
        table64: false,
        minimum: table.initial,
        maximum: table.maximum,
        shared: false,
    }
}

/// Convert parser GlobalType to encoder GlobalType.
///
/// `content_type` may be a concrete typed-ref; its module-level type index is
/// remapped to the merged-module index via [`remap_concrete_val_type`].
fn convert_global_type(
    global: &GlobalType,
    comp_idx: usize,
    mod_idx: usize,
    merged: &MergedModule,
) -> EncoderGlobalType {
    EncoderGlobalType {
        val_type: remap_concrete_val_type(global.content_type, comp_idx, mod_idx, merged),
        mutable: global.mutable,
        shared: false,
    }
}

/// Display name for a component (its declared name, else `component-<idx>`).
/// Used in #326 diagnostics.
fn component_display_name(components: &[ParsedComponent], comp_idx: usize) -> String {
    components
        .get(comp_idx)
        .and_then(|c| c.name.clone())
        .unwrap_or_else(|| format!("component-{comp_idx}"))
}

/// Whether `module` performs any *direct* (non-bulk) linear-memory access — an
/// `i32.load`/`i32.store` family instruction whose effective address may embed
/// a baked-in absolute address.
///
/// Bulk-memory ops (`memory.copy`/`fill`/`init`) are deliberately excluded: the
/// rewriter rebases their runtime address operands dynamically
/// ([`crate::rewriter`]'s `append_rebased_address`), so a module whose only
/// memory touches are bulk ops is safe to place at a non-zero shared-memory
/// base even without relocation metadata. This is what lets #326's path-F gate
/// fire precisely — on modules that could hide an un-rebased absolute address —
/// without rejecting the (safe) bulk-only case.
///
/// KNOWN LIMITATION (#326 Finding A, tracked follow-up): this catches an
/// address embedded in a load/store, but NOT an `i32.const`/`i64.const` whose
/// value is itself an absolute address used purely as a *value* (handed to an
/// imported `memcpy`/`fd_write` or returned across the module boundary) with no
/// direct access. Such a no-reloc module still slips the gate. A sound fix
/// needs data-flow (a bare const is indistinguishable from an integer, and
/// bulk-op-consumed consts ARE safe — rejecting all consts regresses the
/// legitimate bulk-only case, `test_address_rebasing_end_to_end`). Note this
/// residual gap does NOT affect the supported path: `--emit-relocs` inputs
/// carry reloc metadata, so their address consts are rebased via `reloc.CODE`.
fn module_has_direct_memory_access(module: &CoreModule) -> Result<bool> {
    let Some((start, end)) = module.code_section_range else {
        return Ok(false);
    };
    let code_bytes = &module.bytes[start..end];
    let reader = wasmparser::CodeSectionReader::new(wasmparser::BinaryReader::new(code_bytes, 0))?;
    for body in reader {
        let body = body?;
        for op in body.get_operators_reader()? {
            if is_direct_memory_access(&op?) {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

/// True for the standard integer/float load & store operators (the ones that
/// carry a `memarg`). See [`module_has_direct_memory_access`].
fn is_direct_memory_access(op: &wasmparser::Operator<'_>) -> bool {
    use wasmparser::Operator::*;
    matches!(
        op,
        I32Load { .. }
            | I64Load { .. }
            | F32Load { .. }
            | F64Load { .. }
            | I32Load8S { .. }
            | I32Load8U { .. }
            | I32Load16S { .. }
            | I32Load16U { .. }
            | I64Load8S { .. }
            | I64Load8U { .. }
            | I64Load16S { .. }
            | I64Load16U { .. }
            | I64Load32S { .. }
            | I64Load32U { .. }
            | I32Store { .. }
            | I64Store { .. }
            | F32Store { .. }
            | F64Store { .. }
            | I32Store8 { .. }
            | I32Store16 { .. }
            | I64Store8 { .. }
            | I64Store16 { .. }
            | I64Store32 { .. }
    )
}

/// Build IndexMaps for a module from the merger's index maps
///
/// This creates a local view of index remappings for a specific module,
/// which is used when rewriting function bodies.
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_index_maps_for_module(
    comp_idx: usize,
    mod_idx: usize,
    module: &CoreModule,
    merged: &MergedModule,
    memory_strategy: MemoryStrategy,
    address_rebasing: bool,
    memory_base_offset: u64,
    memory64: bool,
    memory_initial_pages: Option<u64>,
    data_segment_base: u32,
    elem_segment_base: u32,
    code_addr_relocs: Option<std::collections::HashSet<u32>>,
) -> IndexMaps {
    let mut maps = IndexMaps::new();
    maps.address_rebasing = address_rebasing;
    maps.memory_base_offset = memory_base_offset;
    maps.memory64 = memory64;
    maps.memory_initial_pages = memory_initial_pages;
    maps.code_addr_relocs = code_addr_relocs;

    // Build function map (including imported functions)
    let import_func_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Function(_)))
        .count() as u32;

    // Map imported functions (they're resolved elsewhere, map to self for now)
    for i in 0..import_func_count {
        if let Some(&new_idx) = merged.function_index_map.get(&(comp_idx, mod_idx, i)) {
            maps.functions.insert(i, new_idx);
        }
    }

    // Map defined functions
    for old_idx in 0..module.functions.len() as u32 {
        let full_idx = import_func_count + old_idx;
        if let Some(&new_idx) = merged
            .function_index_map
            .get(&(comp_idx, mod_idx, full_idx))
        {
            maps.functions.insert(full_idx, new_idx);
        }
    }

    // Build type map
    for old_idx in 0..module.types.len() as u32 {
        if let Some(&new_idx) = merged.type_index_map.get(&(comp_idx, mod_idx, old_idx)) {
            maps.types.insert(old_idx, new_idx);
        }
    }

    // Build global map (including imported globals)
    let import_global_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Global(_)))
        .count() as u32;

    // Map imported globals (they may be resolved via module_resolutions)
    for i in 0..import_global_count {
        if let Some(&new_idx) = merged.global_index_map.get(&(comp_idx, mod_idx, i)) {
            maps.globals.insert(i, new_idx);
        }
    }

    // Map defined globals
    for old_idx in 0..module.globals.len() as u32 {
        let full_idx = import_global_count + old_idx;
        if let Some(&new_idx) = merged.global_index_map.get(&(comp_idx, mod_idx, full_idx)) {
            maps.globals.insert(full_idx, new_idx);
        }
    }

    // Build table map (including imported tables)
    let import_table_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Table(_)))
        .count() as u32;

    // Map imported tables (they may be resolved via module_resolutions)
    for i in 0..import_table_count {
        if let Some(&new_idx) = merged.table_index_map.get(&(comp_idx, mod_idx, i)) {
            maps.tables.insert(i, new_idx);
        }
    }

    // Map defined tables
    for old_idx in 0..module.tables.len() as u32 {
        let full_idx = import_table_count + old_idx;
        if let Some(&new_idx) = merged.table_index_map.get(&(comp_idx, mod_idx, full_idx)) {
            maps.tables.insert(full_idx, new_idx);
        }
    }

    // Build memory map
    let import_mem_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Memory(_)))
        .count() as u32;

    let total_memories = import_mem_count + module.memories.len() as u32;
    if memory_strategy == MemoryStrategy::SharedMemory {
        for idx in 0..total_memories {
            maps.memories.insert(idx, 0);
        }
    } else {
        // Multi-memory: map both imported and defined memory indices
        for idx in 0..import_mem_count {
            if let Some(&new_idx) = merged.memory_index_map.get(&(comp_idx, mod_idx, idx)) {
                maps.memories.insert(idx, new_idx);
            }
        }
        for old_idx in 0..module.memories.len() as u32 {
            let full_idx = import_mem_count + old_idx;
            if let Some(&new_idx) = merged.memory_index_map.get(&(comp_idx, mod_idx, full_idx)) {
                maps.memories.insert(full_idx, new_idx);
            }
        }
    }

    // Build data-segment and element-segment maps.
    //
    // The merger concatenates every module's segments into one shared
    // section in deterministic merge order, so this module's local segment
    // `local` lands at fused ordinal `base + local`, where `base` is the
    // number of segments contributed by all PRIOR modules. The caller
    // supplies that base (captured from `merged.data_segments.len()` /
    // `merged.elements.len()` BEFORE this module's segments are appended —
    // the same timing as `func_offset = merged.functions.len()`).
    //
    // Data/element segments are never imported in core wasm, so there is
    // no import-count adjustment as there is for funcs/globals/tables/mems.
    let data_segment_count = crate::segments::count_data_segments(module);
    for local in 0..data_segment_count {
        maps.data_segments.insert(local, data_segment_base + local);
    }
    let elem_segment_count = crate::segments::count_element_segments(module);
    for local in 0..elem_segment_count {
        maps.elements.insert(local, elem_segment_base + local);
    }

    maps
}

/// Create a default global initializer expression
fn create_global_init(val_type: &ValType) -> ConstExpr {
    match val_type {
        ValType::I32 => ConstExpr::i32_const(0),
        ValType::I64 => ConstExpr::i64_const(0),
        ValType::F32 => ConstExpr::f32_const(0.0_f32.into()),
        ValType::F64 => ConstExpr::f64_const(0.0_f64.into()),
        ValType::V128 => ConstExpr::v128_const(0),
        ValType::Ref(rt) => ConstExpr::ref_null(rt.heap_type),
    }
}

/// Convert stored init expression bytes into a `wasm_encoder::ConstExpr`,
/// remapping any global or function indices through the merged module maps.
///
/// Falls back to `create_global_init` (zeros) when `bytes` is empty (e.g. for
/// imported globals which have no initializer stored), and to raw byte emission
/// for any unrecognised operator pattern.
fn convert_init_expr(
    bytes: &[u8],
    comp_idx: usize,
    mod_idx: usize,
    merged: &MergedModule,
    val_type: &ValType,
) -> ConstExpr {
    if bytes.is_empty() {
        return create_global_init(val_type);
    }

    // Append the End opcode so wasmparser sees a complete const-expr
    let mut full = bytes.to_vec();
    full.push(0x0B);

    let bin_reader = wasmparser::BinaryReader::new(&full, 0);
    let parser_expr = wasmparser::ConstExpr::new(bin_reader);
    let mut ops = parser_expr.get_operators_reader();

    let op = match ops.read() {
        Ok(op) => op,
        Err(_) => return ConstExpr::raw(bytes.iter().copied()),
    };

    match op {
        // For an i32 / i64 const, the wasm 2.0 extended-const proposal
        // permits further `i32.add` / `i32.sub` / `i32.mul` (and i64
        // counterparts) before `end`. Fold them into a single value via
        // the shared helper so the merged global preserves the source's
        // semantic initializer. Prior versions of this function read
        // only the first op and silently dropped the rest, producing a
        // wrong-valued global (LS-A-11).
        wasmparser::Operator::I32Const { value } => {
            match crate::segments::fold_extended_const_i32(&mut ops, value) {
                Ok(folded) => ConstExpr::i32_const(folded),
                Err(_) => ConstExpr::raw(bytes.iter().copied()),
            }
        }
        wasmparser::Operator::I64Const { value } => {
            match crate::segments::fold_extended_const_i64(&mut ops, value) {
                Ok(folded) => ConstExpr::i64_const(folded),
                Err(_) => ConstExpr::raw(bytes.iter().copied()),
            }
        }
        wasmparser::Operator::F32Const { value } => {
            ConstExpr::f32_const(f32::from_bits(value.bits()).into())
        }
        wasmparser::Operator::F64Const { value } => {
            ConstExpr::f64_const(f64::from_bits(value.bits()).into())
        }
        wasmparser::Operator::V128Const { value } => {
            ConstExpr::v128_const(i128::from_le_bytes(*value.bytes()))
        }
        wasmparser::Operator::GlobalGet { global_index } => {
            let remapped = merged
                .global_index_map
                .get(&(comp_idx, mod_idx, global_index))
                .copied()
                .unwrap_or(global_index);
            ConstExpr::global_get(remapped)
        }
        wasmparser::Operator::RefFunc { function_index } => {
            let remapped = merged
                .function_index_map
                .get(&(comp_idx, mod_idx, function_index))
                .copied()
                .unwrap_or(function_index);
            ConstExpr::ref_func(remapped)
        }
        wasmparser::Operator::RefNull { hty } => {
            let heap_type = match hty {
                wasmparser::HeapType::Abstract { shared, ty } => wasm_encoder::HeapType::Abstract {
                    shared,
                    ty: convert_abstract_heap_type(ty),
                },
                wasmparser::HeapType::Concrete(idx) | wasmparser::HeapType::Exact(idx) => {
                    let old_idx = idx.as_module_index().unwrap_or(0);
                    let new_idx = merged
                        .type_index_map
                        .get(&(comp_idx, mod_idx, old_idx))
                        .copied()
                        .unwrap_or(old_idx);
                    wasm_encoder::HeapType::Concrete(new_idx)
                }
            };
            ConstExpr::ref_null(heap_type)
        }
        // Unrecognised pattern — emit the raw bytes as-is
        _ => ConstExpr::raw(bytes.iter().copied()),
    }
}

/// Extract and rewrite function body from module bytes
///
/// This function:
/// 1. Parses the code section from the module bytes
/// 2. Finds the function body at the specified index
/// 3. Rewrites all index references using the provided maps
pub(crate) fn extract_function_body(
    module: &CoreModule,
    func_idx: usize,
    param_count: u32,
    maps: &IndexMaps,
) -> Result<Function> {
    // If no code section, return an unreachable function
    let Some((start, end)) = module.code_section_range else {
        let mut func = Function::new([]);
        func.instruction(&wasm_encoder::Instruction::Unreachable);
        func.instruction(&wasm_encoder::Instruction::End);
        return Ok(func);
    };

    // Parse the code section to find the function body
    let code_bytes = &module.bytes[start..end];
    let binary_reader = wasmparser::BinaryReader::new(code_bytes, 0);
    let reader = wasmparser::CodeSectionReader::new(binary_reader)?;

    let mut current_func_idx = 0;
    for body in reader {
        let body = body?;
        if current_func_idx == func_idx {
            // Found the function - rewrite it with the index maps
            return rewrite_function_body(&body, param_count, maps);
        }
        current_func_idx += 1;
    }

    // Function not found - return unreachable
    Err(Error::IndexOutOfBounds {
        kind: "function",
        index: func_idx as u32,
        max: current_func_idx as u32,
    })
}

impl Default for Merger {
    fn default() -> Self {
        Self::new(MemoryStrategy::MultiMemory, false)
    }
}

/// Pre-compute unresolved import counts and per-import index assignments.
/// Find the merged memory index for a component's first defined memory.
pub(crate) fn component_memory_index(merged: &MergedModule, comp_idx: usize) -> u32 {
    for (&(ci, _mi, mem_i), &merged_idx) in &merged.memory_index_map {
        if ci == comp_idx && mem_i == 0 {
            return merged_idx;
        }
    }
    0 // fallback: memory 0
}

/// Find the merged function index of a component's cabi_realloc.
///
/// Prefers module 0's realloc (the main module). If module 0 has no
/// realloc, falls back to the realloc bound to the **lowest** module
/// index for this component — chosen deterministically rather than via
/// HashMap iteration order, which would let the hasher state pick a
/// different module on every run and produce non-reproducible output
/// (LS-A-15).
pub(crate) fn component_realloc_index(merged: &MergedModule, comp_idx: usize) -> Option<u32> {
    // Prefer module 0's realloc (the main module)
    if let Some(&idx) = merged.realloc_map.get(&(comp_idx, 0)) {
        return Some(idx);
    }
    // Fallback: pick the smallest module index belonging to this component,
    // deterministically. HashMap.iter() returns entries in hash-seed
    // order, which varies per process; collect-and-sort gives reproducible
    // output and removes the multi-realloc race condition.
    let mut module_idxs: Vec<usize> = merged
        .realloc_map
        .keys()
        .filter(|(ci, _)| *ci == comp_idx)
        .map(|(_, mi)| *mi)
        .collect();
    module_idxs.sort_unstable();
    module_idxs
        .first()
        .and_then(|mi| merged.realloc_map.get(&(comp_idx, *mi)).copied())
}

///
/// # Import Order Invariant
///
/// This function and [`Merger::add_unresolved_imports`] **must** iterate
/// `graph.unresolved_imports` in exactly the same order and apply the same
/// skip/dedup logic for shared-memory imports.  The indices assigned here
/// are used during `merge_core_module` to populate `function_index_map`,
/// `global_index_map`, and `table_index_map` for unresolved imports.
/// Later, `add_unresolved_imports` emits the actual import entries at those
/// same positions.  If the two functions diverge, an import at position N
/// in the merged section will have a different entity than the index maps
/// expect, producing silently incorrect wasm output.
///
/// `add_unresolved_imports` contains `debug_assert!` checks that verify
/// the per-kind counts match what this function computed.  These fire in
/// debug/test builds if the invariant is ever broken.
fn compute_unresolved_import_assignments(
    graph: &DependencyGraph,
    shared_memory_plan: Option<&SharedMemoryPlan>,
    components: &[ParsedComponent],
    memory_strategy: MemoryStrategy,
) -> (ImportCounts, UnresolvedImportAssignments, ImportDedupInfo) {
    use crate::parser::FuncType;

    let mut counts = ImportCounts::default();
    let mut assignments = UnresolvedImportAssignments {
        func: HashMap::new(),
        global: HashMap::new(),
        table: HashMap::new(),
    };
    let mut shared_memory_import_counted = false;

    // Per-kind dedup: map dedup key → (first-assigned position, type signature).
    // In multi-memory mode the key includes the component index so each
    // component gets its own import slot for per-component canon lower.
    let mut seen_func: HashMap<DedupKey, (u32, Option<FuncType>)> = HashMap::new();
    // Table/global dedup maps also carry the entity TYPE alongside the first
    // assigned position, mirroring the function arm. Two same-named imports
    // with structurally different types must NOT be merged into one slot — the
    // second importer's code would then operate on the wrong-typed entity,
    // producing an invalid fused module. Type identity:
    //   TableType  = (element_type, initial, maximum)
    //   GlobalType = (content_type, mutable)
    // (init_expr_bytes is irrelevant: imported globals carry no initializer.)
    type TableSig = (ValType, u64, Option<u64>);
    type GlobalSig = (ValType, bool);
    let mut seen_table: HashMap<DedupKey, (u32, TableSig)> = HashMap::new();
    let mut seen_global: HashMap<DedupKey, (u32, GlobalSig)> = HashMap::new();

    // Track highest version for each dedup key
    let mut best_module_version: HashMap<DedupKey, String> = HashMap::new();
    // Track entries where type mismatch prevented deduplication
    let mut type_mismatch_entries: HashSet<(usize, usize, String, String)> = HashSet::new();

    let mut adapter_skip_count = 0usize;
    for unresolved in &graph.unresolved_imports {
        // Skip imports that are resolved by adapter sites (cross-component
        // or per-function interface wiring).  Match on both raw core names
        // (module_name/field_name) and display names (display_module/display_field)
        // because indirect-table shim modules use synthetic names (module="",
        // field="0") while their display names carry the original interface names.
        let resolved_by_adapter = graph.adapter_sites.iter().any(|site| {
            if site.from_component != unresolved.component_idx {
                return false;
            }
            // Direct match: same module, field matches import_name
            let direct = site.from_module == unresolved.module_idx
                && site.import_name == unresolved.field_name;
            // Display match: display_field matches import_name (for shim modules
            // whose raw field is a numeric index)
            let display = unresolved.display_field.as_deref() == Some(&site.import_name);
            direct || display
        });
        if resolved_by_adapter {
            adapter_skip_count += 1;
            continue;
        }

        if let (Some(plan), ImportKind::Memory(_)) = (shared_memory_plan, &unresolved.kind) {
            if plan.import.is_some() && !shared_memory_import_counted {
                counts.memory += 1;
                shared_memory_import_counted = true;
            }
            continue;
        }

        let (eff_module_norm, eff_field) = effective_import_key(unresolved);
        let comp_dim = if memory_strategy == MemoryStrategy::MultiMemory {
            Some(unresolved.component_idx)
        } else {
            None
        };
        let dedup_key: DedupKey = (eff_module_norm, eff_field, comp_dim);
        let eff_module = effective_module_name(unresolved);

        // Update best version for this dedup key
        match best_module_version.entry(dedup_key.clone()) {
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(eff_module.to_string());
            }
            std::collections::hash_map::Entry::Occupied(mut e) => {
                let existing_ver = extract_version(e.get());
                let new_ver = extract_version(eff_module);
                if let (Some(ev), Some(nv)) = (existing_ver, new_ver) {
                    if compare_version(nv, ev) == std::cmp::Ordering::Greater {
                        e.insert(eff_module.to_string());
                    }
                }
            }
        }

        match &unresolved.kind {
            ImportKind::Function(type_idx) => {
                // Look up the structural function type for compatibility checking.
                let func_type = components
                    .get(unresolved.component_idx)
                    .and_then(|c| c.core_modules.get(unresolved.module_idx))
                    .and_then(|m| m.types.get(*type_idx as usize))
                    .cloned();

                let position = match seen_func.entry(dedup_key) {
                    std::collections::hash_map::Entry::Occupied(e) => {
                        let (pos, ref first_type) = *e.get();
                        // Type compatibility check: only dedup if the function
                        // signatures match structurally. If they differ, this is
                        // NOT the same function despite matching (module, field)
                        // names — allocate a fresh position.
                        if first_type == &func_type {
                            pos
                        } else {
                            log::warn!(
                                "Import dedup: type mismatch for {:?} — \
                                 first={:?}, current={:?}; skipping dedup",
                                e.key(),
                                first_type,
                                func_type,
                            );
                            type_mismatch_entries.insert((
                                unresolved.component_idx,
                                unresolved.module_idx,
                                unresolved.module_name.clone(),
                                unresolved.field_name.clone(),
                            ));
                            let pos = counts.func;
                            counts.func += 1;
                            pos
                        }
                    }
                    std::collections::hash_map::Entry::Vacant(e) => {
                        let pos = counts.func;
                        e.insert((pos, func_type));
                        counts.func += 1;
                        pos
                    }
                };
                // Always insert the assignment so merge_core_module lookup works
                // for every (comp_idx, mod_idx, module_name, field_name) tuple.
                assignments.func.insert(
                    (
                        unresolved.component_idx,
                        unresolved.module_idx,
                        unresolved.module_name.clone(),
                        unresolved.field_name.clone(),
                    ),
                    position,
                );
            }
            ImportKind::Table(table_type) => {
                let table_sig: TableSig = (
                    table_type.element_type,
                    table_type.initial,
                    table_type.maximum,
                );
                let position = match seen_table.entry(dedup_key) {
                    std::collections::hash_map::Entry::Occupied(e) => {
                        let (pos, ref first_sig) = *e.get();
                        // Type compatibility: only dedup if element type AND
                        // limits match the first occurrence. Otherwise this is
                        // a distinct table despite the matching (module, field)
                        // names — allocate a fresh slot (mirrors function arm).
                        if first_sig == &table_sig {
                            pos
                        } else {
                            log::warn!(
                                "Import dedup: table type mismatch for {:?} — \
                                 first={:?}, current={:?}; skipping dedup",
                                e.key(),
                                first_sig,
                                table_sig,
                            );
                            type_mismatch_entries.insert((
                                unresolved.component_idx,
                                unresolved.module_idx,
                                unresolved.module_name.clone(),
                                unresolved.field_name.clone(),
                            ));
                            let pos = counts.table;
                            counts.table += 1;
                            pos
                        }
                    }
                    std::collections::hash_map::Entry::Vacant(e) => {
                        let pos = counts.table;
                        e.insert((pos, table_sig));
                        counts.table += 1;
                        pos
                    }
                };
                assignments.table.insert(
                    (
                        unresolved.component_idx,
                        unresolved.module_idx,
                        unresolved.module_name.clone(),
                        unresolved.field_name.clone(),
                    ),
                    position,
                );
            }
            ImportKind::Memory(_) => {
                counts.memory += 1;
            }
            ImportKind::Global(global_type) => {
                let global_sig: GlobalSig = (global_type.content_type, global_type.mutable);
                let position = match seen_global.entry(dedup_key) {
                    std::collections::hash_map::Entry::Occupied(e) => {
                        let (pos, ref first_sig) = *e.get();
                        // Type compatibility: only dedup if content type AND
                        // mutability match the first occurrence. Otherwise this
                        // is a distinct global despite the matching (module,
                        // field) names — allocate a fresh slot (mirrors
                        // function arm).
                        if first_sig == &global_sig {
                            pos
                        } else {
                            log::warn!(
                                "Import dedup: global type mismatch for {:?} — \
                                 first={:?}, current={:?}; skipping dedup",
                                e.key(),
                                first_sig,
                                global_sig,
                            );
                            type_mismatch_entries.insert((
                                unresolved.component_idx,
                                unresolved.module_idx,
                                unresolved.module_name.clone(),
                                unresolved.field_name.clone(),
                            ));
                            let pos = counts.global;
                            counts.global += 1;
                            pos
                        }
                    }
                    std::collections::hash_map::Entry::Vacant(e) => {
                        let pos = counts.global;
                        e.insert((pos, global_sig));
                        counts.global += 1;
                        pos
                    }
                };
                assignments.global.insert(
                    (
                        unresolved.component_idx,
                        unresolved.module_idx,
                        unresolved.module_name.clone(),
                        unresolved.field_name.clone(),
                    ),
                    position,
                );
            }
        }
    }

    // Trailing shared memory import (same as add_unresolved_imports)
    if let Some(plan) = shared_memory_plan {
        if plan.import.is_some() && !shared_memory_import_counted {
            counts.memory += 1;
        }
    }

    if adapter_skip_count > 0 {
        log::debug!(
            "compute_unresolved_import_assignments: skipped {} adapter-resolved imports \
             (remaining: {} func, {} table, {} global, {} memory)",
            adapter_skip_count,
            counts.func,
            counts.table,
            counts.global,
            counts.memory
        );
    }

    let dedup_info = ImportDedupInfo {
        best_module_version,
        type_mismatch_entries,
    };

    (counts, assignments, dedup_info)
}

/// #328: parse a WASM `name` custom section and accumulate its
/// function-name entries into `out`, remapping each function index from
/// this module's index space `(comp_idx, mod_idx, orig_idx)` into the
/// fused index space via `function_index_map`.
///
/// Entries with no mapping (a dead / internalized function) are dropped —
/// the coalesced section must never carry a wrong index (LS-D-1: correct or
/// nothing). Non-function subsections (module / local / label / type / …
/// names) are ignored in this pass: their indices would also need
/// remapping, and dropping them keeps the emitted section correct rather
/// than plausibly-wrong. A malformed section is dropped whole.
fn accumulate_remapped_function_names(
    data: &[u8],
    comp_idx: usize,
    mod_idx: usize,
    function_index_map: &HashMap<(usize, usize, u32), u32>,
    out: &mut std::collections::BTreeMap<u32, String>,
) {
    let reader = wasmparser::NameSectionReader::new(wasmparser::BinaryReader::new(data, 0));
    for subsection in reader {
        let Ok(subsection) = subsection else {
            return; // malformed — never guess
        };
        if let wasmparser::Name::Function(namemap) = subsection {
            for naming in namemap {
                let Ok(naming) = naming else { continue };
                if let Some(&fused) = function_index_map.get(&(comp_idx, mod_idx, naming.index)) {
                    out.insert(fused, naming.name.to_string());
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// #328: the name-section remap accumulates function names under their
    /// FUSED indices, and drops entries whose source index isn't in the
    /// fused map (dead/internalized) — never emitting a wrong index.
    #[test]
    fn accumulate_remapped_function_names_remaps_and_drops_unmapped() {
        // A `name` section body with a function-name subsection (id 1)
        // naming source func 0 -> "foo" and source func 5 -> "bar".
        // Layout: [subsec_id=1][size=0x0b][count=2][idx=0,len=3,"foo"][idx=5,len=3,"bar"]
        let data: Vec<u8> = vec![
            0x01, 0x0b, 0x02, 0x00, 0x03, b'f', b'o', b'o', 0x05, 0x03, b'b', b'a', b'r',
        ];
        // Fused index map for (comp 0, module 0): 0 -> 10; source 5 is
        // intentionally unmapped (should be dropped).
        let mut map: HashMap<(usize, usize, u32), u32> = HashMap::new();
        map.insert((0, 0, 0), 10);

        let mut out: std::collections::BTreeMap<u32, String> = std::collections::BTreeMap::new();
        accumulate_remapped_function_names(&data, 0, 0, &map, &mut out);

        assert_eq!(
            out.get(&10).map(String::as_str),
            Some("foo"),
            "source 0 -> fused 10"
        );
        assert_eq!(
            out.len(),
            1,
            "unmapped source func 5 (\"bar\") must be dropped, not emitted at a wrong index"
        );
    }

    #[test]
    fn test_convert_memory_type() {
        let mem = MemoryType {
            memory64: false,
            shared: false,
            initial: 1,
            maximum: Some(10),
        };
        let converted = convert_memory_type(&mem);
        assert_eq!(converted.minimum, 1);
        assert_eq!(converted.maximum, Some(10));
        assert!(!converted.memory64);
        assert!(!converted.shared);
    }

    #[test]
    fn test_create_global_init() {
        let expr = create_global_init(&ValType::I32);
        // The expression should be valid (we can't easily inspect it)
        let _ = expr;

        let expr = create_global_init(&ValType::F64);
        let _ = expr;
    }

    #[test]
    fn test_combine_memory_types_rebased() {
        let mem_a = MemoryType {
            memory64: false,
            shared: false,
            initial: 2,
            maximum: Some(5),
        };
        let mem_b = MemoryType {
            memory64: false,
            shared: false,
            initial: 3,
            maximum: Some(7),
        };

        let combined = combine_memory_types_rebased(&[mem_a, mem_b]).unwrap();
        assert_eq!(combined.initial, 5);
        assert_eq!(combined.maximum, Some(12));
    }

    #[test]
    fn test_combine_memory_types_shared() {
        let mem_a = MemoryType {
            memory64: false,
            shared: false,
            initial: 2,
            maximum: Some(10),
        };
        let mem_b = MemoryType {
            memory64: false,
            shared: false,
            initial: 4,
            maximum: Some(8),
        };

        let combined = combine_memory_types_shared(&[mem_a, mem_b]).unwrap();
        assert_eq!(combined.initial, 4);
        assert_eq!(combined.maximum, Some(8));
    }

    fn make_test_module(memories: Vec<MemoryType>) -> CoreModule {
        CoreModule {
            index: 0,
            bytes: Vec::new(),
            types: Vec::new(),
            imports: Vec::new(),
            exports: Vec::new(),
            functions: Vec::new(),
            memories,
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
        }
    }

    #[test]
    fn test_multi_memory_index_maps() {
        // Simulate two modules each with one defined memory in multi-memory mode
        let module_a = make_test_module(vec![MemoryType {
            memory64: false,
            shared: false,
            initial: 1,
            maximum: None,
        }]);
        let module_b = make_test_module(vec![MemoryType {
            memory64: false,
            shared: false,
            initial: 2,
            maximum: None,
        }]);

        let mut merged = MergedModule {
            types: Vec::new(),
            imports: Vec::new(),
            functions: Vec::new(),
            tables: Vec::new(),
            memories: Vec::new(),
            globals: Vec::new(),
            exports: Vec::new(),
            start_function: None,
            elements: Vec::new(),
            data_segments: Vec::new(),
            custom_sections: Vec::new(),
            fused_function_names: std::collections::BTreeMap::new(),
            function_index_map: HashMap::new(),
            memory_index_map: HashMap::new(),
            table_index_map: HashMap::new(),
            global_index_map: HashMap::new(),
            type_index_map: HashMap::new(),
            realloc_map: HashMap::new(),
            import_counts: ImportCounts::default(),
            import_memory_indices: Vec::new(),
            import_realloc_indices: Vec::new(),
            resource_rep_by_component: HashMap::new(),
            resource_new_by_component: HashMap::new(),
            handle_tables: HashMap::new(),
            task_return_shims: HashMap::new(),
            async_result_globals: HashMap::new(),
            segment_bases: HashMap::new(),
        };

        // Simulate multi-memory merging for module A (comp 0, mod 0)
        let mem_offset_a = merged.memories.len() as u32; // 0
        merged.memory_index_map.insert((0, 0, 0), mem_offset_a);
        merged
            .memories
            .push(convert_memory_type(&module_a.memories[0]));

        // Simulate multi-memory merging for module B (comp 1, mod 0)
        let mem_offset_b = merged.memories.len() as u32; // 1
        merged.memory_index_map.insert((1, 0, 0), mem_offset_b);
        merged
            .memories
            .push(convert_memory_type(&module_b.memories[0]));

        // Verify: 2 separate memories
        assert_eq!(merged.memories.len(), 2);
        assert_eq!(merged.memories[0].minimum, 1);
        assert_eq!(merged.memories[1].minimum, 2);

        // Verify: index maps point to different memories
        assert_eq!(merged.memory_index_map[&(0, 0, 0)], 0);
        assert_eq!(merged.memory_index_map[&(1, 0, 0)], 1);

        // Verify: IndexMaps for rewriter map correctly
        let maps_a = build_index_maps_for_module(
            0,
            0,
            &module_a,
            &merged,
            MemoryStrategy::MultiMemory,
            false,
            0,
            false,
            None,
            0,
            0,
            None,
        );
        assert_eq!(maps_a.remap_memory(0), 0);

        let maps_b = build_index_maps_for_module(
            1,
            0,
            &module_b,
            &merged,
            MemoryStrategy::MultiMemory,
            false,
            0,
            false,
            None,
            0,
            0,
            None,
        );
        assert_eq!(maps_b.remap_memory(0), 1);
    }

    /// Mythos finding B (PR #220): an unresolved `MemoryStrategy::Auto`
    /// reaching `Merger::new` directly must normalize to MultiMemory.
    /// Without normalization the merger is split-brained — `== SharedMemory`
    /// sites treat Auto as multi while `== MultiMemory` sites treat it as
    /// shared, silently dropping the second component's memory export.
    #[test]
    fn test_merger_new_normalizes_auto_to_multi_memory() {
        let merger = Merger::new(MemoryStrategy::Auto, false);
        assert_eq!(
            merger.memory_strategy,
            MemoryStrategy::MultiMemory,
            "Merger::new(Auto, _) must normalize to MultiMemory"
        );
    }

    /// Regression test for Bug #7: Merger::default() must use MultiMemory strategy.
    /// The default memory strategy should be MultiMemory (not SharedMemory) because
    /// SharedMemory is broken when any component uses memory.grow.
    #[test]
    fn test_merger_default_uses_multi_memory() {
        let merger = Merger::default();
        assert_eq!(
            merger.memory_strategy,
            MemoryStrategy::MultiMemory,
            "Merger::default() must use MultiMemory strategy"
        );
        assert!(
            !merger.address_rebasing,
            "Merger::default() must not enable address rebasing"
        );
    }

    /// Test decompose_component_core_func_index for single-module components
    #[test]
    fn test_decompose_core_func_index_single_module() {
        use crate::parser::ParsedComponent;

        // Single module with 2 imported functions + 3 defined functions = 5 total
        let module = CoreModule {
            index: 0,
            bytes: Vec::new(),
            types: Vec::new(),
            imports: vec![
                crate::parser::ModuleImport {
                    module: "env".to_string(),
                    name: "f0".to_string(),
                    kind: ImportKind::Function(0),
                },
                crate::parser::ModuleImport {
                    module: "env".to_string(),
                    name: "f1".to_string(),
                    kind: ImportKind::Function(0),
                },
            ],
            exports: Vec::new(),
            functions: vec![0, 0, 0], // 3 defined functions
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

        let component = ParsedComponent {
            name: None,
            core_modules: vec![module],
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
        };

        // Function indices 0-4 should all map to (module 0, local idx)
        assert_eq!(
            decompose_component_core_func_index(&component, 0),
            Some((0, 0))
        );
        assert_eq!(
            decompose_component_core_func_index(&component, 2),
            Some((0, 2))
        );
        assert_eq!(
            decompose_component_core_func_index(&component, 4),
            Some((0, 4))
        );
        // Index 5 is out of bounds
        assert_eq!(decompose_component_core_func_index(&component, 5), None);
    }

    /// Test decompose_component_core_func_index for multi-module components
    #[test]
    fn test_decompose_core_func_index_multi_module() {
        use crate::parser::ParsedComponent;

        // Module A: 1 import + 2 defined = 3 total (indices 0, 1, 2)
        let module_a = CoreModule {
            index: 0,
            bytes: Vec::new(),
            types: Vec::new(),
            imports: vec![crate::parser::ModuleImport {
                module: "env".to_string(),
                name: "f0".to_string(),
                kind: ImportKind::Function(0),
            }],
            exports: Vec::new(),
            functions: vec![0, 0],
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

        // Module B: 0 imports + 4 defined = 4 total (indices 3, 4, 5, 6)
        let module_b = CoreModule {
            index: 1,
            bytes: Vec::new(),
            types: Vec::new(),
            imports: Vec::new(),
            exports: Vec::new(),
            functions: vec![0, 0, 0, 0],
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

        let component = ParsedComponent {
            name: None,
            core_modules: vec![module_a, module_b],
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
        };

        // Indices 0-2 belong to module A
        assert_eq!(
            decompose_component_core_func_index(&component, 0),
            Some((0, 0))
        );
        assert_eq!(
            decompose_component_core_func_index(&component, 2),
            Some((0, 2))
        );

        // Indices 3-6 belong to module B (local indices 0-3)
        assert_eq!(
            decompose_component_core_func_index(&component, 3),
            Some((1, 0))
        );
        assert_eq!(
            decompose_component_core_func_index(&component, 6),
            Some((1, 3))
        );

        // Index 7 is out of bounds
        assert_eq!(decompose_component_core_func_index(&component, 7), None);
    }

    /// Verify that `compute_unresolved_import_assignments` and
    /// `add_unresolved_imports` agree on import counts for a graph with
    /// mixed unresolved import kinds.
    ///
    /// This test constructs a `DependencyGraph` with several unresolved
    /// imports (function, global, table, memory) and runs the full merge
    /// pipeline, which triggers the debug assertions inside
    /// `add_unresolved_imports`.  If the two functions ever diverge in
    /// iteration order, the assertions will fire and this test will fail.
    #[test]
    fn test_import_order_invariant_holds() {
        use crate::parser::{FuncType, ModuleImport, ParsedComponent};
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        // Build a single component with one module that has several
        // unresolved imports of different kinds.
        let module = CoreModule {
            index: 0,
            bytes: Vec::new(),
            types: vec![FuncType {
                params: vec![],
                results: vec![],
            }],
            imports: vec![
                ModuleImport {
                    module: "env".to_string(),
                    name: "imported_func".to_string(),
                    kind: ImportKind::Function(0),
                },
                ModuleImport {
                    module: "env".to_string(),
                    name: "imported_global".to_string(),
                    kind: ImportKind::Global(GlobalType {
                        content_type: ValType::I32,
                        mutable: false,
                        init_expr_bytes: Vec::new(),
                    }),
                },
                ModuleImport {
                    module: "env".to_string(),
                    name: "imported_table".to_string(),
                    kind: ImportKind::Table(TableType {
                        element_type: ValType::Ref(RefType::FUNCREF),
                        initial: 1,
                        maximum: None,
                    }),
                },
            ],
            exports: Vec::new(),
            functions: Vec::new(),
            memories: vec![MemoryType {
                memory64: false,
                shared: false,
                initial: 1,
                maximum: None,
            }],
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

        let component = ParsedComponent {
            name: None,
            core_modules: vec![module],
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
        };

        let graph = DependencyGraph {
            instantiation_order: vec![0],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "env".to_string(),
                    field_name: "imported_func".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: None,
                    display_field: None,
                },
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "env".to_string(),
                    field_name: "imported_global".to_string(),
                    kind: ImportKind::Global(GlobalType {
                        content_type: ValType::I32,
                        mutable: false,
                        init_expr_bytes: Vec::new(),
                    }),
                    display_module: None,
                    display_field: None,
                },
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "env".to_string(),
                    field_name: "imported_table".to_string(),
                    kind: ImportKind::Table(TableType {
                        element_type: ValType::Ref(RefType::FUNCREF),
                        initial: 1,
                        maximum: None,
                    }),
                    display_module: None,
                    display_field: None,
                },
            ],
        };

        let merger = Merger::new(MemoryStrategy::MultiMemory, false);
        // This will trigger debug_assert! inside add_unresolved_imports
        // if the import order invariant is broken.
        let result = merger.merge(&[component], &graph);
        assert!(result.is_ok(), "merge should succeed: {:?}", result.err());

        let merged = result.unwrap();
        // Verify the counts match what we expect
        assert_eq!(merged.import_counts.func, 1, "one unresolved func import");
        assert_eq!(
            merged.import_counts.global, 1,
            "one unresolved global import"
        );
        assert_eq!(merged.import_counts.table, 1, "one unresolved table import");
        assert_eq!(
            merged.import_counts.memory, 0,
            "no unresolved memory import"
        );

        // Verify the actual imports match
        assert_eq!(merged.imports.len(), 3);
        assert_eq!(merged.imports[0].name, "imported_func");
        assert_eq!(merged.imports[1].name, "imported_global");
        assert_eq!(merged.imports[2].name, "imported_table");
    }

    // -----------------------------------------------------------------------
    // Import deduplication utility tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_normalize_wasi_module_name() {
        // WASI names with version suffix
        assert_eq!(
            normalize_wasi_module_name("wasi:io/error@0.2.0"),
            "wasi:io/error"
        );
        assert_eq!(
            normalize_wasi_module_name("wasi:cli/stderr@0.2.6"),
            "wasi:cli/stderr"
        );
        assert_eq!(
            normalize_wasi_module_name("wasi:io/streams@0.2.6"),
            "wasi:io/streams"
        );
        // Non-WASI names should be unchanged
        assert_eq!(normalize_wasi_module_name("env"), "env");
        assert_eq!(normalize_wasi_module_name(""), "");
        // Email-like strings (@ without colon) should NOT strip
        assert_eq!(normalize_wasi_module_name("user@host"), "user@host");
    }

    #[test]
    fn test_compare_version() {
        use std::cmp::Ordering;
        // Pure numeric triples (existing coverage).
        assert_eq!(compare_version("0.2.6", "0.2.0"), Ordering::Greater);
        assert_eq!(compare_version("0.2.0", "0.2.6"), Ordering::Less);
        assert_eq!(compare_version("0.2.6", "0.2.6"), Ordering::Equal);
        assert_eq!(compare_version("1.0.0", "0.9.9"), Ordering::Greater);
        assert_eq!(compare_version("0.3.0", "0.2.9"), Ordering::Greater);
    }

    #[test]
    fn test_compare_version_prerelease_regression_issue_98() {
        use std::cmp::Ordering;
        // Issue #98: previously returned Less because filter_map(parse::<u32>)
        // dropped the "99-rc1" segment, leaving [0, 2] vs [0, 2, 0]. After the
        // fix the pre-release suffix is split off and 99 > 0 wins.
        assert_eq!(compare_version("0.2.99-rc1", "0.2.0"), Ordering::Greater);
    }

    #[test]
    fn test_compare_version_prerelease_below_release() {
        use std::cmp::Ordering;
        // Per semver §11: a pre-release version sorts BELOW the same version
        // without a pre-release suffix.
        assert_eq!(compare_version("0.2.0-rc1", "0.2.0"), Ordering::Less);
        assert_eq!(compare_version("0.2.0", "0.2.0-rc1"), Ordering::Greater);
        assert_eq!(compare_version("1.0.0-alpha", "1.0.0"), Ordering::Less);
    }

    #[test]
    fn test_compare_version_prerelease_ordering() {
        use std::cmp::Ordering;
        // Both have pre-release: compare identifier-wise.
        assert_eq!(compare_version("1.0.0-alpha", "1.0.0-beta"), Ordering::Less);
        assert_eq!(compare_version("1.0.0-rc1", "1.0.0-rc2"), Ordering::Less);
        // Numeric identifiers sort below alphanumeric ones (semver §11.4.3).
        assert_eq!(compare_version("1.0.0-1", "1.0.0-alpha"), Ordering::Less);
        // Longer pre-release wins when shared segments match.
        assert_eq!(
            compare_version("1.0.0-alpha", "1.0.0-alpha.1"),
            Ordering::Less
        );
        assert_eq!(
            compare_version("1.0.0-alpha.1", "1.0.0-alpha.1"),
            Ordering::Equal
        );
    }

    #[test]
    fn test_compare_version_build_metadata_ignored() {
        use std::cmp::Ordering;
        // Build metadata (+...) does not affect precedence.
        assert_eq!(
            compare_version("1.0.0+meta", "1.0.0+other"),
            Ordering::Equal
        );
        assert_eq!(compare_version("1.0.0+meta", "1.0.0"), Ordering::Equal);
        assert_eq!(compare_version("0.2.6+sha.abc", "0.2.0"), Ordering::Greater);
        // Build metadata after pre-release is also ignored.
        assert_eq!(
            compare_version("1.0.0-rc1+build.5", "1.0.0-rc1"),
            Ordering::Equal
        );
    }

    #[test]
    fn test_compare_version_missing_segments() {
        use std::cmp::Ordering;
        // Missing trailing segments default to 0.
        assert_eq!(compare_version("0.2", "0.2.0"), Ordering::Equal);
        assert_eq!(compare_version("1", "1.0.0"), Ordering::Equal);
        assert_eq!(compare_version("0.3", "0.2.99"), Ordering::Greater);
        assert_eq!(compare_version("0.2", "0.2.1"), Ordering::Less);
    }

    #[test]
    fn test_compare_version_mixed_alphanumeric() {
        use std::cmp::Ordering;
        // Non-numeric main segments fall back to lexical comparison of that
        // segment so we never silently drop them like the old impl did.
        assert_eq!(compare_version("0.2.x", "0.2.x"), Ordering::Equal);
        // Different non-numeric segments compare lexically.
        assert_ne!(compare_version("0.2.a", "0.2.b"), Ordering::Equal);
        // A numeric segment vs a non-numeric one is decidable (not silently
        // dropped) — exact ordering depends on lexical fallback, but it
        // must not be Equal.
        assert_ne!(compare_version("0.2.0", "0.2.x"), Ordering::Equal);
    }

    #[test]
    fn test_compare_version_large_numbers() {
        use std::cmp::Ordering;
        // u64-range segments must compare numerically, not lexically.
        // Lexical "10" < "9" but numeric 10 > 9.
        assert_eq!(compare_version("0.0.10", "0.0.9"), Ordering::Greater);
        assert_eq!(
            compare_version("0.0.4294967296", "0.0.4294967295"),
            Ordering::Greater
        );
    }

    #[test]
    fn test_extract_version() {
        assert_eq!(extract_version("wasi:io/error@0.2.6"), Some("0.2.6"));
        assert_eq!(extract_version("wasi:io/error@0.2.0"), Some("0.2.0"));
        assert_eq!(extract_version("env"), None);
        assert_eq!(extract_version("user@host"), None);
    }

    #[test]
    fn test_import_dedup_exact_match() {
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        // Two imports with identical effective (module, field) should dedup
        let graph = DependencyGraph {
            instantiation_order: vec![0],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                    display_field: Some("get-stderr".to_string()),
                },
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 1,
                    module_name: "".to_string(),
                    field_name: "5".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                    display_field: Some("get-stderr".to_string()),
                },
            ],
        };

        let (counts, assignments, _dedup_info) =
            compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

        // Should be 1 unique func import, not 2
        assert_eq!(counts.func, 1, "duplicate imports should be deduplicated");

        // Both assignments should point to the same position (0)
        assert_eq!(
            assignments.func[&(0, 0, "".to_string(), "0".to_string())],
            0
        );
        assert_eq!(
            assignments.func[&(0, 1, "".to_string(), "5".to_string())],
            0
        );
    }

    #[test]
    fn test_import_dedup_version_mismatch() {
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        // Two imports for the same WASI function but different versions
        let graph = DependencyGraph {
            instantiation_order: vec![0],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:io/error@0.2.0".to_string()),
                    display_field: Some("drop".to_string()),
                },
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 1,
                    module_name: "".to_string(),
                    field_name: "3".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:io/error@0.2.6".to_string()),
                    display_field: Some("drop".to_string()),
                },
            ],
        };

        let (counts, assignments, dedup_info) =
            compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

        // Should be 1 unique func import (version-normalized key matches)
        assert_eq!(
            counts.func, 1,
            "version-mismatched imports should be deduplicated"
        );

        // Both assignments point to position 0
        assert_eq!(
            assignments.func[&(0, 0, "".to_string(), "0".to_string())],
            0
        );
        assert_eq!(
            assignments.func[&(0, 1, "".to_string(), "3".to_string())],
            0
        );

        // Best version should be the higher one (@0.2.6)
        // In SharedMemory mode, dedup key has None as the component dimension
        let key = ("wasi:io/error".to_string(), "drop".to_string(), None);
        assert_eq!(dedup_info.best_module_version[&key], "wasi:io/error@0.2.6");
    }

    #[test]
    fn test_import_dedup_different_fields_not_deduped() {
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        // Same module, different field — should NOT dedup
        let graph = DependencyGraph {
            instantiation_order: vec![0],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                    display_field: Some("get-stderr".to_string()),
                },
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "1".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                    display_field: Some("write".to_string()),
                },
            ],
        };

        let (counts, _assignments, _dedup_info) =
            compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

        assert_eq!(
            counts.func, 2,
            "different fields should remain separate imports"
        );
    }

    // -----------------------------------------------------------------------
    // Multi-memory WASI import lowering tests
    // -----------------------------------------------------------------------

    /// In MultiMemory mode, the same (module, field) from two different
    /// components must get separate import slots (different DedupKey because
    /// the component dimension differs). Each slot gets its own canon lower
    /// with the correct Memory(N) and Realloc(N).
    #[test]
    fn test_multi_memory_dedup_separates_components() {
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        let graph = DependencyGraph {
            instantiation_order: vec![0, 1],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                    display_field: Some("get-stderr".to_string()),
                },
                UnresolvedImport {
                    component_idx: 1,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                    display_field: Some("get-stderr".to_string()),
                },
            ],
        };

        let (counts, assignments, _dedup_info) =
            compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::MultiMemory);

        // MultiMemory: same (module, field) from different components -> 2 slots
        assert_eq!(
            counts.func, 2,
            "multi-memory mode must allocate separate import slots per component"
        );

        // Each component's import should map to a distinct position
        let pos_comp0 = assignments.func[&(0, 0, "".to_string(), "0".to_string())];
        let pos_comp1 = assignments.func[&(1, 0, "".to_string(), "0".to_string())];
        assert_ne!(
            pos_comp0, pos_comp1,
            "component 0 and component 1 must have different import positions"
        );
    }

    /// In SharedMemory mode, the same (module, field) from two different
    /// components should still deduplicate to a single import slot (the
    /// component dimension is None).
    #[test]
    fn test_shared_memory_dedup_merges_components() {
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        let graph = DependencyGraph {
            instantiation_order: vec![0, 1],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                    display_field: Some("get-stderr".to_string()),
                },
                UnresolvedImport {
                    component_idx: 1,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                    display_field: Some("get-stderr".to_string()),
                },
            ],
        };

        let (counts, assignments, _dedup_info) =
            compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

        // SharedMemory: same effective key -> 1 slot (deduped)
        assert_eq!(
            counts.func, 1,
            "shared-memory mode must deduplicate same (module, field) across components"
        );

        // Both assignments point to the same position
        let pos_comp0 = assignments.func[&(0, 0, "".to_string(), "0".to_string())];
        let pos_comp1 = assignments.func[&(1, 0, "".to_string(), "0".to_string())];
        assert_eq!(
            pos_comp0, pos_comp1,
            "deduplicated imports must share the same position"
        );
    }

    /// Two components import the same-named global `env.g` at DIFFERENT types
    /// (comp0: i32 immutable, comp1: i64 mutable). The structural type check
    /// must refuse to dedup them: TWO distinct global import slots, and the
    /// two components' assignments (which feed `global_index_map`) must point
    /// at DIFFERENT positions. Pre-fix this collapsed to a single slot.
    #[test]
    fn ls_m_10_test_global_import_type_mismatch_not_deduped() {
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        let graph = DependencyGraph {
            instantiation_order: vec![0, 1],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "env".to_string(),
                    field_name: "g".to_string(),
                    kind: ImportKind::Global(GlobalType {
                        content_type: ValType::I32,
                        mutable: false,
                        init_expr_bytes: Vec::new(),
                    }),
                    display_module: None,
                    display_field: None,
                },
                UnresolvedImport {
                    component_idx: 1,
                    module_idx: 0,
                    module_name: "env".to_string(),
                    field_name: "g".to_string(),
                    kind: ImportKind::Global(GlobalType {
                        content_type: ValType::I64,
                        mutable: true,
                        init_expr_bytes: Vec::new(),
                    }),
                    display_module: None,
                    display_field: None,
                },
            ],
        };

        let (counts, assignments, dedup_info) =
            compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

        assert_eq!(
            counts.global, 2,
            "globals with mismatched (type, mutability) must NOT dedup"
        );
        let pos0 = assignments.global[&(0, 0, "env".to_string(), "g".to_string())];
        let pos1 = assignments.global[&(1, 0, "env".to_string(), "g".to_string())];
        assert_ne!(
            pos0, pos1,
            "mismatched-type globals must map to different import slots"
        );
        // The second occurrence must be recorded as a type mismatch so the
        // emit side knows to emit a separate import.
        assert!(
            dedup_info
                .type_mismatch_entries
                .contains(&(1, 0, "env".to_string(), "g".to_string())),
            "mismatched global must be recorded in type_mismatch_entries"
        );
    }

    /// Two components import the same-named table `env.t` at DIFFERENT types
    /// (comp0: funcref[1..], comp1: externref[5..]). Must emit TWO distinct
    /// table import slots with distinct assignment positions.
    #[test]
    fn test_table_import_type_mismatch_not_deduped() {
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        let graph = DependencyGraph {
            instantiation_order: vec![0, 1],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "env".to_string(),
                    field_name: "t".to_string(),
                    kind: ImportKind::Table(TableType {
                        element_type: ValType::Ref(RefType::FUNCREF),
                        initial: 1,
                        maximum: None,
                    }),
                    display_module: None,
                    display_field: None,
                },
                UnresolvedImport {
                    component_idx: 1,
                    module_idx: 0,
                    module_name: "env".to_string(),
                    field_name: "t".to_string(),
                    kind: ImportKind::Table(TableType {
                        element_type: ValType::Ref(RefType::EXTERNREF),
                        initial: 5,
                        maximum: None,
                    }),
                    display_module: None,
                    display_field: None,
                },
            ],
        };

        let (counts, assignments, dedup_info) =
            compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

        assert_eq!(
            counts.table, 2,
            "tables with mismatched (element_type, limits) must NOT dedup"
        );
        let pos0 = assignments.table[&(0, 0, "env".to_string(), "t".to_string())];
        let pos1 = assignments.table[&(1, 0, "env".to_string(), "t".to_string())];
        assert_ne!(
            pos0, pos1,
            "mismatched-type tables must map to different import slots"
        );
        assert!(
            dedup_info
                .type_mismatch_entries
                .contains(&(1, 0, "env".to_string(), "t".to_string())),
            "mismatched table must be recorded in type_mismatch_entries"
        );
    }

    /// Regression: two components importing the SAME-typed `env.g`
    /// (i32 immutable) must still deduplicate to ONE slot (current behaviour).
    #[test]
    fn test_global_import_same_type_still_deduped() {
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        let mk = |comp: usize| UnresolvedImport {
            component_idx: comp,
            module_idx: 0,
            module_name: "env".to_string(),
            field_name: "g".to_string(),
            kind: ImportKind::Global(GlobalType {
                content_type: ValType::I32,
                mutable: false,
                init_expr_bytes: Vec::new(),
            }),
            display_module: None,
            display_field: None,
        };

        let graph = DependencyGraph {
            instantiation_order: vec![0, 1],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![mk(0), mk(1)],
        };

        let (counts, assignments, dedup_info) =
            compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

        assert_eq!(
            counts.global, 1,
            "same-typed globals must dedup to one slot"
        );
        let pos0 = assignments.global[&(0, 0, "env".to_string(), "g".to_string())];
        let pos1 = assignments.global[&(1, 0, "env".to_string(), "g".to_string())];
        assert_eq!(pos0, pos1, "same-typed globals must share the slot");
        assert!(
            dedup_info.type_mismatch_entries.is_empty(),
            "no mismatch must be recorded for identical types"
        );
    }

    /// Regression: two components importing the SAME-typed `env.t`
    /// (funcref[1..]) must still deduplicate to ONE slot.
    #[test]
    fn test_table_import_same_type_still_deduped() {
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        let mk = |comp: usize| UnresolvedImport {
            component_idx: comp,
            module_idx: 0,
            module_name: "env".to_string(),
            field_name: "t".to_string(),
            kind: ImportKind::Table(TableType {
                element_type: ValType::Ref(RefType::FUNCREF),
                initial: 1,
                maximum: Some(10),
            }),
            display_module: None,
            display_field: None,
        };

        let graph = DependencyGraph {
            instantiation_order: vec![0, 1],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![mk(0), mk(1)],
        };

        let (counts, assignments, dedup_info) =
            compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

        assert_eq!(counts.table, 1, "same-typed tables must dedup to one slot");
        let pos0 = assignments.table[&(0, 0, "env".to_string(), "t".to_string())];
        let pos1 = assignments.table[&(1, 0, "env".to_string(), "t".to_string())];
        assert_eq!(pos0, pos1, "same-typed tables must share the slot");
        assert!(
            dedup_info.type_mismatch_entries.is_empty(),
            "no mismatch must be recorded for identical types"
        );
    }

    /// Verify that `add_unresolved_imports` populates `import_memory_indices`
    /// and `import_realloc_indices` with per-component values. Component 0's
    /// import should reference memory 0, component 1's import should reference
    /// memory 1.
    #[test]
    fn test_import_memory_and_realloc_indices_populated() {
        use crate::parser::{FuncType, ModuleExport, ModuleImport, ParsedComponent};
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        // Build two components, each with one module. Each module has:
        // - 1 unresolved func import (WASI-like)
        // - 1 memory
        // - 1 cabi_realloc export
        let make_module = |idx: usize| -> CoreModule {
            CoreModule {
                index: 0,
                bytes: Vec::new(),
                types: vec![
                    // type 0: () -> ()  (for the unresolved import)
                    FuncType {
                        params: vec![],
                        results: vec![],
                    },
                    // type 1: (i32, i32, i32, i32) -> i32  (cabi_realloc)
                    FuncType {
                        params: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
                        results: vec![ValType::I32],
                    },
                ],
                imports: vec![ModuleImport {
                    module: "".to_string(),
                    name: format!("{}", idx),
                    kind: ImportKind::Function(0),
                }],
                exports: vec![ModuleExport {
                    name: "cabi_realloc".to_string(),
                    kind: ExportKind::Function,
                    index: 1, // defined func 0 = func idx 1 (after 1 import)
                }],
                functions: vec![1], // one defined function with type 1 (cabi_realloc sig)
                memories: vec![MemoryType {
                    memory64: false,
                    shared: false,
                    initial: 1,
                    maximum: None,
                }],
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
            }
        };

        let make_component = |idx: usize| -> ParsedComponent {
            ParsedComponent {
                name: None,
                core_modules: vec![make_module(idx)],
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
        };

        let components = vec![make_component(0), make_component(1)];

        let graph = DependencyGraph {
            instantiation_order: vec![0, 1],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                    display_field: Some("get-stderr".to_string()),
                },
                UnresolvedImport {
                    component_idx: 1,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                    display_field: Some("get-stderr".to_string()),
                },
            ],
        };

        let merger = Merger::new(MemoryStrategy::MultiMemory, false);
        let merged = merger
            .merge(&components, &graph)
            .expect("merge should succeed");

        // Should have 2 function imports (one per component)
        assert_eq!(
            merged.import_counts.func, 2,
            "multi-memory: two func imports"
        );

        // import_memory_indices should have one entry per func import
        assert_eq!(
            merged.import_memory_indices.len(),
            2,
            "should have memory index for each func import"
        );

        // Component 0's memory index and component 1's should differ
        // (each component's memory is separate in multi-memory mode)
        let mem_idx_0 = merged.import_memory_indices[0];
        let mem_idx_1 = merged.import_memory_indices[1];
        assert_ne!(
            mem_idx_0, mem_idx_1,
            "components must reference different memories: comp0={}, comp1={}",
            mem_idx_0, mem_idx_1,
        );

        // import_realloc_indices should also have one entry per func import
        assert_eq!(
            merged.import_realloc_indices.len(),
            2,
            "should have realloc index for each func import"
        );

        // Both components define cabi_realloc, so both should be Some
        assert!(
            merged.import_realloc_indices[0].is_some(),
            "component 0 should have a realloc index"
        );
        assert!(
            merged.import_realloc_indices[1].is_some(),
            "component 1 should have a realloc index"
        );

        // The realloc indices should be different (different merged functions)
        assert_ne!(
            merged.import_realloc_indices[0], merged.import_realloc_indices[1],
            "each component's realloc should map to a different merged function"
        );
    }

    /// Verify that in multi-memory mode, merging generates `cabi_realloc$N`
    /// exports for component indices > 0.
    #[test]
    fn test_cabi_realloc_suffixed_exports_generated() {
        use crate::parser::{FuncType, ModuleExport, ModuleImport, ParsedComponent};
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        let make_module = |idx: usize| -> CoreModule {
            CoreModule {
                index: 0,
                bytes: Vec::new(),
                types: vec![
                    FuncType {
                        params: vec![],
                        results: vec![],
                    },
                    FuncType {
                        params: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
                        results: vec![ValType::I32],
                    },
                ],
                imports: vec![ModuleImport {
                    module: "".to_string(),
                    name: format!("{}", idx),
                    kind: ImportKind::Function(0),
                }],
                exports: vec![ModuleExport {
                    name: "cabi_realloc".to_string(),
                    kind: ExportKind::Function,
                    index: 1, // defined func 0 = wasm idx 1 (after 1 import)
                }],
                functions: vec![1], // cabi_realloc signature
                memories: vec![MemoryType {
                    memory64: false,
                    shared: false,
                    initial: 1,
                    maximum: None,
                }],
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
            }
        };

        let make_component = |idx: usize| -> ParsedComponent {
            ParsedComponent {
                name: None,
                core_modules: vec![make_module(idx)],
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
        };

        let components = vec![make_component(0), make_component(1), make_component(2)];

        let graph = DependencyGraph {
            instantiation_order: vec![0, 1, 2],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:io/error@0.2.6".to_string()),
                    display_field: Some("drop".to_string()),
                },
                UnresolvedImport {
                    component_idx: 1,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:io/error@0.2.6".to_string()),
                    display_field: Some("drop".to_string()),
                },
                UnresolvedImport {
                    component_idx: 2,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:io/error@0.2.6".to_string()),
                    display_field: Some("drop".to_string()),
                },
            ],
        };

        let merger = Merger::new(MemoryStrategy::MultiMemory, false);
        let merged = merger
            .merge(&components, &graph)
            .expect("merge should succeed");

        // Component 0's cabi_realloc should be exported as "cabi_realloc" (plain)
        let has_plain = merged.exports.iter().any(|e| e.name == "cabi_realloc");
        assert!(has_plain, "component 0 should export plain cabi_realloc");

        // Component 1 should get cabi_realloc$1
        let has_suffixed_1 = merged.exports.iter().any(|e| e.name == "cabi_realloc$1");
        assert!(has_suffixed_1, "component 1 should export cabi_realloc$1");

        // Component 2 should get cabi_realloc$2
        let has_suffixed_2 = merged.exports.iter().any(|e| e.name == "cabi_realloc$2");
        assert!(has_suffixed_2, "component 2 should export cabi_realloc$2");

        // The suffixed exports should point to different function indices
        let realloc_1_idx = merged
            .exports
            .iter()
            .find(|e| e.name == "cabi_realloc$1")
            .unwrap()
            .index;
        let realloc_2_idx = merged
            .exports
            .iter()
            .find(|e| e.name == "cabi_realloc$2")
            .unwrap()
            .index;
        assert_ne!(
            realloc_1_idx, realloc_2_idx,
            "cabi_realloc$1 and cabi_realloc$2 must point to different functions"
        );
    }

    /// Verify that in SharedMemory mode, no `cabi_realloc$N` suffixed
    /// exports are generated (only the plain `cabi_realloc` is present).
    #[test]
    fn test_shared_memory_no_suffixed_realloc_exports() {
        use crate::parser::{FuncType, ModuleExport, ModuleImport, ParsedComponent};
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        let make_module = |idx: usize| -> CoreModule {
            CoreModule {
                index: 0,
                bytes: Vec::new(),
                types: vec![
                    FuncType {
                        params: vec![],
                        results: vec![],
                    },
                    FuncType {
                        params: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
                        results: vec![ValType::I32],
                    },
                ],
                imports: vec![ModuleImport {
                    module: "".to_string(),
                    name: format!("{}", idx),
                    kind: ImportKind::Function(0),
                }],
                exports: vec![ModuleExport {
                    name: "cabi_realloc".to_string(),
                    kind: ExportKind::Function,
                    index: 1,
                }],
                functions: vec![1],
                memories: vec![MemoryType {
                    memory64: false,
                    shared: false,
                    initial: 1,
                    maximum: None,
                }],
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
            }
        };

        let make_component = |idx: usize| -> ParsedComponent {
            ParsedComponent {
                name: None,
                core_modules: vec![make_module(idx)],
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
        };

        let components = vec![make_component(0), make_component(1)];

        let graph = DependencyGraph {
            instantiation_order: vec![0, 1],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:io/error@0.2.6".to_string()),
                    display_field: Some("drop".to_string()),
                },
                UnresolvedImport {
                    component_idx: 1,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:io/error@0.2.6".to_string()),
                    display_field: Some("drop".to_string()),
                },
            ],
        };

        let merger = Merger::new(MemoryStrategy::SharedMemory, false);
        let merged = merger
            .merge(&components, &graph)
            .expect("merge should succeed");

        // SharedMemory should NOT produce cabi_realloc$1
        let has_suffixed = merged
            .exports
            .iter()
            .any(|e| e.name.starts_with("cabi_realloc$"));
        assert!(
            !has_suffixed,
            "shared-memory mode must not generate cabi_realloc$N exports, \
             but found: {:?}",
            merged
                .exports
                .iter()
                .filter(|e| e.name.starts_with("cabi_realloc$"))
                .map(|e| &e.name)
                .collect::<Vec<_>>()
        );
    }

    /// #298 kill-criterion oracle (in-repo reproduction).
    ///
    /// Until now this failure was only reproducible *externally* — via gale's
    /// `crates/gale-app-demo/dissolve.sh` on a real wit-bindgen component pair.
    /// This pins it inside meld: fusing an all-scalar-boundary component pair in
    /// the real MCU config (`SharedMemory` ⟹ `address_rebasing = true`, exactly
    /// what `lib.rs` forces for shared memory) currently **hard-fails** because
    /// the vestigial canonical-ABI allocator's `memory.grow` (here standing in
    /// for `cabi_realloc → … → $sbrk → memory.grow`) reaches the address-rebase
    /// rewriter, which rejects `memory.grow` (`rewriter.rs` `MemoryGrow` arm).
    ///
    /// The boundary between the two components is fully internalized and scalar,
    /// so the allocator is provably dead — but the rewrite chokes on it *during
    /// merge*, before any DCE/reachability pass could run. That ordering is the
    /// crux of #298 (and why #298 ⟺ #299 are coupled).
    ///
    /// This asserts **today's** behavior (the hard-fail). When the #298
    /// dead-allocator handling lands, this test goes red — at which point its
    /// assertion must flip to the success criterion: merge succeeds, the fused
    /// core exports **0** `cabi_realloc`, and contains **0** `memory.grow`.
    #[test]
    fn test_298_vestigial_grow_blocks_shared_rebase_fusion() {
        use crate::parser::{FuncType, ModuleExport, ModuleImport, ParsedComponent};
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        // A real core module whose exported `cabi_realloc` body contains a
        // `memory.grow` — the canonical-ABI allocator meld must learn to drop.
        let src = r#"(module
            (type (func))
            (type (func (param i32 i32 i32 i32) (result i32)))
            (import "" "0" (func (type 0)))
            (memory 1)
            (func (type 1)
                i32.const 1
                memory.grow
                drop
                i32.const 0)
            (export "cabi_realloc" (func 1)))"#;
        let module_bytes = wat::parse_str(src).expect("wat compiles");

        // Locate the code section payload range (the parser fills this in real
        // runs; we mirror it so `extract_function_body` reads real bytes).
        let mut code_range = None;
        for payload in wasmparser::Parser::new(0).parse_all(&module_bytes) {
            if let wasmparser::Payload::CodeSectionStart { range, .. } = payload.expect("payload") {
                code_range = Some((range.start, range.end));
            }
        }
        let code_range = code_range.expect("module has a code section");

        let make_module = move || -> CoreModule {
            CoreModule {
                index: 0,
                bytes: module_bytes.clone(),
                types: vec![
                    FuncType {
                        params: vec![],
                        results: vec![],
                    },
                    FuncType {
                        params: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
                        results: vec![ValType::I32],
                    },
                ],
                imports: vec![ModuleImport {
                    module: "".to_string(),
                    name: "0".to_string(),
                    kind: ImportKind::Function(0),
                }],
                exports: vec![ModuleExport {
                    name: "cabi_realloc".to_string(),
                    kind: ExportKind::Function,
                    index: 1, // imported func 0, defined func = wasm idx 1
                }],
                functions: vec![1], // one defined func, type 1
                memories: vec![MemoryType {
                    memory64: false,
                    shared: false,
                    initial: 1,
                    maximum: None,
                }],
                tables: Vec::new(),
                globals: Vec::new(),
                start: None,
                data_count: None,
                element_count: 0,
                custom_sections: Vec::new(),
                code_section_range: Some(code_range),
                global_section_range: None,
                element_section_range: None,
                data_section_range: None,
            }
        };

        let make_component = |module: CoreModule| -> ParsedComponent {
            ParsedComponent {
                name: None,
                core_modules: vec![module],
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
        };

        let components = vec![make_component(make_module()), make_component(make_module())];

        let graph = DependencyGraph {
            instantiation_order: vec![0, 1],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:io/error@0.2.6".to_string()),
                    display_field: Some("drop".to_string()),
                },
                UnresolvedImport {
                    component_idx: 1,
                    module_idx: 0,
                    module_name: "".to_string(),
                    field_name: "0".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("wasi:io/error@0.2.6".to_string()),
                    display_field: Some("drop".to_string()),
                },
            ],
        };

        // Real MCU config: shared memory forces address rebasing.
        let merger = Merger::new(MemoryStrategy::SharedMemory, true);
        let result = merger.merge(&components, &graph);

        // TODO(#298): when the dead-allocator handling lands, flip this to:
        //   let merged = result.expect("fusion of a scalar boundary succeeds");
        //   assert!(!merged.exports.iter().any(|e| e.name.starts_with("cabi_realloc")));
        //   // and assert 0 memory.grow in the encoded core.
        let err = result.expect_err(
            "today: shared+rebase fusion must reject the vestigial allocator's memory.grow",
        );
        let msg = err.to_string();
        assert!(
            msg.contains("memory.grow"),
            "expected the memory.grow rebase rejection (the #298 coupling), got: {msg}"
        );
    }

    /// #298 positive control — validates the fork-side no-grow approach
    /// (pulseengine/wit-bindgen `integration/embedded-rt-no-grow`, which backs
    /// `cabi_realloc` with an embedder arena instead of `dlmalloc → $sbrk →
    /// memory.grow`).
    ///
    /// The hypothesis the fork branch rests on: a component whose `cabi_realloc`
    /// carries **no** `memory.grow` already fuses under `--memory shared`
    /// (⟹ `address_rebasing`) **today**, with no #298 fix — because the
    /// rewriter only rejects `memory.grow`, nothing else about the allocator.
    ///
    /// This faithfully mirrors the **real** fork output shape (verified against
    /// `pulseengine/wit-bindgen@4753871d`, the `cabi-realloc-extern` feature):
    /// `cabi_realloc` stays **exported** (so the same build still links on a
    /// composing host like wasmtime) but its body **forwards to an imported**
    /// `__cabi_arena_realloc(old_ptr, old_len, align, new_len) -> ptr` — the
    /// embedder-provided bounded arena that traps on exhaustion instead of
    /// calling `memory.grow`. The arena import is left **unresolved** (gale, the
    /// embedder, links it post-fuse over one policy for the whole image).
    ///
    /// This must SUCCEED and the fused core must (a) still export `cabi_realloc`
    /// and (b) retain the `__cabi_arena_realloc` import (the embedder seam).
    ///
    /// So the two fixes are complementary: the fork's no-grow `cabi_realloc`
    /// unblocks the MCU path directly (belt), and #298's meld-side drop handles
    /// the mixed/un-elided case (suspenders).
    #[test]
    fn test_298_fork_arena_realloc_fuses_under_shared_rebase_today() {
        use crate::parser::{FuncType, ModuleExport, ModuleImport, ParsedComponent};
        use crate::resolver::{DependencyGraph, UnresolvedImport};

        // The real fork shape: cabi_realloc forwards to the imported arena
        // function; NO memory.grow anywhere.
        let src = r#"(module
            (type (func (param i32 i32 i32 i32) (result i32)))
            (import "pulseengine:embedder/arena" "__cabi_arena_realloc" (func (type 0)))
            (memory 1)
            (func (type 0)
                local.get 0
                local.get 1
                local.get 2
                local.get 3
                call 0)
            (export "cabi_realloc" (func 1)))"#;
        let module_bytes = wat::parse_str(src).expect("wat compiles");

        let mut code_range = None;
        for payload in wasmparser::Parser::new(0).parse_all(&module_bytes) {
            if let wasmparser::Payload::CodeSectionStart { range, .. } = payload.expect("payload") {
                code_range = Some((range.start, range.end));
            }
        }
        let code_range = code_range.expect("module has a code section");

        let make_module = move || -> CoreModule {
            CoreModule {
                index: 0,
                bytes: module_bytes.clone(),
                types: vec![FuncType {
                    params: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
                    results: vec![ValType::I32],
                }],
                imports: vec![ModuleImport {
                    module: "pulseengine:embedder/arena".to_string(),
                    name: "__cabi_arena_realloc".to_string(),
                    kind: ImportKind::Function(0),
                }],
                exports: vec![ModuleExport {
                    name: "cabi_realloc".to_string(),
                    kind: ExportKind::Function,
                    index: 1, // imported arena func 0, defined cabi_realloc = wasm idx 1
                }],
                functions: vec![0],
                memories: vec![MemoryType {
                    memory64: false,
                    shared: false,
                    initial: 1,
                    maximum: None,
                }],
                tables: Vec::new(),
                globals: Vec::new(),
                start: None,
                data_count: None,
                element_count: 0,
                custom_sections: Vec::new(),
                code_section_range: Some(code_range),
                global_section_range: None,
                element_section_range: None,
                data_section_range: None,
            }
        };

        let make_component = |module: CoreModule| -> ParsedComponent {
            ParsedComponent {
                name: None,
                core_modules: vec![module],
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
        };

        let components = vec![make_component(make_module()), make_component(make_module())];

        let graph = DependencyGraph {
            instantiation_order: vec![0, 1],
            resolved_imports: HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            // The arena function is the embedder seam: gale provides it
            // post-fuse, so it stays unresolved through fusion.
            unresolved_imports: vec![
                UnresolvedImport {
                    component_idx: 0,
                    module_idx: 0,
                    module_name: "pulseengine:embedder/arena".to_string(),
                    field_name: "__cabi_arena_realloc".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("pulseengine:embedder/arena".to_string()),
                    display_field: Some("__cabi_arena_realloc".to_string()),
                },
                UnresolvedImport {
                    component_idx: 1,
                    module_idx: 0,
                    module_name: "pulseengine:embedder/arena".to_string(),
                    field_name: "__cabi_arena_realloc".to_string(),
                    kind: ImportKind::Function(0),
                    display_module: Some("pulseengine:embedder/arena".to_string()),
                    display_field: Some("__cabi_arena_realloc".to_string()),
                },
            ],
        };

        let merger = Merger::new(MemoryStrategy::SharedMemory, true);
        let merged = merger.merge(&components, &graph).expect(
            "a fork arena-backed (grow-free) realloc must fuse under shared+rebase TODAY \
             (no #298 needed)",
        );

        // Success under address-rebasing IS the grow-free proof: the rewriter
        // rejects any reachable `memory.grow` (see the kill-criterion oracle),
        // so a completed merge means no body grew memory. Both cabi_realloc
        // bodies survive (the suspenders #298 will later drop are belt here).
        assert_eq!(
            merged.functions.len(),
            2,
            "both arena-backed cabi_realloc bodies survive the rebase fuse"
        );

        // The fused core must still export cabi_realloc (kept present for a
        // composing host) ...
        assert!(
            merged.exports.iter().any(|e| e.name == "cabi_realloc"),
            "fused core keeps cabi_realloc exported (wasmtime-composability), \
             got exports: {:?}",
            merged.exports.iter().map(|e| &e.name).collect::<Vec<_>>()
        );

        // ... and must retain the __cabi_arena_realloc import — the embedder
        // seam gale links post-fuse. Without it the fused core could not
        // allocate, so meld must not drop or mis-wire it.
        assert!(
            merged
                .imports
                .iter()
                .any(|i| i.name == "__cabi_arena_realloc"),
            "fused core must retain the embedder arena import, got imports: {:?}",
            merged
                .imports
                .iter()
                .map(|i| format!("{}/{}", i.module, i.name))
                .collect::<Vec<_>>()
        );

        // #301: the retained import's module is in the recognized
        // `pulseengine:embedder` namespace, so meld preserves it as INTENTIONAL
        // embedder passthrough — not merely incidental survival of an unresolved
        // import. This ties the real fork fixture's module name to the explicit
        // recognition predicate the strict-resolution carve-out relies on.
        assert!(
            merged
                .imports
                .iter()
                .any(|i| i.name == "__cabi_arena_realloc"
                    && crate::resolver::is_embedder_passthrough(&i.module)),
            "retained arena import must be recognized as embedder passthrough by namespace, \
             got imports: {:?}",
            merged
                .imports
                .iter()
                .map(|i| format!("{}/{}", i.module, i.name))
                .collect::<Vec<_>>()
        );
    }

    // -- SR-31: Multiply-instantiated module detection -------------------------

    /// Helper to build a minimal ParsedComponent with given instances.
    fn make_component_with_instances(
        instances: Vec<crate::parser::ComponentInstance>,
    ) -> ParsedComponent {
        ParsedComponent {
            name: None,
            core_modules: vec![],
            imports: vec![],
            exports: vec![],
            types: vec![],
            instances,
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

    /// LS-M-5 gate-convention regression: a component that
    /// instantiates the same core module twice must be rejected at
    /// merge time with `DuplicateModuleInstantiation`, never silently
    /// mis-merged. This pins the detection-and-reject mitigation that
    /// closes the LS-M-5 silent-corruption hazard. (Named to satisfy
    /// the LS-N verification gate's `ls_<letter>_<num>_*` convention;
    /// `test_duplicate_module_instantiation_rejected` below predates
    /// the convention and is kept as-is.)
    #[test]
    fn ls_m_5_multiply_instantiated_module_rejected() {
        let comp = make_component_with_instances(vec![
            crate::parser::ComponentInstance {
                index: 0,
                kind: crate::parser::InstanceKind::Instantiate {
                    module_idx: 2,
                    args: vec![],
                },
            },
            crate::parser::ComponentInstance {
                index: 1,
                kind: crate::parser::InstanceKind::Instantiate {
                    module_idx: 2, // same module instantiated again
                    args: vec![],
                },
            },
        ]);
        let err = Merger::check_no_duplicate_instantiations(&[comp])
            .expect_err("multiply-instantiated module must be rejected");
        match err {
            Error::DuplicateModuleInstantiation {
                component_idx,
                module_idx,
            } => {
                assert_eq!(component_idx, 0);
                assert_eq!(module_idx, 2);
            }
            other => panic!("expected DuplicateModuleInstantiation, got {other:?}"),
        }
    }

    #[test]
    fn test_duplicate_module_instantiation_rejected() {
        let comp = make_component_with_instances(vec![
            crate::parser::ComponentInstance {
                index: 0,
                kind: crate::parser::InstanceKind::Instantiate {
                    module_idx: 0,
                    args: vec![],
                },
            },
            crate::parser::ComponentInstance {
                index: 1,
                kind: crate::parser::InstanceKind::Instantiate {
                    module_idx: 0, // duplicate!
                    args: vec![],
                },
            },
        ]);
        let result = Merger::check_no_duplicate_instantiations(&[comp]);
        assert!(result.is_err());
        let err_msg = format!("{}", result.unwrap_err());
        assert!(
            err_msg.contains("instantiates core module 0 more than once"),
            "Error should mention duplicate module: {}",
            err_msg
        );
    }

    #[test]
    fn test_single_instantiation_accepted() {
        let comp = make_component_with_instances(vec![
            crate::parser::ComponentInstance {
                index: 0,
                kind: crate::parser::InstanceKind::Instantiate {
                    module_idx: 0,
                    args: vec![],
                },
            },
            crate::parser::ComponentInstance {
                index: 1,
                kind: crate::parser::InstanceKind::Instantiate {
                    module_idx: 1, // different module — OK
                    args: vec![],
                },
            },
        ]);
        let result = Merger::check_no_duplicate_instantiations(&[comp]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_no_instances_accepted() {
        let comp = make_component_with_instances(vec![]);
        let result = Merger::check_no_duplicate_instantiations(&[comp]);
        assert!(result.is_ok());
    }

    // ---------------------------------------------------------------
    // LS-A-11 — extended-const truncation in global initializers
    // LS-A-15 — HashMap iteration non-determinism
    //
    // Shared empty-merged fixture used by both regression suites.
    // ---------------------------------------------------------------

    fn empty_merged_fixture() -> MergedModule {
        MergedModule {
            types: Vec::new(),
            imports: Vec::new(),
            functions: Vec::new(),
            tables: Vec::new(),
            memories: Vec::new(),
            globals: Vec::new(),
            exports: Vec::new(),
            start_function: None,
            elements: Vec::new(),
            data_segments: Vec::new(),
            custom_sections: Vec::new(),
            fused_function_names: std::collections::BTreeMap::new(),
            function_index_map: std::collections::HashMap::new(),
            memory_index_map: std::collections::HashMap::new(),
            table_index_map: std::collections::HashMap::new(),
            global_index_map: std::collections::HashMap::new(),
            type_index_map: std::collections::HashMap::new(),
            realloc_map: std::collections::HashMap::new(),
            import_counts: Default::default(),
            import_memory_indices: Vec::new(),
            import_realloc_indices: Vec::new(),
            resource_rep_by_component: std::collections::HashMap::new(),
            resource_new_by_component: std::collections::HashMap::new(),
            handle_tables: std::collections::HashMap::new(),
            task_return_shims: std::collections::HashMap::new(),
            async_result_globals: std::collections::HashMap::new(),
            segment_bases: std::collections::HashMap::new(),
        }
    }

    // LS-A-11: convert_init_expr must fold multi-op extended-const
    // expressions (was previously truncating to the first operator).
    #[test]
    fn ls_a_11_convert_init_expr_folds_extended_const_i32_add() {
        // Init expr bytes WITHOUT trailing `end` (the function appends
        // it). Use small operands that fit in single-byte sleb (no sign
        // bit at position 6): i32.const 5, i32.const 10, i32.add → 15.
        let bytes: Vec<u8> = vec![0x41, 5, 0x41, 10, 0x6A];
        let merged = empty_merged_fixture();

        let expr = convert_init_expr(&bytes, 0, 0, &merged, &ValType::I32);

        let mut encoded = Vec::new();
        wasm_encoder::Encode::encode(&expr, &mut encoded);
        let mut expected = Vec::new();
        wasm_encoder::Encode::encode(&ConstExpr::i32_const(15), &mut expected);

        assert_eq!(
            encoded, expected,
            "convert_init_expr must fold (i32.const 5)(i32.const 10) i32.add \
             to i32.const 15; got bytes {encoded:?}",
        );
    }

    #[test]
    fn ls_a_11_convert_init_expr_preserves_single_const() {
        // Regression: the fold path must not change behavior for a
        // simple single-const initializer.
        let bytes: Vec<u8> = vec![0x41, 5];
        let merged = empty_merged_fixture();

        let expr = convert_init_expr(&bytes, 0, 0, &merged, &ValType::I32);
        let mut encoded = Vec::new();
        wasm_encoder::Encode::encode(&expr, &mut encoded);
        let mut expected = Vec::new();
        wasm_encoder::Encode::encode(&ConstExpr::i32_const(5), &mut expected);
        assert_eq!(encoded, expected);
    }

    // LS-A-15: component_realloc_index fallback must be deterministic
    // when multiple modules carry cabi_realloc (was hash-seed dependent).
    #[test]
    fn ls_a_15_component_realloc_index_picks_lowest_module_deterministically() {
        // Component 0 has reallocs at modules 1 (idx 10), 2 (idx 11),
        // and 3 (idx 12), but no module 0. The function must
        // deterministically pick the realloc bound to the LOWEST module
        // index (module 1 → idx 10), not whatever HashMap happens to
        // iterate first.
        //
        // Rebuilding the HashMap from scratch each iteration gives
        // each instance a fresh hash seed, so iteration order varies
        // across iterations — if the impl picked an arbitrary entry,
        // we'd see more than one observed value.
        let mut observed = std::collections::HashSet::new();
        for _ in 0..64 {
            let mut merged = empty_merged_fixture();
            merged.realloc_map.insert((0, 1), 10);
            merged.realloc_map.insert((0, 2), 11);
            merged.realloc_map.insert((0, 3), 12);
            let got = component_realloc_index(&merged, 0).unwrap();
            observed.insert(got);
        }
        assert_eq!(
            observed.len(),
            1,
            "component_realloc_index must return a deterministic value \
             across runs; saw {observed:?}",
        );
        assert!(
            observed.contains(&10),
            "lowest module index (1 → realloc 10) must be selected; \
             observed {observed:?}",
        );
    }

    #[test]
    fn ls_a_15_component_realloc_index_prefers_module_0() {
        // Regression: when module 0 has a realloc, the function must
        // return it regardless of other modules in the map.
        let mut merged = empty_merged_fixture();
        merged.realloc_map.insert((0, 0), 100);
        merged.realloc_map.insert((0, 1), 200);
        assert_eq!(component_realloc_index(&merged, 0), Some(100));
    }

    // LS-A-19: find_exact_resource_import_idx must match the full
    // `[resource-{rep,new}]<name>` import string exactly. The prior
    // `imp.name.ends_with(rn)` form let `float` match both
    // `[resource-rep]float` and `[resource-rep]bigfloat`, so the
    // dedup-skip path would register the wrong import for the
    // wrong-suffix component (silent cross-resource confusion at
    // runtime, no host trap).
    fn merged_import(name: &str) -> MergedImport {
        MergedImport {
            module: "test".to_string(),
            name: name.to_string(),
            entity_type: EntityType::Function(0),
            component_idx: None,
        }
    }

    #[test]
    fn ls_a_19_exact_match_picks_float_not_bigfloat() {
        // imports[0] = [resource-rep]bigfloat
        // imports[1] = [resource-rep]float
        // Tracking has both indices. Asking for "[resource-rep]float"
        // must return 1, not 0 — even though the buggy ends_with
        // would have matched bigfloat first under some iteration
        // orders.
        let mut merged = empty_merged_fixture();
        merged.imports.push(merged_import("[resource-rep]bigfloat"));
        merged.imports.push(merged_import("[resource-rep]float"));
        merged
            .resource_rep_by_component
            .insert((0, "bigfloat".to_string()), 0);
        merged
            .resource_rep_by_component
            .insert((1, "float".to_string()), 1);

        let idx = find_exact_resource_import_idx(
            &merged.resource_rep_by_component,
            &merged.imports,
            "[resource-rep]float",
        );
        assert_eq!(
            idx,
            Some(1),
            "exact match must pick float (idx 1), not bigfloat"
        );
    }

    #[test]
    fn ls_a_19_no_match_returns_none_even_with_suffix_collision() {
        // Only bigfloat in tracking, but caller asks for plain float.
        // The buggy ends_with("float") would have returned bigfloat's
        // index. Exact match must return None.
        let mut merged = empty_merged_fixture();
        merged.imports.push(merged_import("[resource-rep]bigfloat"));
        merged
            .resource_rep_by_component
            .insert((0, "bigfloat".to_string()), 0);

        let idx = find_exact_resource_import_idx(
            &merged.resource_rep_by_component,
            &merged.imports,
            "[resource-rep]float",
        );
        assert_eq!(
            idx, None,
            "no exact match for 'float' must return None even though \
             'bigfloat' shares the suffix",
        );
    }

    #[test]
    fn ls_a_19_resource_new_lookup_is_also_exact() {
        // Same suffix-collision case for [resource-new] table.
        let mut merged = empty_merged_fixture();
        merged.imports.push(merged_import("[resource-new]bigfloat"));
        merged.imports.push(merged_import("[resource-new]float"));
        merged
            .resource_new_by_component
            .insert((0, "bigfloat".to_string()), 0);
        merged
            .resource_new_by_component
            .insert((1, "float".to_string()), 1);

        let idx = find_exact_resource_import_idx(
            &merged.resource_new_by_component,
            &merged.imports,
            "[resource-new]float",
        );
        assert_eq!(idx, Some(1));
    }
}

// ---------------------------------------------------------------------------
// Kani bounded-verification harnesses
//
// These harnesses verify core index-arithmetic properties of the merger using
// bounded model checking.  They operate on *model functions* that capture the
// exact same arithmetic as the real code but accept simple numeric inputs
// instead of full `ParsedComponent`/`MergedModule` structs.
//
// Run: `cargo kani --package meld-core`
// ---------------------------------------------------------------------------
#[cfg(kani)]
mod kani_proofs {
    /// Maximum number of modules Kani will explore.
    const MAX_MODULES: usize = 4;
    /// Maximum functions per module (import + defined).
    const MAX_FUNCS_PER_MODULE: u32 = 10;

    // -- Model functions (mirror merger.rs arithmetic) -----------------------

    /// Model of `decompose_component_core_func_index`.
    /// Given per-module function counts, find which module owns `index`.
    fn model_decompose(counts: &[u32], index: u32) -> Option<(usize, u32)> {
        let mut running: u32 = 0;
        for (i, &count) in counts.iter().enumerate() {
            if index < running.saturating_add(count) {
                return Some((i, index - running));
            }
            running = running.saturating_add(count);
        }
        None
    }

    /// Reconstruct a flat index from (module_idx, local_idx).
    fn model_reconstruct(counts: &[u32], mod_idx: usize, local_idx: u32) -> u32 {
        let offset: u32 = counts[..mod_idx].iter().copied().sum();
        offset + local_idx
    }

    /// Model of `function_index_map` value computation.
    /// For defined function at `array_position` in module `mod_idx`:
    ///   absolute_wasm_idx = import_count + cumulative_offset + array_position
    fn model_absolute_index(
        import_count: u32,
        defined_counts: &[u32],
        mod_idx: usize,
        array_position: u32,
    ) -> u32 {
        let offset: u32 = defined_counts[..mod_idx].iter().copied().sum();
        import_count + offset + array_position
    }

    /// Model of `defined_func`: convert absolute wasm index to array position.
    fn model_defined_func(import_count: u32, wasm_idx: u32) -> Option<u32> {
        if wasm_idx < import_count {
            None
        } else {
            Some(wasm_idx - import_count)
        }
    }

    // -- Harness 1: Decompose ↔ Reconstruct roundtrip -----------------------

    /// For any valid flat index, decompose then reconstruct yields the
    /// original index, and the local index is within the module's bounds.
    #[kani::proof]
    #[kani::unwind(5)]
    fn check_decompose_roundtrip() {
        let num_modules: usize = kani::any();
        kani::assume(num_modules > 0 && num_modules <= MAX_MODULES);

        let mut counts = [0u32; MAX_MODULES];
        let mut total: u32 = 0;
        for i in 0..MAX_MODULES {
            if i < num_modules {
                counts[i] = kani::any();
                kani::assume(counts[i] > 0 && counts[i] <= MAX_FUNCS_PER_MODULE);
                total = total.saturating_add(counts[i]);
            }
        }
        kani::assume(total > 0);
        kani::assume(total <= (MAX_MODULES as u32) * MAX_FUNCS_PER_MODULE);

        let index: u32 = kani::any();
        kani::assume(index < total);

        let result = model_decompose(&counts[..num_modules], index);
        assert!(result.is_some(), "valid index must decompose");

        let (mod_idx, local_idx) = result.unwrap();
        assert!(mod_idx < num_modules, "module index in range");
        assert!(local_idx < counts[mod_idx], "local index within module");

        let reconstructed = model_reconstruct(&counts[..num_modules], mod_idx, local_idx);
        assert_eq!(reconstructed, index, "roundtrip must preserve index");
    }

    // -- Harness 2: Absolute index is bounded -------------------------------

    /// Every absolute wasm index produced by the index map is strictly less
    /// than `import_count + total_defined`.
    #[kani::proof]
    #[kani::unwind(5)]
    fn check_function_index_map_bounded() {
        let num_modules: usize = kani::any();
        kani::assume(num_modules > 0 && num_modules <= MAX_MODULES);

        let import_count: u32 = kani::any();
        kani::assume(import_count <= 20);

        let mut defined_counts = [0u32; MAX_MODULES];
        let mut total_defined: u32 = 0;
        for i in 0..MAX_MODULES {
            if i < num_modules {
                defined_counts[i] = kani::any();
                kani::assume(defined_counts[i] <= MAX_FUNCS_PER_MODULE);
                total_defined = total_defined.saturating_add(defined_counts[i]);
            }
        }
        kani::assume(total_defined > 0);

        // Pick an arbitrary module and array position
        let mod_idx: usize = kani::any();
        kani::assume(mod_idx < num_modules);
        let array_pos: u32 = kani::any();
        kani::assume(array_pos < defined_counts[mod_idx]);

        let abs_idx = model_absolute_index(
            import_count,
            &defined_counts[..num_modules],
            mod_idx,
            array_pos,
        );

        assert!(
            abs_idx < import_count + total_defined,
            "absolute index must be < import_count + total_defined"
        );
        assert!(
            abs_idx >= import_count,
            "absolute index of defined func must be >= import_count"
        );
    }

    // -- Harness 3: Remap injectivity (no collisions) -----------------------

    /// Two different (mod_idx, local_idx) pairs always produce different
    /// absolute wasm indices.
    #[kani::proof]
    #[kani::unwind(5)]
    fn check_remap_injective_small() {
        let num_modules: usize = kani::any();
        kani::assume(num_modules > 0 && num_modules <= MAX_MODULES);

        let import_count: u32 = kani::any();
        kani::assume(import_count <= 20);

        let mut defined_counts = [0u32; MAX_MODULES];
        for i in 0..MAX_MODULES {
            if i < num_modules {
                defined_counts[i] = kani::any();
                kani::assume(defined_counts[i] > 0 && defined_counts[i] <= MAX_FUNCS_PER_MODULE);
            }
        }

        // Pick two different (mod_idx, array_pos) pairs
        let mod_a: usize = kani::any();
        let pos_a: u32 = kani::any();
        let mod_b: usize = kani::any();
        let pos_b: u32 = kani::any();
        kani::assume(mod_a < num_modules && mod_b < num_modules);
        kani::assume(pos_a < defined_counts[mod_a] && pos_b < defined_counts[mod_b]);
        kani::assume(mod_a != mod_b || pos_a != pos_b);

        let idx_a =
            model_absolute_index(import_count, &defined_counts[..num_modules], mod_a, pos_a);
        let idx_b =
            model_absolute_index(import_count, &defined_counts[..num_modules], mod_b, pos_b);

        assert_ne!(
            idx_a, idx_b,
            "different source locations must map to different indices"
        );
    }

    // -- Harness 4: Absolute index monotonicity -----------------------------

    /// Within a single module, defined function indices are strictly
    /// increasing with array position.
    #[kani::proof]
    #[kani::unwind(5)]
    fn check_absolute_index_monotonic() {
        let num_modules: usize = kani::any();
        kani::assume(num_modules > 0 && num_modules <= MAX_MODULES);

        let import_count: u32 = kani::any();
        kani::assume(import_count <= 20);

        let mut defined_counts = [0u32; MAX_MODULES];
        for i in 0..MAX_MODULES {
            if i < num_modules {
                defined_counts[i] = kani::any();
                kani::assume(defined_counts[i] >= 2 && defined_counts[i] <= MAX_FUNCS_PER_MODULE);
            }
        }

        let mod_idx: usize = kani::any();
        kani::assume(mod_idx < num_modules);

        let pos_lo: u32 = kani::any();
        let pos_hi: u32 = kani::any();
        kani::assume(pos_lo < pos_hi && pos_hi < defined_counts[mod_idx]);

        let idx_lo = model_absolute_index(
            import_count,
            &defined_counts[..num_modules],
            mod_idx,
            pos_lo,
        );
        let idx_hi = model_absolute_index(
            import_count,
            &defined_counts[..num_modules],
            mod_idx,
            pos_hi,
        );

        assert!(
            idx_lo < idx_hi,
            "indices must be strictly monotonic within a module"
        );
    }

    // -- Harness 5: defined_func roundtrip ----------------------------------

    /// `defined_func(absolute_index(import_count, offset, pos))` returns
    /// the correct array position, and indices below import_count return None.
    #[kani::proof]
    fn check_defined_func_roundtrip() {
        let import_count: u32 = kani::any();
        kani::assume(import_count <= 20);

        let total_defined: u32 = kani::any();
        kani::assume(total_defined > 0 && total_defined <= 40);

        let array_pos: u32 = kani::any();
        kani::assume(array_pos < total_defined);

        let wasm_idx = import_count + array_pos;

        // defined_func should succeed and return the array position
        let result = model_defined_func(import_count, wasm_idx);
        assert_eq!(result, Some(array_pos));

        // Any index below import_count should return None
        if import_count > 0 {
            let below: u32 = kani::any();
            kani::assume(below < import_count);
            assert_eq!(model_defined_func(import_count, below), None);
        }
    }
}
