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

mod handle_tables;
mod imports;
mod index_maps;
mod memory;
mod merge_core;
mod naming;

#[cfg(test)]
mod tests_a;
#[cfg(test)]
mod tests_b;

pub(crate) use self::imports::UnresolvedImportAssignments;
pub(crate) use self::imports::{
    accumulate_remapped_function_names, compute_unresolved_import_assignments,
};
pub(crate) use self::index_maps::{
    build_index_maps_for_module, component_memory_index, component_realloc_index,
    convert_global_type, convert_init_expr, convert_table_type,
    decompose_component_core_func_index, extract_function_body, remap_concrete_val_type,
};
pub(crate) use self::memory::{
    SharedMemoryPlan, convert_memory_type, module_has_direct_memory_access, module_memory_type,
};
pub(crate) use self::naming::{
    compare_version, component_display_name, extract_version, ht_export_suffix,
    normalize_wasi_module_name, strip_dollar_suffix,
};
// Re-exports consumed only by the test submodules (widening these into the
// non-test build would flag as unused under `-D warnings`).
#[cfg(test)]
pub(crate) use self::imports::find_exact_resource_import_idx;
#[cfg(test)]
pub(crate) use self::index_maps::create_global_init;
#[cfg(test)]
pub(crate) use self::memory::{combine_memory_types_rebased, combine_memory_types_shared};

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

    /// #353 (static PIC): merged (absolute) global index → constant i32 value,
    /// for **defined** globals whose init folds to a constant i32 (e.g. a
    /// `__memory_base` a `$main` module provides). Consumed by the data/element
    /// offset fold in `ParsedConstExpr::reindex` via `IndexMaps`.
    pub defined_global_i32_const: std::collections::HashMap<u32, i32>,

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

    /// SR-66 / #380: under `--share-stack`, the top of the single shared
    /// shadow-stack region (`max_i(sp_i)`, 16-byte-aligned base of the first
    /// provider's data). `None` when `--share-stack` is off. Consumed by
    /// `mcu_dissolve::coalesce_stack_pointers` to fuse every `__stack_pointer`
    /// onto one survivor initialised to this value (regardless of the providers'
    /// original inits).
    pub shared_stack_top: Option<u64>,
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

/// Module merger
pub struct Merger {
    memory_strategy: MemoryStrategy,
    address_rebasing: bool,
    /// #298: the upstream `cabi_realloc`-is-vestigial verdict
    /// (`Fuser::cabi_realloc_drop_provably_safe`). When set, module bodies are
    /// rewritten with `IndexMaps::defer_grow_under_rebase`, so a `memory.grow`
    /// in the (now provably dead) vestigial allocator emits `unreachable`
    /// under address rebasing instead of hard-failing. Defaults `false`
    /// (current behavior preserved everywhere the gated wiring is absent).
    defer_grow_under_rebase: bool,
    /// (interface, resource_name) tuples marked opaque-rep — skip handle
    /// table allocation for these resources because their reps are already
    /// valid integer handles (no Box dereferencing in user code).
    opaque_resources: Vec<(String, String)>,
    /// SR-57 / #370: compact used-extent rebasing. When set (and rebasing is
    /// active), each module is placed at its actual used data extent (16-byte
    /// aligned) instead of its declared page count, and the combined memory is
    /// sized to the packed total. See [`FuserConfig::pack_rebase`] for the
    /// soundness envelope.
    pack_rebase: bool,
    /// SR-66 / #380: collapse the per-provider shadow stacks into one shared
    /// region. Builds on `pack_rebase` (the caller sets `pack_rebase` too). See
    /// [`FuserConfig::share_stack`] for the layout and soundness envelope.
    share_stack: bool,
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
            defer_grow_under_rebase: false,
            opaque_resources: Vec::new(),
            pack_rebase: false,
            share_stack: false,
        }
    }

    /// Mark resources as opaque-rep so handle table allocation skips them.
    pub fn with_opaque_resources(mut self, opaque: Vec<(String, String)>) -> Self {
        self.opaque_resources = opaque;
        self
    }

    /// #298: thread the upstream vestigial-`cabi_realloc` verdict in. When
    /// `true`, the vestigial allocator's `memory.grow` is deferred to
    /// `unreachable` under address rebasing (see
    /// [`IndexMaps::defer_grow_under_rebase`]) rather than hard-failing —
    /// sound only because the caller has proved that allocator dead.
    pub fn with_defer_grow_under_rebase(mut self, defer: bool) -> Self {
        self.defer_grow_under_rebase = defer;
        self
    }

    /// SR-57 / #370: enable compact used-extent rebasing (see the
    /// [`pack_rebase`](Self::pack_rebase) field). No effect unless rebasing is
    /// active, since the per-module base map is only built under rebasing.
    pub fn with_pack_rebase(mut self, pack: bool) -> Self {
        self.pack_rebase = pack;
        self
    }

    /// SR-66 / #380: enable shared-shadow-stack packing (see the
    /// [`share_stack`](Self::share_stack) field). The caller also enables
    /// `pack_rebase`; this only takes effect on the rebased shared-memory path.
    pub fn with_share_stack(mut self, share: bool) -> Self {
        self.share_stack = share;
        self
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
            defined_global_i32_const: std::collections::HashMap::new(),
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
            shared_stack_top: None,
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
            merged.shared_stack_top = plan.shared_stack_top;
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

impl Default for Merger {
    fn default() -> Self {
        Self::new(MemoryStrategy::MultiMemory, false)
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
