//! Dependency resolution for component fusion
//!
//! This module handles building the import/export graph between components
//! and performing topological sort for instantiation order.

use crate::merger::decompose_component_core_func_index;
use crate::parser::{
    CanonStringEncoding, ComponentExport, ExportKind, ImportKind, ModuleExport, ParsedComponent,
};
use crate::{Error, MemoryStrategy, Result};
use std::collections::{HashMap, HashSet};

/// Compose a (module_idx, module_local_func_idx) pair into a component-level
/// core function index.  This is the inverse of `decompose_component_core_func_index`.
///
/// The component-level core function index space concatenates all functions
/// (imports + defined) from each module in order: module 0, module 1, ...
fn compose_component_core_func_index(
    component: &ParsedComponent,
    target_module_idx: usize,
    module_local_func_idx: u32,
) -> Option<u32> {
    let mut running: u32 = 0;
    for (mod_idx, module) in component.core_modules.iter().enumerate() {
        let import_func_count = module
            .imports
            .iter()
            .filter(|i| matches!(i.kind, ImportKind::Function(_)))
            .count() as u32;
        let module_func_count = import_func_count + module.functions.len() as u32;
        if mod_idx == target_module_idx {
            if module_local_func_idx < module_func_count {
                return Some(running + module_local_func_idx);
            } else {
                return None;
            }
        }
        running = running.saturating_add(module_func_count);
    }
    None
}

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
    /// Import module name
    pub module_name: String,
    /// Import field name
    pub field_name: String,
    /// Import kind
    pub kind: ImportKind,
}

/// A cross-component call that needs an adapter
#[derive(Debug, Clone)]
pub struct AdapterSite {
    /// Source component index
    pub from_component: usize,
    /// Source module index within component
    pub from_module: usize,
    /// Import being resolved
    pub import_name: String,

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
        let mut graph = DependencyGraph {
            instantiation_order: Vec::new(),
            resolved_imports: HashMap::new(),
            unresolved_imports: Vec::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
        };

        // Build export index
        let export_index = self.build_export_index(components);

        // Resolve component-level imports
        self.resolve_component_imports(components, &export_index, &mut graph)?;

        // Resolve module-level imports within each component
        self.resolve_module_imports(components, &mut graph)?;

        // Detect cycles in intra-component module dependencies
        for (comp_idx, component) in components.iter().enumerate() {
            Self::detect_module_cycles(
                comp_idx,
                component.core_modules.len(),
                &graph.module_resolutions,
            )?;
        }

        // Build dependency graph for topological sort
        let dependencies = self.build_dependency_edges(components, &graph);

        // Topological sort
        graph.instantiation_order = self.topological_sort(components.len(), &dependencies)?;

        // Identify adapter sites (cross-component)
        self.identify_adapter_sites(components, &mut graph)?;

        // Identify intra-component adapter sites for module pairs with
        // different canonical options (string encoding, memory, realloc).
        // This must run after identify_adapter_sites and may promote some
        // module_resolutions entries to adapter_sites.
        self.identify_intra_component_adapter_sites(components, &mut graph)?;

        Ok(graph)
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
    fn resolve_component_imports(
        &self,
        components: &[ParsedComponent],
        export_index: &HashMap<String, Vec<(usize, &ComponentExport)>>,
        graph: &mut DependencyGraph,
    ) -> Result<()> {
        for (comp_idx, component) in components.iter().enumerate() {
            for import in &component.imports {
                // Look for a matching export
                if let Some(exports) = export_index.get(&import.name) {
                    // Find an export from a different component
                    if let Some((export_comp_idx, _export)) =
                        exports.iter().find(|(idx, _)| *idx != comp_idx)
                    {
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

    /// Resolve module-level imports within each component
    fn resolve_module_imports(
        &self,
        components: &[ParsedComponent],
        graph: &mut DependencyGraph,
    ) -> Result<()> {
        for (comp_idx, component) in components.iter().enumerate() {
            // Build export index for this component's modules
            let mut module_exports: HashMap<(&str, &str), (usize, &ModuleExport)> = HashMap::new();

            for (mod_idx, module) in component.core_modules.iter().enumerate() {
                for export in &module.exports {
                    // Key is (module name pattern, export name)
                    // In component model, modules don't have names directly,
                    // but instances do. For simplicity, we use module index as "name"
                    let key = ("", export.name.as_str());
                    module_exports.insert(key, (mod_idx, export));
                }
            }

            // Resolve imports within this component
            for (from_mod_idx, module) in component.core_modules.iter().enumerate() {
                for import in &module.imports {
                    // Try to find a matching export
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
                        // Unresolved - will need to be imported in final module
                        graph.unresolved_imports.push(UnresolvedImport {
                            component_idx: comp_idx,
                            module_idx: from_mod_idx,
                            module_name: import.module.clone(),
                            field_name: import.name.clone(),
                            kind: import.kind.clone(),
                        });
                    }
                }
            }
        }

        Ok(())
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

    /// Perform topological sort on components
    fn topological_sort(&self, n: usize, edges: &[(usize, usize)]) -> Result<Vec<usize>> {
        // Build adjacency list and in-degree count
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
        let mut in_degree = vec![0usize; n];

        for &(from, to) in edges {
            adj[from].push(to);
            in_degree[to] += 1;
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
            return Err(Error::CircularDependency);
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
        for ((from_comp, import_name), (to_comp, export_name)) in &graph.resolved_imports {
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
                    // Find the target module that exports this
                    for (to_mod_idx, to_module) in to_component.core_modules.iter().enumerate() {
                        let has_export =
                            to_module.exports.iter().any(|exp| exp.name == *export_name);

                        if has_export {
                            // Find the exported function's original index.
                            // This should always succeed since has_export is true.
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

                            // Determine if this call crosses a memory boundary
                            let crosses_memory = match self.memory_strategy {
                                MemoryStrategy::SharedMemory => false,
                                MemoryStrategy::MultiMemory => {
                                    let has_memory = |c: &ParsedComponent| {
                                        c.core_modules.iter().any(|m| {
                                            !m.memories.is_empty()
                                                || m.imports.iter().any(|i| {
                                                    matches!(i.kind, ImportKind::Memory(_))
                                                })
                                        })
                                    };
                                    has_memory(from_component) && has_memory(to_component)
                                }
                            };

                            // Populate canonical requirements from lift/lower options
                            let mut requirements = AdapterRequirements::default();

                            // Callee side: look up lift options for the exported core function
                            let callee_lift_map = to_component.lift_options_by_core_func();
                            if let Some(lift_opts) = callee_lift_map.get(&export_func_idx) {
                                requirements.callee_encoding = Some(lift_opts.string_encoding);
                                // Decompose post_return from component-level core function index
                                // to (module_idx, module_local_func_idx) for correct function_index_map lookup
                                requirements.callee_post_return =
                                    lift_opts.post_return.and_then(|pr_idx| {
                                        decompose_component_core_func_index(to_component, pr_idx)
                                    });
                                requirements.callee_realloc = lift_opts.realloc;
                            }

                            // Caller side: look up lower options by import func index.
                            // The Lower entry's func_index is a component function
                            // index. Try to match it to the component import whose
                            // name equals import_name by counting function-typed
                            // imports in order (each function import occupies a
                            // slot in the component function index space).
                            let caller_lower_map = from_component.lower_options_by_func();
                            let mut matched_caller_encoding = None;

                            // Attempt name-based match via component imports
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

                            // Fall back: if name-based match failed, use the first
                            // Lower entry. This is correct for single-import
                            // components (the common case).
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

                            // Set string_transcoding flag when encodings differ
                            if let (Some(caller_enc), Some(callee_enc)) =
                                (requirements.caller_encoding, requirements.callee_encoding)
                            {
                                requirements.string_transcoding = caller_enc != callee_enc;
                            }

                            graph.adapter_sites.push(AdapterSite {
                                from_component: *from_comp,
                                from_module: from_mod_idx,
                                import_name: import_name.clone(),
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

            // Compose the target function's component-level core function index
            // so we can look up Lift options.
            let target_comp_func_idx = match compose_component_core_func_index(
                component,
                res.to_module,
                export_func_idx,
            ) {
                Some(idx) => idx,
                None => continue, // Cannot compose, skip
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

            // Decompose callee's post-return
            if let Some(lift_opts) = callee_lift {
                requirements.callee_post_return = lift_opts
                    .post_return
                    .and_then(|pr_idx| decompose_component_core_func_index(component, pr_idx));
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
    fn test_topological_sort_circular() {
        let resolver = Resolver::new();
        // 0 -> 1 -> 2 -> 0
        let edges = vec![(0, 1), (1, 2), (2, 0)];
        let result = resolver.topological_sort(3, &edges);
        assert!(matches!(result, Err(Error::CircularDependency)));
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
}
