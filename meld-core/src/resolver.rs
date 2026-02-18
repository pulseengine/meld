//! Dependency resolution for component fusion
//!
//! This module handles building the import/export graph between components
//! and performing topological sort for instantiation order.

use crate::parser::{
    CanonStringEncoding, ComponentExport, ImportKind, ModuleExport, ParsedComponent,
};
use crate::{Error, MemoryStrategy, Result};
use std::collections::HashMap;

/// Result of dependency resolution
#[derive(Debug, Clone)]
pub struct DependencyGraph {
    /// Ordered list of component indices (topological order)
    pub instantiation_order: Vec<usize>,

    /// Resolved imports: maps (component_idx, import_name) → (component_idx, export_name)
    pub resolved_imports: HashMap<(usize, String), (usize, String)>,

    /// Unresolved imports that must remain as module imports
    pub unresolved_imports: Vec<UnresolvedImport>,

    /// Cross-component call sites that need adapters
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
    /// Callee's post-return function (component-local core function index)
    pub callee_post_return: Option<u32>,
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

        // Build dependency graph for topological sort
        let dependencies = self.build_dependency_edges(components, &graph);

        // Topological sort
        graph.instantiation_order = self.topological_sort(components.len(), &dependencies)?;

        // Identify adapter sites
        self.identify_adapter_sites(components, &mut graph)?;

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
                                requirements.callee_post_return = lift_opts.post_return;
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
}
