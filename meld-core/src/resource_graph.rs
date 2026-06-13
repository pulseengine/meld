//! Resource ownership graph for multi-component resource handle routing.
//!
//! The component composition forms a directed acyclic graph where resources
//! flow from defining components through re-exporting intermediates to
//! consumers. This module builds that graph and provides O(1) queries for:
//!
//! - Does a component define (own) a resource? → `defines_resource(comp, resource)`
//! - Which component defines a given resource? → `resource_definer(resource)`
//! - Is a component a re-exporter for a resource? → `is_reexporter(comp, resource)`

use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::EdgeRef;
use std::collections::HashMap;

/// A node in the resource ownership graph.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GraphNode {
    /// A flattened component (by index).
    Component(usize),
    /// A resource type identified by (interface_name, resource_name).
    Resource(String, String),
}

/// An edge in the resource ownership graph.
#[derive(Debug, Clone)]
pub enum GraphEdge {
    /// Component defines/owns this resource (has canonical ResourceRep).
    Defines,
    /// Component imports this resource from another component.
    ImportsFrom,
    /// Component re-exports this resource (imports AND exports same interface).
    Reexports,
    /// Component A's import is resolved to component B's export for this interface.
    ResolvesTo { interface: String },
}

/// Which `[resource-*]` prefix a core import carries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ResourcePrefixKind {
    Rep,
    New,
    Drop,
}

/// The resource ownership graph.
pub struct ResourceGraph {
    graph: DiGraph<GraphNode, GraphEdge>,
    /// Quick lookup: component index → node index
    comp_nodes: HashMap<usize, NodeIndex>,
    /// Quick lookup: (interface, resource) → node index
    resource_nodes: HashMap<(String, String), NodeIndex>,
    /// Cache: (comp_idx, resource_key) → defines?
    defines_cache: HashMap<(usize, String, String), bool>,
    /// Cache: (interface, resource) → defining comp_idx
    definer_cache: HashMap<(String, String), Option<usize>>,
}

impl Clone for ResourceGraph {
    fn clone(&self) -> Self {
        Self {
            graph: self.graph.clone(),
            comp_nodes: self.comp_nodes.clone(),
            resource_nodes: self.resource_nodes.clone(),
            defines_cache: self.defines_cache.clone(),
            definer_cache: self.definer_cache.clone(),
        }
    }
}

impl std::fmt::Debug for ResourceGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ResourceGraph")
            .field("nodes", &self.graph.node_count())
            .field("edges", &self.graph.edge_count())
            .field("defines_cache", &self.defines_cache)
            .field("definer_cache", &self.definer_cache)
            .finish()
    }
}

impl ResourceGraph {
    /// Build the resource graph from resolved imports and parsed components.
    ///
    /// `resolved_imports` maps (importer_comp, import_name) → (exporter_comp, export_name).
    /// `components` provides the parsed component data for canonical function detection.
    pub fn build(
        resolved_imports: &HashMap<(usize, String), (usize, String)>,
        components: &[crate::parser::ParsedComponent],
    ) -> Self {
        let mut graph = DiGraph::new();
        let mut comp_nodes = HashMap::new();
        let mut resource_nodes = HashMap::new();

        // Create component nodes
        for i in 0..components.len() {
            let idx = graph.add_node(GraphNode::Component(i));
            comp_nodes.insert(i, idx);
        }

        // Create resolution edges (comp A imports from comp B)
        for ((from_comp, import_name), (to_comp, _export_name)) in resolved_imports {
            if from_comp == to_comp {
                continue;
            }
            if let (Some(&from_node), Some(&to_node)) =
                (comp_nodes.get(from_comp), comp_nodes.get(to_comp))
            {
                graph.add_edge(
                    from_node,
                    to_node,
                    GraphEdge::ResolvesTo {
                        interface: import_name.clone(),
                    },
                );
            }
        }

        // Detect which components define vs import resources.
        // A component "defines" a resource if it has canonical ResourceRep entries
        // that can be traced through its core instances (Step 4 in the old approach).
        // A component that only has ResourceNew (no ResourceRep) re-exports.
        for (comp_idx, comp) in components.iter().enumerate() {
            let has_rep = comp
                .canonical_functions
                .iter()
                .any(|e| matches!(e, crate::parser::CanonicalEntry::ResourceRep { .. }));
            let has_new = comp
                .canonical_functions
                .iter()
                .any(|e| matches!(e, crate::parser::CanonicalEntry::ResourceNew { .. }));

            if has_rep || has_new {
                // This component participates in resource handling.
                // Determine which resources it handles by scanning core module imports.
                //
                // LS-A-18: also register a resource node for any
                // [resource-drop]X import even if X is a *foreign*
                // resource that the component neither reps nor news.
                // Prior to the fix, drop-only imports against foreign
                // resources were silently invisible to the graph (the
                // second pass that strips [resource-drop] only fires
                // when `!has_any_canon`), so the merger would route
                // the drop to a wrong handle table.
                for module in &comp.core_modules {
                    for imp in &module.imports {
                        if let crate::parser::ImportKind::Function(_) = &imp.kind {
                            let (prefix, kind) =
                                if let Some(rn) = imp.name.strip_prefix("[resource-rep]") {
                                    (rn, ResourcePrefixKind::Rep)
                                } else if let Some(rn) = imp.name.strip_prefix("[resource-new]") {
                                    (rn, ResourcePrefixKind::New)
                                } else if let Some(rn) = imp.name.strip_prefix("[resource-drop]") {
                                    (rn, ResourcePrefixKind::Drop)
                                } else {
                                    continue;
                                };

                            let interface = imp.module.clone();
                            let resource_name = prefix.to_string();
                            let resource_key = (interface.clone(), resource_name.clone());

                            // Ensure resource node exists
                            let resource_node =
                                *resource_nodes.entry(resource_key).or_insert_with(|| {
                                    graph.add_node(GraphNode::Resource(
                                        interface.clone(),
                                        resource_name.clone(),
                                    ))
                                });

                            if let Some(&comp_node) = comp_nodes.get(&comp_idx) {
                                match kind {
                                    ResourcePrefixKind::Rep if has_rep => {
                                        // Canonical ResourceRep AND imports [resource-rep]
                                        // → it defines this resource
                                        graph.add_edge(
                                            comp_node,
                                            resource_node,
                                            GraphEdge::Defines,
                                        );
                                    }
                                    ResourcePrefixKind::New if !has_rep && has_new => {
                                        // Only ResourceNew, no ResourceRep → re-exporter
                                        graph.add_edge(
                                            comp_node,
                                            resource_node,
                                            GraphEdge::Reexports,
                                        );
                                    }
                                    _ => {
                                        // Includes:
                                        //   - [resource-drop]X imports (foreign
                                        //     resource being dropped — pure
                                        //     consumer of X)
                                        //   - Rep / New imports that don't
                                        //     match the canonical entries
                                        //     (also pure consumer behavior)
                                        graph.add_edge(
                                            comp_node,
                                            resource_node,
                                            GraphEdge::ImportsFrom,
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Also mark components that import resource interfaces but have no
        // canonical entries (pure consumers like the runner).
        for (comp_idx, comp) in components.iter().enumerate() {
            let has_any_canon = comp.canonical_functions.iter().any(|e| {
                matches!(
                    e,
                    crate::parser::CanonicalEntry::ResourceRep { .. }
                        | crate::parser::CanonicalEntry::ResourceNew { .. }
                )
            });
            if !has_any_canon {
                for module in &comp.core_modules {
                    for imp in &module.imports {
                        if let crate::parser::ImportKind::Function(_) = &imp.kind {
                            let rn = if let Some(rn) = imp.name.strip_prefix("[resource-rep]") {
                                rn
                            } else if let Some(rn) = imp.name.strip_prefix("[resource-new]") {
                                rn
                            } else if let Some(rn) = imp.name.strip_prefix("[resource-drop]") {
                                rn
                            } else {
                                continue;
                            };

                            let interface = imp.module.clone();
                            let resource_key = (interface.clone(), rn.to_string());
                            let resource_node =
                                *resource_nodes.entry(resource_key).or_insert_with(|| {
                                    graph.add_node(GraphNode::Resource(
                                        interface.clone(),
                                        rn.to_string(),
                                    ))
                                });

                            if let Some(&comp_node) = comp_nodes.get(&comp_idx) {
                                graph.add_edge(comp_node, resource_node, GraphEdge::ImportsFrom);
                            }
                        }
                    }
                }
            }
        }

        // Build caches using composition DAG.
        // A component DEFINES a resource if:
        // 1. It has a Defines edge to the resource node (canonical ResourceRep), OR
        // 2. It exports the resource's interface but does NOT import it
        //    (terminal exporter in the composition chain = the definer).
        let mut defines_cache = HashMap::new();
        let mut definer_cache = HashMap::new();

        // Collect components with Defines edges (candidates, may include re-exporters)
        let mut defines_candidates: HashMap<(usize, String, String), bool> = HashMap::new();
        for ((iface, rn), &resource_node) in &resource_nodes {
            for edge in graph.edges_directed(resource_node, petgraph::Direction::Incoming) {
                if matches!(edge.weight(), GraphEdge::Defines)
                    && let GraphNode::Component(idx) = graph[edge.source()]
                {
                    defines_candidates.insert((idx, iface.clone(), rn.clone()), true);
                }
            }
        }

        // Second pass: use ResolvesTo edges for definer detection.
        // For each interface, find the terminal component — the one that
        // exports but doesn't import (no outgoing ResolvesTo for this interface).
        // This handles cases where canonical_functions is empty after flattening.
        for ((_from_comp, import_name), (to_comp, _)) in resolved_imports {
            // Determine whether `to_comp` is a re-exporter for *this
            // specific interface* (i.e. it imports an interface that
            // carries the resources we're about to attribute) or a
            // terminal definer.
            //
            // Prior to the LS-A-17 fix this check ran
            // `resource_nodes.keys().any(...)` against ANY iface, so
            // any consumer that imported `wasi:io/poll` alongside the
            // app's resources would mis-classify the app's true
            // definer as a re-exporter. The fix scopes the check to
            // `import_name` (and its `[export]`-prefixed variants).
            let to_also_imports_resource = resolved_imports.keys().any(|(comp, iname)| {
                *comp == *to_comp
                    && (iname == import_name
                        || iname.strip_prefix("[export]") == Some(import_name.as_str())
                        || import_name.strip_prefix("[export]") == Some(iname.as_str()))
                    && resource_nodes.keys().any(|(ri, _)| {
                        ri == iname || ri.strip_prefix("[export]") == Some(iname.as_str())
                    })
            });
            if !to_also_imports_resource {
                // Terminal exporter — true definer
                for (iface, rn) in resource_nodes.keys() {
                    let iface_matches = iface == import_name
                        || iface.strip_prefix("[export]") == Some(import_name.as_str());
                    if iface_matches {
                        defines_cache.insert((*to_comp, iface.clone(), rn.clone()), true);
                        definer_cache.insert((iface.clone(), rn.clone()), Some(*to_comp));
                    }
                }
            }
        }

        // Merge: candidates from first pass that weren't overridden by second pass
        for (idx, iface, rn) in defines_candidates.keys() {
            defines_cache
                .entry((*idx, iface.clone(), rn.clone()))
                .or_insert(true);
            definer_cache
                .entry((iface.clone(), rn.clone()))
                .or_insert(Some(*idx));
        }

        // Remove defines entries for components that also import the SAME
        // resource interface (they're re-exporters, not definers).
        // Only remove entries whose interface matches the imported one.
        for (from_comp, import_name) in resolved_imports.keys() {
            let matching_resource_ifaces: Vec<_> = resource_nodes
                .keys()
                .filter(|(ri, _)| {
                    ri == import_name
                        || ri.strip_prefix("[export]") == Some(import_name.as_str())
                        || import_name.strip_prefix("[export]") == Some(ri.as_str())
                })
                .cloned()
                .collect();
            for (ri, rn) in &matching_resource_ifaces {
                // Remove the component's definer entry **only** for the
                // specific (interface, resource_name) pair matched here.
                //
                // Prior to the LS-A-17 fix this filter ignored the
                // interface (`|(idx, _iface, r)| ...`), so a component
                // that imported `[resource-drop]X` from interface `I_x`
                // AND defined its own resource `X` in unrelated
                // interface `I_y` lost the `(comp, I_y, X)` definer
                // entry too. Same-resource-name across different
                // interfaces is permitted by the Component Model.
                let keys_to_remove: Vec<_> = defines_cache
                    .keys()
                    .filter(|(idx, iface, r)| *idx == *from_comp && iface == ri && r == rn)
                    .cloned()
                    .collect();
                for key in keys_to_remove {
                    defines_cache.remove(&key);
                    if let Some(entry) = definer_cache.get_mut(&(key.1.clone(), key.2.clone()))
                        && *entry == Some(*from_comp)
                    {
                        *entry = None;
                    }
                }
            }
        }

        ResourceGraph {
            graph,
            comp_nodes,
            resource_nodes,
            defines_cache,
            definer_cache,
        }
    }

    /// Does the given component define (own) the resource?
    /// A defining component has canonical ResourceRep entries.
    /// Tries both bare and `[export]`-prefixed interface name variants.
    pub fn defines_resource(&self, comp_idx: usize, interface: &str, resource_name: &str) -> bool {
        let rn = resource_name.to_string();
        // Try exact match first
        if let Some(&v) = self
            .defines_cache
            .get(&(comp_idx, interface.to_string(), rn.clone()))
        {
            return v;
        }
        // Try with [export] prefix added
        if let Some(&v) =
            self.defines_cache
                .get(&(comp_idx, format!("[export]{}", interface), rn.clone()))
        {
            return v;
        }
        // Try with [export] prefix stripped
        if let Some(stripped) = interface.strip_prefix("[export]")
            && let Some(&v) = self
                .defines_cache
                .get(&(comp_idx, stripped.to_string(), rn))
        {
            return v;
        }
        false
    }

    /// Which component defines the given resource? Returns None if unknown.
    /// Tries both bare and `[export]`-prefixed interface name variants.
    pub fn resource_definer(&self, interface: &str, resource_name: &str) -> Option<usize> {
        let rn = resource_name.to_string();
        if let Some(&v) = self.definer_cache.get(&(interface.to_string(), rn.clone())) {
            return v;
        }
        if let Some(&v) = self
            .definer_cache
            .get(&(format!("[export]{}", interface), rn.clone()))
        {
            return v;
        }
        if let Some(stripped) = interface.strip_prefix("[export]")
            && let Some(&v) = self.definer_cache.get(&(stripped.to_string(), rn))
        {
            return v;
        }
        None
    }

    /// Is the component a re-exporter for the resource?
    /// A re-exporter has ResourceNew but not ResourceRep.
    pub fn is_reexporter(&self, comp_idx: usize, interface: &str, resource_name: &str) -> bool {
        if let Some(&comp_node) = self.comp_nodes.get(&comp_idx) {
            let key = (interface.to_string(), resource_name.to_string());
            if let Some(&resource_node) = self.resource_nodes.get(&key) {
                return self
                    .graph
                    .edges_directed(resource_node, petgraph::Direction::Incoming)
                    .any(|e| {
                        e.source() == comp_node && matches!(e.weight(), GraphEdge::Reexports)
                    });
            }
        }
        false
    }

    /// Does the given component participate in handling this resource at all?
    pub fn uses_resource(&self, comp_idx: usize, interface: &str, resource_name: &str) -> bool {
        if let Some(&comp_node) = self.comp_nodes.get(&comp_idx) {
            let key = (interface.to_string(), resource_name.to_string());
            if let Some(&resource_node) = self.resource_nodes.get(&key) {
                return self
                    .graph
                    .edges_directed(resource_node, petgraph::Direction::Incoming)
                    .any(|e| e.source() == comp_node);
            }
        }
        false
    }

    /// Debug: dump the graph structure.
    pub fn dump(&self) {
        for node_idx in self.graph.node_indices() {
            let node = &self.graph[node_idx];
            let edges: Vec<_> = self
                .graph
                .edges_directed(node_idx, petgraph::Direction::Outgoing)
                .map(|e| format!("{:?} -> {:?}", e.weight(), self.graph[e.target()]))
                .collect();
            if !edges.is_empty() {
                eprintln!("  {:?}: {}", node, edges.join(", "));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{CanonicalEntry, CoreModule, ImportKind, ModuleImport, ParsedComponent};

    fn empty_pc() -> ParsedComponent {
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

    fn empty_cm() -> CoreModule {
        CoreModule {
            index: 0,
            bytes: vec![],
            types: vec![],
            imports: vec![],
            exports: vec![],
            functions: vec![],
            memories: vec![],
            tables: vec![],
            globals: vec![],
            start: None,
            data_count: None,
            element_count: 0,
            custom_sections: vec![],
            code_section_range: None,
            global_section_range: None,
            element_section_range: None,
            data_section_range: None,
        }
    }

    fn imp(module: &str, name: &str) -> ModuleImport {
        ModuleImport {
            module: module.into(),
            name: name.into(),
            kind: ImportKind::Function(0),
        }
    }

    /// LS-A-17 F1 — definer purge ignores interface name.
    ///
    /// Component 0 imports a resource named "data" from `shared:lib/storage`.
    /// Component 1 ALSO has a resource named "data" — but in interface
    /// `ns:other/cache`, completely unrelated. Prior to the fix, the
    /// cleanup loop filtered the defines_cache by `(comp == 1) &&
    /// (resource_name == "data")` ignoring iface, purging component 1's
    /// legitimate definer entry for (ns:other/cache, data).
    #[test]
    fn ls_a_17_definer_survives_unrelated_import_with_same_resource_name() {
        let mut c0 = empty_pc();
        c0.canonical_functions
            .push(CanonicalEntry::ResourceRep { resource: 0 });
        let mut m0 = empty_cm();
        m0.imports
            .push(imp("shared:lib/storage", "[resource-rep]data"));
        c0.core_modules.push(m0);

        let mut c1 = empty_pc();
        c1.canonical_functions
            .push(CanonicalEntry::ResourceRep { resource: 0 });
        let mut m1 = empty_cm();
        m1.imports.push(imp("ns:other/cache", "[resource-rep]data"));
        c1.core_modules.push(m1);

        let mut resolved = HashMap::new();
        resolved.insert(
            (1usize, "shared:lib/storage".to_string()),
            (0usize, "shared:lib/storage".to_string()),
        );

        let rg = ResourceGraph::build(&resolved, &[c0, c1]);
        assert!(
            rg.defines_resource(1, "ns:other/cache", "data"),
            "comp 1's definer entry for ns:other/cache#data was purged \
             by an unrelated import that shares the resource name"
        );
        assert_eq!(rg.resource_definer("ns:other/cache", "data"), Some(1));
    }

    /// LS-A-17 F2 — terminal exporter pass uses an over-broad
    /// `to_also_imports_resource` check.
    ///
    /// Component 0 imports two unrelated resource interfaces:
    /// `svc:bridge/api` and `wasi:io/poll`. Component 1 is the definer
    /// of `svc:bridge/api#thing`. Prior to the fix, the terminal
    /// exporter pass marked comp 1 as NOT terminal because comp 0
    /// imported "any resource interface" — including the unrelated
    /// wasi:io/poll. The fix scopes the check to the specific iface
    /// being attributed.
    #[test]
    fn ls_a_17_terminal_definer_with_unrelated_resource_import() {
        let mut c0 = empty_pc();
        let mut m0 = empty_cm();
        m0.imports
            .push(imp("svc:bridge/api", "[resource-drop]thing"));
        m0.imports
            .push(imp("wasi:io/poll", "[resource-drop]pollable"));
        c0.core_modules.push(m0);

        // Comp 1 — terminal definer for svc:bridge/api#thing, but with
        // empty canonical_functions (post-flatten case).
        let c1 = empty_pc();

        let mut resolved = HashMap::new();
        resolved.insert(
            (0usize, "svc:bridge/api".to_string()),
            (1usize, "svc:bridge/api".to_string()),
        );
        // External host import — also produces a resource_node from
        // c0's [resource-drop] but should not affect comp 1's
        // attribution.
        resolved.insert(
            (0usize, "wasi:io/poll".to_string()),
            (usize::MAX, "wasi:io/poll".to_string()),
        );

        let rg = ResourceGraph::build(&resolved, &[c0, c1]);
        assert_eq!(
            rg.resource_definer("svc:bridge/api", "thing"),
            Some(1),
            "terminal-exporter pass mis-classified comp 1 as a re-exporter \
             because comp 0 imports an unrelated resource interface"
        );
    }

    /// LS-A-18 — [resource-drop] only handled when !has_any_canon.
    ///
    /// A re-exporter (has ResourceNew) that ALSO drops a foreign
    /// resource Y must register Y in the graph. Prior to the fix, the
    /// first pass stripped only [resource-rep] and [resource-new]; the
    /// second pass that handles [resource-drop] only ran when
    /// `!has_any_canon`, so a re-exporter dropping a foreign resource
    /// had its drop call invisible to the graph.
    #[test]
    fn ls_a_18_drop_on_foreign_resource_registers_node_for_reexporter() {
        let mut c0 = empty_pc();
        c0.canonical_functions
            .push(CanonicalEntry::ResourceNew { resource: 0 });
        let mut m = empty_cm();
        m.imports.push(imp("iface:a/x", "[resource-new]thingX"));
        m.imports.push(imp("iface:b/y", "[resource-drop]thingY"));
        c0.core_modules.push(m);

        let rg = ResourceGraph::build(&HashMap::new(), &[c0]);
        assert!(
            rg.uses_resource(0, "iface:b/y", "thingY"),
            "re-exporter that drops a foreign resource must register \
             a graph node for that resource (LS-A-18); otherwise the \
             merger routes the drop to the wrong handle table"
        );
    }
}
