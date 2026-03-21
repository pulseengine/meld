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
                for module in &comp.core_modules {
                    for imp in &module.imports {
                        if let crate::parser::ImportKind::Function(_) = &imp.kind {
                            let (prefix, is_rep) =
                                if let Some(rn) = imp.name.strip_prefix("[resource-rep]") {
                                    (rn, true)
                                } else if let Some(rn) = imp.name.strip_prefix("[resource-new]") {
                                    (rn, false)
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
                                if is_rep && has_rep {
                                    // Component has canonical ResourceRep AND imports [resource-rep]
                                    // → it defines this resource
                                    graph.add_edge(comp_node, resource_node, GraphEdge::Defines);
                                } else if !has_rep && has_new {
                                    // Only ResourceNew, no ResourceRep → re-exporter
                                    graph.add_edge(comp_node, resource_node, GraphEdge::Reexports);
                                } else {
                                    // Has imports but no canonical entries → pure consumer
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

        // First pass: check Defines edges
        for ((iface, rn), &resource_node) in &resource_nodes {
            let mut definer = None;
            for edge in graph.edges_directed(resource_node, petgraph::Direction::Incoming) {
                if matches!(edge.weight(), GraphEdge::Defines)
                    && let GraphNode::Component(idx) = graph[edge.source()]
                {
                    defines_cache.insert((idx, iface.clone(), rn.clone()), true);
                    definer = Some(idx);
                }
            }
            definer_cache.insert((iface.clone(), rn.clone()), definer);
        }

        // Second pass: use ResolvesTo edges for definer detection.
        // For each interface, find the terminal component — the one that
        // exports but doesn't import (no outgoing ResolvesTo for this interface).
        // This handles cases where canonical_functions is empty after flattening.
        for ((_from_comp, import_name), (to_comp, _)) in resolved_imports {
            let to_also_imports = resolved_imports.contains_key(&(*to_comp, import_name.clone()));
            if !to_also_imports {
                for (iface, rn) in resource_nodes.keys() {
                    let iface_matches = iface == import_name
                        || iface.strip_prefix("[export]") == Some(import_name.as_str());
                    if iface_matches {
                        defines_cache
                            .entry((*to_comp, iface.clone(), rn.clone()))
                            .or_insert(true);
                        definer_cache
                            .entry((iface.clone(), rn.clone()))
                            .or_insert(Some(*to_comp));
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
    pub fn defines_resource(&self, comp_idx: usize, interface: &str, resource_name: &str) -> bool {
        self.defines_cache
            .get(&(comp_idx, interface.to_string(), resource_name.to_string()))
            .copied()
            .unwrap_or(false)
    }

    /// Which component defines the given resource? Returns None if unknown.
    pub fn resource_definer(&self, interface: &str, resource_name: &str) -> Option<usize> {
        self.definer_cache
            .get(&(interface.to_string(), resource_name.to_string()))
            .copied()
            .flatten()
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
