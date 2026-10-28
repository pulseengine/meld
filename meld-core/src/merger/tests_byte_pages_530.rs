//! SR-107 (#530): merger-level refusals for byte-sized memories.

use super::*;
use crate::MemoryPageSize;
use crate::resolver::DependencyGraph;

// rivet: verifies SWV-119
#[test]
fn byte_pages_are_refused_with_resource_reexporters() {
    // A re-exporter's handle table is allocated in 64 KiB pages of the memory
    // (`allocate_handle_tables`), the wrong unit on a (pagesize 1) memory.
    let graph = DependencyGraph {
        instantiation_order: Vec::new(),
        resolved_imports: std::collections::HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: vec![(0, "iface".to_string(), "res".to_string())],
        unresolved_imports: Vec::new(),
    };
    let merge = |page: MemoryPageSize| {
        Merger::new(MemoryStrategy::SharedMemory, true)
            .with_pack_rebase(true)
            .with_memory_page_size(page)
            .merge(&[], &graph)
    };
    let err = merge(MemoryPageSize::Byte).unwrap_err().to_string();
    assert!(err.contains("resource re-exporters"), "{err}");
    // Control: the same merge with page-sized memories is not refused for that
    // reason (it has no components, so it merges to an empty module).
    merge(MemoryPageSize::Page).expect("control: page-sized merge of no components");
}
