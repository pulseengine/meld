//! Merger idempotence fuzz target.
//!
//! Property: For any byte input that successfully parses+resolves, running
//! `Merger::merge(...)` twice on the same `(components, graph)` must produce
//! structurally identical merged modules. This is a determinism / purity
//! property — the merger is supposed to be a pure function of its inputs.
//!
//! Failure modes this catches:
//!   * HashMap ordering leaks (non-determinism)
//!   * Hidden interior mutability that flips state across calls
//!   * Allocation-order-dependent behavior in resource routing
//!
//! "merge(merge(x)) == merge(x)" in the literal sense is awkward because the
//! merger output is a flat core module, not a component graph. The
//! determinism property below is the strongest idempotence we can express
//! without re-encoding+re-parsing through the full pipeline (which is
//! covered by `fuzz_fusion_roundtrip`).
#![no_main]

use libfuzzer_sys::fuzz_target;
use meld_core::{ComponentParser, MemoryStrategy, Resolver};
use meld_core::merger::Merger;

fuzz_target!(|data: &[u8]| {
    // Phase 1: parse. Discard parse failures — they are exercised by
    // `fuzz_parse_component`.
    let parser = ComponentParser::without_validation();
    let parsed = match parser.parse(data) {
        Ok(p) => p,
        Err(_) => return,
    };

    let components = vec![parsed];

    // Phase 2: resolve. Discard resolver failures — exercised by
    // `fuzz_resolver_terminates`.
    let resolver = Resolver::with_strategy(MemoryStrategy::MultiMemory);
    let graph = match resolver.resolve(&components) {
        Ok(g) => g,
        Err(_) => return,
    };

    // Phase 3: merge twice. Both invocations MUST succeed identically or
    // both fail. Diverging outcomes break determinism.
    let merger_a = Merger::new(MemoryStrategy::MultiMemory, false);
    let merger_b = Merger::new(MemoryStrategy::MultiMemory, false);

    let result_a = merger_a.merge(&components, &graph);
    let result_b = merger_b.merge(&components, &graph);

    match (result_a, result_b) {
        (Ok(a), Ok(b)) => {
            // Compare structural fingerprints. Full PartialEq is not
            // implemented on MergedModule, so check the load-bearing
            // counts/maps. Any mismatch indicates non-determinism.
            assert_eq!(a.types.len(), b.types.len(), "type count diverged");
            assert_eq!(a.imports.len(), b.imports.len(), "import count diverged");
            assert_eq!(
                a.functions.len(),
                b.functions.len(),
                "function count diverged"
            );
            assert_eq!(a.tables.len(), b.tables.len(), "table count diverged");
            assert_eq!(a.memories.len(), b.memories.len(), "memory count diverged");
            assert_eq!(a.globals.len(), b.globals.len(), "global count diverged");
            assert_eq!(a.exports.len(), b.exports.len(), "export count diverged");
            assert_eq!(
                a.start_function, b.start_function,
                "start function diverged"
            );
            assert_eq!(
                a.elements.len(),
                b.elements.len(),
                "element segment count diverged"
            );
            assert_eq!(
                a.data_segments.len(),
                b.data_segments.len(),
                "data segment count diverged"
            );
            assert_eq!(
                a.function_index_map, b.function_index_map,
                "function index map diverged"
            );
            assert_eq!(
                a.memory_index_map, b.memory_index_map,
                "memory index map diverged"
            );
            assert_eq!(
                a.table_index_map, b.table_index_map,
                "table index map diverged"
            );
            assert_eq!(
                a.global_index_map, b.global_index_map,
                "global index map diverged"
            );
            assert_eq!(
                a.type_index_map, b.type_index_map,
                "type index map diverged"
            );
            assert_eq!(
                a.import_counts.func, b.import_counts.func,
                "func import count diverged"
            );
            assert_eq!(
                a.import_counts.memory, b.import_counts.memory,
                "memory import count diverged"
            );
            assert_eq!(
                a.import_counts.table, b.import_counts.table,
                "table import count diverged"
            );
            assert_eq!(
                a.import_counts.global, b.import_counts.global,
                "global import count diverged"
            );
        }
        (Err(_), Err(_)) => {
            // Both failed — acceptable, treat as deterministic refusal.
        }
        (Ok(_), Err(_)) | (Err(_), Ok(_)) => {
            panic!("merger non-deterministic: succeeded on one run, failed on the other");
        }
    }
});
