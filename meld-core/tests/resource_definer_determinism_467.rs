//! #467: fusing a component in which two inputs both qualify as a resource's
//! definer must produce the same bytes every time.
//!
//! `resource-import-and-export.wasm` has two components (0 and 3) that both
//! carry a `ResourceRep` for `test:resource-import-and-export/test#thing`.
//! Component 3 also imports that interface, so it is a re-exporter, not the
//! definer; component 0 is. `ResourceGraph::build` used to record whichever
//! candidate its `HashMap` walk visited first, so the answer (and with it
//! whether component 0 got a handle table, the function indices, a global and
//! the memory size) changed from process to process.
//!
//! `HashMap` seeds are drawn per map, so repeating the fusion in ONE process
//! is enough to see the variation; no subprocess is needed.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use std::collections::BTreeSet;
use std::path::Path;

/// Each run also asserts the outcome (component 0 gets its handle table),
/// which the unfixed code got wrong on about half of all runs, so a few runs
/// suffice here; the order-independence itself is exercised 200 times by the
/// unit test `issue_467_definer_is_the_terminal_candidate_not_the_first_visited`.
const RUNS: usize = 4;

/// Number of `$ht_new_*` exports: one per handle table meld generated.
fn handle_table_count(fused: &[u8]) -> usize {
    let mut n = 0;
    for payload in wasmparser::Parser::new(0).parse_all(fused) {
        if let Ok(wasmparser::Payload::ExportSection(reader)) = payload {
            for export in reader.into_iter().flatten() {
                if export.name.starts_with("$ht_new_") {
                    n += 1;
                }
            }
        }
    }
    n
}

fn fuse_once(bytes: &[u8]) -> Vec<u8> {
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        // The comparison is about FUSION output. Under the optional
        // `attestation` (wsc) feature the attestation section carries
        // `HashMap` fields whose order meld cannot control (a known,
        // documented limitation; see `safety_profile_386.rs`), which would
        // make this test fail for an unrelated reason. Dropping the section
        // keeps the test feature-independent.
        attestation: false,
        reproducible: true,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(bytes, Some("resource-import-and-export"))
        .expect("add component");
    fuser.fuse().expect("fuse")
}

#[test]
fn two_candidate_definers_fuse_to_identical_bytes() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../tests/wit_bindgen/fixtures/resource-import-and-export.wasm");
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("fixture {}: {e}", path.display()));

    let mut distinct: BTreeSet<Vec<u8>> = BTreeSet::new();
    for run in 0..RUNS {
        let fused = fuse_once(&bytes);
        // Component 0 (the definer) and component 3 (the re-exporter) each
        // get a handle table. Picking the re-exporter as definer and then
        // discarding it left component 0 without one.
        assert_eq!(
            handle_table_count(&fused),
            2,
            "run {run}: the definer must get its own handle table (#467)"
        );
        distinct.insert(fused);
    }
    assert_eq!(
        distinct.len(),
        1,
        "{RUNS} fusions of the same input produced {} distinct outputs (#467)",
        distinct.len()
    );
}
