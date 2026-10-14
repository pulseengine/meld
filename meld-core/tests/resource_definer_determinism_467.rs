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

/// The unfixed code gives two outcomes at roughly even odds, so a run of this
/// length passes by luck with probability about 2^-(RUNS-1).
const RUNS: usize = 20;

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
    for _ in 0..RUNS {
        distinct.insert(fuse_once(&bytes));
    }
    assert_eq!(
        distinct.len(),
        1,
        "{RUNS} fusions of the same input produced {} distinct outputs (#467)",
        distinct.len()
    );
}
