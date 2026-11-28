//! #711 / SR-144: a fused module records each input by file name, never by
//! the directory it was read from.
//!
//! meld-cli passes the command-line path as the component name, and without
//! `--reproducible` that name went into the attestation
//! (`inputs[].artifact.name`) and `component-provenance` (`component_id`). An
//! absolute input path put the builder's home or volume directory into every
//! fused module.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn fixture(rel: &str) -> Vec<u8> {
    let path = format!("{}/../{}", env!("CARGO_MANIFEST_DIR"), rel);
    std::fs::read(&path).unwrap_or_else(|e| panic!("tracked fixture {path} missing: {e}"))
}

fn contains(haystack: &[u8], needle: &str) -> bool {
    haystack
        .windows(needle.len())
        .any(|w| w == needle.as_bytes())
}

fn fuse_named(names: [&str; 2]) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: true,
        component_provenance: true,
        reproducible: false,
        ..Default::default()
    });
    let inputs = [
        fixture("tests/wit_bindgen/fixtures/compose/provider.wasm"),
        fixture("tests/wit_bindgen/fixtures/compose/consumer.wasm"),
    ];
    for (bytes, name) in inputs.iter().zip(names) {
        fuser.add_component_named(bytes, Some(name)).expect("add");
    }
    fuser.fuse().expect("fusion")
}

// rivet: verifies SWV-154
#[test]
fn fused_module_records_input_file_names_not_directories() {
    // A POSIX-style and a Windows-style path, so the result is the same
    // whichever host meld runs on.
    let fused = fuse_named([
        "/private-build-root/nested/dir/provider.wasm",
        r"C:\private-build-root\nested\consumer.wasm",
    ]);
    for dir in ["private-build-root", "nested"] {
        assert!(
            !contains(&fused, dir),
            "the fused module carries the directory component {dir:?}"
        );
    }
    // The file names are still recorded, so the inputs stay identifiable by
    // name as well as by hash.
    assert!(contains(&fused, "provider.wasm"));
    assert!(contains(&fused, "consumer.wasm"));
}

/// Control: a bare file name is recorded unchanged.
// rivet: verifies SWV-154
#[test]
fn a_bare_file_name_is_recorded_unchanged() {
    let fused = fuse_named(["provider.wasm", "consumer.wasm"]);
    assert!(contains(&fused, "provider.wasm"));
    assert!(contains(&fused, "consumer.wasm"));
}
