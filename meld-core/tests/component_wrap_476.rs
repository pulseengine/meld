//! #476: `--component` on a component that `use`s types from an imported
//! interface. wit-bindgen emits each such type as an `alias export <instance>`
//! of the imported interface; the wrapper failed with "cannot find source type
//! definition". Its lifts also lacked the `memory`/`realloc` a spilled
//! parameter list (> 16 flat values) or a return area needs.
//!
//! Validation is not the oracle here: the wrapped component must COMPUTE the
//! same thing. Every exported function of the original and of the fused
//! component is called on wasmtime, in the same order, with the same
//! generated arguments, and every result must match.

use std::path::Path;

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasmtime::component::Component;
use wasmtime::{Config, Engine};

#[path = "support/component_transcript.rs"]
mod support;
use support::transcript;

fn fixture(name: &str) -> Vec<u8> {
    std::fs::read(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/issue_461")
            .join(name),
    )
    .expect("fixture")
}

fn fuse_component(input: &[u8], strategy: MemoryStrategy) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: strategy,
        output_format: OutputFormat::Component,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component(input).unwrap();
    fuser.fuse().expect("--component fuses (#476)")
}

// rivet: verifies SR-123
// rivet: verifies SWV-137
#[test]
fn component_output_using_imported_interface_types_computes_the_same() {
    for name in [
        "falcon_cascade_estimator_cm.wasm",
        "falcon_cascade_control_cm.wasm",
    ] {
        let original = fixture(name);
        let expected = transcript(&original);
        // Potency: the transcript must exercise spilled params and records,
        // or a match would say little.
        assert!(
            expected.len() >= 2,
            "{name}: only {} calls in the transcript",
            expected.len()
        );
        assert!(
            expected.iter().any(|l| l.contains("Record(")),
            "{name}: no record crossed the boundary"
        );
        let fused = fuse_component(&original, MemoryStrategy::MultiMemory);
        assert_eq!(
            transcript(&fused),
            expected,
            "{name}: fused component differs"
        );
    }
}

// rivet: verifies SR-123
#[test]
fn split_with_imported_interfaces_wraps_and_validates() {
    // The split also imports two function interfaces, which the stub linker
    // cannot answer meaningfully, so this checks wrapping and validation only.
    let fused = fuse_component(
        &fixture("falcon_cascade_split_cm.wasm"),
        MemoryStrategy::MultiMemory,
    );
    let mut config = Config::new();
    config.wasm_component_model(true);
    config.wasm_multi_memory(true);
    Component::new(&Engine::new(&config).unwrap(), &fused).expect("wrapped split loads");
}
