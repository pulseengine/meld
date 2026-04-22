//! Regression test for issue #97.
//!
//! file_ops.wasm has two component imports both named `now` (one from
//! `wasi:clocks/wall-clock@0.2.0`, one from `wasi:clocks/monotonic-clock@0.2.0`).
//! The merger's intra-component resolution lookup used to match by
//! `import.name` only and would route both `now` callers to whichever module
//! resolution happened to be in the list, producing a fused module that calls
//! a void-returning shim where an i64 was expected.
//!
//! This test fuses the fixture and runs `wasmparser::Validator` over the
//! result, ensuring the bug stays fixed.

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};

const FIXTURE: &str = "../tests/issue_97/file_ops.wasm";

fn fixture_exists() -> bool {
    if std::path::Path::new(FIXTURE).is_file() {
        true
    } else {
        eprintln!("skipping: fixture not found at {FIXTURE}");
        false
    }
}

#[test]
fn file_ops_fuses_and_validates() {
    if !fixture_exists() {
        return;
    }

    let bytes = std::fs::read(FIXTURE).expect("read fixture");
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        output_format: OutputFormat::CoreModule,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser.add_component(&bytes).expect("add_component");
    let fused = fuser.fuse().expect("fuse");

    // Validate using a wasm validator that supports multi-memory + the same
    // feature set the meld CLI enables for --validate.
    let mut features = wasmparser::WasmFeatures::default();
    features.set(wasmparser::WasmFeatures::MULTI_MEMORY, true);
    let mut validator = wasmparser::Validator::new_with_features(features);
    validator
        .validate_all(&fused)
        .expect("fused module must validate");
}
