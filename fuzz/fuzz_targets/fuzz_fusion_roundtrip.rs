//! Fusion roundtrip fuzz target.
//!
//! Property: `fuse(parse(bytes))` outputs something parseable.
//! Concretely: if `Fuser` accepts an input and produces output bytes,
//! those bytes MUST be valid WebAssembly (either a core module or a
//! P2 component depending on `OutputFormat`). A "successful but malformed"
//! fusion output is a serious bug — downstream consumers (loom, wasmtime,
//! etc.) will panic or reject.
//!
//! We accept any failure mode along the way (parse error, resolve error,
//! merge error, encode error) — those are exercised by the other targets.
//! What we cannot accept is `Fuser::fuse` returning `Ok(bytes)` where
//! `wasmparser::Validator` rejects `bytes`.
#![no_main]

use libfuzzer_sys::fuzz_target;
use meld_core::{Fuser, FuserConfig};

fuzz_target!(|data: &[u8]| {
    // Disable attestation: it adds a custom section but does not affect the
    // structural validity of the output, and skipping it makes each fuzz
    // iteration faster.
    let config = FuserConfig {
        attestation: false,
        ..FuserConfig::default()
    };
    let mut fuser = Fuser::new(config);

    // Add the fuzz input as a single component. Failure here is fine.
    if fuser.add_component_named(data, Some("fuzz")).is_err() {
        return;
    }

    // Fuse. Any error path is acceptable.
    let fused = match fuser.fuse() {
        Ok(bytes) => bytes,
        Err(_) => return,
    };

    // The output is a core module by default. Validate it with wasmparser.
    // If validation fails, we have produced malformed wasm from a "successful"
    // fusion — that is a bug.
    let mut validator = wasmparser::Validator::new_with_features(
        wasmparser::WasmFeatures::default()
            | wasmparser::WasmFeatures::CM_FIXED_LENGTH_LISTS
            | wasmparser::WasmFeatures::CM_ASYNC,
    );
    if let Err(e) = validator.validate_all(&fused) {
        panic!(
            "fusion produced invalid wasm ({} bytes): {}",
            fused.len(),
            e
        );
    }
});
