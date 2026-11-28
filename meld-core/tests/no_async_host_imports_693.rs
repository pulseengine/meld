//! #693 / SR-142: meld adds no `pulseengine:async` imports to a fused module.
//!
//! Until #693, fusing a component with P3 stream/future canonical built-ins
//! appended one `pulseengine:async` import per built-in kind (`stream_new`,
//! `stream_write`, ...). No fused code called them: on simple-call-import the
//! six imports had zero `call` sites and appeared in no element segment. Every
//! host still had to bind them. ADR-10 section 6 retires that ABI.
//!
//! None of these inputs imports `pulseengine:async` itself, so any such import
//! in the output was added by meld.

use meld_core::p3_async::HOST_INTRINSIC_MODULE;
use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use std::path::{Path, PathBuf};

fn repo(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join(rel)
}

/// Every function import of `bytes` under `module`.
fn imports_under(bytes: &[u8], module: &str) -> Vec<String> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let Ok(wasmparser::Payload::ImportSection(reader)) = payload {
            for imp in reader.into_imports().flatten() {
                if imp.module == module {
                    out.push(imp.name.to_string());
                }
            }
        }
    }
    out
}

fn fuse(bytes: &[u8]) -> meld_core::Result<Vec<u8>> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..FuserConfig::default()
    });
    fuser.add_component(bytes)?;
    fuser.fuse()
}

/// The corpus: the #662 stream fixtures and every wit-bindgen runtime fixture.
fn corpus() -> Vec<(String, Vec<u8>)> {
    let mut out = Vec::new();
    for name in [
        "stream_write_via_shim_wt1263.wat",
        "stream_write_via_shim.wat",
    ] {
        let path = repo(&format!("meld-core/tests/fixtures/issue_662/{name}"));
        out.push((
            name.to_string(),
            wat::parse_file(&path).expect("fixture parses"),
        ));
    }
    let dir = repo("tests/wit_bindgen/fixtures");
    let mut entries: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("{} must be tracked (SR-85): {e}", dir.display()))
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "wasm"))
        .collect();
    entries.sort();
    for path in entries {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        out.push((name, std::fs::read(&path).expect("read fixture")));
    }
    out
}

// rivet: verifies SWV-152
#[test]
fn no_fused_corpus_module_imports_pulseengine_async() {
    let mut fused_count = 0;
    let mut with_p3 = Vec::new();
    let mut offenders = Vec::new();
    for (name, bytes) in corpus() {
        assert!(
            imports_under(&bytes, HOST_INTRINSIC_MODULE).is_empty(),
            "{name}: the input itself imports {HOST_INTRINSIC_MODULE}"
        );
        // Some fixtures are refused on purpose (see EXPECTED_REFUSALS in
        // wit_bindgen_runtime.rs); only fused outputs say anything here.
        let Ok(fused) = fuse(&bytes) else { continue };
        fused_count += 1;
        let names = imports_under(&fused, HOST_INTRINSIC_MODULE);
        if !names.is_empty() {
            offenders.push(format!("{name}: {names:?}"));
        }
        if name.contains("stream") || name.contains("future") || name == "simple-call-import.wasm" {
            with_p3.push(name);
        }
    }
    // The fixtures that had the dead imports before #693 must be in the set
    // that fused, or the assertion below proves nothing about them.
    for must in [
        "stream_write_via_shim_wt1263.wat",
        "simple-call-import.wasm",
    ] {
        assert!(
            with_p3.iter().any(|n| n == must),
            "{must} must fuse for this test to cover the #693 case; fused P3 inputs: {with_p3:?}"
        );
    }
    assert!(fused_count >= 40, "only {fused_count} corpus inputs fused");
    assert!(
        offenders.is_empty(),
        "{} of {fused_count} fused outputs import {HOST_INTRINSIC_MODULE}:\n{}",
        offenders.len(),
        offenders.join("\n")
    );
}
