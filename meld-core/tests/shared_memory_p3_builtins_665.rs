//! #665: under `--memory shared`, the per-instance P3 built-ins of different
//! components were merged into one import. `run1` and `run2` each create a
//! stream (of `u32` and of `string`) and a waitable set; fused shared, the
//! output had one `[stream-new-0]get` and one `[waitable-set-new]` import,
//! and a host serving them could not tell which instance or element type a
//! call is for. Exit 0, output valid. meld now refuses two or more P3
//! components under shared; `--memory multi`
//! keeps one import per component and is the control.

use std::path::Path;

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn fixture(name: &str) -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/issue_665")
        .join(name);
    wat::parse_file(&path).unwrap_or_else(|e| panic!("tracked fixture {name}: {e}"))
}

fn fuse(memory_strategy: MemoryStrategy, address_rebasing: bool) -> meld_core::Result<Vec<u8>> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy,
        address_rebasing,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component(&fixture("run1.wat"))?;
    fuser.add_component(&fixture("run2.wat"))?;
    fuser.fuse()
}

fn func_imports(fused: &[u8]) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(fused) {
        if let Ok(wasmparser::Payload::ImportSection(reader)) = payload {
            for import in reader.into_imports() {
                let import = import.expect("import");
                if matches!(import.ty, wasmparser::TypeRef::Func(_)) {
                    out.push((import.module.to_string(), import.name.to_string()));
                }
            }
        }
    }
    out
}

#[test]
fn shared_memory_refuses_p3_builtins() {
    for rebase in [false, true] {
        let err = fuse(MemoryStrategy::SharedMemory, rebase)
            .expect_err("merging per-instance built-ins: meld must refuse");
        assert!(err.to_string().contains("#665"), "rebase={rebase}: {err}");
    }
}

#[test]
fn multi_memory_keeps_one_builtin_import_per_component() {
    let fused = fuse(MemoryStrategy::MultiMemory, false).expect("multi fuses");
    let imports = func_imports(&fused);
    let count = |field: &str| imports.iter().filter(|(_, f)| f.starts_with(field)).count();
    assert_eq!(count("[stream-new-0]get"), 2, "{imports:?}");
    assert_eq!(count("[waitable-set-new]"), 2, "{imports:?}");
}

/// One component has nothing to merge its built-ins with: it still fuses
/// under shared, as a single threaded component does under ADR-9.
#[test]
fn shared_memory_single_p3_component_still_fuses() {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component(&fixture("run1.wat")).expect("parse");
    fuser.fuse().expect("one P3 component fuses under shared");
}
