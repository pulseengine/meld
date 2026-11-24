//! #552: meld bound a P3 built-in by the core module's own import name, not
//! by the canonical function the instantiation supplies. In
//! `swapped_builtin_names` the module's `[waitable-set-drop]` import is wired
//! to `stream.drop-readable` and its `[stream-drop-readable-0]x` import to
//! `waitable-set.drop`. Fused, both calls went to the single import
//! `$root::[waitable-set-drop]`, so one built-in ran with the other's
//! semantics, at exit 0. meld now refuses a field name that names a
//! different built-in than the one wired to it.
//!
//! `matching_builtin_names` is the control: names and built-ins agree, and
//! the fused module keeps two distinct imports, one per call.

use std::path::Path;

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn fixture(name: &str) -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/issue_552")
        .join(name);
    wat::parse_file(&path).unwrap_or_else(|e| panic!("tracked fixture {name}: {e}"))
}

fn fuse(bytes: &[u8]) -> meld_core::Result<Vec<u8>> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component(bytes)?;
    fuser.fuse()
}

fn root_imports(fused: &[u8]) -> Vec<String> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(fused) {
        if let Ok(wasmparser::Payload::ImportSection(reader)) = payload {
            for import in reader.into_imports() {
                let import = import.expect("import");
                if import.module == "$root" {
                    out.push(import.name.to_string());
                }
            }
        }
    }
    out
}

#[test]
fn builtin_wired_under_another_builtins_name_is_refused() {
    let err = fuse(&fixture("swapped_builtin_names.wat"))
        .expect_err("two built-ins would reach one import: meld must refuse");
    assert!(err.to_string().contains("#552"), "unexpected error: {err}");
}

#[test]
fn matching_builtin_names_keep_one_import_each() {
    let fused = fuse(&fixture("matching_builtin_names.wat")).expect("names agree");
    let mut imports = root_imports(&fused);
    imports.sort();
    assert_eq!(
        imports,
        ["[stream-drop-readable-0]x", "[waitable-set-drop]"],
        "one import per built-in"
    );
}
