//! #547 / ADR-9, driven through the real binary: a P3 cooperative-thread
//! component fuses with the DEFAULT validation (which must accept the
//! threading built-ins), the import map names every built-in as a `p3-builtin`
//! and ties `thread.new-indirect` to the exported `__meld_thread_table`, and the
//! default attestation records the table.

use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture() -> PathBuf {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../tests/p3/coop_threads_547/t1_new_resume.wasm");
    // #405: a missing fixture fails; it must not pass by asserting over nothing.
    assert!(
        p.is_file(),
        "fixture missing at {} -- it must be tracked in git (.gitignore exempts tests/p3)",
        p.display()
    );
    p
}

fn exported_table(core: &[u8], name: &str) -> Option<u32> {
    for payload in wasmparser::Parser::new(0).parse_all(core) {
        if let Ok(wasmparser::Payload::ExportSection(r)) = payload {
            for e in r.into_iter().flatten() {
                if e.name == name && e.kind == wasmparser::ExternalKind::Table {
                    return Some(e.index);
                }
            }
        }
    }
    None
}

fn attestation_json(core: &[u8]) -> serde_json::Value {
    for payload in wasmparser::Parser::new(0).parse_all(core) {
        if let Ok(wasmparser::Payload::CustomSection(c)) = payload
            && c.name() == "wsc.transformation.attestation"
        {
            return serde_json::from_slice(c.data()).expect("attestation is JSON");
        }
    }
    panic!("no attestation section");
}

// rivet: verifies SWV-122
#[test]
fn cli_fuses_a_cooperative_thread_component_and_records_the_table() {
    let dir = std::env::temp_dir();
    let out = dir.join(format!("meld-547-{}.wasm", std::process::id()));
    let map = dir.join(format!("meld-547-{}.json", std::process::id()));
    let _ = std::fs::remove_file(&out);
    let run = Command::new(env!("CARGO_BIN_EXE_meld"))
        .arg("fuse")
        .arg(fixture())
        .args(["--memory", "multi", "-o"])
        .arg(&out)
        .arg("--emit-import-map")
        .arg(&map)
        .output()
        .expect("meld binary runs");
    assert!(
        run.status.success(),
        "must fuse and pass the default validation: {}",
        String::from_utf8_lossy(&run.stderr)
    );

    let core = std::fs::read(&out).expect("output written");
    let table = exported_table(&core, "__meld_thread_table").expect("__meld_thread_table exported");

    let map: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&map).expect("map written")).unwrap();
    let imports = map["imports"].as_array().unwrap();
    let thread: Vec<_> = imports
        .iter()
        .filter(|i| i["name"].as_str().unwrap().starts_with("[thread-"))
        .collect();
    assert_eq!(
        thread.len(),
        4,
        "t1 uses index, new-indirect, resume-later, yield"
    );
    for i in &thread {
        assert_eq!(i["module"], "$root");
        assert_eq!(i["kind"], "p3-builtin", "{i}");
        assert!(i["memory"].is_null() && i["realloc"].is_null(), "{i}");
        if i["name"] == "[thread-new-indirect-v0]" {
            assert_eq!(i["thread_table"]["index"], table);
            assert_eq!(i["thread_table"]["export"], "__meld_thread_table");
        } else {
            assert!(i.get("thread_table").is_none(), "{i}");
        }
    }

    let att = attestation_json(&core);
    assert_eq!(
        att["metadata"]["thread_table"],
        serde_json::json!({ "index": table, "export": "__meld_thread_table" })
    );
}
