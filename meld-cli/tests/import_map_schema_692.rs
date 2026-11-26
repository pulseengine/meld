//! #692: the `--emit-import-map` JSON is a published interface. synth and
//! kiln read its key spellings (`builtin.kind`, `builtin.element.size`,
//! `builtin.async`, ...), and the struct-level test in
//! `meld-core/tests/stream_builtin_names_662.rs` cannot see a renamed JSON key.
//! These tests drive the real binary and pin the bytes.
//!
//! When the map changes on purpose, regenerate the golden file with the
//! command in `golden/README.md`, bump the map's `version` if a consumer
//! would read the change differently, and say so in the release notes.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

fn repo(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join(rel)
}

/// Fuse `input` under `--memory multi` and return the import map's text.
fn import_map(input: &Path, tag: &str) -> String {
    let dir = std::env::temp_dir();
    let pid = std::process::id();
    let out = dir.join(format!("meld-692-{pid}-{tag}.wasm"));
    let map = dir.join(format!("meld-692-{pid}-{tag}.json"));
    let run = Command::new(env!("CARGO_BIN_EXE_meld"))
        .arg("fuse")
        .arg(input)
        .args([
            "--memory",
            "multi",
            "--no-attestation",
            "--reproducible",
            "--emit-import-map",
        ])
        .arg(&map)
        .arg("-o")
        .arg(&out)
        .output()
        .expect("meld binary runs");
    assert!(
        run.status.success(),
        "meld fuse failed: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let text = std::fs::read_to_string(&map).expect("import map written");
    let _ = std::fs::remove_file(&out);
    let _ = std::fs::remove_file(&map);
    text
}

#[test]
fn the_import_map_of_the_662_stream_fixture_matches_the_golden_bytes() {
    let wat = repo("meld-core/tests/fixtures/issue_662/stream_write_via_shim_wt1263.wat");
    let wasm = wat::parse_file(&wat).expect("fixture parses");
    let input = std::env::temp_dir().join(format!("meld-692-{}-in.wasm", std::process::id()));
    std::fs::write(&input, wasm).expect("write input");
    let got = import_map(&input, "golden");
    let _ = std::fs::remove_file(&input);

    let golden_path = repo("meld-cli/tests/golden/import_map_stream_write_662.json");
    let golden = std::fs::read_to_string(&golden_path).expect("golden file");
    assert_eq!(
        got.trim_end(),
        golden.trim_end(),
        "the import map JSON changed; if on purpose, regenerate {} (see golden/README.md)",
        golden_path.display()
    );
}

#[test]
fn every_builtin_object_spells_exactly_kind_element_async() {
    // simple-call-import imports 16 built-in kinds (#692), so this covers more
    // than the one fixture the golden file pins.
    let text = import_map(
        &repo("tests/wit_bindgen/fixtures/simple-call-import.wasm"),
        "corpus",
    );
    let map: serde_json::Value = serde_json::from_str(&text).expect("valid JSON");
    assert_eq!(map["version"], 2, "top-level version");
    let imports = map["imports"].as_array().expect("imports array");

    let want: BTreeSet<&str> = ["async", "element", "kind"].into();
    let mut kinds = BTreeSet::new();
    for entry in imports {
        let Some(builtin) = entry.get("builtin") else {
            continue;
        };
        let obj = builtin.as_object().expect("builtin is an object");
        let keys: BTreeSet<&str> = obj.keys().map(String::as_str).collect();
        assert_eq!(keys, want, "builtin keys of {entry}");
        assert!(obj["async"].is_boolean(), "{entry}");
        let kind = obj["kind"].as_str().expect("kind is a string");
        kinds.insert(kind.to_string());
        match &obj["element"] {
            serde_json::Value::Null => {}
            serde_json::Value::Object(e) => {
                let ek: BTreeSet<&str> = e.keys().map(String::as_str).collect();
                assert_eq!(ek, ["align", "size"].into(), "element keys of {entry}");
                assert!(e["align"].is_u64() && e["size"].is_u64(), "{entry}");
            }
            other => panic!("element is neither null nor an object: {other}"),
        }
    }
    assert_eq!(kinds.len(), 16, "built-in kinds seen: {kinds:?}");
}
