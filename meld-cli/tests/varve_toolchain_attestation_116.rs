//! SR-116: under a varve shim the attestation names the toolchain layer.
//!
//! varve's dispatcher sets `VARVE_LAYER` and `VARVE_LAYER_MANIFEST_DIGEST`
//! when it runs a tool. meld records both in the attestation's `tool`
//! object, so "which toolchain produced this artifact?" can be answered
//! from the artifact alone. They are left out when unset or empty, and
//! under `--reproducible`, whose bytes must not depend on the environment.
//!
//! Each case runs the real binary in a child process with its own
//! environment. Setting or clearing it in this process would race the other
//! tests.

use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join(rel)
}

/// Fuse the fixture pair with the given environment and flags. Returns the
/// output bytes.
fn fuse(env: &[(&str, &str)], extra: &[&str], tag: &str) -> Vec<u8> {
    let out = std::env::temp_dir().join(format!("meld-116-{}-{tag}.wasm", std::process::id()));
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_meld"));
    cmd.arg("fuse")
        .arg(fixture("tests/wit_bindgen/fixtures/compose/provider.wasm"))
        .arg(fixture("tests/wit_bindgen/fixtures/compose/consumer.wasm"))
        .args(["--memory", "multi", "-o"])
        .arg(&out)
        .args(extra)
        .env_remove("VARVE_LAYER")
        .env_remove("VARVE_LAYER_MANIFEST_DIGEST");
    for (k, v) in env {
        cmd.env(k, v);
    }
    let run = cmd.output().expect("meld binary runs");
    assert!(
        run.status.success(),
        "meld fuse failed: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let bytes = std::fs::read(&out).expect("output written");
    let _ = std::fs::remove_file(&out);
    bytes
}

/// The `tool` object of the embedded attestation.
fn tool(bytes: &[u8]) -> serde_json::Value {
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let Ok(wasmparser::Payload::CustomSection(c)) = payload
            && c.name() == "wsc.transformation.attestation"
        {
            let v: serde_json::Value = serde_json::from_slice(c.data()).expect("attestation JSON");
            return v["tool"].clone();
        }
    }
    panic!("no attestation section in the output");
}

const LAYER: (&str, &str) = ("VARVE_LAYER", "2026.08.2");
const DIGEST: (&str, &str) = ("VARVE_LAYER_MANIFEST_DIGEST", "sha256:5e1f00d");

// rivet: verifies SR-116
#[test]
fn varve_layer_is_recorded_when_set() {
    let t = tool(&fuse(&[LAYER, DIGEST], &[], "set"));
    assert_eq!(t["name"], "meld");
    assert_eq!(t["toolchain"], LAYER.1, "{t}");
    assert_eq!(t["toolchain_manifest_digest"], DIGEST.1, "{t}");
}

// rivet: verifies SR-116
#[test]
fn no_toolchain_keys_outside_varve_or_when_empty() {
    for (tag, env) in [
        ("unset", &[][..]),
        (
            "empty",
            &[("VARVE_LAYER", ""), ("VARVE_LAYER_MANIFEST_DIGEST", "")][..],
        ),
    ] {
        let t = tool(&fuse(env, &[], tag));
        let obj = t.as_object().expect("tool is an object");
        assert!(
            !obj.contains_key("toolchain") && !obj.contains_key("toolchain_manifest_digest"),
            "{tag}: {t}"
        );
    }
}

// rivet: verifies SR-116
#[test]
fn reproducible_output_does_not_depend_on_the_varve_environment() {
    let with_env = fuse(&[LAYER, DIGEST], &["--reproducible"], "repro-set");
    let without = fuse(&[], &["--reproducible"], "repro-unset");
    let t = tool(&with_env);
    assert!(t.get("toolchain").is_none(), "{t}");
    assert!(
        with_env == without,
        "--reproducible bytes changed with VARVE_LAYER set"
    );
}
