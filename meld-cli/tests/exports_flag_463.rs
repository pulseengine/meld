//! #463: the `--exports` flag, driven through the real binary.
//!
//! The export-set semantics are tested in `meld-core/tests/exports_world_463.rs`;
//! this covers what only the CLI decides: the spelling, the exit codes for a
//! bad value or a refused combination, and that the flag reaches the fuser.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn composed() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../meld-core/tests/fixtures/issue_463/composed.wasm")
}

fn meld(extra: &[&str], tag: &str) -> (Output, PathBuf) {
    let out = std::env::temp_dir().join(format!("meld-463-{}-{tag}.wasm", std::process::id()));
    let run = Command::new(env!("CARGO_BIN_EXE_meld"))
        .arg("fuse")
        .arg(composed())
        .args(["--memory", "shared", "--address-rebase", "-o"])
        .arg(&out)
        .args(extra)
        .output()
        .expect("meld binary runs");
    (run, out)
}

fn exports(wasm: &[u8]) -> Vec<String> {
    let mut names = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(wasm) {
        if let Ok(wasmparser::Payload::ExportSection(reader)) = payload {
            names.extend(reader.into_iter().flatten().map(|e| e.name.to_string()));
        }
    }
    names
}

#[test]
fn world_limits_the_export_list_and_all_is_the_default() {
    let (run, out) = meld(&[], "default");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    let default = exports(&std::fs::read(&out).expect("output"));
    let _ = std::fs::remove_file(&out);

    let (run, out) = meld(&["--exports", "all"], "all");
    assert!(run.status.success());
    let all = exports(&std::fs::read(&out).expect("output"));
    let _ = std::fs::remove_file(&out);
    assert_eq!(default, all, "`all` is the default");
    assert!(default.iter().any(|n| n == "__heap_base"), "control");

    let (run, out) = meld(&["--exports", "world"], "world");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    let world = exports(&std::fs::read(&out).expect("output"));
    let _ = std::fs::remove_file(&out);
    assert_eq!(world.len(), 4, "memory + three world functions: {world:?}");
    assert!(
        world
            .iter()
            .all(|n| n == "memory" || n.contains("/controller@") || n.contains("/observer@"))
    );
}

#[test]
fn an_unknown_mode_exits_2() {
    let (run, out) = meld(&["--exports", "bogus"], "bogus");
    let _ = std::fs::remove_file(&out);
    assert_eq!(run.status.code(), Some(2), "usage error");
    let stderr = String::from_utf8_lossy(&run.stderr);
    assert!(
        stderr.contains("world") && stderr.contains("all"),
        "names the choices: {stderr}"
    );
}

#[test]
fn world_with_component_exits_2_and_says_why() {
    let (run, out) = meld(&["--exports", "world", "--component"], "component");
    let _ = std::fs::remove_file(&out);
    assert_eq!(run.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&run.stderr).contains("--component"));
}

#[test]
fn the_flag_is_in_the_help() {
    let run = Command::new(env!("CARGO_BIN_EXE_meld"))
        .args(["fuse", "--help"])
        .output()
        .expect("meld binary runs");
    let help = String::from_utf8_lossy(&run.stdout);
    assert!(help.contains("--exports <MODE>"), "{help}");
}
