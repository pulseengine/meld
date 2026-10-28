//! SR-107 (#530): `--memory-page-size`, driven through the real binary.
//!
//! The sizing itself is tested in `meld-core/tests/byte_pages_530.rs`; this
//! covers what only the CLI decides: the accepted spellings, the exit codes for
//! a bad value or a refused combination, that the output is validated with the
//! custom-page-sizes feature (so a byte-paged module is not rejected by meld's
//! own check), and that the flag reaches the fuser.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../tests/wit_bindgen/fixtures/domains_427")
        .join(format!("{name}.comp.wasm"))
}

fn meld(extra: &[&str], tag: &str) -> (Output, PathBuf) {
    let out = std::env::temp_dir().join(format!("meld-530-{}-{tag}.wasm", std::process::id()));
    let run = Command::new(env!("CARGO_BIN_EXE_meld"))
        .arg("fuse")
        .arg(fixture("consumer"))
        .arg(fixture("provider"))
        .arg("-o")
        .arg(&out)
        .args(extra)
        .output()
        .expect("meld binary runs");
    (run, out)
}

fn first_memory(wasm: &[u8]) -> (u64, Option<u64>, Option<u32>) {
    for payload in wasmparser::Parser::new(0).parse_all(wasm) {
        if let Ok(wasmparser::Payload::MemorySection(reader)) = payload {
            let m = reader.into_iter().next().expect("a memory").expect("ok");
            return (m.initial, m.maximum, m.page_size_log2);
        }
    }
    panic!("no memory section");
}

const PACK: &[&str] = &["--memory", "shared", "--address-rebase", "--pack-rebase"];

// rivet: verifies SWV-119
#[test]
fn byte_pages_are_accepted_with_pack_rebase_and_validate() {
    let mut args = PACK.to_vec();
    args.extend(["--memory-page-size", "1"]);
    let (run, out) = meld(&args, "ok");
    let stderr = String::from_utf8_lossy(&run.stderr).to_string();
    assert!(run.status.success(), "{stderr}");
    let stdout = String::from_utf8_lossy(&run.stdout);
    // Validation is implied under --memory shared and must have PASSED with
    // the custom-page-sizes feature on.
    assert!(stdout.contains("Validation passed"), "{stdout}");
    let (initial, maximum, log2) = first_memory(&std::fs::read(&out).expect("output"));
    let _ = std::fs::remove_file(&out);
    assert_eq!(log2, Some(0));
    assert_eq!(Some(initial), maximum);

    // 65536 is the default spelled out: no pagesize, and page units.
    let mut args = PACK.to_vec();
    args.extend(["--memory-page-size", "65536"]);
    let (run, out) = meld(&args, "default");
    assert!(run.status.success());
    let (_, _, log2) = first_memory(&std::fs::read(&out).expect("output"));
    let _ = std::fs::remove_file(&out);
    assert_eq!(log2, None);
}

// rivet: verifies SWV-119
#[test]
fn share_stack_counts_as_pack_rebase_for_byte_pages() {
    // --share-stack implies --pack-rebase, so the flag is not refused at the
    // usage level; whatever the (unrelated) share-stack gates decide, it must
    // not be the exit-2 usage error.
    let (run, out) = meld(
        &[
            "--memory",
            "shared",
            "--share-stack",
            "--memory-page-size",
            "1",
        ],
        "ss",
    );
    let _ = std::fs::remove_file(&out);
    assert_ne!(run.status.code(), Some(2), "{:?}", run);
}

// rivet: verifies SWV-119
#[test]
fn other_page_sizes_exit_2() {
    let mut args = PACK.to_vec();
    args.extend(["--memory-page-size", "4096"]);
    let (run, out) = meld(&args, "4096");
    let _ = std::fs::remove_file(&out);
    assert_eq!(run.status.code(), Some(2), "usage error");
    assert!(String::from_utf8_lossy(&run.stderr).contains("4096"));
}

// rivet: verifies SWV-119
#[test]
fn byte_pages_without_pack_rebase_exit_2() {
    let (run, out) = meld(
        &[
            "--memory",
            "shared",
            "--address-rebase",
            "--memory-page-size",
            "1",
        ],
        "nopack",
    );
    assert!(!out.exists(), "no output file for a refused invocation");
    assert_eq!(run.status.code(), Some(2), "usage error");
    assert!(String::from_utf8_lossy(&run.stderr).contains("--pack-rebase"));
}

// rivet: verifies SWV-119
#[test]
fn byte_pages_with_component_exit_2() {
    let mut args = PACK.to_vec();
    args.extend(["--memory-page-size", "1", "--component"]);
    let (run, out) = meld(&args, "comp");
    assert!(!out.exists());
    assert_eq!(run.status.code(), Some(2), "usage error");
    assert!(String::from_utf8_lossy(&run.stderr).contains("--component"));
}
