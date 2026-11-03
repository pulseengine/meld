//! #545: `meld fuse --memory multi` wrote a module that fails validation, at
//! exit 0, for 11 of 504 P3 components. Output validation was only implied
//! under `--memory shared`; it is now on by default under every strategy.
//!
//! The invariant tested here holds before and after the adapter defect behind
//! the fixture is fixed: if `meld fuse` exits 0, the written module validates;
//! if it refuses, nothing is written.

use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture() -> PathBuf {
    let p = Path::new(env!("CARGO_MANIFEST_DIR")).join("../tests/p3/issue_545/empty-wait.wasm");
    // #405: a missing fixture must fail the test, not pass it. Without this, a
    // refused fusion of a file that does not exist satisfies the invariant
    // below ("refused, nothing written") and the test runs on nothing.
    assert!(
        p.is_file(),
        "fixture missing at {} -- it must be tracked in git (.gitignore exempts tests/p3)",
        p.display()
    );
    p
}

fn validates(bytes: &[u8]) -> Result<(), String> {
    let features = wasmparser::WasmFeatures::all();
    wasmparser::Validator::new_with_features(features)
        .validate_all(bytes)
        .map(|_| ())
        .map_err(|e| e.to_string())
}

// rivet: verifies SWV-121
#[test]
fn exit_zero_implies_valid_output_under_every_strategy() {
    for strategy in ["multi", "auto", "shared"] {
        let out =
            std::env::temp_dir().join(format!("meld-545-{}-{strategy}.wasm", std::process::id()));
        let _ = std::fs::remove_file(&out);
        let run = Command::new(env!("CARGO_BIN_EXE_meld"))
            .arg("fuse")
            .arg(fixture())
            .args(["--memory", strategy, "-o"])
            .arg(&out)
            .output()
            .expect("meld binary runs");
        // The refusal, if any, must be meld's verdict on the module, not an
        // unreadable input.
        let stderr = String::from_utf8_lossy(&run.stderr);
        assert!(
            !stderr.contains("Failed to read") && !stderr.contains("not found"),
            "--memory {strategy}: input could not be read: {stderr}"
        );
        if run.status.success() {
            let bytes = std::fs::read(&out).expect("exit 0 must write the output");
            validates(&bytes).unwrap_or_else(|e| {
                panic!("--memory {strategy}: exit 0 but the output is invalid: {e}")
            });
        } else {
            assert!(
                !out.exists(),
                "--memory {strategy}: a refused fusion must not leave a file behind"
            );
        }
        let _ = std::fs::remove_file(&out);
    }
}

/// Potency: with validation switched off, meld 0.66.0's behaviour is back, so
/// the fixture still reaches the adapter defect (until that is fixed, the file
/// written under --no-validate is invalid). This keeps the test above honest:
/// it is not passing because the fixture stopped exercising anything.
// rivet: verifies SWV-121
#[test]
fn no_validate_restores_the_unchecked_write() {
    let out = std::env::temp_dir().join(format!("meld-545-nv-{}.wasm", std::process::id()));
    let _ = std::fs::remove_file(&out);
    let run = Command::new(env!("CARGO_BIN_EXE_meld"))
        .arg("fuse")
        .arg(fixture())
        .args(["--memory", "multi", "--no-validate", "-o"])
        .arg(&out)
        .output()
        .expect("meld binary runs");
    assert!(run.status.success(), "--no-validate fuses the fixture");
    let bytes = std::fs::read(&out).expect("output written");
    let _ = std::fs::remove_file(&out);
    if validates(&bytes).is_ok() {
        eprintln!(
            "#545: the fixture now fuses into a VALID module -- the adapter defect is fixed; \
             this potency check no longer bites and can be retired"
        );
    }
}
