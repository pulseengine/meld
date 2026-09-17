//! #414: `meld fuse --stats` printed a nonsense reduction when the output was
//! larger than the input.
//!
//! `print_stats` subtracted two `usize` before casting to `f64`, so a
//! composition that grows (the normal case: adapters, attestation and
//! provenance all add bytes) wrapped to `1033431040543952384.0%` in a release
//! build and panicked in a debug one. The default summary of the same run,
//! computed separately, printed the correct increase.
//!
//! These tests drive the real binary through the flag-to-output path, which
//! nothing exercised before (#405). The expected figure is computed here from
//! the file sizes on disk, not from anything meld prints.

use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join(rel)
}

fn inputs() -> Vec<PathBuf> {
    vec![
        fixture("tests/wit_bindgen/fixtures/compose/provider.wasm"),
        fixture("tests/wit_bindgen/fixtures/compose/consumer.wasm"),
    ]
}

/// Run `meld fuse` on the fixture pair. Returns (stdout, input bytes, output bytes).
fn fuse(extra: &[&str], tag: &str) -> (String, u64, u64) {
    let out = std::env::temp_dir().join(format!("meld-414-{}-{tag}.wasm", std::process::id()));
    let run = Command::new(env!("CARGO_BIN_EXE_meld"))
        .arg("fuse")
        .args(inputs())
        .args(["--memory", "multi", "-o"])
        .arg(&out)
        .args(extra)
        .output()
        .expect("meld binary runs");
    let stdout = String::from_utf8_lossy(&run.stdout).into_owned();
    assert!(
        run.status.success(),
        "meld fuse {extra:?} failed ({}):\nstdout:\n{stdout}\nstderr:\n{}",
        run.status,
        String::from_utf8_lossy(&run.stderr)
    );
    let input: u64 = inputs()
        .iter()
        .map(|p| std::fs::metadata(p).expect("fixture exists").len())
        .sum();
    let output = std::fs::metadata(&out).expect("output written").len();
    let _ = std::fs::remove_file(&out);
    (stdout, input, output)
}

/// The size-change line, e.g. "Size increase: 34.6%", with its label and value.
fn size_change_line(stdout: &str) -> (String, f64) {
    let line = stdout
        .lines()
        .find(|l| {
            let t = l.trim_start();
            t.starts_with("Size increase:")
                || t.starts_with("Size reduction:")
                || t.starts_with("Reduction:")
        })
        .unwrap_or_else(|| panic!("no size-change line in output:\n{stdout}"));
    let (label, value) = line.trim().split_once(':').expect("label: value");
    let value = value
        .trim()
        .trim_end_matches('%')
        .parse::<f64>()
        .unwrap_or_else(|e| panic!("unparseable percentage in {line:?}: {e}"));
    (label.to_string(), value)
}

fn expected_increase_percent(input: u64, output: u64) -> f64 {
    (output as f64 - input as f64) / input as f64 * 100.0
}

// rivet: verifies SR-77
#[test]
fn stats_reports_an_increase_when_the_output_grows() {
    let (stdout, input, output) = fuse(&["--stats"], "stats");

    // Guard the guard: this test only means something if the output grew.
    assert!(
        output > input,
        "fixture must grow to reach #414 (input {input} B, output {output} B)"
    );

    let (label, value) = size_change_line(&stdout);
    assert_eq!(
        label, "Size increase",
        "an output larger than its input is an increase:\n{stdout}"
    );
    let expected = expected_increase_percent(input, output);
    assert!(
        (value - expected).abs() <= 0.05,
        "--stats reported {value}% but the files grew by {expected:.2}%:\n{stdout}"
    );
}

/// The two summaries of one run must not disagree, which is how #414 was
/// spotted: one printed the increase, the other a wrapped reduction.
// rivet: verifies SR-77
#[test]
fn stats_and_default_summary_report_the_same_change() {
    let (stats_out, ..) = fuse(&["--stats"], "agree-stats");
    let (plain_out, ..) = fuse(&[], "agree-plain");
    assert_eq!(
        size_change_line(&stats_out),
        size_change_line(&plain_out),
        "--stats and the default summary report different size changes"
    );
}
