//! #580: the Rocq extracts must not drift silently from the code they model.
//!
//! `proofs/rust_verified/*.rs` are hand-written, simplified extracts of
//! meld-core functions. rocq-of-rust translates them and the Rocq proofs are
//! about the translation. `proofs.yml` (the `Rocq proofs` check) runs only on
//! `proofs/**`, so a change to the meld-core function an extract models never
//! re-checks the proofs. Nothing compares the two.
//!
//! This test pins each extract item to the source function(s) it models:
//! `proofs/rust_verified/extract-pins.tsv` records the sha256 of every source
//! function's text. When a pinned function changes, this test fails in `Test`
//! (ci.yml, which runs on every code change). The fix is to re-read the
//! extract against the new source, update the extract if the modelled
//! arithmetic changed (that change then runs `Rocq proofs`), and re-bless the
//! hashes with `MELD_BLESS=1`. The bless is the reviewable claim that the
//! extract still models the source.
//!
//! What it cannot see: a semantic change made outside the pinned functions
//! (a helper the pinned function calls). The pins name the functions where the
//! modelled arithmetic lives today.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

const PINS: &str = "proofs/rust_verified/extract-pins.tsv";
const EXTRACT_DIR: &str = "proofs/rust_verified";

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root")
        .to_path_buf()
}

struct Pin {
    item: String,
    source: String,
    func: String,
    sha256: String,
}

fn read_pins(text: &str) -> Vec<Pin> {
    text.lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        .map(|l| {
            let cols: Vec<&str> = l.split('\t').collect();
            assert_eq!(cols.len(), 4, "{PINS}: want 4 tab-separated columns: {l:?}");
            Pin {
                item: cols[0].to_string(),
                source: cols[1].to_string(),
                func: cols[2].to_string(),
                sha256: cols[3].to_string(),
            }
        })
        .collect()
}

/// The text of `fn <name>` in rustfmt'd source: from its `fn` line to the
/// first later line that is the same indentation followed by `}`. `Format`
/// (cargo fmt --check) keeps that shape. Zero or several definitions is an
/// error: a pin must name exactly one function.
fn function_span(src: &str, name: &str) -> Result<String, String> {
    let lines: Vec<&str> = src.lines().collect();
    let is_def = |l: &str| {
        let t = l.trim_start();
        let rest = ["pub(crate) fn ", "pub(super) fn ", "pub fn ", "fn "]
            .iter()
            .find_map(|p| t.strip_prefix(p));
        rest.is_some_and(|r| {
            r.strip_prefix(name)
                .is_some_and(|after| after.starts_with('(') || after.starts_with('<'))
        })
    };
    let starts: Vec<usize> = (0..lines.len()).filter(|&i| is_def(lines[i])).collect();
    let start = match starts.as_slice() {
        [s] => *s,
        [] => return Err(format!("no `fn {name}`")),
        many => return Err(format!("`fn {name}` defined {} times", many.len())),
    };
    let indent = &lines[start][..lines[start].len() - lines[start].trim_start().len()];
    let close = format!("{indent}}}");
    let end = (start + 1..lines.len())
        .find(|&i| lines[i] == close)
        .ok_or_else(|| format!("`fn {name}`: no closing `{close}`"))?;
    Ok(lines[start..=end].join("\n"))
}

fn sha256_hex(text: &str) -> String {
    Sha256::digest(text.as_bytes())
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Every public extract function except constructors, as `module::[Type::]fn`.
/// Test modules are skipped.
fn extract_items(root: &Path) -> BTreeSet<String> {
    let mut items = BTreeSet::new();
    let mut files: Vec<_> = std::fs::read_dir(root.join(EXTRACT_DIR))
        .expect("extract dir")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "rs"))
        .collect();
    files.sort();
    assert!(!files.is_empty(), "no extracts under {EXTRACT_DIR}");
    for path in files {
        let module = path.file_stem().unwrap().to_string_lossy().to_string();
        let text = std::fs::read_to_string(&path).expect("read extract");
        let mut current_impl: Option<String> = None;
        for line in text.lines() {
            if line.starts_with("#[cfg(test)]") {
                break;
            }
            if let Some(rest) = line.strip_prefix("impl ") {
                current_impl = Some(rest.trim_end_matches('{').trim().to_string());
                continue;
            }
            if line == "}" {
                current_impl = None;
                continue;
            }
            let Some(rest) = line.trim_start().strip_prefix("pub fn ") else {
                continue;
            };
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if name == "new" {
                continue;
            }
            items.insert(match &current_impl {
                Some(ty) => format!("{module}::{ty}::{name}"),
                None => format!("{module}::{name}"),
            });
        }
    }
    items
}

// rivet: verifies SR-119
// rivet: verifies SWV-133
#[test]
fn extract_sources_match_their_pins() {
    let root = repo_root();
    let pins_path = root.join(PINS);
    let text = std::fs::read_to_string(&pins_path).expect("pins file");
    let pins = read_pins(&text);
    assert!(!pins.is_empty(), "{PINS} pins nothing");

    let bless = std::env::var_os("MELD_BLESS").is_some();
    let mut stale = Vec::new();
    let mut blessed = text.clone();
    for pin in &pins {
        let src = std::fs::read_to_string(root.join(&pin.source))
            .unwrap_or_else(|e| panic!("{}: pinned source {}: {e}", pin.item, pin.source));
        let span = function_span(&src, &pin.func)
            .unwrap_or_else(|e| panic!("{}: {} in {}", pin.item, e, pin.source));
        let now = sha256_hex(&span);
        if now != pin.sha256 {
            stale.push(format!(
                "  {} models {}::{} (pinned {}, now {})",
                pin.item,
                pin.source,
                pin.func,
                &pin.sha256[..pin.sha256.len().min(12)],
                &now[..12]
            ));
            blessed = blessed.replace(
                &format!("{}\t{}\t{}\t{}", pin.item, pin.source, pin.func, pin.sha256),
                &format!("{}\t{}\t{}\t{}", pin.item, pin.source, pin.func, now),
            );
        }
    }
    if bless && !stale.is_empty() {
        std::fs::write(&pins_path, blessed).expect("write pins");
        return;
    }
    assert!(
        stale.is_empty(),
        "#580: source functions modelled by a Rocq extract changed:\n{}\n\
         Re-read each extract in {EXTRACT_DIR}/ against its source. If the modelled \
         arithmetic changed, update the extract (that re-runs `Rocq proofs`). Then \
         re-bless: MELD_BLESS=1 cargo test -p meld-core --test proof_extract_pins_580",
        stale.join("\n")
    );
}

// rivet: verifies SR-119
// rivet: verifies SWV-133
#[test]
fn every_extract_item_is_pinned() {
    // Without this, a new extract function would model code nobody pins.
    let root = repo_root();
    let pins = read_pins(&std::fs::read_to_string(root.join(PINS)).expect("pins file"));
    let pinned: BTreeSet<String> = pins.iter().map(|p| p.item.clone()).collect();
    let items = extract_items(&root);
    let unpinned: Vec<_> = items.difference(&pinned).collect();
    let unknown: Vec<_> = pinned.difference(&items).collect();
    assert!(
        unpinned.is_empty(),
        "extract items with no pin in {PINS}: {unpinned:?}"
    );
    assert!(
        unknown.is_empty(),
        "pins naming no extract item: {unknown:?}"
    );
}

// rivet: verifies SR-119
// rivet: verifies SWV-133
#[test]
fn pin_check_can_fail() {
    // Negative controls for the instrument itself: a one-character edit
    // inside the function changes its hash, an edit outside does not, and a
    // missing or duplicated function is an error rather than a skip.
    let src = "fn a(x: u32) -> u32 {\n    x + 1\n}\n\nfn b() {}\n";
    let base = sha256_hex(&function_span(src, "a").unwrap());
    let edited = src.replace("x + 1", "x + 2");
    assert_ne!(base, sha256_hex(&function_span(&edited, "a").unwrap()));
    let outside = src.replace("fn b() {}", "fn b() { let _ = 0; }");
    assert_eq!(base, sha256_hex(&function_span(&outside, "a").unwrap()));
    assert!(function_span(src, "missing").is_err());
    assert!(function_span(&format!("{src}{src}"), "a").is_err());
    // A prefix of another name is not a match.
    assert!(function_span("fn ab() {\n}\n", "a").is_err());
}
