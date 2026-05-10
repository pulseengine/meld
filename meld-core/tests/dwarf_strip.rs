//! DWARF strip-by-default policy test (Phase 1.5 of the witness-mapping
//! epic, issue #130).
//!
//! # Why this exists
//!
//! Phase 1 (issue #130 / PR #131) documented that meld passes input
//! `.debug_*` sections through verbatim, so every DWARF address in the
//! fused output points at the wrong instruction. Phase 1.5 makes the
//! policy explicit:
//!
//! - `DwarfHandling::Strip` (default) drops every `.debug_*` section so
//!   downstream consumers (e.g. `pulseengine/witness` MC/DC) see no
//!   DWARF rather than corrupted DWARF.
//! - `DwarfHandling::PassThrough` is opt-in for the rare case a caller
//!   wants the lossy old behaviour for diagnostics.
//!
//! Phase 2 will add an actual address-remap pass; until then, "no
//! DWARF" is strictly safer than "wrong DWARF".

use meld_core::{DwarfHandling, Fuser, FuserConfig};

const DEBUG_INFO_FIXTURE: &str = "../tests/wit_bindgen/fixtures/lists.wasm";

const DWARF_SECTION_NAMES: &[&str] = &[
    ".debug_abbrev",
    ".debug_info",
    ".debug_line",
    ".debug_str",
    ".debug_line_str",
    ".debug_str_offsets",
    ".debug_addr",
    ".debug_rnglists",
    ".debug_loclists",
    ".debug_ranges",
    ".debug_loc",
];

fn fixture_available() -> bool {
    if std::path::Path::new(DEBUG_INFO_FIXTURE).is_file() {
        true
    } else {
        eprintln!("skipping: fixture not found at {DEBUG_INFO_FIXTURE}");
        false
    }
}

fn count_dwarf_sections(bytes: &[u8]) -> usize {
    let parser = wasmparser::Parser::new(0);
    let mut total = 0usize;
    for payload in parser.parse_all(bytes) {
        let payload = match payload {
            Ok(p) => p,
            Err(_) => break,
        };
        if let wasmparser::Payload::CustomSection(reader) = payload
            && DWARF_SECTION_NAMES.contains(&reader.name())
        {
            total += 1;
        }
    }
    total
}

fn fuse_with(handling: DwarfHandling) -> Vec<u8> {
    let bytes = std::fs::read(DEBUG_INFO_FIXTURE).expect("fixture must read");
    let config = FuserConfig {
        dwarf_handling: handling,
        ..FuserConfig::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&bytes, Some("lists"))
        .expect("fixture parses");
    let (fused, _stats) = fuser.fuse_with_stats().expect("fuse succeeds");
    fused
}

/// Default `FuserConfig` strips DWARF — the fused module carries zero
/// `.debug_*` sections at the top level.
#[test]
fn default_strips_dwarf() {
    if !fixture_available() {
        return;
    }
    let fused = fuse_with(FuserConfig::default().dwarf_handling);
    assert_eq!(
        count_dwarf_sections(&fused),
        0,
        "default DwarfHandling::Strip must produce zero DWARF sections"
    );
}

/// `DwarfHandling::PassThrough` preserves the (lossy) prior behaviour:
/// DWARF sections are present in the fused output. Their addresses are
/// still wrong against the merged code section — that is the point of
/// the explicit opt-in.
#[test]
fn passthrough_preserves_dwarf() {
    if !fixture_available() {
        return;
    }
    let fused = fuse_with(DwarfHandling::PassThrough);
    assert!(
        count_dwarf_sections(&fused) > 0,
        "PassThrough must emit at least one DWARF section when input \
         carries one"
    );
}

/// Smoke check: `Default::default()` resolves to `DwarfHandling::Strip`,
/// not `PassThrough`. If the default ever flips, this test must be
/// updated together with the LS-CP-N entry.
#[test]
fn default_is_strip() {
    let cfg = FuserConfig::default();
    assert_eq!(cfg.dwarf_handling, DwarfHandling::Strip);
}
