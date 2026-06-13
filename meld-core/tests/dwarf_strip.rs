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
//! - `DwarfHandling::Strip` drops every `.debug_*` section so
//!   downstream consumers (e.g. `pulseengine/witness` MC/DC) see no
//!   DWARF rather than corrupted DWARF.
//! - `DwarfHandling::PassThrough` is opt-in for the rare case a caller
//!   wants the lossy old behaviour for diagnostics.
//! - `DwarfHandling::Remap` (default since v0.25.0, #143/#144 complete)
//!   address-remaps single-source DWARF and attributes meld-generated
//!   code to per-class `<meld-adapter>` lines; with multiple DWARF
//!   sources it drops the source DWARF (#208) but keeps the synthetic
//!   unit. The LS-CP-4 invariant is unchanged: the DEFAULT never emits
//!   address-wrong DWARF — `PassThrough` stays a deliberate opt-in.

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
fn strip_strips_dwarf() {
    if !fixture_available() {
        return;
    }
    let fused = fuse_with(DwarfHandling::Strip);
    assert_eq!(
        count_dwarf_sections(&fused),
        0,
        "DwarfHandling::Strip must produce zero DWARF sections"
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

/// `Default::default()` resolves to `DwarfHandling::Remap` (v0.25.0),
/// and — the actual LS-CP-4 invariant — NEVER to `PassThrough`, whose
/// addresses are wrong against the fused code section.
#[test]
fn default_is_remap_never_passthrough() {
    let cfg = FuserConfig::default();
    assert_eq!(cfg.dwarf_handling, DwarfHandling::Remap);
    assert_ne!(cfg.dwarf_handling, DwarfHandling::PassThrough);
}

// LS-N verification gate convention aliases. These delegate to the
// existing tests above; their purpose is the discoverable
// `ls_cp_4_*` name that `tools/run_ls_verification.py` matches
// against. The original tests stay in place as the canonical bodies
// (preserves git blame + grep continuity).
//
// LS-CP-4 ("DWARF passthrough emits address-incorrect debug info on
// fused output") is the loss scenario the Strip-default policy
// directly mitigates — Phase 1.5 made Strip the default so the
// broken passthrough is no longer the silent fallback. These tests
// pin that policy.

#[test]
fn ls_cp_4_strip_strips_dwarf() {
    strip_strips_dwarf();
}

#[test]
fn ls_cp_4_passthrough_preserves_dwarf_explicitly() {
    passthrough_preserves_dwarf();
}

#[test]
fn ls_cp_4_default_is_never_passthrough() {
    default_is_remap_never_passthrough();
}
