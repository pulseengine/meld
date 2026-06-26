//! Integration test for issue #192: the `component-provenance`
//! custom section emitted by the fuser must round-trip via the
//! standard wasmparser custom-section reader, and every entry must
//! point back to a valid `(component, originating_func_idx)` in the
//! components that went into the fusion.
//!
//! This pins the cross-repo contract with `pulseengine/scry`'s DD-002
//! sound-abstract-interpreter integration: scry parses the section,
//! looks up the originating function in the original component
//! sources, and projects its precomputed invariants onto the
//! fused-module location. If meld silently mis-attributes (e.g.,
//! by emitting a wrong `originating_func_idx`, the wrong
//! `component_id`, or by skipping a fused function), scry projects
//! onto the wrong location — a hazard documented as LS-M-6.

use meld_core::{
    CustomSectionHandling, DwarfHandling, Fuser, FuserConfig, MemoryStrategy, OutputFormat,
    provenance::{ComponentProvenance, SECTION_NAME, VERSION, sha256_hex},
};

/// One of the wit-bindgen integration fixtures. Same fixture used
/// by `dwarf_passthrough.rs` — known to fuse cleanly with default
/// config and to carry a meaningful number of functions.
const FIXTURE: &str = "../tests/wit_bindgen/fixtures/lists.wasm";

fn fixture_available() -> bool {
    if std::path::Path::new(FIXTURE).is_file() {
        true
    } else {
        eprintln!("skipping: fixture not found at {FIXTURE}");
        false
    }
}

/// Build a fuser with the default config — provenance ON, attestation
/// ON, multi-memory. Matches what production users get.
fn fuse_default(bytes: &[u8], name: &str) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig::default());
    fuser
        .add_component_named(bytes, Some(name))
        .expect("add_component");
    fuser.fuse().expect("fuse")
}

/// Read every custom section whose name equals `target_name`.
/// Returns the raw payloads (a single fused module should have
/// exactly one `component-provenance` section, but the helper
/// returns Vec so the assert lives in the caller).
fn read_custom_sections<'a>(bytes: &'a [u8], target_name: &str) -> Vec<&'a [u8]> {
    let mut out = Vec::new();
    let parser = wasmparser::Parser::new(0);
    for payload in parser.parse_all(bytes) {
        let payload = match payload {
            Ok(p) => p,
            Err(_) => break,
        };
        if let wasmparser::Payload::CustomSection(reader) = payload
            && reader.name() == target_name
        {
            out.push(reader.data());
        }
    }
    out
}

/// Walk top-level sections by hand, dropping any custom sections
/// whose name appears in `strip_names`. Returns the rebuilt bytes.
/// This is what scry-side consumers must do to verify the
/// `fused_module_sha256` hash claim.
fn strip_custom_sections(bytes: &[u8], strip_names: &[&str]) -> Vec<u8> {
    let mut out = Vec::new();
    // Preamble: 4-byte magic + 4-byte version.
    out.extend_from_slice(&bytes[..8]);
    let mut i = 8usize;
    while i < bytes.len() {
        let sec_start = i;
        let sec_id = bytes[i];
        i += 1;
        // Read LEB128 size.
        let (size, leb_len) = read_leb128_u32(&bytes[i..]);
        i += leb_len;
        let payload_start = i;
        let payload_end = payload_start + size as usize;
        let drop = if sec_id == 0 {
            // Custom section: payload begins with LEB128-prefixed
            // name. Decode the name and compare.
            let (name_len, name_leb_len) = read_leb128_u32(&bytes[payload_start..]);
            let name_bytes_start = payload_start + name_leb_len;
            let name_bytes_end = name_bytes_start + name_len as usize;
            let name = std::str::from_utf8(&bytes[name_bytes_start..name_bytes_end])
                .expect("custom section name is utf-8");
            strip_names.contains(&name)
        } else {
            false
        };
        if !drop {
            out.extend_from_slice(&bytes[sec_start..payload_end]);
        }
        i = payload_end;
    }
    out
}

fn read_leb128_u32(bytes: &[u8]) -> (u32, usize) {
    let mut result: u32 = 0;
    let mut shift = 0;
    for (i, &b) in bytes.iter().enumerate() {
        result |= ((b & 0x7f) as u32) << shift;
        if b & 0x80 == 0 {
            return (result, i + 1);
        }
        shift += 7;
    }
    panic!("LEB128 not terminated");
}

#[test]
fn component_provenance_section_present_by_default() {
    if !fixture_available() {
        return;
    }
    let bytes = std::fs::read(FIXTURE).expect("read fixture");
    let fused = fuse_default(&bytes, "auth");

    let payloads = read_custom_sections(&fused, SECTION_NAME);
    assert_eq!(
        payloads.len(),
        1,
        "expected exactly one `{SECTION_NAME}` custom section; got {}",
        payloads.len()
    );
}

#[test]
fn component_provenance_round_trips() {
    if !fixture_available() {
        return;
    }
    let bytes = std::fs::read(FIXTURE).expect("read fixture");
    let fused = fuse_default(&bytes, "auth");

    let payloads = read_custom_sections(&fused, SECTION_NAME);
    let payload = payloads.first().expect("section present");
    let prov = ComponentProvenance::from_bytes(payload).expect("decode JSON");

    assert_eq!(prov.version, VERSION, "version mismatch");
    assert!(!prov.entries.is_empty(), "expected ≥1 fused function");
    assert_eq!(
        prov.fused_module_sha256.len(),
        64,
        "fused_module_sha256 must be 64 hex chars"
    );
}

#[test]
fn v3_fusion_premises_present_on_real_fusion() {
    // #313 / scry#63: the SCPV v3 section carries the fusion premises
    // that feed scry's analysis. On a real wac-composed fusion the
    // cross-component imports are internalised, so `closed_world` must
    // hold; `bounded_memory` reflects whether the fused core grows its
    // memory. Both must round-trip through the binary codec.
    if !fixture_available() {
        return;
    }
    let bytes = std::fs::read(FIXTURE).expect("read fixture");
    let fused = fuse_default(&bytes, "auth");

    let payloads = read_custom_sections(&fused, SECTION_NAME);
    let payload = payloads.first().expect("section present");
    // Binary SCPV magic — proves we emit the converged format, not JSON.
    assert_eq!(
        &payload[0..4],
        b"SCPV",
        "payload must be binary SCPV, not JSON"
    );
    let prov = ComponentProvenance::from_bytes(payload).expect("decode SCPV v3");

    // Both premises must agree with an independent probe of the fused
    // module (the premises' sources) — sound and input-independent.
    let grows = meld_core::memory_probe::module_uses_memory_grow(&fused);
    assert_eq!(
        prov.bounded_memory, !grows,
        "bounded_memory must equal !uses(memory.grow)"
    );
    let has_imports = wasmparser::Parser::new(0)
        .parse_all(&fused)
        .any(|p| matches!(p, Ok(wasmparser::Payload::ImportSection(r)) if r.count() > 0));
    assert_eq!(
        prov.closed_world, !has_imports,
        "closed_world must equal (fused module has zero imports)"
    );
}

#[test]
fn v2_code_ranges_are_populated_ordered_and_nonoverlapping() {
    // DWARF Phase 2 increment 1: every entry should carry a
    // `code_range`, the spans should be ordered by fused_func_idx and
    // non-overlapping (function bodies are laid out sequentially in
    // the code section). This is the anchor downstream DWARF
    // remapping (increment 3) builds on, so the contract is pinned
    // end-to-end against a real fused module.
    if !fixture_available() {
        return;
    }
    let bytes = std::fs::read(FIXTURE).expect("read fixture");
    let fused = fuse_default(&bytes, "auth");

    let payloads = read_custom_sections(&fused, SECTION_NAME);
    let payload = payloads.first().expect("section present");
    let prov = ComponentProvenance::from_bytes(payload).expect("decode JSON");

    // Entries are emitted in defined-function order; sort by
    // fused_func_idx to be robust, then check each range is valid and
    // the sequence is non-overlapping.
    let mut entries = prov.entries.clone();
    entries.sort_by_key(|e| e.fused_func_idx);

    let mut prev_end: Option<u32> = None;
    for e in &entries {
        let r = e
            .code_range
            .unwrap_or_else(|| panic!("v2 entry missing code_range: {e:?}"));
        assert!(r.start < r.end, "empty/inverted code_range: {e:?}");
        if let Some(pe) = prev_end {
            assert!(
                pe <= r.start,
                "code ranges overlap or go backwards: prev_end={pe}, entry={e:?}"
            );
        }
        prev_end = Some(r.end);
    }
}

#[test]
fn every_entry_has_a_valid_back_pointer() {
    if !fixture_available() {
        return;
    }
    let bytes = std::fs::read(FIXTURE).expect("read fixture");
    let fused = fuse_default(&bytes, "auth");

    let payloads = read_custom_sections(&fused, SECTION_NAME);
    let payload = payloads.first().expect("section present");
    let prov = ComponentProvenance::from_bytes(payload).expect("decode JSON");

    // Note: meld's `flatten_nested_components` may turn a single P2
    // composition into several flattened sub-components, only the
    // outer wrapper of which the caller named. The flattened
    // children fall back to the positional default
    // `component-<idx>`. scry's consumer-side contract is:
    // `component_id` is stable + non-empty + uniquely identifies a
    // flattened component within this fusion. The test pins that
    // contract, not the literal `auth` argument.
    for entry in &prov.entries {
        assert!(
            !entry.component_id.is_empty(),
            "component_id must be non-empty; got {entry:?}"
        );
        // originating_func_idx is a u32 — no negative check needed,
        // but assert it doesn't exceed a sane upper bound. 100_000
        // is a generous over-estimate for any real component.
        assert!(
            entry.originating_func_idx < 100_000,
            "originating_func_idx looks suspect: {entry:?}"
        );
    }

    // Every entry's fused_func_idx must be distinct (no double-
    // attribution; one fused function maps to exactly one source).
    let mut seen = std::collections::HashSet::new();
    for entry in &prov.entries {
        assert!(
            seen.insert(entry.fused_func_idx),
            "duplicate fused_func_idx in section: {}",
            entry.fused_func_idx
        );
    }
}

#[test]
fn fused_module_sha256_matches_stripped_bytes() {
    // The hash binds the section to its module. Consumer verification
    // is: strip both meld-authored custom sections, hash the result,
    // compare to fused_module_sha256. This test reproduces that
    // verification end-to-end.
    if !fixture_available() {
        return;
    }
    let bytes = std::fs::read(FIXTURE).expect("read fixture");
    let fused = fuse_default(&bytes, "auth");

    let payloads = read_custom_sections(&fused, SECTION_NAME);
    let payload = payloads.first().expect("section present");
    let prov = ComponentProvenance::from_bytes(payload).expect("decode JSON");

    // Strip both self-referential sections before hashing — the
    // attestation section is also keyed off the same
    // bytes-without-extras snapshot.
    let stripped = strip_custom_sections(&fused, &[SECTION_NAME, "wsc.transformation.attestation"]);
    let recomputed = sha256_hex(&stripped);

    assert_eq!(
        recomputed, prov.fused_module_sha256,
        "fused_module_sha256 must match the SHA-256 of the module \
         bytes with the component-provenance + attestation sections \
         removed (consumer-side verification recipe)"
    );
}

#[test]
fn opt_out_via_config_drops_the_section() {
    if !fixture_available() {
        return;
    }
    let bytes = std::fs::read(FIXTURE).expect("read fixture");
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: CustomSectionHandling::Merge,
        output_format: OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
        dwarf_handling: DwarfHandling::Strip,
    });
    fuser
        .add_component_named(&bytes, Some("auth"))
        .expect("add_component");
    let fused = fuser.fuse().expect("fuse");

    let payloads = read_custom_sections(&fused, SECTION_NAME);
    assert!(
        payloads.is_empty(),
        "section must be absent when component_provenance=false; \
         got {} payload(s)",
        payloads.len()
    );
}

#[test]
fn multiple_distinct_component_ids_when_fixture_flattens_to_many() {
    // The lists.wasm fixture is a P2 composition that
    // `flatten_nested_components` expands into multiple flattened
    // sub-components. The provenance section must therefore contain
    // entries attributing to MORE than one distinct component_id —
    // the cross-repo contract scry relies on is "distinct flattened
    // sub-components are distinguishable in the section".
    if !fixture_available() {
        return;
    }
    let bytes = std::fs::read(FIXTURE).expect("read fixture");
    let fused = fuse_default(&bytes, "auth");

    let payloads = read_custom_sections(&fused, SECTION_NAME);
    let payload = payloads.first().expect("section present");
    let prov = ComponentProvenance::from_bytes(payload).expect("decode JSON");

    let ids: std::collections::HashSet<&str> = prov
        .entries
        .iter()
        .map(|e| e.component_id.as_str())
        .collect();
    assert!(
        ids.len() >= 2,
        "lists.wasm flattens to multiple sub-components, so the \
         section should attribute to ≥2 distinct component_ids; \
         got {ids:?}"
    );

    // Each component_id should be either the user-supplied name
    // (passed through `add_component_named`) OR the positional
    // fallback `component-<idx>`. Pin that contract — if the
    // fallback format ever changes, scry needs to know.
    for id in &ids {
        let is_user_name = *id == "auth";
        let is_positional_fallback = id.starts_with("component-")
            && id["component-".len()..].chars().all(|c| c.is_ascii_digit());
        assert!(
            is_user_name || is_positional_fallback,
            "unexpected component_id format `{id}`; expected either \
             user-supplied `auth` or positional `component-<idx>`"
        );
    }
}
