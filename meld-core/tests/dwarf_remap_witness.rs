//! DWARF remap falsification oracle (#143 Phase 2, #130 witness
//! integration — v0.20.0).
//!
//! `DwarfHandling::Remap` claims that, for a single-DWARF-source fusion,
//! every function's `.debug_*` code addresses are rewritten to point at
//! the function's *fused* location. This test falsifies that claim on a
//! real compiler-emitted fixture by tying two independently-derived
//! facts together:
//!
//! 1. The **component-provenance** `code_range.start` of each fused
//!    function — computed by re-parsing the fused code section
//!    (`provenance::code_section_function_ranges`), completely separate
//!    from the DWARF path.
//! 2. Each `DW_TAG_subprogram`'s `DW_AT_low_pc` in the **remapped
//!    output DWARF** — parsed back with `gimli`.
//!
//! WebAssembly DWARF's `low_pc` is the function body start, which the
//! remap sends to `output_body_start` == `code_range.start`. So every
//! non-tombstone subprogram `low_pc` MUST equal some fused function's
//! `code_range.start`. If the remap math were wrong, the addresses
//! would not line up. This is the cross-repo contract `pulseengine/
//! witness` relies on (code offset → source line), validated in-tree.
//!
//! Dead-code functions that meld drops are tombstoned to `0xFFFF_FFFF`
//! by the remap (never a wrong address); those are skipped here.

use std::collections::BTreeSet;

use meld_core::{
    CustomSectionHandling, DwarfHandling, Fuser, FuserConfig, MemoryStrategy, OutputFormat,
};

/// A single-DWARF-source fixture: a real Rust component whose main core
/// module carries `debuginfo`, with no second DWARF-bearing module (so
/// `Remap` exercises the address-rewrite path rather than the
/// multi-source strip fallback).
const SINGLE_SOURCE_FIXTURE: &str = "../tests/wit_bindgen/fixtures/release-0.2.0/hello_rust.wasm";

const TOMBSTONE: u64 = 0xFFFF_FFFF;

fn fixture_available() -> bool {
    if std::path::Path::new(SINGLE_SOURCE_FIXTURE).is_file() {
        true
    } else {
        eprintln!("skipping: fixture not found at {SINGLE_SOURCE_FIXTURE}");
        false
    }
}

fn fuse_remap(input: &[u8]) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        component_provenance: true,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: CustomSectionHandling::Merge,
        output_format: OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
        dwarf_handling: DwarfHandling::Remap,
    });
    fuser
        .add_component_named(input, Some("hello-rust"))
        .expect("add_component");
    fuser.fuse().expect("fuse")
}

/// Collect the `.debug_*` custom sections from a fused core module.
fn debug_sections(bytes: &[u8]) -> std::collections::HashMap<String, Vec<u8>> {
    let mut out = std::collections::HashMap::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let Ok(wasmparser::Payload::CustomSection(reader)) = payload
            && reader.name().starts_with(".debug_")
        {
            out.insert(reader.name().to_string(), reader.data().to_vec());
        }
    }
    out
}

/// The `component-provenance` `code_range.start` of every fused
/// function — the fused-code-section body starts, derived without
/// touching DWARF.
fn provenance_body_starts(bytes: &[u8]) -> BTreeSet<u64> {
    let mut section = None;
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let Ok(wasmparser::Payload::CustomSection(reader)) = payload
            && reader.name() == meld_core::provenance::SECTION_NAME
        {
            section = Some(reader.data().to_vec());
        }
    }
    let data = section.expect("fused output carries component-provenance section");
    let prov = meld_core::provenance::ComponentProvenance::from_bytes(&data)
        .expect("decode component-provenance");
    prov.entries
        .iter()
        .filter_map(|e| e.code_range.map(|r| r.start as u64))
        .collect()
}

/// Every `DW_TAG_subprogram` `DW_AT_low_pc` (as a concrete address) in
/// the remapped output DWARF.
fn subprogram_low_pcs(sections: &std::collections::HashMap<String, Vec<u8>>) -> Vec<u64> {
    let endian = gimli::LittleEndian;
    let load = |id: gimli::SectionId| -> Result<gimli::EndianSlice<'_, gimli::LittleEndian>, gimli::Error> {
        let data = sections.get(id.name()).map(|v| v.as_slice()).unwrap_or(&[]);
        Ok(gimli::EndianSlice::new(data, endian))
    };
    let dwarf = gimli::Dwarf::load(load).expect("load output dwarf");

    let mut low_pcs = Vec::new();
    let mut units = dwarf.units();
    while let Some(header) = units.next().expect("unit header") {
        let unit = dwarf.unit(header).expect("parse unit");
        let mut entries = unit.entries();
        while let Some((_, entry)) = entries.next_dfs().expect("dfs walk") {
            if entry.tag() == gimli::constants::DW_TAG_subprogram
                && let Some(gimli::AttributeValue::Addr(a)) = entry
                    .attr_value(gimli::constants::DW_AT_low_pc)
                    .expect("low_pc attr")
            {
                low_pcs.push(a);
            }
        }
    }
    low_pcs
}

#[test]
fn remapped_subprogram_low_pcs_match_fused_body_starts() {
    if !fixture_available() {
        return;
    }
    let input = std::fs::read(SINGLE_SOURCE_FIXTURE).expect("read fixture");
    let fused = fuse_remap(&input);

    // The remap ran (didn't strip): the fused module carries DWARF.
    let sections = debug_sections(&fused);
    assert!(
        sections.contains_key(".debug_info"),
        "Remap on a single-DWARF-source fixture must emit remapped \
         `.debug_info`; got sections: {:?}",
        sections.keys().collect::<Vec<_>>()
    );

    let body_starts = provenance_body_starts(&fused);
    assert!(
        !body_starts.is_empty(),
        "expected component-provenance code ranges in the fused output"
    );

    let low_pcs = subprogram_low_pcs(&sections);
    assert!(
        !low_pcs.is_empty(),
        "expected at least one DW_TAG_subprogram with a low_pc"
    );

    // FALSIFICATION: every concrete (non-tombstone) subprogram low_pc
    // must equal some fused function's provenance body start. A wrong
    // remap would land low_pcs off the fused function boundaries.
    let mut matched = 0usize;
    let mut tombstoned = 0usize;
    for &pc in &low_pcs {
        if pc == TOMBSTONE {
            tombstoned += 1;
            continue;
        }
        assert!(
            body_starts.contains(&pc),
            "remapped subprogram low_pc {pc:#x} does not match any fused \
             function body start (component-provenance code_range). The \
             DWARF address remap is wrong."
        );
        matched += 1;
    }

    // Sanity: the remap mapped the overwhelming majority of functions,
    // only tombstoning the few meld dropped. If most were tombstoned the
    // remap would be vacuously "correct" while useless.
    assert!(
        matched > body_starts.len() / 2,
        "only {matched} subprogram low_pcs matched fused body starts \
         ({tombstoned} tombstoned, {} fused functions) — remap is \
         tombstoning too much to be meaningful",
        body_starts.len()
    );
    eprintln!(
        "DWARF remap witness: {matched} subprogram low_pcs land exactly on \
         fused body starts, {tombstoned} dead-code subprograms tombstoned"
    );
}
