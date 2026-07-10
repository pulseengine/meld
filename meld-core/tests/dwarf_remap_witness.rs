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
        reproducible: false,
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

/// A multi-inner-module fixture whose `.debug_ranges` carry inlined
/// subroutines (base-relative offset pairs) — the #319 inc-2 surface.
const RANGES_FIXTURE: &str = "../tests/wit_bindgen/fixtures/records.wasm";

/// #319 inc 2: no `DW_AT_ranges` DIE may escape its enclosing subprogram in
/// the remapped output. `records.wasm` carries inlined subroutines whose
/// `.debug_ranges` are base-relative offset pairs; before the fix gimli
/// mis-routed those *offsets* through `convert_address` (treating a small
/// offset as an absolute address), sending the ranges to unrelated output
/// locations — `llvm-dwarfdump --verify`: "DIE address ranges are not
/// contained in its parent's ranges". This re-parses the fused DWARF and
/// asserts every resolved range sits inside the enclosing subprogram.
#[test]
fn inc2_die_ranges_stay_within_enclosing_subprogram() {
    if !std::path::Path::new(RANGES_FIXTURE).is_file() {
        eprintln!("skipping: fixture not found at {RANGES_FIXTURE}");
        return;
    }
    let input = std::fs::read(RANGES_FIXTURE).expect("read fixture");
    let fused = fuse_remap(&input);
    let sections = debug_sections(&fused);
    assert!(
        sections.contains_key(".debug_info"),
        "Remap must emit remapped .debug_info for the ranges fixture"
    );

    let endian = gimli::LittleEndian;
    let load = |id: gimli::SectionId| -> Result<gimli::EndianSlice<'_, gimli::LittleEndian>, gimli::Error> {
        let data = sections.get(id.name()).map(|v| v.as_slice()).unwrap_or(&[]);
        Ok(gimli::EndianSlice::new(data, endian))
    };
    let dwarf = gimli::Dwarf::load(load).expect("load output dwarf");

    let mut checked = 0usize;
    let mut units = dwarf.units();
    while let Some(header) = units.next().expect("unit header") {
        let unit = dwarf.unit(header).expect("parse unit");
        let mut entries = unit.entries();
        let mut depth = 0isize;
        // Stack of enclosing subprogram ranges: (die_depth, low, end).
        let mut encl: Vec<(isize, u64, u64)> = Vec::new();
        while let Some((delta, entry)) = entries.next_dfs().expect("dfs walk") {
            depth += delta;
            while matches!(encl.last(), Some(&(d, _, _)) if d >= depth) {
                encl.pop();
            }
            if entry.tag() == gimli::constants::DW_TAG_subprogram
                && let Some(gimli::AttributeValue::Addr(low)) = entry
                    .attr_value(gimli::constants::DW_AT_low_pc)
                    .expect("low_pc")
                && low != TOMBSTONE
                && let Some(hp) = entry
                    .attr_value(gimli::constants::DW_AT_high_pc)
                    .expect("high_pc")
            {
                let end = match hp {
                    gimli::AttributeValue::Udata(len) => low + len,
                    gimli::AttributeValue::Addr(a) => a,
                    _ => low,
                };
                encl.push((depth, low, end));
            }
            // A DIE carrying a range LIST, checked against its enclosing
            // subprogram (the class that escaped in #319).
            if entry
                .attr_value(gimli::constants::DW_AT_ranges)
                .expect("ranges attr")
                .is_some()
                && let Some(&(_, plow, pend)) = encl.last()
            {
                let mut ranges = dwarf.die_ranges(&unit, entry).expect("die_ranges");
                while let Some(r) = ranges.next().expect("range") {
                    // Skip tombstone / dead-code sentinel entries.
                    if r.begin >= 0xffff_fffe {
                        continue;
                    }
                    assert!(
                        r.begin >= plow && r.end <= pend,
                        "inc2: DW_AT_ranges [{:#x},{:#x}) escapes enclosing \
                         subprogram [{plow:#x},{pend:#x}) — base-relative range \
                         offset was remapped as an absolute address (#319)",
                        r.begin,
                        r.end
                    );
                    checked += 1;
                }
            }
        }
    }
    assert!(
        checked > 0,
        "expected at least one DW_AT_ranges DIE inside a subprogram to check"
    );
    eprintln!("inc2: {checked} DW_AT_ranges entries all contained in their subprogram");
}

/// #319 inc 3: no `DW_AT_location` location-list entry may have an
/// out-of-module range in the remapped output. Location-list entries carry
/// base-relative begin/end offsets identical to `.debug_ranges` (inc 2);
/// before the fix gimli mis-routed those offsets through `convert_address`,
/// producing garbage ranges (e.g. `[0x905993c0, …)`) that derailed the
/// list decode (`llvm-dwarfdump`: "Invalid DW_AT_location" / "Invalid DWARF
/// expressions"). This fuses the fixture and asserts every location-list
/// entry's range lies within the fused module's byte length — a garbage
/// remap (≈2.4 GiB begin) fails; a correct fused-code offset (< a few MiB)
/// passes.
#[test]
fn inc3_location_list_ranges_stay_in_module() {
    if !std::path::Path::new(RANGES_FIXTURE).is_file() {
        eprintln!("skipping: fixture not found at {RANGES_FIXTURE}");
        return;
    }
    let input = std::fs::read(RANGES_FIXTURE).expect("read fixture");
    let fused = fuse_remap(&input);
    // Generous upper bound: no real fused-code address exceeds the whole
    // module size; the pre-fix garbage (~0x905993c0) blows past it.
    let bound = fused.len() as u64;
    let sections = debug_sections(&fused);
    assert!(
        sections.contains_key(".debug_info"),
        "expected remapped DWARF"
    );

    let endian = gimli::LittleEndian;
    let load = |id: gimli::SectionId| -> Result<gimli::EndianSlice<'_, gimli::LittleEndian>, gimli::Error> {
        let data = sections.get(id.name()).map(|v| v.as_slice()).unwrap_or(&[]);
        Ok(gimli::EndianSlice::new(data, endian))
    };
    let dwarf = gimli::Dwarf::load(load).expect("load output dwarf");

    let mut checked = 0usize;
    let mut units = dwarf.units();
    while let Some(header) = units.next().expect("unit header") {
        let unit = dwarf.unit(header).expect("parse unit");
        let mut entries = unit.entries();
        while let Some((_, entry)) = entries.next_dfs().expect("dfs walk") {
            let Some(loc) = entry
                .attr_value(gimli::constants::DW_AT_location)
                .expect("location attr")
            else {
                continue;
            };
            // Only location LISTS (a bare exprloc → None).
            let Some(mut locs) = dwarf.attr_locations(&unit, loc).expect("attr_locations") else {
                continue;
            };
            while let Some(le) = locs.next().expect("loc entry") {
                assert!(
                    le.range.begin <= le.range.end && le.range.end <= bound,
                    "inc3: DW_AT_location entry range [{:#x},{:#x}) is out of the \
                     fused module (len {bound:#x}) — a base-relative location \
                     offset was remapped as an absolute address (#319)",
                    le.range.begin,
                    le.range.end
                );
                checked += 1;
            }
        }
    }
    assert!(
        checked > 0,
        "expected at least one DW_AT_location list entry to check"
    );
    eprintln!("inc3: {checked} DW_AT_location list entries all within the fused module");
}
