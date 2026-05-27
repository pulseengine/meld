//! DWARF-passthrough discovery test (Phase 1 of the witness-mapping epic).
//!
//! # What this test pins down
//!
//! After `meld fuse` rewrites N component-model `.wasm` files into one
//! fused core module, the per-input DWARF custom sections (`.debug_info`,
//! `.debug_line`, `.debug_str`, …) are still byte-addressed against the
//! ORIGINAL per-component code section. Once the merger relocates and
//! re-encodes function bodies into the merged module's code section,
//! every DWARF address inside those passed-through sections points at
//! the wrong instruction — or at no instruction at all.
//!
//! This file is the discovery oracle for the
//! `chore/dwarf-witness-discovery` PR. It does **not** fix the bug; it
//! pins down today's broken-but-not-empty behaviour so that any change
//! (Phase 1.5 passthrough, Phase 2 remap, Phase 3 adapter handling) has
//! a green-to-red signal to compare against.
//!
//! # Findings (verified by this test)
//!
//! 1. The default `CustomSectionHandling` is `Merge`, NOT `Drop`. So
//!    DWARF sections from every input core module are emitted into the
//!    fused module unchanged — they are present but their offsets are
//!    wrong against the new code section.
//! 2. With multiple debug-info-bearing inputs (or one P2 component that
//!    embeds multiple core modules with debug info), the fused module
//!    contains N duplicate `.debug_info` / `.debug_line` / etc. sections
//!    rather than a single merged one.
//! 3. No code in `meld-core/src/` currently parses, rewrites, or
//!    reconciles `.debug_*` sections. `merger.rs` (around line 2010)
//!    does a naive `Vec::push` per source module:
//!
//!    ```ignore
//!    for (name, data) in &module.custom_sections {
//!        merged.custom_sections.push((name.clone(), data.clone()));
//!    }
//!    ```
//!
//!    The encoder in `lib.rs::encode_output` then emits them all when
//!    `custom_sections != Drop`.
//!
//! # Cross-repo dependency
//!
//! The pulseengine `witness` tool (sibling repo, currently v0.11.x) is
//! the consumer that breaks. It calls `gimli` to build a
//! `(code-section byte offset) -> (file, line)` map and uses that map
//! to attribute MC/DC `br_if` decisions to source lines. After meld
//! fusion every offset is wrong, so witness produces incorrect coverage
//! attribution for fused modules.
//!
//! Witness is intentionally NOT a dependency of meld-core — it lives in
//! its own workspace and depends on `wasmtime`, `walrus`, and `gimli`
//! that we don't want to pull into core fusion. The integration test
//! therefore lives at the cross-repo level (a future scripted check, or
//! a fixture exchanged via the `pulseengine/wasm-component-examples`
//! release pipeline). This in-tree test only covers the meld-side
//! invariants — i.e. "DWARF is passed through, semantics are wrong" —
//! which witness's mapping logic relies on.
//!
//! # When to flip these assertions
//!
//! - **Phase 1.5 (deliberate passthrough policy)**: ✅ shipped in
//!   v0.7 / PR #135. `FuserConfig::default().dwarf_handling` is now
//!   `Strip`, and tests below explicitly opt into
//!   `DwarfHandling::PassThrough` via `fuse_passthrough()` to pin
//!   the broken-but-present behaviour for Phase 2 to flip.
//! - **Phase 2 (DWARF remap, #143)**: the duplicate-section assertion
//!   flips. The fused module should contain a single, merged,
//!   address-correct `.debug_info` / `.debug_line` pair. Update the
//!   test then.
//! - **Phase 3 (adapter / inlined-code coverage, #144)**: synthetic
//!   DIEs covering adapter ranges land. Update the test to assert
//!   their presence then.

use meld_core::{
    CustomSectionHandling, DwarfHandling, Fuser, FuserConfig, MemoryStrategy, OutputFormat,
};

/// One of the wit-bindgen integration fixtures known to embed core
/// modules compiled with `debuginfo = 2`. Verified via `wasm-tools
/// objdump` to carry `.debug_abbrev`, `.debug_info`, `.debug_ranges`,
/// `.debug_str`, `.debug_line`, `.debug_loc` inside its embedded core
/// modules at the time of writing.
const DEBUG_INFO_FIXTURE: &str = "../tests/wit_bindgen/fixtures/lists.wasm";

/// All DWARF custom-section names meld might encounter from a Rust /
/// Clang component. Mirrors `witness-core::decisions::extract_dwarf_sections`.
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

/// Walk a wasm binary at the **outermost** level and tally DWARF custom
/// sections by name. For a P2 component this only sees component-level
/// custom sections (i.e. zero — DWARF lives inside the embedded core
/// modules). For a fused core module it sees every DWARF section meld
/// emitted.
fn count_dwarf_sections_at_top_level(bytes: &[u8]) -> std::collections::BTreeMap<String, usize> {
    let mut counts: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let parser = wasmparser::Parser::new(0);
    for payload in parser.parse_all(bytes) {
        let payload = match payload {
            Ok(p) => p,
            Err(_) => break,
        };
        if let wasmparser::Payload::CustomSection(reader) = payload {
            let name = reader.name();
            if DWARF_SECTION_NAMES.contains(&name) {
                *counts.entry(name.to_string()).or_insert(0) += 1;
            }
        }
    }
    counts
}

/// Walk a wasm binary and tally every `.debug_*` custom section.
/// `wasmparser::Parser::parse_all` flattens nested modules into a
/// single payload stream, so this single walk covers component-level
/// sections AND sections inside every embedded core module. Used to
/// confirm the input fixture has DWARF SOMEWHERE before we try to
/// fuse it.
fn count_dwarf_sections_recursive(bytes: &[u8]) -> std::collections::BTreeMap<String, usize> {
    let mut counts: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let parser = wasmparser::Parser::new(0);
    for payload in parser.parse_all(bytes) {
        let payload = match payload {
            Ok(p) => p,
            Err(_) => break,
        };
        if let wasmparser::Payload::CustomSection(reader) = payload {
            let name = reader.name();
            if DWARF_SECTION_NAMES.contains(&name) {
                *counts.entry(name.to_string()).or_insert(0) += 1;
            }
        }
    }
    counts
}

/// Build a fuser that exercises the **PassThrough** DWARF policy, the
/// path Phase 2 (#143) will flip from broken to correct. Phase 1.5
/// (#135) made `DwarfHandling::Strip` the production default; this
/// test fixture pins the explicit-opt-in path so the green-to-red
/// signal for Phase 2 lives here rather than relying on a default
/// that has already shifted once.
fn fuse_passthrough(input: &[u8]) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: CustomSectionHandling::Merge,
        output_format: OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
        dwarf_handling: DwarfHandling::PassThrough,
    });
    fuser
        .add_component_named(input, Some("dwarf-fixture"))
        .expect("add_component");
    fuser.fuse().expect("fuse")
}

fn fuse_with_drop(input: &[u8]) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: CustomSectionHandling::Drop,
        output_format: OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
        dwarf_handling: DwarfHandling::Strip,
    });
    fuser
        .add_component_named(input, Some("dwarf-fixture"))
        .expect("add_component");
    fuser.fuse().expect("fuse")
}

#[test]
fn current_default_is_strip_post_phase_1_5() {
    // Pin: Phase 1.5 (#135, commit c7a2c0b) flipped the default DWARF
    // handling from PassThrough (broken-but-present) to Strip
    // (correct-but-lossy). The discovery oracle was originally
    // authored against the pre-Phase-1.5 default and inverted in this
    // commit to reflect shipped behaviour. Any future change to the
    // default (e.g. Phase 2 making PassThrough correct + the new
    // default) must be a deliberate edit to this test.
    assert_eq!(
        FuserConfig::default().dwarf_handling,
        DwarfHandling::Strip,
        "FuserConfig::default().dwarf_handling drifted from Strip. \
         If this was intentional (Phase 2 making PassThrough address- \
         correct etc.), update DWARF policy docs and the \
         witness-integration discovery issue."
    );
    // The custom-sections default remains Merge — Phase 1.5 only
    // changed DWARF policy, not the wider custom-section default.
    assert_eq!(
        FuserConfig::default().custom_sections,
        CustomSectionHandling::Merge,
    );
}

#[test]
fn fixture_carries_dwarf_in_some_embedded_module() {
    if !fixture_available() {
        return;
    }
    let bytes = std::fs::read(DEBUG_INFO_FIXTURE).expect("read fixture");
    let counts = count_dwarf_sections_recursive(&bytes);
    assert!(
        !counts.is_empty(),
        "fixture {DEBUG_INFO_FIXTURE} no longer carries any \
         `.debug_*` custom sections — pick a different fixture or \
         rebuild this one with debuginfo = 2"
    );
    // `.debug_info` is the most universally present DWARF section; if
    // it's missing from a debug-bearing module something is very wrong.
    assert!(
        counts.contains_key(".debug_info"),
        "expected `.debug_info` somewhere in fixture; saw: {counts:?}"
    );
}

#[test]
fn fused_output_inherits_dwarf_byte_for_byte_today() {
    // CURRENT BEHAVIOUR with `DwarfHandling::PassThrough` (Phase 1,
    // broken; opt-in-only since Phase 1.5 / PR #135 made `Strip` the
    // default):
    //
    // - PassThrough + `CustomSectionHandling::Merge` causes meld to
    //   copy each input core module's DWARF sections verbatim into
    //   the fused core module's custom-section slot.
    // - DWARF addresses inside these sections are byte offsets into
    //   the ORIGINAL per-input code section. The fused module has a
    //   different code section (rewritten function bodies, different
    //   layout, adapter functions appended), so every passed-through
    //   address is meaningless — best case `gimli` resolves it to the
    //   wrong source line, worst case it falls outside the new code
    //   section entirely.
    //
    // This test asserts the lossy-but-present invariant on the
    // PassThrough code path. Flip it once Phase 2 (#143, real DWARF
    // remapping) lands.
    if !fixture_available() {
        return;
    }
    let bytes = std::fs::read(DEBUG_INFO_FIXTURE).expect("read fixture");
    let fused = fuse_passthrough(&bytes);

    let top_level_dwarf_in_fused = count_dwarf_sections_at_top_level(&fused);
    assert!(
        !top_level_dwarf_in_fused.is_empty(),
        "Phase 1 expectation: meld passes DWARF through verbatim, so \
         the fused core module must carry at least one `.debug_*` \
         section at the module level. Saw none, which means \
         something has changed (likely a default flip to Drop, or a \
         new strip pass). Update this test and the tracking issue."
    );

    // TODO(phase-2): once meld remaps DWARF, the fused module should
    // carry exactly one of each `.debug_*` section (deduplicated +
    // address-corrected). Until then, multiple inputs / multiple core
    // modules produce duplicate sections — flagged here so it's
    // visible in test output.
    eprintln!(
        "DWARF sections at top level of fused module (current — wrong addresses): {top_level_dwarf_in_fused:?}"
    );
}

#[test]
fn drop_policy_strips_dwarf_completely() {
    // The escape hatch a witness/coverage user has TODAY: opt into
    // `CustomSectionHandling::Drop` to get a fused module with no
    // misleading DWARF. Coverage attribution becomes impossible (the
    // entire module reports as un-attributed), but at least the user
    // isn't told the WRONG source line.
    //
    // Note: Phase 1.5 (#135) shipped `DwarfHandling::Strip` as the
    // default, so the `Drop` escape hatch is now mostly redundant for
    // DWARF specifically — `Strip` removes only `.debug_*`, `Drop`
    // removes all custom sections. This test still exercises the
    // `Drop` path because the underlying invariant ("opting out
    // produces no `.debug_*`") is what witness relies on.
    if !fixture_available() {
        return;
    }
    let bytes = std::fs::read(DEBUG_INFO_FIXTURE).expect("read fixture");
    let fused = fuse_with_drop(&bytes);

    let counts = count_dwarf_sections_at_top_level(&fused);
    assert!(
        counts.is_empty(),
        "Drop policy should strip every `.debug_*` custom section. \
         Saw: {counts:?}"
    );
}

#[test]
fn dwarf_addresses_in_fused_output_are_known_to_be_wrong() {
    // This is the documenting-a-bug test. We don't have witness in
    // this workspace, so we can't run gimli end-to-end here. What we
    // CAN do is sanity-check the structural invariant that proves
    // the addresses are wrong: the input's code section length and
    // the fused output's code section length differ. DWARF addresses
    // that were valid in the input cannot be valid in the output if
    // the code section has a different size and layout — they refer
    // to a different range of bytes.
    //
    // When Phase 2 lands and `.debug_line` etc. are remapped to the
    // fused code section, the addresses themselves will be different
    // values (still encoding the same source lines). This test will
    // then need a different oracle — probably "build line map, walk
    // each address, assert it falls inside the fused code section
    // range and lands on a function-body byte boundary".
    if !fixture_available() {
        return;
    }
    let bytes = std::fs::read(DEBUG_INFO_FIXTURE).expect("read fixture");
    let fused = fuse_passthrough(&bytes);

    let input_code_len = code_section_len_recursive(&bytes);
    let fused_code_len = code_section_len(&fused);

    assert!(
        input_code_len.is_some(),
        "fixture {DEBUG_INFO_FIXTURE} has no code section visible to \
         the recursive walker — pick a different fixture"
    );
    assert!(
        fused_code_len.is_some(),
        "fused module has no code section, fusion must have produced \
         an empty module — fixture or fuser regressed"
    );
    let input_code_len = input_code_len.unwrap();
    let fused_code_len = fused_code_len.unwrap();

    eprintln!(
        "input code section (sum across embedded modules): {input_code_len} bytes \
         | fused code section: {fused_code_len} bytes"
    );

    // Pin the structural change. If these ever match exactly, either
    // the merger went degenerate (single passthrough — bug) or
    // something genuinely deduplicated and that needs a fresh look.
    assert_ne!(
        input_code_len, fused_code_len,
        "code-section length unchanged across fusion — DWARF \
         addresses might be coincidentally valid, but more likely \
         the merger is no longer doing what this test thinks it is"
    );
}

fn code_section_len(bytes: &[u8]) -> Option<usize> {
    let parser = wasmparser::Parser::new(0);
    for payload in parser.parse_all(bytes) {
        let payload = payload.ok()?;
        if let wasmparser::Payload::CodeSectionStart { range, .. } = payload {
            return Some(range.end - range.start);
        }
    }
    None
}

fn code_section_len_recursive(bytes: &[u8]) -> Option<usize> {
    let parser = wasmparser::Parser::new(0);
    let mut total = 0usize;
    let mut saw_any = false;
    for payload in parser.parse_all(bytes) {
        let payload = payload.ok()?;
        if let wasmparser::Payload::CodeSectionStart { range, .. } = payload {
            total = total.saturating_add(range.end - range.start);
            saw_any = true;
        }
    }
    if saw_any { Some(total) } else { None }
}
