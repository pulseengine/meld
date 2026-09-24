//! #400 — the fused module states how to invoke its exports.
//!
//! The manifest is only worth carrying if `core` and `wit` come from different
//! places: `wit` from the component's types, `core` **read back from the bytes
//! meld emitted**. Derived from one source they would agree by construction,
//! kiln's cross-check would always pass, and the field would be decoration.
//! `core_comes_from_the_module_not_the_wit` is the control for exactly that.

use meld_core::signature_manifest::{self, SignatureManifest};
use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn fixture() -> Option<Vec<u8>> {
    let path = format!(
        "{}/../tests/wit_bindgen/fixtures/compose_record_use_wide/composed_wide_use.wasm",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read(path).ok()
}

fn fuse_with_manifest(bytes: &[u8]) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        reproducible: true,
        signature_manifest: true,
        ..Default::default()
    });
    fuser
        .add_component_named(bytes, Some("composed_wide_use"))
        .expect("fixture parses");
    fuser.fuse().expect("fusion succeeds")
}

fn read_manifest(fused: &[u8]) -> Option<SignatureManifest> {
    for payload in wasmparser::Parser::new(0).parse_all(fused) {
        if let Ok(wasmparser::Payload::CustomSection(reader)) = payload
            && reader.name() == signature_manifest::SECTION_NAME
        {
            return Some(serde_json::from_slice(reader.data()).expect("manifest is valid JSON"));
        }
    }
    None
}

/// Every entry's `core` must equal the type the module actually exports, read
/// here by an independent parse rather than from the manifest's own source.
// rivet: verifies SR-80
#[test]
fn core_matches_the_emitted_module() {
    let Some(bytes) = fixture() else {
        panic!(
            "compose_record_use_wide fixture absent — skipping — every fixture a test reads is tracked in the repository \
             (SR-85); a missing one is a repository error, not a reason to report success"
        );
    };
    let fused = fuse_with_manifest(&bytes);
    let manifest = read_manifest(&fused).expect("the section is present");

    assert_eq!(manifest.version, signature_manifest::VERSION);
    assert!(
        manifest.exports.len() >= 2,
        "guard: the fixture has a wide lifted export and a runner; got {:?}",
        manifest
            .exports
            .iter()
            .map(|e| &e.export)
            .collect::<Vec<_>>()
    );
    assert!(
        manifest.omitted.is_empty(),
        "nothing should be unresolvable here: {:?}",
        manifest.omitted
    );

    let emitted = signature_manifest::emitted_exports(&fused);
    for entry in &manifest.exports {
        let actual = emitted
            .funcs
            .get(&entry.export)
            .unwrap_or_else(|| panic!("{} is exported", entry.export));
        assert_eq!(
            &entry.core, actual,
            "#400: `core` must be the emitted type for {}",
            entry.export
        );
    }
}

/// The control for the property above. If `core` were rendered from `wit`, a
/// two-parameter function of 14 + 4 floats would show 18 flat values. It shows
/// the single pointer the emitted module actually takes, which only the bytes
/// know — the WIT never mentions a pointer.
// rivet: verifies SR-80
#[test]
fn core_comes_from_the_module_not_the_wit() {
    let Some(bytes) = fixture() else {
        panic!(
            "compose_record_use_wide fixture absent — skipping — every fixture a test reads is tracked in the repository \
             (SR-85); a missing one is a repository error, not a reason to report success"
        );
    };
    let fused = fuse_with_manifest(&bytes);
    let manifest = read_manifest(&fused).expect("the section is present");

    let tick = manifest
        .exports
        .iter()
        .find(|e| e.export.ends_with("#tick"))
        .expect("the wide export is described");

    assert_eq!(tick.wit.params.len(), 2, "guard: two WIT parameters");
    assert_eq!(tick.flat_param_count, 18, "guard: 18 flattened values");
    assert_eq!(
        tick.core.params,
        vec!["i32".to_string()],
        "#400: `core` is what the module takes — one pointer — not a rendering \
         of the WIT, which would be 18 values"
    );
    assert!(
        !tick.wit.params.iter().any(|(_, t)| t.contains("i32")),
        "guard: the WIT side never mentions the core type the pointer shape uses"
    );

    // And an export the module does not have cannot acquire a `core` from the
    // WIT: reading a module with no exports yields nothing to describe.
    let empty = wasm_encoder::Module::new().finish();
    assert!(
        signature_manifest::emitted_exports(&empty).funcs.is_empty(),
        "guard: an export-less module yields no signatures"
    );
}

/// #423's shape, stated in the manifest: 18 flattened params is over the limit,
/// so the core signature is a single pointer and invoking it needs the guest's
/// allocator. A regression in the flat count shows up here as `flat_param_count`
/// disagreeing with a `core` of one `i32`.
// rivet: verifies SR-80
#[test]
fn a_wide_export_states_the_pointer_shape_and_its_allocator() {
    let Some(bytes) = fixture() else {
        panic!(
            "compose_record_use_wide fixture absent — skipping — every fixture a test reads is tracked in the repository \
             (SR-85); a missing one is a repository error, not a reason to report success"
        );
    };
    let fused = fuse_with_manifest(&bytes);
    let manifest = read_manifest(&fused).expect("the section is present");

    let tick = manifest
        .exports
        .iter()
        .find(|e| e.export.ends_with("#tick"))
        .expect("the wide export is described");

    assert_eq!(tick.flat_param_count, 18, "14 f32 + 4 f32 through `use`");
    assert_eq!(
        tick.core.params,
        vec!["i32".to_string()],
        "over MAX_FLAT_PARAMS the arguments travel through a pointer"
    );
    assert!(
        tick.needs.realloc,
        "the argument tuple is allocated by the guest"
    );
    assert!(tick.needs.memory);

    // Resolved through fusion, and it must really be an export of this module.
    let realloc = tick
        .realloc
        .as_ref()
        .expect("the provider's allocator survives fusion as an export");
    let emitted = signature_manifest::emitted_exports(&fused);
    assert!(
        emitted.func_indices.contains_key(realloc),
        "#400: `realloc` must name an export of this module, not a likely-looking name"
    );

    let area = tick
        .return_area
        .as_ref()
        .expect("a 4-field record is returned");
    assert_eq!((area.size, area.align), (16, 4));
    assert_eq!(
        area.layout
            .iter()
            .map(|l| (l.offset, l.field.as_str(), l.size))
            .collect::<Vec<_>>(),
        vec![(0, "o1", 4), (4, "o2", 4), (8, "o3", 4), (12, "o4", 4)]
    );
}

/// An export that needs nothing must say so, rather than naming a memory and an
/// allocator that a host would then call for no reason. Both branches are
/// present in this one fixture, so neither is asserted vacuously.
// rivet: verifies SR-80
#[test]
fn an_export_that_needs_nothing_names_nothing() {
    let Some(bytes) = fixture() else {
        panic!(
            "compose_record_use_wide fixture absent — skipping — every fixture a test reads is tracked in the repository \
             (SR-85); a missing one is a repository error, not a reason to report success"
        );
    };
    let fused = fuse_with_manifest(&bytes);
    let manifest = read_manifest(&fused).expect("the section is present");

    let run = manifest
        .exports
        .iter()
        .find(|e| e.export.ends_with("#run"))
        .expect("the runner is described");

    assert_eq!(run.flat_param_count, 0);
    assert!(!run.needs.memory && !run.needs.realloc);
    assert_eq!(run.memory, None);
    assert_eq!(run.realloc, None);
    assert_eq!(
        run.return_area, None,
        "one flat result is returned directly"
    );

    assert!(
        manifest.exports.iter().any(|e| e.needs.realloc),
        "guard: the fixture must also contain an export that DOES need one, or \
         this test passes vacuously"
    );
}

/// Found by the Mythos delta-pass on this change: the manifest named the FIRST
/// exported memory for every export. A multi-memory fusion exports one memory
/// per input component, so half the entries pointed a host at another
/// component's memory — the exact guess this manifest exists to remove. Each
/// export must name the memory ITS OWN lift uses, resolved through fusion.
// rivet: verifies SR-80
#[test]
fn each_export_names_its_own_memory() {
    let dir = format!(
        "{}/../tests/wit_bindgen/fixtures",
        env!("CARGO_MANIFEST_DIR")
    );
    let (Ok(wide), Ok(narrow)) = (
        std::fs::read(format!("{dir}/compose_record_use_wide/provider.wasm")),
        std::fs::read(format!("{dir}/compose_record_use/provider.wasm")),
    ) else {
        panic!(
            "provider fixtures absent — skipping — every fixture a test reads is tracked in the repository \
             (SR-85); a missing one is a repository error, not a reason to report success"
        );
    };

    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        reproducible: true,
        signature_manifest: true,
        ..Default::default()
    });
    fuser
        .add_component_named(&wide, Some("wide"))
        .expect("parses");
    fuser
        .add_component_named(&narrow, Some("narrow"))
        .expect("parses");
    let fused = fuser.fuse().expect("fusion succeeds");
    let manifest = read_manifest(&fused).expect("the section is present");
    let emitted = signature_manifest::emitted_exports(&fused);

    assert!(
        emitted.memories.len() >= 2,
        "guard: two components must contribute two memories, got {:?}",
        emitted.memories
    );

    let named: Vec<(&str, &str)> = manifest
        .exports
        .iter()
        .filter_map(|e| Some((e.export.as_str(), e.memory.as_deref()?)))
        .collect();
    assert!(
        named.len() >= 2,
        "guard: at least two exports must need a memory, got {named:?}"
    );
    for (export, memory) in &named {
        assert!(
            emitted.memories.contains_key(*memory),
            "{export} names `{memory}`, which this module does not export"
        );
    }
    assert!(
        named
            .iter()
            .map(|(_, m)| *m)
            .collect::<std::collections::BTreeSet<_>>()
            .len()
            >= 2,
        "#400: exports from different components must not all name one memory: {named:?}"
    );
}

/// Opt-in: a default fusion carries no manifest, so existing artifacts do not
/// change size.
// rivet: verifies SR-80
#[test]
fn the_section_is_absent_unless_asked_for() {
    let Some(bytes) = fixture() else {
        panic!(
            "compose_record_use_wide fixture absent — skipping — every fixture a test reads is tracked in the repository \
             (SR-85); a missing one is a repository error, not a reason to report success"
        );
    };
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        reproducible: true,
        ..Default::default()
    });
    fuser
        .add_component_named(&bytes, Some("composed_wide_use"))
        .expect("fixture parses");
    let fused = fuser.fuse().expect("fusion succeeds");

    assert!(
        read_manifest(&fused).is_none(),
        "#400: the manifest is opt-in"
    );
}
