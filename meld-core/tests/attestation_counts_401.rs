//! #401 — the attestation must report a number the caller can check.
//!
//! `components_fused` read the FLATTENED component list, which gains an entry
//! per nested sub-component: five input files were attested as ten components.
//! v0.55.0 corrected the console line (`Fusing N components...`) but not this,
//! so for one run the tool printed one number and shipped another.
//!
//! As the reporter put it, the two disagreeing is worse than both being wrong:
//! it reads as two independent facts rather than one number and one bug. The
//! attestation is the half that travels with the artifact and that an auditor
//! reasons from, so it is the half that had to be right.
//!
//! `modules_merged` already carries the internal structure and was correct
//! throughout — the two fields answer different questions and are pinned here
//! as distinct on purpose.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn fixture() -> Option<Vec<u8>> {
    let path = format!(
        "{}/../tests/wit_bindgen/fixtures/compose_record_use/composed_record_use.wasm",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read(path).ok()
}

/// What the attestation says must equal what the caller passed — and what the
/// CLI printed, which reports `input_count()`.
// rivet: verifies SR-74
#[test]
fn components_fused_counts_inputs_not_flattened_components() {
    let Some(bytes) = fixture() else {
        eprintln!("compose_record_use fixture absent — skipping");
        return;
    };
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        reproducible: true,
        ..Default::default()
    });
    fuser
        .add_component_named(&bytes, Some("composed"))
        .expect("add");

    let inputs = fuser.input_count();
    let flattened = fuser.component_count();
    let (_out, stats) = fuser.fuse_with_stats().expect("fusion");

    assert_eq!(
        stats.components_fused, inputs,
        "#401: the attestation must report the components the caller fused ({inputs}), \
         not the flattened list ({flattened}) — the console reports the former, and a \
         run that prints one number and ships another reads as two independent facts"
    );

    // The fixture nests, so this is a real distinction rather than a tautology:
    // if flattening ever stopped adding entries, this test would still pass
    // above while proving nothing, and this assert says so out loud.
    assert!(
        flattened > inputs,
        "#401: this fixture must actually nest, or the assertion above is vacuous \
         (inputs={inputs}, flattened={flattened})"
    );
}

/// `modules_merged` answers a different question and must not be collapsed into
/// the one above. It was correct throughout and stays independent.
// rivet: verifies SR-74
#[test]
fn modules_merged_is_independent_of_the_input_count() {
    let Some(bytes) = fixture() else {
        eprintln!("compose_record_use fixture absent — skipping");
        return;
    };
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        reproducible: true,
        ..Default::default()
    });
    fuser
        .add_component_named(&bytes, Some("composed"))
        .expect("add");
    let (_out, stats) = fuser.fuse_with_stats().expect("fusion");

    assert!(
        stats.modules_merged >= stats.components_fused,
        "one input contributes at least one core module (merged={}, fused={})",
        stats.modules_merged,
        stats.components_fused
    );
}
