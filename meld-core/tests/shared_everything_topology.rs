//! ADR-7 path-H inc 4 (#353) — static PIC / shared-everything flattening.
//!
//! BASELINE + FINDING. Against a real `wasm-tools component link` shared-everything
//! output (a PIC dylib with `(data (global.get $__memory_base) …)` linked so
//! `$main` owns+exports the memory and `$__init` imports it), current meld
//! (post ADR-7 inc 1–3) already:
//!   - models the instance-level memory sharing → the fused core has ONE memory
//!     (NOT the two the #353 spike observed on its fixture), and
//!   - folds `global.get $__memory_base` → `i32.const <base>` in globals/data via
//!     the #338 extended-const machinery, producing a VALID single core module.
//!
//! So the spike's "mints 2 memories / needs new topology modeling" premise does
//! not reproduce here. The one thing this cannot yet assert is end-to-end address
//! *correctness* (does the dylib's base-relative data read back right at runtime):
//! the linked component lifts no exports, so there is nothing to execute — exactly
//! the gap the spike flagged as "the one remaining verification". Closing it needs
//! a WIT-lifted executable PIC fixture. This test pins the structural baseline so
//! any regression to 2 memories / invalid output is caught meanwhile.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn base_config() -> FuserConfig {
    FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        reproducible: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    }
}

#[test]
fn shared_everything_fuses_to_valid_single_memory_core() {
    // Skip gracefully if the fixture isn't present (same convention as
    // nested_component.rs) so CI never breaks on a missing fixture.
    let Ok(component) = std::fs::read("../tests/pic-fixtures/shared_everything_linked.wasm") else {
        eprintln!("skipping: shared_everything_linked.wasm fixture not present");
        return;
    };
    let mut fuser = Fuser::new(base_config());
    fuser
        .add_component_named(&component, Some("shared-everything"))
        .unwrap();
    let (fused, _) = fuser
        .fuse_with_stats()
        .expect("shared-everything PIC component must fuse");

    // Structural baseline: exactly one memory (the shared-everything memory is
    // unified, not duplicated).
    let mut mems = 0;
    let mut has_base_folded_data = false;
    for p in wasmparser::Parser::new(0).parse_all(&fused) {
        match p {
            Ok(wasmparser::Payload::MemorySection(r)) => mems = r.count(),
            Ok(wasmparser::Payload::DataSection(r)) => {
                // At least one active data segment sits at the folded base
                // constant (0x100000), i.e. `global.get __memory_base` was
                // folded to an i32.const rather than left as an (invalid at
                // runtime) locally-defined global.get.
                for d in r.into_iter().flatten() {
                    if let wasmparser::DataKind::Active { offset_expr, .. } = d.kind {
                        let mut ops = offset_expr.get_operators_reader();
                        if let Ok(wasmparser::Operator::I32Const { value }) = ops.read() {
                            if value == 0x0010_0000 {
                                has_base_folded_data = true;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    assert_eq!(mems, 1, "shared-everything memory must be unified to one");
    assert!(
        has_base_folded_data,
        "expected a data segment folded to the base constant 0x100000 \
         (global.get __memory_base folded to i32.const)"
    );
    assert!(
        wasmparser::Validator::new().validate_all(&fused).is_ok(),
        "fused shared-everything core must validate"
    );
}
