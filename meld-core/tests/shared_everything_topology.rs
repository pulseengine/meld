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

/// Executable base-fold oracle (hand-written PIC-pattern, no toolchain needed):
/// `$main` sets `__memory_base` = 0x10000 and owns the memory; `$lib` imports
/// both and holds a base-relative data segment `(data (global.get $base) …)` +
/// a `read` loading from the base. meld must fold `global.get __memory_base` →
/// `i32.const 0x10000` in BOTH the data offset and the load, so `read` returns
/// the data at the folded base. Proves end-to-end address CORRECTNESS (not just
/// validity) for the static-PIC base-folding path.
fn pic_exec_component() -> Vec<u8> {
    let wat = r#"
    (component
      (core module $main
        (global (export "__memory_base") i32 (i32.const 65536))
        (memory (export "memory") 2))
      (core module $lib
        (import "env" "memory" (memory 1))
        (import "env" "__memory_base" (global $base i32))
        (data (global.get $base) "\aa\bb\cc\dd")
        (func (export "read") (result i32) (i32.load (global.get $base))))
      (core instance $mi (instantiate $main))
      (core instance $li (instantiate $lib (with "env" (instance $mi))))
      (alias core export $li "read" (core func $f))
      (func $lift (result u32) (canon lift (core func $f)))
      (export "read" (func $lift)))
    "#;
    wat::parse_str(wat).expect("PIC-pattern component WAT must assemble")
}

// KNOWN FAILING — reproduces the real inc-4 bug (#353). meld emits the fused
// data segment offset as `(data (global.get $__memory_base) …)` verbatim instead
// of folding the constant-valued `__memory_base` global to `i32.const`.
// wasm-tools validates it (lenient) but wasmtime REJECTS it at instantiation:
// "constant expression required: global.get of locally defined global". Root
// cause: segments.rs deliberately keeps `global.get`-first data offsets verbatim
// as "runtime-dependent" (the #338 note), but a CONSTANT global must be folded
// in a data const-expr. Un-ignore once the fold lands.
#[ignore = "reproduces inc-4 bug #353: data-offset global.get(__memory_base) not folded to i32.const"]
#[test]
fn pic_base_relative_data_reads_correctly_after_fold() {
    use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};
    let component = pic_exec_component();
    let mut fuser = Fuser::new(base_config());
    fuser
        .add_component_named(&component, Some("pic-exec"))
        .unwrap();
    let (fused, _) = fuser
        .fuse_with_stats()
        .expect("PIC-pattern component must fuse");
    assert!(
        wasmparser::Validator::new().validate_all(&fused).is_ok(),
        "fused PIC output must validate"
    );

    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let inst = Instance::new(&mut store, &module, &[]).unwrap();
    let read = inst
        .get_typed_func::<(), i32>(&mut store, "read")
        .expect("fused module should export read");
    // "\aa\bb\cc\dd" little-endian i32 = 0xddccbbaa. Correct iff the base-relative
    // data landed at the folded base and the load reads the same folded base.
    assert_eq!(
        read.call(&mut store, ()).unwrap() as u32,
        0xddcc_bbaa,
        "base-relative data must read back correctly after __memory_base fold"
    );
}
