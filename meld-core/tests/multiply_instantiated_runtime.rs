//! RFC-46 Q1 "duplicate" — differential EXECUTION oracle (ADR-7 path-H inc 3).
//!
//! The gating oracle for enabling multiply-instantiated-module support: fuse a
//! component that instantiates ONE core module TWICE, each holding a mutable
//! counter global, then execute the fused core module on wasmtime and assert the
//! two instances keep **independent** mutable state (STPA H-1). If duplication
//! silently shared state, `inc2()` would observe `inc1()`'s increments.
//!
//! Until the `core_instance_topology` normalization is wired into the fuse
//! pipeline, meld REJECTS this component (SR-31, `DuplicateModuleInstantiation`);
//! `baseline_currently_rejects` pins that pre-wiring behavior and doubles as a
//! check that the fixture is a genuine multiply-instantiated component.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

/// A component with a single core module (a mutable counter + `inc`), instantiated
/// twice, whose two instances' `inc` are lifted as component exports `inc1`/`inc2`.
fn multiply_instantiated_component() -> Vec<u8> {
    let wat = r#"
    (component
      (core module $m
        (global $ctr (mut i32) (i32.const 0))
        (func $inc (result i32)
          global.get $ctr
          i32.const 1
          i32.add
          global.set $ctr
          global.get $ctr)
        (export "inc" (func $inc)))
      (core instance $i1 (instantiate $m))
      (core instance $i2 (instantiate $m))
      (alias core export $i1 "inc" (core func $f1))
      (alias core export $i2 "inc" (core func $f2))
      (func $lift1 (result u32) (canon lift (core func $f1)))
      (func $lift2 (result u32) (canon lift (core func $f2)))
      (export "inc1" (func $lift1))
      (export "inc2" (func $lift2)))
    "#;
    wat::parse_str(wat).expect("multiply-instantiated component WAT must assemble")
}

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

/// The differential execution oracle: fuse the multiply-instantiated component
/// and prove the two instances keep INDEPENDENT mutable counter state.
///
/// Each `inc()` returns the post-increment counter. Interleaving the two exports:
///   inc1 → 1, inc1 → 2, inc2 → 1, inc1 → 3, inc2 → 2
/// Independent state gives 1,2,1,3,2. **Shared** state (the H-1 corruption this
/// feature must avoid) would give 1,2,3,4,5 — so the load-bearing assertion is
/// that `inc2`'s FIRST call returns 1, not 3.
#[test]
fn two_instances_keep_independent_counter_state() {
    use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};

    let component = multiply_instantiated_component();
    let mut fuser = Fuser::new(base_config());
    fuser
        .add_component_named(&component, Some("multiply-instantiated"))
        .unwrap();
    let (fused, _stats) = fuser
        .fuse_with_stats()
        .expect("multiply-instantiated module must now fuse (RFC-46 Q1 duplicate support)");

    // Fused output must be a valid core module.
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("fused multiply-instantiated output should validate");

    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);
    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // The two instances both export the core name `inc`; meld disambiguates the
    // second instance's export with a `$0` suffix (identical-name dedup). These
    // are two DISTINCT merged functions over two DISTINCT counter globals.
    let inc1 = instance
        .get_typed_func::<(), i32>(&mut store, "inc")
        .expect("fused module should export inc (instance 1)");
    let inc2 = instance
        .get_typed_func::<(), i32>(&mut store, "inc$0")
        .expect("fused module should export inc$0 (instance 2)");

    assert_eq!(inc1.call(&mut store, ()).unwrap(), 1, "inc1 #1");
    assert_eq!(inc1.call(&mut store, ()).unwrap(), 2, "inc1 #2");
    assert_eq!(
        inc2.call(&mut store, ()).unwrap(),
        1,
        "inc2's FIRST call must be 1 — independent state; a 3 here means the two \
         instances share the counter global (H-1 corruption)"
    );
    assert_eq!(inc1.call(&mut store, ()).unwrap(), 3, "inc1 #3");
    assert_eq!(inc2.call(&mut store, ()).unwrap(), 2, "inc2 #2");
}
