//! #462 (Mythos delta-pass on PR #477): an intra-component import promoted to
//! an `AdapterSite` must still order the provider module before the importer.
//!
//! The resolver REMOVES the promoted `module_resolutions` entry, and merge
//! order was computed from `module_resolutions` alone, so an importer defined
//! BEFORE its provider was merged first: its import was unmapped at merge time
//! (a `call` became `Error::UnmappedFunctionImport`; an elem slot held a stub
//! or, before #462, the identity index, i.e. `run` itself).
//!
//! All three variants must return 42 at run time, as the unfused component
//! does. The provider-first variant is the control.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasmtime::{Config, Engine, Instance, Module, Store};

/// `importer_first`: module A (the importer) precedes module B (the provider).
/// `elem`: A reaches `$f` through a table slot instead of a direct `call`.
fn component(importer_first: bool, elem: bool) -> String {
    let importer = if elem {
        r#"(core module $A
            (type $t (func (result i32)))
            (import "b" "f" (func $f (result i32)))
            (memory (export "mem") 1)
            (table 1 funcref)
            (elem (i32.const 0) func $f)
            (func (export "run") (result i32)
              i32.const 0
              call_indirect (type $t)))"#
    } else {
        r#"(core module $A
            (import "b" "f" (func $f (result i32)))
            (memory (export "mem") 1)
            (func (export "run") (result i32) call $f))"#
    };
    let provider = r#"(core module $B
            (memory (export "mem") 1)
            (func (export "f") (result i32) i32.const 42))"#;
    let modules = if importer_first {
        format!("{importer}\n{provider}")
    } else {
        format!("{provider}\n{importer}")
    };
    format!(
        r#"(component
          {modules}
          (core instance $b (instantiate $B))
          (alias core export $b "f" (core func $lf))
          (core instance $fi (export "f" (func $lf)))
          (core instance $a (instantiate $A (with "b" (instance $fi))))
          (func (export "run") (result u32) (canon lift (core func $a "run"))))"#
    )
}

fn fuse_and_run(importer_first: bool, elem: bool) -> i32 {
    let bytes = wat::parse_str(component(importer_first, elem)).expect("component text");
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    fuser
        .add_component_named(&bytes, Some("poc.wasm"))
        .expect("add");
    let fused = fuser.fuse().expect("fuse must succeed");

    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).expect("engine");
    let module = Module::new(&engine, &fused).expect("fused module must validate");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiate");
    instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("run export")
        .call(&mut store, ())
        .expect("run must not trap")
}

#[test]
fn provider_first_control_returns_42() {
    assert_eq!(fuse_and_run(false, false), 42);
}

#[test]
fn importer_first_call_returns_42() {
    assert_eq!(fuse_and_run(true, false), 42);
}

#[test]
fn importer_first_elem_slot_returns_42() {
    assert_eq!(fuse_and_run(true, true), 42);
}
