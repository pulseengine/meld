//! #482 regression: a defined global's `ref.func` initialiser is converted before
//! the module's function indices are mapped, so it keeps the MODULE-LOCAL
//! index, which in the fused index space names another module's function.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasmtime::{Config, Engine, Instance, Module, Store};

fn component(global_init: bool) -> String {
    // A: run() calls the funcref it obtains either from a global initialised
    // with `ref.func $seven` or (control) from a `ref.func $seven` in the body.
    let a = if global_init {
        r#"(core module $A
            (type $t (func (result i32)))
            (memory (export "mem") 1)
            (table 1 funcref)
            (global $g funcref (ref.func $seven))
            (func $seven (result i32) i32.const 7)
            (func (export "run") (result i32)
              i32.const 0
              global.get $g
              table.set 0
              i32.const 0
              call_indirect (type $t)))"#
    } else {
        r#"(core module $A
            (type $t (func (result i32)))
            (memory (export "mem") 1)
            (table 1 funcref)
            (elem declare func $seven)
            (func $seven (result i32) i32.const 7)
            (func (export "run") (result i32)
              i32.const 0
              ref.func $seven
              table.set 0
              i32.const 0
              call_indirect (type $t)))"#
    };
    format!(
        r#"(component
          (core module $B
            (memory (export "mem") 1)
            (func (export "f") (result i32) i32.const 42))
          {a}
          (core instance $b (instantiate $B))
          (core instance $a (instantiate $A))
          (func (export "f") (result u32) (canon lift (core func $b "f")))
          (func (export "run") (result u32) (canon lift (core func $a "run"))))"#
    )
}

fn run_unfused(global_init: bool) -> u32 {
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    let engine = Engine::new(&cfg).unwrap();
    let bytes = wat::parse_str(component(global_init)).unwrap();
    let c = wasmtime::component::Component::new(&engine, &bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let linker = wasmtime::component::Linker::<()>::new(&engine);
    let inst = linker.instantiate(&mut store, &c).unwrap();
    let f = inst
        .get_typed_func::<(), (u32,)>(&mut store, "run")
        .unwrap();
    f.call(&mut store, ()).unwrap().0
}

fn run_fused(global_init: bool) -> i32 {
    let bytes = wat::parse_str(component(global_init)).expect("component text");
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component_named(&bytes, Some("poc.wasm")).unwrap();
    let fused = fuser.fuse().expect("fuse must succeed");
    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).unwrap();
    let module = Module::new(&engine, &fused).expect("fused module must validate");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiate");
    instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap()
        .call(&mut store, ())
        .expect("run must not trap")
}

#[test]
fn control_body_ref_func_matches_unfused() {
    assert_eq!(run_unfused(false), 7);
    assert_eq!(run_fused(false), 7);
}

#[test]
fn global_init_ref_func_matches_unfused() {
    assert_eq!(run_unfused(true), 7);
    assert_eq!(run_fused(true), 7, "fused diverges from unfused");
}
