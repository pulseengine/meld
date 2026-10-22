//! #515 — the adapter must take the caller's `realloc` from the `canon lower`
//! that names it, not from "the calling module's own `cabi_realloc`".
//!
//! When a component's allocator lives in a different core module than the
//! module that calls the adapted import, `merged.realloc_map` has no entry
//! for the CALLING module. The adapter's conditional result copy (an
//! `option<string>` / `result<string, _>` pointer pair) was gated on
//! `options.caller_realloc.is_some()` and was silently skipped: the caller
//! kept the callee's pointer, read its own memory at that address, and got the
//! wrong answer at exit 0.
//!
//! Layout of the fixture (`--memory multi`):
//!
//! * component `$A`: `get() -> option<string>` = `some("hello")`.
//! * component `$B`: module `$mm` owns the caller memory and `cabi_realloc`;
//!   module `$bm` (a DIFFERENT module) calls the lowered `get` and returns the
//!   first byte of the string it received.
//!
//! The `canon lower` names `$mm`'s memory and `$mm`'s realloc; `$bm` defines no
//! allocator. Oracle: the unfused component under wasmtime returns `'h'`.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasmtime::{Config, Engine, Instance, Module, Store};

/// `result_variant`: `false` = `option<string>`, `true` = `result<string, u32>`.
///
/// Component `$A` (the provider) exports `get`. Component `$B` (the caller)
/// lowers it into `$mm`'s memory with `$mm`'s `cabi_realloc`; the module that
/// actually CALLS the lowered function is `$bm`, which defines no allocator.
fn component(result_variant: bool) -> String {
    let (ty, disc_ok) = if result_variant {
        ("(result string (error u32))", 0)
    } else {
        ("(option string)", 1)
    };
    format!(
        r#"(component
  (component $A
    (core module $am
      (memory (export "mem") 1)
      (data (i32.const 16) "\{disc_ok:02x}\00\00\00\40\00\00\00\05\00\00\00")
      (data (i32.const 64) "hello")
      (func (export "get") (result i32) i32.const 16))
    (core instance $ai (instantiate $am))
    (func (export "get") (result {ty})
      (canon lift (core func $ai "get") (memory (core memory $ai "mem")))))
  (component $B
    (import "get" (func $get (result {ty})))
    (core module $mm
      (memory (export "mem") 1)
      (global $bump (mut i32) (i32.const 1024))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r))
    (core instance $mi (instantiate $mm))
    (core func $gl (canon lower (func $get)
      (memory (core memory $mi "mem"))
      (realloc (core func $mi "cabi_realloc"))))
    (core module $bm
      (import "env" "mem" (memory 1))
      (import "env" "get" (func $get (param i32)))
      (func (export "run") (result i32)
        (call $get (i32.const 128))
        (i32.load8_u (i32.load (i32.const 132)))))
    (core instance $env (export "mem" (memory $mi "mem")) (export "get" (func $gl)))
    (core instance $bi (instantiate $bm (with "env" (instance $env))))
    (func (export "run") (result u32) (canon lift (core func $bi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "get" (func $a "get"))))
  (export "run" (func $b "run")))"#
    )
}

fn run_unfused(wat: &str) -> u32 {
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    let engine = Engine::new(&cfg).unwrap();
    let bytes = wat::parse_str(wat).unwrap();
    let c = wasmtime::component::Component::new(&engine, &bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let linker = wasmtime::component::Linker::<()>::new(&engine);
    let inst = linker.instantiate(&mut store, &c).unwrap();
    let f = inst
        .get_typed_func::<(), (u32,)>(&mut store, "run")
        .unwrap();
    f.call(&mut store, ()).unwrap().0
}

fn fuse_and_run(result_variant: bool) -> i32 {
    let wat_text = component(result_variant);
    assert_eq!(
        run_unfused(&wat_text),
        u32::from(b'h'),
        "fixture sanity: the unfused component (the oracle)"
    );
    let bytes = wat::parse_str(&wat_text).expect("component text");
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    fuser
        .add_component_named(&bytes, Some("poc515.wasm"))
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

// rivet: verifies SR-16
#[test]
fn option_string_copied_when_realloc_is_in_another_module() {
    assert_eq!(
        fuse_and_run(false),
        i32::from(b'h'),
        "#515: the caller must receive a copy of the string in ITS memory"
    );
}

// rivet: verifies SR-16
#[test]
fn result_string_copied_when_realloc_is_in_another_module() {
    assert_eq!(
        fuse_and_run(true),
        i32::from(b'h'),
        "#515: the caller must receive a copy of the string in ITS memory"
    );
}
