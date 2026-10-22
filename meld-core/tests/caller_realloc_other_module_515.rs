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

// ---------------------------------------------------------------------------
// Which `canon lower` supplies the CALLER's realloc (Mythos finding on #515).
//
// The first cut picked the lower by component-function index / import name.
// `lower_options_by_func` keeps only the LAST lower of a function, and miscounts
// when a `canon lift` precedes the import, so with one import lowered twice the
// adapter for `$bx` allocated with `$my`'s realloc and `memory.copy`'d into
// `$mx`: live caller data corrupted at exit 0 (worse than the skipped copy).
// The lower is now found by tracing the calling module's actual import.
//
// `$bx` calls the lowering into `$mx` (sentinel `S` at 1024, allocator bump at
// 2048); `$by` calls the one into `$my` (bump at 1024 -- exactly the sentinel).
// Oracle for `run`: 'S' * 256 + 'h' = 21352. Any allocation from the wrong
// allocator overwrites the sentinel or lands in the wrong memory.
// ---------------------------------------------------------------------------

/// The same import lowered twice; the lowering `$bx` uses is the FIRST.
const DOUBLE_LOWER_Y_LAST: &str = r####"(component
  (component $A
    (core module $am
      (memory (export "mem") 1)
      (data (i32.const 16) "\40\00\00\00\05\00\00\00")
      (data (i32.const 64) "hello")
      (func (export "get") (result i32) i32.const 16))
    (core instance $ai (instantiate $am))
    (func (export "get") (result string)
      (canon lift (core func $ai "get") (memory (core memory $ai "mem")))))
  (component $B
    (import "get" (func $get (result string)))
    (core module $mx
      (memory (export "mem") 1)
      (data (i32.const 1024) "S")
      (global $bump (mut i32) (i32.const 2048))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r))
    (core module $my
      (memory (export "memy") 1)
      (global $bump (mut i32) (i32.const 1024))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r))
    (core instance $xi (instantiate $mx))
    (core instance $yi (instantiate $my))
    (core func $gx (canon lower (func $get)
      (memory (core memory $xi "mem"))
      (realloc (core func $xi "cabi_realloc"))))
    (core func $gy (canon lower (func $get)
      (memory (core memory $yi "memy"))
      (realloc (core func $yi "cabi_realloc"))))
    (core module $bx
      (import "env" "mem" (memory 1))
      (import "env" "get" (func $get (param i32)))
      (func (export "run") (result i32)
        (call $get (i32.const 128))
        ;; sentinel byte at 1024 must still be 'S'; plus first byte of string
        (i32.add
          (i32.mul (i32.load8_u (i32.const 1024)) (i32.const 256))
          (i32.load8_u (i32.load (i32.const 128))))))
    (core module $by
      (import "env" "mem" (memory 1))
      (import "env" "get" (func $get (param i32)))
      (func (export "run") (result i32)
        (call $get (i32.const 128))
        (i32.load8_u (i32.load (i32.const 128)))))
    (core instance $envx (export "mem" (memory $xi "mem")) (export "get" (func $gx)))
    (core instance $envy (export "mem" (memory $yi "memy")) (export "get" (func $gy)))
    (core instance $bxi (instantiate $bx (with "env" (instance $envx))))
    (core instance $byi (instantiate $by (with "env" (instance $envy))))
    (func (export "run") (result u32) (canon lift (core func $bxi "run")))
    (func (export "run2") (result u32) (canon lift (core func $byi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "get" (func $a "get"))))
  (export "run" (func $b "run"))
  (export "run2" (func $b "run2")))"####;
/// Control: the lowerings are declared in the other order.
const DOUBLE_LOWER_X_LAST: &str = r####"(component
  (component $A
    (core module $am
      (memory (export "mem") 1)
      (data (i32.const 16) "\40\00\00\00\05\00\00\00")
      (data (i32.const 64) "hello")
      (func (export "get") (result i32) i32.const 16))
    (core instance $ai (instantiate $am))
    (func (export "get") (result string)
      (canon lift (core func $ai "get") (memory (core memory $ai "mem")))))
  (component $B
    (import "get" (func $get (result string)))
    (core module $mx
      (memory (export "mem") 1)
      (data (i32.const 1024) "S")
      (global $bump (mut i32) (i32.const 2048))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r))
    (core module $my
      (memory (export "memy") 1)
      (global $bump (mut i32) (i32.const 1024))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r))
    (core instance $xi (instantiate $mx))
    (core instance $yi (instantiate $my))
    (core func $gy (canon lower (func $get)
      (memory (core memory $yi "memy"))
      (realloc (core func $yi "cabi_realloc"))))
    (core func $gx (canon lower (func $get)
      (memory (core memory $xi "mem"))
      (realloc (core func $xi "cabi_realloc"))))
    (core module $bx
      (import "env" "mem" (memory 1))
      (import "env" "get" (func $get (param i32)))
      (func (export "run") (result i32)
        (call $get (i32.const 128))
        ;; sentinel byte at 1024 must still be 'S'; plus first byte of string
        (i32.add
          (i32.mul (i32.load8_u (i32.const 1024)) (i32.const 256))
          (i32.load8_u (i32.load (i32.const 128))))))
    (core module $by
      (import "env" "mem" (memory 1))
      (import "env" "get" (func $get (param i32)))
      (func (export "run") (result i32)
        (call $get (i32.const 128))
        (i32.load8_u (i32.load (i32.const 128)))))
    (core instance $envx (export "mem" (memory $xi "mem")) (export "get" (func $gx)))
    (core instance $envy (export "mem" (memory $yi "memy")) (export "get" (func $gy)))
    (core instance $bxi (instantiate $bx (with "env" (instance $envx))))
    (core instance $byi (instantiate $by (with "env" (instance $envy))))
    (func (export "run") (result u32) (canon lift (core func $bxi "run")))
    (func (export "run2") (result u32) (canon lift (core func $byi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "get" (func $a "get"))))
  (export "run" (func $b "run"))
  (export "run2" (func $b "run2")))"####;
/// A `canon lift` precedes the lowered import in the function space.
const LIFT_BEFORE_IMPORT: &str = r####"(component
  (component $A
    (core module $am
      (memory (export "mem") 1)
      (data (i32.const 16) "\40\00\00\00\05\00\00\00")
      (data (i32.const 64) "hello")
      (func (export "get") (result i32) i32.const 16))
    (core instance $ai (instantiate $am))
    (func (export "get") (result string)
      (canon lift (core func $ai "get") (memory (core memory $ai "mem")))))
  (component $B
    (core module $my
      (memory (export "memy") 1)
      (data (i32.const 16) "\40\00\00\00\01\00\00\00")
      (data (i32.const 64) "z")
      (global $bump (mut i32) (i32.const 1024))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r)
      (func (export "f") (result i32) i32.const 16))
    (core instance $yi (instantiate $my))
    (func $f (result string)
      (canon lift (core func $yi "f") (memory (core memory $yi "memy"))))
    (import "get" (func $get (result string)))
    (core module $mx
      (memory (export "mem") 1)
      (data (i32.const 1024) "S")
      (global $bump (mut i32) (i32.const 2048))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r))
    (core instance $xi (instantiate $mx))
    (core func $fy (canon lower (func $f)
      (memory (core memory $yi "memy"))
      (realloc (core func $yi "cabi_realloc"))))
    (core func $gx (canon lower (func $get)
      (memory (core memory $xi "mem"))
      (realloc (core func $xi "cabi_realloc"))))
    (core module $bx
      (import "env" "mem" (memory 1))
      (import "env" "get" (func $get (param i32)))
      (func (export "run") (result i32)
        (call $get (i32.const 128))
        (i32.add
          (i32.mul (i32.load8_u (i32.const 1024)) (i32.const 256))
          (i32.load8_u (i32.load (i32.const 128))))))
    (core instance $envx (export "mem" (memory $xi "mem")) (export "get" (func $gx)))
    (core instance $bxi (instantiate $bx (with "env" (instance $envx))))
    (func (export "run") (result u32) (canon lift (core func $bxi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "get" (func $a "get"))))
  (export "run" (func $b "run")))
"####;

fn fuse_and_run_export(wat_text: &str, export: &str) -> u32 {
    let bytes = wat::parse_str(wat_text).expect("component text");
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    fuser
        .add_component_named(&bytes, Some("mythos515.wasm"))
        .expect("add");
    let fused = fuser.fuse().expect("fuse must succeed");
    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).expect("engine");
    let module = Module::new(&engine, &fused).expect("fused module must validate");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiate");
    instance
        .get_typed_func::<(), i32>(&mut store, export)
        .expect("export")
        .call(&mut store, ())
        .expect("must not trap") as u32
}

fn run_unfused_export(wat_text: &str, export: &str) -> u32 {
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    let engine = Engine::new(&cfg).unwrap();
    let bytes = wat::parse_str(wat_text).unwrap();
    let c = wasmtime::component::Component::new(&engine, &bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let linker = wasmtime::component::Linker::<()>::new(&engine);
    let inst = linker.instantiate(&mut store, &c).unwrap();
    let f = inst
        .get_typed_func::<(), (u32,)>(&mut store, export)
        .unwrap();
    f.call(&mut store, ()).unwrap().0
}

const SENTINEL_ANSWER: u32 = (b'S' as u32) * 256 + b'h' as u32;

// rivet: verifies SR-16
#[test]
fn double_lowered_import_uses_the_lowering_the_caller_imports() {
    assert_eq!(
        run_unfused_export(DOUBLE_LOWER_Y_LAST, "run"),
        SENTINEL_ANSWER,
        "oracle"
    );
    assert_eq!(
        fuse_and_run_export(DOUBLE_LOWER_Y_LAST, "run"),
        SENTINEL_ANSWER,
        "#515: `$bx` must allocate with `$mx`'s realloc into `$mx`'s memory"
    );
}

// rivet: verifies SR-16
#[test]
fn double_lowered_import_second_caller_uses_its_own_lowering() {
    // The fused core module exposes one component export, so export `$by`'s
    // `run` AS `run` instead (`$bx` is then never called).
    // Both modules export `run`; rename `$by`'s so the fused names stay distinct.
    let by_wat = DOUBLE_LOWER_Y_LAST
        .replace(
            "(func (export \"run\") (result i32)\n        (call $get (i32.const 128))\n        ;; sentinel",
            "(func (export \"runx\") (result i32)\n        (call $get (i32.const 128))\n        ;; sentinel",
        )
        .replace(
            "(func (export \"run\") (result i32)\n        (call $get (i32.const 128))\n        (i32.load8_u",
            "(func (export \"runy\") (result i32)\n        (call $get (i32.const 128))\n        (i32.load8_u",
        )
        .replace(
            r#"(func (export "run") (result u32) (canon lift (core func $bxi "run")))"#,
            r#"(func (export "run") (result u32) (canon lift (core func $byi "runy")))"#,
        )
        .replace(r#"(canon lift (core func $byi "run"))"#, r#"(canon lift (core func $byi "runy"))"#);
    assert_ne!(by_wat, DOUBLE_LOWER_Y_LAST, "fixture edit applied");
    assert_eq!(
        run_unfused_export(&by_wat, "run"),
        u32::from(b'h'),
        "oracle"
    );
    assert_eq!(
        fuse_and_run_export(&by_wat, "runy"),
        u32::from(b'h'),
        "#515: `$by` must allocate with `$my`'s realloc into `$my`'s memory"
    );
}

// rivet: verifies SR-16
#[test]
fn lift_before_import_does_not_shift_the_lower_attribution() {
    assert_eq!(
        run_unfused_export(LIFT_BEFORE_IMPORT, "run"),
        SENTINEL_ANSWER,
        "oracle"
    );
    assert_eq!(
        fuse_and_run_export(LIFT_BEFORE_IMPORT, "run"),
        SENTINEL_ANSWER,
        "#515: a canon lift before the import must not re-attribute the lower"
    );
}

// rivet: verifies SR-16
#[test]
fn double_lowered_import_declared_in_the_other_order_control() {
    assert_eq!(
        fuse_and_run_export(DOUBLE_LOWER_X_LAST, "run"),
        SENTINEL_ANSWER
    );
}
