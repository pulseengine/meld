//! #515 round 2: which `canon lower`/`canon lift` supplies the allocator, and
//! that its MEMORY and REALLOC always come from the same option set.
//!
//! Every behavioural test compares the fused core module (`--memory multi`)
//! with the unfused component under wasmtime. Where refusal is the specification
//! (the call site cannot be attributed to one lowering) the test asserts a loud
//! `#515` fusion error instead of a value.
//!
//! | test                         | shape                                              | spec    |
//! |------------------------------|----------------------------------------------------|---------|
//! | lead1                        | two imports of one func, both traced, DISAGREE     | refuse  |
//! | lead1_single                 | same, only the called import                       | oracle  |
//! | lead2b_control               | called import untraced (shim), ONE lowering        | oracle  |
//! | lead3                        | called import untraced, sibling traced, no own realloc | refuse |
//! | poc1                         | calling module has no memory                       | oracle  |
//! | poc2 / poc2b                 | lower names memory 1, module memory 0 is another   | oracle  |

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasmtime::{Config, Engine, Instance, Module, Store};

const PROVIDER: &str = r#"(component $A
    (core module $am
      (memory (export "mem") 1)
      (data (i32.const 16) "\40\00\00\00\05\00\00\00")
      (data (i32.const 64) "hello")
      (func (export "get") (result i32) i32.const 16))
    (core instance $ai (instantiate $am))
    (func (export "get") (result string)
      (canon lift (core func $ai "get") (memory (core memory $ai "mem")))))"#;

const MX_MY: &str = r#"(core module $mx
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
      (global $bump (mut i32) (i32.const 4096))
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
      (realloc (core func $yi "cabi_realloc"))))"#;

/// `$bx` body shared by the PoCs: calls env.get, returns sentinel*256 + first byte.
/// `$bx` ALSO exports its own `cabi_realloc` that returns the sentinel address
/// 1024 -- the unfused component never calls it (no canon option names it).
const BX_BODY: &str = r#"(func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        i32.const 1024)
      (func (export "run") (result i32)
        (call $get (i32.const 128))
        (i32.add
          (i32.mul (i32.load8_u (i32.const 1024)) (i32.const 256))
          (i32.load8_u (i32.load (i32.const 128)))))"#;

/// Lead 1: `$bx` imports `get` from TWO bags (`env` -> $gx, `envy` -> $gy).
/// It only calls `env.get`. The secondary site collects both imports, the
/// trace disagrees -> None -> `realloc_map[(B,$bx)]` = `$bx`'s own
/// `cabi_realloc` (name-based) -> returns 1024 = sentinel.
fn lead1() -> String {
    format!(
        r#"(component
  {PROVIDER}
  (component $B
    (import "get" (func $get (result string)))
    {MX_MY}
    (core module $bx
      (import "env" "mem" (memory 1))
      (import "env" "get" (func $get (param i32)))
      (import "envy" "get" (func $gety (param i32)))
      {BX_BODY})
    (core instance $envx (export "mem" (memory $xi "mem")) (export "get" (func $gx)))
    (core instance $envy (export "get" (func $gy)))
    (core instance $bxi (instantiate $bx (with "env" (instance $envx)) (with "envy" (instance $envy))))
    (func (export "run") (result u32) (canon lift (core func $bxi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "get" (func $a "get"))))
  (export "run" (func $b "run")))"#
    )
}

/// Lead 2: `$bx`'s single import is routed through an instantiated module `$s`
/// that imports `$gx` and re-exports it (untraced: `bags.get(src)` is None).
/// Unanimity over {$gx: Rx, $gy: Ry} fails -> None -> realloc_map fallback.
fn lead2() -> String {
    format!(
        r#"(component
  {PROVIDER}
  (component $B
    (import "get" (func $get (result string)))
    {MX_MY}
    (core module $s
      (import "in" "mem" (memory 1))
      (import "in" "get" (func $g (param i32)))
      (export "mem" (memory 0))
      (export "get" (func $g)))
    (core instance $envx (export "mem" (memory $xi "mem")) (export "get" (func $gx)))
    (core instance $si (instantiate $s (with "in" (instance $envx))))
    (core module $bx
      (import "env" "mem" (memory 1))
      (import "env" "get" (func $get (param i32)))
      {BX_BODY})
    (core instance $bxi (instantiate $bx (with "env" (instance $si))))
    (core instance $envy (export "get" (func $gy)))
    (func (export "run") (result u32) (canon lift (core func $bxi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "get" (func $a "get"))))
  (export "run" (func $b "run")))"#
    )
}

/// Lead 2b: like Lead 2 but `$s` re-exports only the function (memory comes
/// straight from the bag), avoiding the unrelated duplicate-export bug.
fn lead2b() -> String {
    lead2()
        .replace("      (import \"in\" \"mem\" (memory 1))\n", "")
        .replace("      (export \"mem\" (memory 0))\n", "")
        .replace(
            "(import \"env\" \"mem\" (memory 1))",
            "(import \"m\" \"mem\" (memory 1))",
        )
        .replace(
            "(with \"env\" (instance $si))",
            "(with \"m\" (instance $envx)) (with \"env\" (instance $si))",
        )
}

/// Lead 3 (no realloc_map involvement): `$bx` has NO own allocator. Its CALLED
/// import `env.get` is untraced (routed via `$s`), a second, never-called
/// import `envy.get` traces to `$gy`. The traced subset is unanimous on Ry, so
/// the trace returns Ry for `$bx`'s adapter. `$my`'s bump starts at 1024, the
/// sentinel address in `$mx`'s memory.
fn lead3() -> String {
    let w = lead2b()
        .replace("(global $bump (mut i32) (i32.const 4096))", "(global $bump (mut i32) (i32.const 1024))")
        .replace("(func (export \"cabi_realloc\") (param i32 i32 i32 i32) (result i32)\n        i32.const 1024)", "")
        .replace("      (import \"env\" \"get\" (func $get (param i32)))\n",
                 "      (import \"env\" \"get\" (func $get (param i32)))\n      (import \"envy\" \"get\" (func $gety (param i32)))\n")
        .replace("(with \"env\" (instance $si)))", "(with \"env\" (instance $si)) (with \"envy\" (instance $envy)))");
    // $envy must be defined before $bxi: move it.
    let w = w.replace(
        "    (core instance $envy (export \"get\" (func $gy)))\n",
        "",
    );
    w.replace(
        "    (core instance $bxi",
        "    (core instance $envy (export \"get\" (func $gy)))\n    (core instance $bxi",
    )
}

/// PoC-1: the CALLING module ($bm) has no memory of its own. analyze_call_site
/// leaves caller_memory at the default 0, which is the CALLEE's fused memory, so
/// the cross-memory string param is never copied (and the #515 gate is skipped
/// by its own `caller_memory == callee_memory` early return).
const POC1: &str = r#"(component
  (component $A
    (core module $am
      (memory (export "mem") 1)
      (data (i32.const 200) "Z")
      (global $bump (mut i32) (i32.const 1024))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r)
      (func (export "first") (param i32 i32) (result i32)
        (i32.load8_u (local.get 0))))
    (core instance $ai (instantiate $am))
    (func (export "first") (param "s" string) (result u32)
      (canon lift (core func $ai "first") (memory (core memory $ai "mem"))
        (realloc (core func $ai "cabi_realloc")))))
  (component $B
    (import "first" (func $first (param "s" string) (result u32)))
    (core module $mm
      (memory (export "mem") 1)
      (data (i32.const 200) "hello")
      (global $bump (mut i32) (i32.const 1024))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r))
    (core instance $mi (instantiate $mm))
    (core func $fl (canon lower (func $first)
      (memory (core memory $mi "mem"))
      (realloc (core func $mi "cabi_realloc"))))
    (core module $bm
      (import "env" "first" (func $first (param i32 i32) (result i32)))
      (func (export "run") (result i32)
        (call $first (i32.const 200) (i32.const 5))))
    (core instance $env (export "first" (func $fl)))
    (core instance $bi (instantiate $bm (with "env" (instance $env))))
    (func (export "run") (result u32) (canon lift (core func $bi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "first" (func $a "first"))))
  (export "run" (func $b "run")))"#;

/// PoC-2: the calling module's memory 0 is NOT the memory the `canon lower`
/// names. $bm imports $om's memory as its memory 0 and $mm's memory as memory 1;
/// the lower names $mm's memory + $mm's realloc. The branch allocates with $mm's
/// realloc (traced) but writes into caller_memory = $om's memory.
const POC2: &str = r#"(component
  (component $A
    (core module $am
      (memory (export "mem") 1)
      (data (i32.const 16) "\01\00\00\00\40\00\00\00\05\00\00\00")
      (data (i32.const 64) "hello")
      (func (export "get") (result i32) i32.const 16))
    (core instance $ai (instantiate $am))
    (func (export "get") (result (option string))
      (canon lift (core func $ai "get") (memory (core memory $ai "mem")))))
  (component $B
    (import "get" (func $get (result (option string))))
    (core module $om
      (memory (export "omem") 1)
      (global $bump (mut i32) (i32.const 4096))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r))
    (core module $mm
      (memory (export "mem") 1)
      (global $bump (mut i32) (i32.const 1024))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r))
    (core instance $oi (instantiate $om))
    (core instance $mi (instantiate $mm))
    (core func $gl (canon lower (func $get)
      (memory (core memory $mi "mem"))
      (realloc (core func $mi "cabi_realloc"))))
    (core module $bm
      (import "o" "mem" (memory $o 1))
      (import "env" "mem" (memory $m 1))
      (import "env" "get" (func $get (param i32)))
      (func (export "run") (result i32)
        (call $get (i32.const 128))
        (i32.load8_u $m (i32.load $m (i32.const 132)))))
    (core instance $oenv (export "mem" (memory $oi "omem")))
    (core instance $env (export "mem" (memory $mi "mem")) (export "get" (func $gl)))
    (core instance $bi (instantiate $bm (with "o" (instance $oenv)) (with "env" (instance $env))))
    (func (export "run") (result u32) (canon lift (core func $bi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "get" (func $a "get"))))
  (export "run" (func $b "run")))"#;

/// PoC-2b: sentinel in $om's memory. A correct fusion never writes $om.
const POC2B: &str = r#"(component
  (component $A
    (core module $am
      (memory (export "mem") 1)
      (data (i32.const 16) "\01\00\00\00\40\00\00\00\05\00\00\00")
      (data (i32.const 64) "hello")
      (func (export "get") (result i32) i32.const 16))
    (core instance $ai (instantiate $am))
    (func (export "get") (result (option string))
      (canon lift (core func $ai "get") (memory (core memory $ai "mem")))))
  (component $B
    (import "get" (func $get (result (option string))))
    (core module $om
      (memory (export "omem") 1)
      (data (i32.const 1024) "S")
      (global $bump (mut i32) (i32.const 4096))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r))
    (core module $mm
      (memory (export "mem") 1)
      (global $bump (mut i32) (i32.const 1024))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r))
    (core instance $oi (instantiate $om))
    (core instance $mi (instantiate $mm))
    (core func $gl (canon lower (func $get)
      (memory (core memory $mi "mem"))
      (realloc (core func $mi "cabi_realloc"))))
    (core module $bm
      (import "o" "mem" (memory $o 1))
      (import "env" "mem" (memory $m 1))
      (import "env" "get" (func $get (param i32)))
      (func (export "run") (result i32)
        (call $get (i32.const 128))
        (i32.load8_u $o (i32.const 1024))))
    (core instance $oenv (export "mem" (memory $oi "omem")))
    (core instance $env (export "mem" (memory $mi "mem")) (export "get" (func $gl)))
    (core instance $bi (instantiate $bm (with "o" (instance $oenv)) (with "env" (instance $env))))
    (func (export "run") (result u32) (canon lift (core func $bi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "get" (func $a "get"))))
  (export "run" (func $b "run")))"#;

fn run_unfused(wat_text: &str) -> u32 {
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).unwrap();
    let bytes = wat::parse_str(wat_text).unwrap();
    let c = wasmtime::component::Component::new(&engine, &bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let linker = wasmtime::component::Linker::<()>::new(&engine);
    let inst = linker.instantiate(&mut store, &c).unwrap();
    let f = inst
        .get_typed_func::<(), (u32,)>(&mut store, "run")
        .unwrap();
    f.call(&mut store, ()).unwrap().0
}

fn fuse(wat_text: &str) -> Result<Vec<u8>, String> {
    let bytes = wat::parse_str(wat_text).expect("component text");
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    fuser
        .add_component_named(&bytes, Some("m515r2.wasm"))
        .map_err(|e| e.to_string())?;
    fuser.fuse().map_err(|e| e.to_string())
}

fn run_fused(fused: &[u8]) -> u32 {
    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).unwrap();
    let module = Module::new(&engine, fused).expect("fused module validates");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiate");
    instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("run export")
        .call(&mut store, ())
        .expect("must not trap") as u32
}

/// Fused result must equal the unfused oracle (and `expect`, pinning the oracle).
fn assert_oracle(wat_text: &str, expect: u32) {
    let oracle = run_unfused(wat_text);
    assert_eq!(oracle, expect, "fixture sanity: the oracle");
    let fused = fuse(wat_text).expect("fusion must succeed");
    assert_eq!(run_fused(&fused), oracle, "fused diverges from the oracle");
}

/// Fusion must REFUSE with a #515 error (never emit a module).
fn assert_refused(wat_text: &str) {
    match fuse(wat_text) {
        Err(e) => assert!(e.contains("#515"), "refused, but not by the #515 gate: {e}"),
        Ok(bytes) => panic!(
            "#515: ambiguous call site fused at exit 0; it returns {} (oracle {})",
            run_fused(&bytes),
            run_unfused(wat_text)
        ),
    }
}

const SENTINEL_ANSWER: u32 = (b'S' as u32) * 256 + b'h' as u32;

// rivet: verifies SR-16
#[test]
fn lead1_traced_imports_that_disagree_are_refused() {
    assert_refused(&lead1());
}

// rivet: verifies SR-16
#[test]
fn lead1_single_import_trace_wins_over_own_realloc() {
    let w = lead1()
        .replace(
            "      (import \"envy\" \"get\" (func $gety (param i32)))\n",
            "",
        )
        .replace(" (with \"envy\" (instance $envy))", "");
    assert!(!w.contains("\"envy\" \"get\""));
    assert_oracle(&w, SENTINEL_ANSWER);
}

// rivet: verifies SR-16
#[test]
fn lead2b_control_single_lowering_untraced_import() {
    let w = lead2b()
        .replace("    (core func $gy (canon lower (func $get)\n      (memory (core memory $yi \"memy\"))\n      (realloc (core func $yi \"cabi_realloc\"))))", "")
        .replace("    (core instance $envy (export \"get\" (func $gy)))\n", "");
    assert!(!w.contains("$gy"));
    assert_oracle(&w, SENTINEL_ANSWER);
}

// rivet: verifies SR-16
#[test]
fn lead3_traced_sibling_must_not_decide_an_untraced_call() {
    let w = lead3();
    assert!(w.contains("(with \"envy\"") && !w.contains("i32.const 4096"));
    assert_refused(&w);
}

// rivet: verifies SR-16
#[test]
fn poc1_calling_module_without_memory_copies_into_the_lowers_memory() {
    assert_oracle(POC1, 104);
}

// rivet: verifies SR-16
#[test]
fn poc2_lower_memory_is_not_the_calling_modules_memory_0() {
    assert_oracle(POC2, 104);
}

// rivet: verifies SR-16
#[test]
fn poc2b_traced_realloc_never_writes_the_other_memory() {
    // Sentinel `S` (83) in `$om`'s memory must survive.
    assert_oracle(POC2B, 83);
}
