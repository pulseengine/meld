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

const BUMP: &str = r#"(global $bump (mut i32) (i32.const BUMPSTART))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r)"#;
fn bump(start: u32) -> String {
    BUMP.replace("BUMPSTART", &start.to_string())
}

// P2: callee lift names memory 1 of its module, memory-only (result string).
fn p2() -> String {
    format!(
        r#"(component
  (component $A
    (core module $am
      (memory $m0 (export "m0") 1)
      (memory $m1 (export "m1") 1)
      (data (memory $m0) (i32.const 16) "\40\00\00\00\05\00\00\00")
      (data (memory $m0) (i32.const 64) "WRONG")
      (data (memory $m1) (i32.const 16) "\40\00\00\00\05\00\00\00")
      (data (memory $m1) (i32.const 64) "hello")
      (func (export "get") (result i32) i32.const 16))
    (core instance $ai (instantiate $am))
    (func (export "get") (result string)
      (canon lift (core func $ai "get") (memory (core memory $ai "m1")))))
  (component $B
    (import "get" (func $get (result string)))
    (core module $mx
      (memory (export "mem") 1)
      {mx})
    (core instance $xi (instantiate $mx))
    (core func $gx (canon lower (func $get)
      (memory (core memory $xi "mem"))
      (realloc (core func $xi "cabi_realloc"))))
    (core module $bx
      (import "env" "mem" (memory 1))
      (import "env" "get" (func $get (param i32)))
      (func (export "run") (result i32)
        (call $get (i32.const 128))
        (i32.load8_u (i32.load (i32.const 128)))))
    (core instance $envx (export "mem" (memory $xi "mem")) (export "get" (func $gx)))
    (core instance $bxi (instantiate $bx (with "env" (instance $envx))))
    (func (export "run") (result u32) (canon lift (core func $bxi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "get" (func $a "get"))))
  (export "run" (func $b "run")))"#,
        mx = bump(1024)
    )
}

// P4: caller lower is memory-only (string PARAM, no realloc needed) and names
// memory 1 of the calling module ($bx mem0 = $om's, mem1 = $mm's).
fn p4() -> String {
    format!(
        r#"(component
  (component $A
    (core module $am
      (memory (export "mem") 1)
      {am}
      (func (export "first") (param i32 i32) (result i32)
        (i32.load8_u (local.get 0))))
    (core instance $ai (instantiate $am))
    (func (export "first") (param "s" string) (result u32)
      (canon lift (core func $ai "first") (memory (core memory $ai "mem"))
        (realloc (core func $ai "cabi_realloc")))))
  (component $B
    (import "first" (func $first (param "s" string) (result u32)))
    (core module $om (memory (export "omem") 1) (data (i32.const 200) "WRONG"))
    (core module $mm (memory (export "mem") 1) (data (i32.const 200) "hello"))
    (core instance $oi (instantiate $om))
    (core instance $mi (instantiate $mm))
    (core func $fl (canon lower (func $first) (memory (core memory $mi "mem"))))
    (core module $bm
      (import "o" "mem" (memory $o 1))
      (import "env" "mem" (memory $m 1))
      (import "env" "first" (func $first (param i32 i32) (result i32)))
      (func (export "run") (result i32)
        (call $first (i32.const 200) (i32.const 5))))
    (core instance $oenv (export "mem" (memory $oi "omem")))
    (core instance $env (export "mem" (memory $mi "mem")) (export "first" (func $fl)))
    (core instance $bi (instantiate $bm (with "o" (instance $oenv)) (with "env" (instance $env))))
    (func (export "run") (result u32) (canon lift (core func $bi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "first" (func $a "first"))))
  (export "run" (func $b "run")))"#,
        am = bump(1024)
    )
}

// P5: the SAME component func `get` lowered twice with IDENTICAL options, each
// written with its own inline alias (so different raw core memory/func
// indices for the same memory and realloc). $bx imports both, calls env.get.
fn p5(own_alloc: bool) -> String {
    let own = if own_alloc {
        r#"(global $ob (mut i32) (i32.const 8192))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $ob local.set $r
        global.get $ob local.get 3 i32.add global.set $ob
        local.get $r)"#
    } else {
        ""
    };
    format!(
        r#"(component
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
      {mx})
    (core instance $xi (instantiate $mx))
    (core func $gx (canon lower (func $get)
      (memory (core memory $xi "mem"))
      (realloc (core func $xi "cabi_realloc"))))
    (core func $gy (canon lower (func $get)
      (memory (core memory $xi "mem"))
      (realloc (core func $xi "cabi_realloc"))))
    (core module $bx
      (import "env" "mem" (memory 1))
      (import "env" "get" (func $get (param i32)))
      (import "envy" "get" (func $gety (param i32)))
      {own}
      (func (export "run") (result i32)
        (call $get (i32.const 128))
        (i32.load8_u (i32.load (i32.const 128)))))
    (core instance $envx (export "mem" (memory $xi "mem")) (export "get" (func $gx)))
    (core instance $envy (export "get" (func $gy)))
    (core instance $bxi (instantiate $bx (with "env" (instance $envx)) (with "envy" (instance $envy))))
    (func (export "run") (result u32) (canon lift (core func $bxi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "get" (func $a "get"))))
  (export "run" (func $b "run")))"#,
        mx = bump(1024),
        own = own
    )
}

fn p5_ptr(own: bool) -> String {
    p5(own).replace(
        "(i32.load8_u (i32.load (i32.const 128)))))\n    (core instance $envx",
        "(i32.load (i32.const 128))))\n    (core instance $envx",
    )
}

/// Caller module `$bm` has NO memory; its component has `$mm` with one.
const CALLER_MEMLESS: &str = r#"(component
  (component $A
    (core module $am
      (memory (export "mem") 1)
      (func (export "add") (param i32) (result i32) local.get 0 i32.const 40 i32.add))
    (core instance $ai (instantiate $am))
    (func (export "add") (param "x" u32) (result u32) (canon lift (core func $ai "add"))))
  (component $B
    (import "add" (func $add (param "x" u32) (result u32)))
    (core module $mm (memory (export "mem") 1))
    (core instance $mi (instantiate $mm))
    (core func $al (canon lower (func $add)))
    (core module $bm
      (import "env" "add" (func $add (param i32) (result i32)))
      (func (export "run") (result i32) (call $add (i32.const 2))))
    (core instance $env (export "add" (func $al)))
    (core instance $bi (instantiate $bm (with "env" (instance $env))))
    (func (export "run") (result u32) (canon lift (core func $bi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "add" (func $a "add"))))
  (export "run" (func $b "run")))"#;

/// Exporting module `$an` has NO memory; its component has `$am` with one.
const CALLEE_MEMLESS: &str = r#"(component
  (component $A
    (core module $am (memory (export "mem") 1))
    (core instance $ai (instantiate $am))
    (core module $an
      (func (export "add") (param i32) (result i32) local.get 0 i32.const 40 i32.add))
    (core instance $ni (instantiate $an))
    (func (export "add") (param "x" u32) (result u32) (canon lift (core func $ni "add"))))
  (component $B
    (import "add" (func $add (param "x" u32) (result u32)))
    (core func $al (canon lower (func $add)))
    (core module $bm
      (import "env" "add" (func $add (param i32) (result i32)))
      (memory (export "mem") 1)
      (func (export "run") (result i32) (call $add (i32.const 2))))
    (core instance $env (export "add" (func $al)))
    (core instance $bi (instantiate $bm (with "env" (instance $env))))
    (func (export "run") (result u32) (canon lift (core func $bi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "add" (func $a "add"))))
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

/// `lead2b` with its second lowering (and the unused bag naming it) removed.
fn lead2b_single() -> String {
    lead2b()
        .replace("    (core func $gy (canon lower (func $get)\n      (memory (core memory $yi \"memy\"))\n      (realloc (core func $yi \"cabi_realloc\"))))", "")
        .replace("    (core instance $envy (export \"get\" (func $gy)))\n", "")
}

// rivet: verifies SR-16
#[test]
fn lead2b_control_single_lowering_untraced_import() {
    let w = lead2b_single();
    assert!(!w.contains("$gy"));
    assert_oracle(&w, SENTINEL_ANSWER);
}

/// D1: the untraced-site heuristic ("every lower names the same pair") is only
/// sound if EVERY lower is complete: an incomplete one (here the option-less
/// lower of a scalar function) could be the one the call uses. Its presence
/// disables the heuristic, and with no allocator of its own the site is refused.
// rivet: verifies SR-16
#[test]
fn incomplete_lower_disables_the_unanimity_heuristic() {
    let rep = |w: String, from: &str, to: &str| {
        assert!(w.contains(from), "fixture edit applies: {from}");
        w.replace(from, to)
    };
    let w = lead2b_single();
    let w = rep(
        w,
        "(func (export \"cabi_realloc\") (param i32 i32 i32 i32) (result i32)\n        i32.const 1024)",
        "",
    );
    let w = rep(
        w,
        "(func (export \"get\") (result i32) i32.const 16))",
        "(func (export \"get\") (result i32) i32.const 16)\n      (func (export \"sc\") (result i32) i32.const 7))",
    );
    let w = rep(
        w,
        "(memory (core memory $ai \"mem\")))))",
        "(memory (core memory $ai \"mem\"))))\n    (func (export \"sc\") (result u32) (canon lift (core func $ai \"sc\"))))",
    );
    let w = rep(
        w,
        "(import \"get\" (func $get (result string)))",
        "(import \"get\" (func $get (result string)))\n    (import \"sc\" (func $sc (result u32)))",
    );
    let w = rep(
        w,
        "    (core module $bx",
        "    (core func $z (canon lower (func $sc)))\n    (core module $bx",
    );
    let w = rep(
        w,
        "(with \"get\" (func $a \"get\"))",
        "(with \"get\" (func $a \"get\")) (with \"sc\" (func $a \"sc\"))",
    );
    assert_refused(&w);
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

// rivet: verifies SR-16
#[test]
fn g1_scalar_call_from_a_memoryless_caller_module_is_not_refused() {
    assert_oracle(CALLER_MEMLESS, 42);
}

// rivet: verifies SR-16
#[test]
fn g1_scalar_call_into_a_memoryless_callee_module_is_not_refused() {
    assert_oracle(CALLEE_MEMLESS, 42);
}

// rivet: verifies SR-16
#[test]
fn f1_identical_options_through_separate_aliases_are_not_a_disagreement() {
    // 'h' = 104 (string byte) ...
    assert_oracle(&p5(false), 104);
    // ... and, with the caller module's own allocator present, the traced one
    // (bump from 1024) still wins over its 8192.
    assert_oracle(&p5(true), 104);
    assert_oracle(&p5_ptr(false), 1024);
    assert_oracle(&p5_ptr(true), 1024);
}

// rivet: verifies SR-16
#[test]
fn f2_memory_only_lift_keeps_its_traced_memory() {
    // The lift names memory 1 of its module and no realloc (result string).
    assert_oracle(&p2(), 104);
}

// rivet: verifies SR-16
#[test]
fn f2_memory_only_lower_keeps_its_traced_memory() {
    // The lower names memory 1 of the calling module and no realloc.
    assert_oracle(&p4(), 104);
}

// ---------------------------------------------------------------------------
// The gate's "does this call copy anything" predicate must be the emitter's:
// the retptr adapter copies the RETURN AREA (callee memory -> caller memory)
// even when the result holds no pointers, and that copy needs the caller's
// memory. With the caller's memory unresolved it would target memory 0.
// ---------------------------------------------------------------------------

/// `pair: func() -> tuple<u32, u32>` (retptr, no pointers). The caller lower is
/// reached through a re-exporting module (untraced) and the calling module
/// owns no memory.
const RETPTR_SCALAR_UNTRACED: &str = r#"(component
  (component $A
    (core module $am
      (memory (export "mem") 1)
      (data (i32.const 16) "\07\00\00\00\e8\03\00\00")
      (func (export "pair") (result i32) i32.const 16))
    (core instance $ai (instantiate $am))
    (func (export "pair") (result (tuple u32 u32))
      (canon lift (core func $ai "pair") (memory (core memory $ai "mem")))))
  (component $B
    (import "pair" (func $pair (result (tuple u32 u32))))
    (core module $mm
      (memory (export "mem") 1)
      (func (export "get") (param i32) (result i32) local.get 0 i32.load))
    (core instance $mi (instantiate $mm))
    (core func $pl (canon lower (func $pair) (memory (core memory $mi "mem"))))
    (core module $s
      (import "in" "pair" (func $p (param i32)))
      (export "pair" (func $p)))
    (core instance $env (export "pair" (func $pl)))
    (core instance $si (instantiate $s (with "in" (instance $env))))
    (core module $bm
      (import "env" "pair" (func $pair (param i32)))
      (import "m" "get" (func $get (param i32) (result i32)))
      (func (export "run") (result i32)
        (call $pair (i32.const 128))
        (i32.add (call $get (i32.const 128)) (call $get (i32.const 132)))))
    (core instance $bi (instantiate $bm (with "env" (instance $si)) (with "m" (instance $mi))))
    (func (export "run") (result u32) (canon lift (core func $bi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "pair" (func $a "pair"))))
  (export "run" (func $b "run")))"#;

/// Same component with the lower reached DIRECTLY (traced): the memory comes
/// from the `canon lower` and the call is sound.
fn retptr_scalar_traced() -> String {
    RETPTR_SCALAR_UNTRACED.replace(
        "(with \"env\" (instance $si))",
        "(with \"env\" (instance $env))",
    )
}

/// The same with `tuple<u64, u64>` (a 16-byte return area).
fn retptr_u64_pair(traced: bool) -> String {
    let base = if traced {
        retptr_scalar_traced()
    } else {
        RETPTR_SCALAR_UNTRACED.to_string()
    };
    base.replace("tuple u32 u32", "tuple u64 u64")
        .replace(
            "(data (i32.const 16) \"\\07\\00\\00\\00\\e8\\03\\00\\00\")",
            "(data (i32.const 16) \"\\07\\00\\00\\00\\00\\00\\00\\00\\e8\\03\\00\\00\\00\\00\\00\\00\")",
        )
        .replace("(call $get (i32.const 132))", "(call $get (i32.const 136))")
}

// rivet: verifies SR-16
#[test]
fn retptr_without_pointers_and_unresolved_caller_memory_is_refused() {
    assert_eq!(run_unfused(RETPTR_SCALAR_UNTRACED), 1007, "oracle");
    assert_refused(RETPTR_SCALAR_UNTRACED);
}

// rivet: verifies SR-16
#[test]
fn retptr_without_pointers_with_traced_caller_memory_is_correct() {
    assert_oracle(&retptr_scalar_traced(), 1007);
}

// rivet: verifies SR-16
#[test]
fn retptr_u64_pair_unresolved_is_refused_and_traced_is_correct() {
    let w = retptr_u64_pair(false);
    assert!(w.contains("tuple u64 u64") && w.contains("i32.const 136"));
    assert_eq!(run_unfused(&w), 1007, "oracle");
    assert_refused(&w);
    assert_oracle(&retptr_u64_pair(true), 1007);
}
