//! #484: `--component` lowered a host import with an arbitrary memory.
//!
//! Under `--memory multi` the wrapper took the `memory` of a `canon lower` from
//! `component_memory_index`, which scanned a `HashMap` and returned the first
//! "memory 0" of ANY module of the importing component. The host then read the
//! lowered string out of another module's memory, and the output varied from
//! run to run. The lower's `realloc` and string encoding had the same
//! per-component (not per-lower) shape.
//!
//! Every test fuses the same input 20 times in ONE process (each `HashMap`
//! draws a fresh hasher seed, so a hash-order dependence shows up as more than
//! one distinct output) and runs each result against a host that records what
//! it is handed.

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use std::collections::BTreeSet;
use wasmtime::component::{Component, Linker};
use wasmtime::{Config, Engine, Store};

const RUNS: usize = 20;

/// The issue's fixture. `order` is the SOURCE order of the three core modules
/// (which decides which merges first); the instantiation graph is unchanged.
/// M owns the memory the lower names; A imports it and its data segment puts
/// `a_data` ("hello") there. B owns a different memory holding "WORLD".
fn issue_fixture(order: &str, lower_opts: &str, a_data: &str, len: u32) -> String {
    let m = r#"(core module $M
        (memory (export "mem") 1)
        (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 0))"#;
    let b = r#"(core module $B
        (memory (export "mem") 1)
        (data (i32.const 0) "WORLD"))"#;
    let a = format!(
        r#"(core module $A
        (import "env" "mem" (memory 1))
        (import "host" "log" (func $log (param i32 i32) (result i32)))
        (data (i32.const 0) "{a_data}")
        (func (export "run") (result i32) i32.const 0 i32.const {len} call $log))"#
    );
    let mods: Vec<&str> = order
        .chars()
        .map(|c| match c {
            'M' => m,
            'B' => b,
            _ => a.as_str(),
        })
        .collect();
    format!(
        r#"(component
  (import "my:h/host" (instance $h
    (export "log" (func (param "s" string) (result u32)))))
  {mods}
  (core instance $m (instantiate $M))
  (core instance $b (instantiate $B))
  (alias export $h "log" (func $log))
  (core func $low (canon lower (func $log) {lower_opts} (memory $m "mem")))
  (core instance $host (export "log" (func $low)))
  (core instance $envi (export "mem" (memory $m "mem")))
  (core instance $a (instantiate $A (with "env" (instance $envi)) (with "host" (instance $host))))
  (func $run (result u32) (canon lift (core func $a "run")))
  (export "run" (func $run)))"#,
        mods = mods.join("\n  ")
    )
}

/// Fixture for the realloc finding: the host RETURNS a string, so the lower
/// calls the realloc it names. B owns the memory and a realloc that returns
/// 100; M's realloc returns 0. `run` returns `ptr + first byte`, read from the
/// lowered memory: 100 + 'f' (102) = 202 when memory AND realloc are B's.
fn realloc_fixture(order: &str) -> String {
    let m = r#"(core module $M
        (memory (export "mem") 1)
        (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 0))"#;
    let b = r#"(core module $B
        (memory (export "mem") 1)
        (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 100))"#;
    let a = r#"(core module $A
        (import "env" "mem" (memory 1))
        (import "host" "get" (func $get (param i32)))
        (func (export "run") (result i32)
          (local $p i32)
          (call $get (i32.const 8))
          (local.set $p (i32.load (i32.const 8)))
          (i32.add (local.get $p) (i32.load8_u (local.get $p)))))"#;
    let mods: Vec<&str> = order
        .chars()
        .map(|c| match c {
            'M' => m,
            'B' => b,
            _ => a,
        })
        .collect();
    format!(
        r#"(component
  (import "my:h/host" (instance $h
    (export "get" (func (result string)))))
  {mods}
  (core instance $m (instantiate $M))
  (core instance $b (instantiate $B))
  (alias export $h "get" (func $get))
  (core func $low (canon lower (func $get) (memory $b "mem") (realloc (func $b "cabi_realloc"))))
  (core instance $host (export "get" (func $low)))
  (core instance $envi (export "mem" (memory $b "mem")))
  (core instance $a (instantiate $A (with "env" (instance $envi)) (with "host" (instance $host))))
  (func $run (result u32) (canon lift (core func $a "run")))
  (export "run" (func $run)))"#,
        mods = mods.join("\n  ")
    )
}

/// Instantiate `bytes` against a host whose `log(s)` records `s` and whose
/// `get()` returns "fixed". Returns (run's result, what the host was handed).
fn run(bytes: &[u8]) -> Result<(u32, Vec<String>), String> {
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).unwrap();
    let c = Component::new(&engine, bytes).map_err(|e| format!("compile: {e:?}"))?;
    let mut linker: Linker<Vec<String>> = Linker::new(&engine);
    {
        let mut inst = linker.instance("my:h/host").unwrap();
        inst.func_wrap(
            "log",
            |mut cx: wasmtime::StoreContextMut<'_, Vec<String>>, (s,): (String,)| {
                let n = s.len() as u32;
                cx.data_mut().push(s);
                Ok((n,))
            },
        )
        .unwrap();
        inst.func_wrap(
            "get",
            |_cx: wasmtime::StoreContextMut<'_, Vec<String>>, (): ()| Ok(("fixed".to_string(),)),
        )
        .unwrap();
    }
    let mut store = Store::new(&engine, Vec::new());
    let inst = linker
        .instantiate(&mut store, &c)
        .map_err(|e| format!("inst: {e:?}"))?;
    let f = inst
        .get_typed_func::<(), (u32,)>(&mut store, "run")
        .map_err(|e| format!("get: {e:?}"))?;
    let (v,) = f.call(&mut store, ()).map_err(|e| format!("call: {e:?}"))?;
    Ok((v, store.into_data()))
}

fn fuse(bytes: &[u8]) -> Result<Vec<u8>, String> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        output_format: OutputFormat::Component,
        ..Default::default()
    });
    fuser
        .add_component_named(bytes, Some("poc.wasm"))
        .map_err(|e| format!("add: {e:?}"))?;
    fuser.fuse().map_err(|e| format!("fuse: {e:?}"))
}

/// Fuse `RUNS` times: exactly one distinct output, and every run behaves like
/// the unfused component. Returns the number of distinct outputs.
fn check(label: &str, wat: &str) {
    let bytes = wat::parse_str(wat).unwrap();
    let want = run(&bytes).unwrap_or_else(|e| panic!("{label}: unfused run failed: {e}"));
    let mut outputs = BTreeSet::new();
    let mut wrong = 0;
    for _ in 0..RUNS {
        let fused = fuse(&bytes).unwrap_or_else(|e| panic!("{label}: {e}"));
        let got = run(&fused).unwrap_or_else(|e| panic!("{label}: fused run failed: {e}"));
        if got != want {
            wrong += 1;
        }
        outputs.insert(fused);
    }
    assert_eq!(
        wrong, 0,
        "{label}: {wrong}/{RUNS} fused runs diverged from the unfused result {want:?}"
    );
    assert_eq!(
        outputs.len(),
        1,
        "{label}: {RUNS} fusions of one input produced {} distinct outputs",
        outputs.len()
    );
}

#[test]
fn unfused_fixture_delivers_hello() {
    let bytes = wat::parse_str(issue_fixture("MBA", "", "hello", 5)).unwrap();
    assert_eq!(run(&bytes).unwrap().1, vec!["hello".to_string()]);
}

/// The issue's reproduction, in every source order of the three modules.
#[test]
fn lower_memory_follows_source_option_in_every_module_order() {
    for order in ["MBA", "MAB", "BMA", "BAM", "AMB", "ABM"] {
        let wat = issue_fixture(order, "", "hello", 5);
        check(&format!("order {order}"), &wat);
        // Belt and braces for the headline claim: the host got "hello".
        let fused = fuse(&wat::parse_str(&wat).unwrap()).unwrap();
        assert_eq!(
            run(&fused).unwrap().1,
            vec!["hello".to_string()],
            "order {order}"
        );
    }
}

/// UTF-16 source lower: the wrapper hard-coded UTF-8, so the host decoded the
/// UTF-16 bytes as UTF-8 (a different string, or a trap).
#[test]
fn utf16_lower_keeps_its_encoding() {
    for order in ["MBA", "ABM"] {
        let wat = issue_fixture(order, "string-encoding=utf16", "h\\00i\\00", 2);
        let bytes = wat::parse_str(&wat).unwrap();
        assert_eq!(
            run(&bytes).unwrap().1,
            vec!["hi".to_string()],
            "unfused, order {order}"
        );
        check(&format!("utf16 order {order}"), &wat);
        let fused = fuse(&bytes).unwrap();
        assert_eq!(
            run(&fused).unwrap().1,
            vec!["hi".to_string()],
            "fused, order {order}"
        );
    }
}

/// The lower's `realloc` is the one the source names (B's), not the one of
/// whichever module is memory 0 (M's, which returns 0).
#[test]
fn lower_realloc_follows_source_option() {
    for order in ["MBA", "BMA", "ABM"] {
        let wat = realloc_fixture(order);
        let bytes = wat::parse_str(&wat).unwrap();
        assert_eq!(run(&bytes).unwrap().0, 202, "unfused, order {order}");
        check(&format!("realloc order {order}"), &wat);
    }
}

/// Two modules lower the same host `log`, each with its OWN memory ($ma / $mc),
/// so the two lowers share one dedup key but disagree on `memory`. A reaches its
/// lower through a plain bag; C reaches its lower either directly
/// (`via_alias == false`) or through an ALIAS re-export of another bag
/// (`via_alias == true`), which the resolver used to leave untraced. Unfused,
/// the host receives ["hello", "WORLD"].
fn shared_key_fixture(c_first: bool, via_alias: bool) -> String {
    let a = r#"(core module $A
    (import "env" "mem" (memory 1))
    (import "my:h/host" "log" (func $log (param i32 i32) (result i32)))
    (data (i32.const 0) "hello")
    (func (export "runa") (result i32) i32.const 0 i32.const 5 call $log))"#;
    let c = r#"(core module $C
    (import "env" "mem" (memory 1))
    (import "my:h/host" "log" (func $log (param i32 i32) (result i32)))
    (data (i32.const 0) "WORLD")
    (func (export "runc") (result i32) i32.const 0 i32.const 5 call $log))"#;
    let ia = r#"(core instance $a (instantiate $A (with "env" (instance $enva)) (with "my:h/host" (instance $hosta))))"#;
    let ic = r#"(core instance $c (instantiate $C (with "env" (instance $envc)) (with "my:h/host" (instance $hostc))))"#;
    let (first_mod, second_mod, first_inst, second_inst) = if c_first {
        (c, a, ic, ia)
    } else {
        (a, c, ia, ic)
    };
    let hostc = if via_alias {
        r#"(core instance $hostc (export "log" (func $hostx "log")))"#
    } else {
        r#"(core instance $hostc (export "log" (func $lowc)))"#
    };
    format!(
        r#"(component
  (import "my:h/host" (instance $h (export "log" (func (param "s" string) (result u32)))))
  (core module $MA (memory (export "mem") 1) (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 0))
  (core module $MC (memory (export "mem") 1))
  {first_mod}
  {second_mod}
  (core instance $ma (instantiate $MA))
  (core instance $mc (instantiate $MC))
  (alias export $h "log" (func $log))
  (core func $lowa (canon lower (func $log) (memory $ma "mem")))
  (core func $lowc (canon lower (func $log) (memory $mc "mem")))
  (core instance $hosta (export "log" (func $lowa)))
  (core instance $hostx (export "log" (func $lowc)))
  {hostc}
  (core instance $enva (export "mem" (memory $ma "mem")))
  (core instance $envc (export "mem" (memory $mc "mem")))
  {first_inst}
  {second_inst}
  (func $runa (result u32) (canon lift (core func $a "runa")))
  (func $runc (result u32) (canon lift (core func $c "runc")))
  (core module $R
    (import "a" "run" (func $ra (result i32)))
    (import "c" "run" (func $rc (result i32)))
    (func (export "run") (result i32) (i32.add (call $ra) (call $rc))))
  (core instance $ra (export "run" (func $a "runa")))
  (core instance $rc (export "run" (func $c "runc")))
  (core instance $r (instantiate $R (with "a" (instance $ra)) (with "c" (instance $rc))))
  (func $run (result u32) (canon lift (core func $r "run")))
  (export "run" (func $run)))"#
    )
}

/// Never a silent wrong delivery: each fusion either delivers exactly what the
/// unfused component does or is refused loudly. Here the two lowers need two
/// different memories behind one fused import, so it must be refused, and the
/// refusal must not depend on whether C's lower was reached through an alias.
#[test]
fn shared_import_with_disagreeing_lowers_is_never_silently_merged() {
    for via_alias in [false, true] {
        for c_first in [false, true] {
            let bytes = wat::parse_str(shared_key_fixture(c_first, via_alias)).unwrap();
            let want = run(&bytes).unwrap().1;
            assert_eq!(want, vec!["hello".to_string(), "WORLD".to_string()]);
            let (mut silent_wrong, mut refused) = (0, 0);
            for _ in 0..RUNS {
                match fuse(&bytes) {
                    Err(e) => {
                        assert!(
                            e.contains("disagree"),
                            "via_alias={via_alias} c_first={c_first}: refused for the wrong reason: {e}"
                        );
                        refused += 1;
                    }
                    Ok(f) => {
                        if run(&f).map(|r| r.1) != Ok(want.clone()) {
                            silent_wrong += 1;
                        }
                    }
                }
            }
            assert_eq!(
                silent_wrong, 0,
                "via_alias={via_alias} c_first={c_first}: {silent_wrong}/{RUNS} fusions \
                 exited 0 and delivered the wrong bytes"
            );
            assert_eq!(
                refused, RUNS,
                "via_alias={via_alias} c_first={c_first}: expected every fusion refused"
            );
        }
    }
}

/// One module A whose `host::log` import is a UTF-16 lower (memory $m) reached
/// through `hops` alias re-exports. B owns a second memory ("WORLD"), so a
/// silently defaulted lower (UTF-8, wrong memory) would deliver "WO".
/// `core_mod` is the core import module name A uses.
fn chain_fixture(hops: usize, core_mod: &str) -> String {
    let mut bags = String::from("(core instance $b0 (export \"log\" (func $low)))\n");
    for k in 1..=hops {
        bags.push_str(&format!(
            "(core instance $b{k} (export \"log\" (func $b{} \"log\")))\n",
            k - 1
        ));
    }
    format!(
        r#"(component
  (import "my:h/host" (instance $h (export "log" (func (param "s" string) (result u32)))))
  (core module $B (memory (export "mem") 1) (data (i32.const 0) "WORLD"))
  (core module $M (memory (export "mem") 1) (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 0))
  (core module $A
    (import "env" "mem" (memory 1))
    (import "{core_mod}" "log" (func $log (param i32 i32) (result i32)))
    (data (i32.const 0) "h\00i\00")
    (func (export "run") (result i32) i32.const 0 i32.const 2 call $log))
  (core instance $b (instantiate $B))
  (core instance $m (instantiate $M))
  (alias export $h "log" (func $log))
  (core func $low (canon lower (func $log) string-encoding=utf16 (memory $m "mem")))
  {bags}
  (core instance $envi (export "mem" (memory $m "mem")))
  (core instance $a (instantiate $A (with "env" (instance $envi)) (with "{core_mod}" (instance $b{hops}))))
  (func $run (result u32) (canon lift (core func $a "run")))
  (export "run" (func $run)))"#
    )
}

/// A lower reached through any number of alias hops is traced (no fixed hop
/// limit), so fusion delivers what the unfused component does. At minimum it
/// may never exit 0 with other bytes.
#[test]
fn long_alias_chain_lower_is_never_silently_defaulted() {
    for hops in [1usize, 255, 256, 300] {
        let bytes = wat::parse_str(chain_fixture(hops, "my:h/host")).unwrap();
        let want = run(&bytes).unwrap();
        assert_eq!(want.1, vec!["hi".to_string()], "unfused, hops={hops}");
        match fuse(&bytes) {
            Ok(f) => assert_eq!(
                run(&f).unwrap(),
                want,
                "hops={hops}: fused exited 0 and delivered other bytes"
            ),
            Err(e) => panic!("hops={hops}: a traceable lower was refused: {e}"),
        }
    }
}

/// One alias hop with a plain core import name (`host::log`, not the WASI
/// name): the display name must be recovered through the traced lower, or
/// fusion fails with "cannot resolve fused import host::log".
#[test]
fn one_hop_alias_keeps_plain_core_import_name() {
    let bytes = wat::parse_str(chain_fixture(1, "host")).unwrap();
    let want = run(&bytes).unwrap();
    assert_eq!(want.1, vec!["hi".to_string()]);
    let fused = fuse(&bytes).unwrap_or_else(|e| panic!("1-hop `host::log` refused: {e}"));
    assert_eq!(run(&fused).unwrap(), want);
}
