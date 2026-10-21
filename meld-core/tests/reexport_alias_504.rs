//! #504: an adapted import that one core module re-exports and another core
//! module imports bypassed the adapter.
//!
//! The intra-component fallback resolves `$cm`'s import of `$bm`'s export `fx`
//! by COPYING `$bm`'s function-map entry for the import `fx` re-exports. The
//! copy is taken before adapters exist, so it names the callee. Adapter wiring
//! then re-pointed only `$bm`'s entry; `$cm`'s body `call`, and the core
//! export `fx`, kept naming the callee and a cross-memory string was never
//! copied. The fused module validated and meld exited 0, but returned 3000
//! where the unfused component returns 3090.
//!
//! Every behavioural test compares the fused result with the unfused component
//! under wasmtime; the structural tests state the property directly (the same
//! import is the same fused function wherever it is named).

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasmtime::{Config, Engine, Instance, Module, Store};

/// Component A exports `f(string) -> u32` (first byte + 1000 * len). Component
/// B lowers it into its OWN memory (so the call crosses memories and needs a
/// memory-copy adapter) and holds the modules under test.
fn comp(bm_body: &str, extra_b: &str, b_wiring: &str, outer_exports: &str) -> String {
    format!(
        r#"(component
  (component $A
    (core module $am
      (memory (export "mem") 1)
      (global $bump (mut i32) (i32.const 1024))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r)
      (func (export "f") (param i32 i32) (result i32)
        local.get 0 i32.load8_u
        local.get 1 i32.const 1000 i32.mul
        i32.add))
    (core instance $ai (instantiate $am))
    (func (export "f") (param "s" string) (result u32)
      (canon lift (core func $ai "f") (memory $ai "mem") (realloc (func $ai "cabi_realloc")))))
  (component $B
    (import "f" (func $f (param "s" string) (result u32)))
    (core module $mm
      (memory (export "mem") 1)
      (data (i32.const 100) "Z"))
    (core instance $mi (instantiate $mm))
    (core func $fl (canon lower (func $f) (memory $mi "mem")))
    (core module $bm
      {bm_body})
    (core instance $env (export "mem" (memory $mi "mem")) (export "f" (func $fl)))
    (core instance $bi (instantiate $bm (with "env" (instance $env))))
    {extra_b}
    {b_wiring})
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "f" (func $a "f"))))
  {outer_exports})"#
    )
}

const BM_REEXPORT: &str = r#"(import "env" "mem" (memory 1))
      (import "env" "f" (func $fi (param i32 i32) (result i32)))
      (export "fx" (func $fi))
      (func (export "brun") (result i32)
        i32.const 100 i32.const 3 call $fi)"#;

const CM_CALL: &str = r#"(core module $cm
      (import "b" "fx" (func $g (param i32 i32) (result i32)))
      (func (export "run") (result i32)
        i32.const 100 i32.const 3 call $g))
    (core instance $ci (instantiate $cm (with "b" (instance $bi))))"#;

const CM_ELEM: &str = r#"(core module $cm
      (import "b" "fx" (func $g (param i32 i32) (result i32)))
      (type $t (func (param i32 i32) (result i32)))
      (table 1 funcref)
      (elem (i32.const 0) func $g)
      (func (export "run") (result i32)
        i32.const 100 i32.const 3 i32.const 0 call_indirect (type $t)))
    (core instance $ci (instantiate $cm (with "b" (instance $bi))))"#;

const WIRE_RUN: &str = r#"(func (export "run") (result u32) (canon lift (core func $ci "run")))"#;
const WIRE_RUN_BRUN: &str = r#"(func (export "run") (result u32) (canon lift (core func $ci "run")))
    (func (export "brun") (result u32) (canon lift (core func $bi "brun")))"#;
const EXPORT_RUN: &str = r#"(export "run" (func $b "run"))"#;
const EXPORT_RUN_BRUN: &str = r#"(export "run" (func $b "run")) (export "brun" (func $b "brun"))"#;

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

fn fuse(wat: &str, strat: MemoryStrategy) -> Vec<u8> {
    let bytes = wat::parse_str(wat).expect("component text");
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: strat,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component_named(&bytes, Some("poc.wasm")).unwrap();
    fuser.fuse().expect("fuse")
}

fn run_fused(wat: &str, strat: MemoryStrategy) -> i32 {
    let fused = fuse(wat, strat);
    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).unwrap();
    let module = Module::new(&engine, &fused).expect("fused module validates");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();
    instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap()
        .call(&mut store, ())
        .unwrap()
}

/// `run` must equal the unfused component under both memory strategies. 3090 is
/// 'Z' (90) + 1000 * len 3; 3000 means the callee ran on a string that was
/// never copied into its memory.
fn assert_matches_unfused(wat: &str) {
    let unfused = run_unfused(wat);
    assert_eq!(unfused, 3090, "fixture sanity: the unfused component");
    for s in [MemoryStrategy::MultiMemory, MemoryStrategy::SharedMemory] {
        assert_eq!(run_fused(wat, s), 3090, "{s:?}");
    }
}

#[test]
fn reexported_import_called_by_another_module_goes_through_the_adapter() {
    assert_matches_unfused(&comp(BM_REEXPORT, CM_CALL, WIRE_RUN, EXPORT_RUN));
}

/// Element items are baked at merge time on main; they follow the map only once
/// #488 (PR #503) lands. The map entry this test depends on is the one #504
/// fixes, so un-ignore it together with #503.
#[test]
#[ignore = "needs #488/#503 (element items re-resolved from the final map)"]
fn reexported_import_in_an_element_segment_goes_through_the_adapter() {
    assert_matches_unfused(&comp(BM_REEXPORT, CM_ELEM, WIRE_RUN, EXPORT_RUN));
}

/// (function exports, `call` targets of each defined body, function imports)
fn scan(fused: &[u8]) -> (Vec<(String, u32)>, Vec<Vec<u32>>, u32) {
    let mut n_imp = 0u32;
    let mut exports = Vec::new();
    let mut bodies: Vec<Vec<u32>> = Vec::new();
    for p in wasmparser::Parser::new(0).parse_all(fused) {
        match p.unwrap() {
            wasmparser::Payload::ImportSection(r) => {
                for i in r.into_imports() {
                    if matches!(i.unwrap().ty, wasmparser::TypeRef::Func(_)) {
                        n_imp += 1;
                    }
                }
            }
            wasmparser::Payload::ExportSection(r) => {
                for e in r {
                    let e = e.unwrap();
                    if e.kind == wasmparser::ExternalKind::Func {
                        exports.push((e.name.to_string(), e.index));
                    }
                }
            }
            wasmparser::Payload::CodeSectionEntry(b) => {
                let mut v = Vec::new();
                for op in b.get_operators_reader().unwrap().into_iter().flatten() {
                    if let wasmparser::Operator::Call { function_index } = op {
                        v.push(function_index);
                    }
                }
                bodies.push(v);
            }
            _ => {}
        }
    }
    (exports, bodies, n_imp)
}

/// The `call` targets of the body of the function exported as `name`.
fn calls_of_export(fused: &[u8], name: &str) -> Vec<u32> {
    let (exports, bodies, n_imp) = scan(fused);
    let idx = exports.iter().find(|(n, _)| n == name).expect(name).1;
    bodies[(idx - n_imp) as usize].clone()
}

fn export_index(fused: &[u8], name: &str) -> u32 {
    scan(fused)
        .0
        .iter()
        .find(|(n, _)| n == name)
        .unwrap_or_else(|| panic!("no export {name}"))
        .1
}

#[test]
fn reexporting_module_and_importing_module_call_the_same_function() {
    let wat = comp(BM_REEXPORT, CM_CALL, WIRE_RUN_BRUN, EXPORT_RUN_BRUN);
    let fused = fuse(&wat, MemoryStrategy::MultiMemory);
    let via_alias = calls_of_export(&fused, "run");
    let direct = calls_of_export(&fused, "brun");
    assert_eq!(
        via_alias, direct,
        "the re-exported import names a different function than the module's own call"
    );
    assert_eq!(direct.len(), 1);

    // The core export `fx` re-exports the same import, so it names it too.
    assert_eq!(
        export_index(&fused, "fx"),
        direct[0],
        "export `fx` bypasses the adapter"
    );
}

/// `$bm` -> `$cm` -> `$dm`: `$cm` imports `$bm`'s `fx` and re-exports it as
/// `gx`; `$dm` imports `gx`. The alias of an alias must follow too.
#[test]
fn a_two_hop_reexport_chain_goes_through_the_adapter() {
    let extra = r#"(core module $cm
      (import "b" "fx" (func $g (param i32 i32) (result i32)))
      (export "gx" (func $g))
      (func (export "crun") (result i32)
        i32.const 100 i32.const 3 call $g))
    (core instance $ci (instantiate $cm (with "b" (instance $bi))))
    (core module $dm
      (import "c" "gx" (func $h (param i32 i32) (result i32)))
      (func (export "run") (result i32)
        i32.const 100 i32.const 3 call $h))
    (core instance $di (instantiate $dm (with "c" (instance $ci))))"#;
    let wire = r#"(func (export "run") (result u32) (canon lift (core func $di "run")))
    (func (export "brun") (result u32) (canon lift (core func $bi "brun")))
    (func (export "crun") (result u32) (canon lift (core func $ci "crun")))"#;
    let wat = comp(
        BM_REEXPORT,
        extra,
        wire,
        r#"(export "run" (func $b "run")) (export "brun" (func $b "brun")) (export "crun" (func $b "crun"))"#,
    );
    assert_matches_unfused(&wat);

    let fused = fuse(&wat, MemoryStrategy::MultiMemory);
    let direct = calls_of_export(&fused, "brun");
    assert_eq!(calls_of_export(&fused, "crun"), direct, "one hop");
    assert_eq!(calls_of_export(&fused, "run"), direct, "two hops");
    for name in ["fx", "gx"] {
        assert_eq!(
            export_index(&fused, name),
            direct[0],
            "export `{name}` bypasses the adapter"
        );
    }
}
