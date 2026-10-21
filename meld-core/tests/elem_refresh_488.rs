//! #488 regression: an element-segment item naming an IMPORTED function that
//! crosses a component boundary needing a memory-copy adapter. The item is
//! resolved in merge_core against the pre-adapter function_index_map; adapter
//! wiring later overwrites that entry and re-rewrites bodies, but not element
//! segments. An active slot kept the callee (bypassing the adapter: 3000, not
//! 3090); a declarative segment no longer matched the body's `ref.func`
//! ("undeclared function reference").
use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasmtime::{Config, Engine, Instance, Module, Store};

/// `Active` / `ActiveExpr`: the import sits in an active segment (function-index
/// and `ref.func` expression forms), called via `call_indirect`. `Declared`: an
/// `elem declare` plus a body `ref.func`. `Direct`: the control, a plain `call`.
#[derive(Clone, Copy)]
enum Mode {
    Active,
    ActiveExpr,
    Declared,
    Direct,
}

fn component3(mode: Mode) -> String {
    let (decl, body) = match mode {
        Mode::Active => (
            "(elem (i32.const 0) func $fi)",
            "i32.const 100 i32.const 3 i32.const 0 call_indirect (type $t)",
        ),
        Mode::ActiveExpr => (
            "(elem (i32.const 0) funcref (ref.func $fi))",
            "i32.const 100 i32.const 3 i32.const 0 call_indirect (type $t)",
        ),
        Mode::Declared => (
            "(elem declare func $fi)",
            "i32.const 0 ref.func $fi table.set 0 i32.const 100 i32.const 3 i32.const 0 call_indirect (type $t)",
        ),
        Mode::Direct => ("", "i32.const 100 i32.const 3 call $fi"),
    };
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
      (import "env" "mem" (memory 1))
      (import "env" "f" (func $fi (param i32 i32) (result i32)))
      (type $t (func (param i32 i32) (result i32)))
      (table 1 funcref)
      {decl}
      (func (export "run") (result i32)
        {body}))
    (core instance $env (export "mem" (memory $mi "mem")) (export "f" (func $fl)))
    (core instance $bi (instantiate $bm (with "env" (instance $env))))
    (func (export "run") (result u32) (canon lift (core func $bi "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "f" (func $a "f"))))
  (export "run" (func $b "run")))"#
    )
}

fn run_unfused(mode: Mode) -> u32 {
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    let engine = Engine::new(&cfg).unwrap();
    let bytes = wat::parse_str(component3(mode)).unwrap();
    let c = wasmtime::component::Component::new(&engine, &bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let linker = wasmtime::component::Linker::<()>::new(&engine);
    let inst = linker.instantiate(&mut store, &c).unwrap();
    let f = inst
        .get_typed_func::<(), (u32,)>(&mut store, "run")
        .unwrap();
    f.call(&mut store, ()).unwrap().0
}

fn fuse(wat: &str) -> Vec<u8> {
    let bytes = wat::parse_str(wat).expect("component text");
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component_named(&bytes, Some("poc.wasm")).unwrap();
    fuser.fuse().expect("fuse must succeed")
}

fn run_fused(mode: Mode) -> i32 {
    let fused = fuse(&component3(mode));
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
fn active_function_index_elem_goes_through_adapter() {
    assert_eq!(run_unfused(Mode::Active), 3090);
    assert_eq!(
        run_fused(Mode::Active),
        3090,
        "table slot bypassed the adapter"
    );
}

#[test]
fn active_expression_elem_goes_through_adapter() {
    assert_eq!(run_unfused(Mode::ActiveExpr), 3090);
    assert_eq!(
        run_fused(Mode::ActiveExpr),
        3090,
        "table slot bypassed the adapter"
    );
}

#[test]
fn declarative_elem_validates_and_goes_through_adapter() {
    assert_eq!(run_unfused(Mode::Declared), 3090);
    assert_eq!(run_fused(Mode::Declared), 3090);
}

#[test]
fn direct_call_control() {
    assert_eq!(run_unfused(Mode::Direct), 3090);
    assert_eq!(run_fused(Mode::Direct), 3090);
}

/// Structural: a module holding BOTH `call $fi` and an element item naming
/// `$fi` (active function-index form and declarative form). The element item
/// must name the same fused function the body `call` names.
fn elem_and_call_agree(extra_decl: &str) {
    let wat = component3(Mode::Direct).replace(
        "(table 1 funcref)",
        &format!("(table 1 funcref)\n      {extra_decl}"),
    );
    let fused = fuse(&wat);
    let mut elem_targets = Vec::new();
    let mut run_idx = None;
    let mut call_targets: Vec<Vec<u32>> = Vec::new();
    let mut n_imp = 0u32;
    for p in wasmparser::Parser::new(0).parse_all(&fused) {
        match p.unwrap() {
            wasmparser::Payload::ImportSection(r) => {
                for i in r.into_imports() {
                    if matches!(i.unwrap().ty, wasmparser::TypeRef::Func(_)) {
                        n_imp += 1;
                    }
                }
            }
            wasmparser::Payload::ElementSection(r) => {
                for e in r {
                    match e.unwrap().items {
                        wasmparser::ElementItems::Functions(fs) => {
                            for f in fs {
                                elem_targets.push(f.unwrap());
                            }
                        }
                        wasmparser::ElementItems::Expressions(_, es) => {
                            for e in es {
                                for op in e.unwrap().get_operators_reader() {
                                    if let Ok(wasmparser::Operator::RefFunc { function_index }) = op
                                    {
                                        elem_targets.push(function_index);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            wasmparser::Payload::ExportSection(r) => {
                for e in r {
                    let e = e.unwrap();
                    if e.name == "run" {
                        run_idx = Some(e.index);
                    }
                }
            }
            wasmparser::Payload::CodeSectionEntry(b) => {
                let mut v = Vec::new();
                for op in b.get_operators_reader().unwrap() {
                    if let Ok(wasmparser::Operator::Call { function_index }) = op {
                        v.push(function_index);
                    }
                }
                call_targets.push(v);
            }
            _ => {}
        }
    }
    let run_calls = &call_targets[(run_idx.unwrap() - n_imp) as usize];
    assert_eq!(elem_targets.len(), 1);
    assert_eq!(run_calls.len(), 1);
    assert_eq!(
        elem_targets[0], run_calls[0],
        "elem item names {} but `call $fi` names {} in the same module",
        elem_targets[0], run_calls[0]
    );
}

#[test]
fn active_elem_item_and_call_name_same_function() {
    elem_and_call_agree("(elem (i32.const 0) func $fi)");
}

#[test]
fn declarative_elem_item_and_call_name_same_function() {
    elem_and_call_agree("(elem declare func $fi)");
}
