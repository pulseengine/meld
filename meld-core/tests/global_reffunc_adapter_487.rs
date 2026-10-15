//! #482/#487 regression: a global `ref.func` of an IMPORTED function that crosses
//! a component boundary needing a memory-copy adapter. The global is resolved in
//! merge_core against the pre-adapter function_index_map; adapter wiring later
//! overwrites that map entry and re-rewrites bodies, but not globals.
use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasmtime::{Config, Engine, Instance, Module, Store};

fn component(global_init: bool) -> String {
    component3(if global_init { 1 } else { 0 })
}
fn component3(mode: u8) -> String {
    let (decl, get) = match mode {
        1 => ("(global $g funcref (ref.func $fi))", "global.get $g"),
        0 => ("(elem declare func $fi)", "ref.func $fi"),
        _ => ("", "DIRECT"),
    };
    let body = if get == "DIRECT" {
        "i32.const 100 i32.const 3 call $fi".to_string()
    } else {
        format!(
            "i32.const 0 {get} table.set 0 i32.const 100 i32.const 3 i32.const 0 call_indirect (type $t)"
        )
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
fn global_ref_func_of_adapted_import() {
    assert_eq!(run_unfused(true), 3090);
    assert_eq!(run_fused(true), 3090, "fused diverges from unfused");
}

#[test]
fn direct_call_of_adapted_import() {
    let bytes = wat::parse_str(component3(2)).unwrap();
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    let engine = Engine::new(&cfg).unwrap();
    let c = wasmtime::component::Component::new(&engine, &bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let linker = wasmtime::component::Linker::<()>::new(&engine);
    let inst = linker.instantiate(&mut store, &c).unwrap();
    let f = inst
        .get_typed_func::<(), (u32,)>(&mut store, "run")
        .unwrap();
    assert_eq!(f.call(&mut store, ()).unwrap().0, 3090);
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component_named(&bytes, Some("poc.wasm")).unwrap();
    let fused = fuser.fuse().unwrap();
    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).unwrap();
    let module = Module::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();
    let got = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap()
        .call(&mut store, ())
        .unwrap();
    assert_eq!(got, 3090, "direct call through adapter diverges");
}

/// Structural: a module holding BOTH `call $fi` and `(global funcref (ref.func $fi))`.
/// After fusion the global must name the same function the call names.
#[test]
fn global_ref_func_and_call_name_same_function() {
    let wat = component3(2).replace(
        "(table 1 funcref)",
        "(table 1 funcref)\n      (global $g (export \"g\") funcref (ref.func $fi))",
    );
    let bytes = wat::parse_str(&wat).unwrap();
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component_named(&bytes, Some("poc.wasm")).unwrap();
    let fused = fuser.fuse().unwrap();
    let mut global_targets = Vec::new();
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
            wasmparser::Payload::GlobalSection(r) => {
                for g in r {
                    let g = g.unwrap();
                    for op in g.init_expr.get_operators_reader() {
                        if let Ok(wasmparser::Operator::RefFunc { function_index }) = op {
                            global_targets.push(function_index);
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
    assert_eq!(global_targets.len(), 1);
    assert_eq!(run_calls.len(), 1);
    assert_eq!(
        global_targets[0], run_calls[0],
        "global ref.func $fi names {} but `call $fi` names {} in the same module",
        global_targets[0], run_calls[0]
    );
}
