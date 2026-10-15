//! #481: `--component` lifted every export from fused memory 0.
//!
//! Under `--memory multi`, fused memory 0 is whichever memory-owning module
//! merged first, not the module whose memory the SOURCE lift's `memory`
//! option names. A string/list export then read its (ptr, len) and bytes from
//! the wrong memory: wrong result, exit 0. The shape needs two memory-owning
//! core modules in one component.

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasmtime::component::{Component, ComponentNamedList, ComponentType, Lift, Linker};
use wasmtime::{Config, Engine, Store};

/// Module A owns the memory the lift names ("hello" at 16) and calls into
/// module B, which owns a different memory ("WORLD" at 16). `importer_first`
/// controls the source order of the two modules, i.e. which one merges first.
fn component(importer_first: bool, result_ty: &str) -> String {
    let a = r#"(core module $A
        (import "b" "f" (func $f (param i32) (result i32)))
        (memory (export "mem") 1)
        (data (i32.const 16) "hello")
        (func (export "run") (result i32)
          (drop (call $f (i32.const 0)))
          (i32.store (i32.const 0) (i32.const 16))
          (i32.store (i32.const 4) (i32.const 5))
          i32.const 0)
        (func (export "cabi_post_run") (param i32)))"#;
    let b = r#"(core module $B
        (memory (export "mem") 1)
        (data (i32.const 16) "WORLD")
        (func (export "f") (param i32) (result i32) local.get 0))"#;
    let mods = if importer_first {
        format!("{a}\n{b}")
    } else {
        format!("{b}\n{a}")
    };
    format!(
        r#"(component
      {mods}
      (core instance $b (instantiate $B))
      (alias core export $b "f" (core func $lf))
      (core instance $fi (export "f" (func $lf)))
      (core instance $a (instantiate $A (with "b" (instance $fi))))
      (alias core export $a "mem" (core memory $m))
      (alias core export $a "run" (core func $run))
      (alias core export $a "cabi_post_run" (core func $pr))
      (func (export "run") (result {result_ty}) (canon lift (core func $run) (memory $m) (post-return $pr))))"#
    )
}

fn run<T>(bytes: &[u8]) -> Result<T, String>
where
    T: Lift + ComponentType + Send + Sync + 'static,
    (T,): ComponentNamedList + Lift,
{
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).unwrap();
    let c = Component::new(&engine, bytes).map_err(|e| format!("compile: {e:?}"))?;
    let linker: Linker<()> = Linker::new(&engine);
    let mut store = Store::new(&engine, ());
    let inst = linker
        .instantiate(&mut store, &c)
        .map_err(|e| format!("inst: {e:?}"))?;
    let f = inst
        .get_typed_func::<(), (T,)>(&mut store, "run")
        .map_err(|e| format!("get: {e:?}"))?;
    let (v,) = f.call(&mut store, ()).map_err(|e| format!("call: {e:?}"))?;
    Ok(v)
}

fn fuse(bytes: &[u8]) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        output_format: OutputFormat::Component,
        ..Default::default()
    });
    fuser.add_component_named(bytes, Some("poc.wasm")).unwrap();
    fuser.fuse().expect("fuse")
}

/// Both source orders must match the unfused component (string return).
#[test]
fn lift_memory_follows_source_option_in_both_module_orders() {
    for importer_first in [true, false] {
        let bytes = wat::parse_str(component(importer_first, "string")).unwrap();
        assert_eq!(run::<String>(&bytes).unwrap(), "hello");
        assert_eq!(
            run::<String>(&fuse(&bytes)).unwrap(),
            "hello",
            "importer_first={importer_first}"
        );
    }
}

/// Same defect through a list return: the element bytes live in the named
/// memory too.
#[test]
fn lift_memory_follows_source_option_for_list_return() {
    for importer_first in [true, false] {
        let bytes = wat::parse_str(component(importer_first, "(list u8)")).unwrap();
        assert_eq!(run::<Vec<u8>>(&bytes).unwrap(), b"hello");
        assert_eq!(
            run::<Vec<u8>>(&fuse(&bytes)).unwrap(),
            b"hello",
            "importer_first={importer_first}"
        );
    }
}
