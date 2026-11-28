//! #485 / SR-145: `--component` exports the lifted function, not a function
//! the depth-0 replay aliased.
//!
//! The component wrapper replays the source's depth-0 sections, including
//! `(alias export $h "log" (func))`, which takes component function index 0.
//! The wrapper then counted its own functions from 0, so the export of `run`
//! named index 1 (meld's alias for the lower) instead of 2 (the lift). The
//! output validated, but wasmtime refused it: "component export 'run' is a
//! reexport of an imported function which is not implemented".

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasmtime::component::{Component, Linker};
use wasmtime::{Config, Engine, Store};

const SOURCE: &str = r#"
(component
  (import "my:h/host" (instance $h
    (export "log" (func (param "s" string) (result u32)))))
  (alias export $h "log" (func $log))
  (core module $M
    (memory (export "mem") 1)
    (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 0))
  (core module $A
    (import "env" "mem" (memory 1))
    (import "host" "log" (func $log (param i32 i32) (result i32)))
    (data (i32.const 0) "hello")
    (func (export "run") (result i32) i32.const 0 i32.const 5 call $log))
  (core instance $m (instantiate $M))
  (alias core export $m "mem" (core memory $mem))
  (core func $low (canon lower (func $log) (memory $mem)))
  (core instance $host (export "log" (func $low)))
  (core instance $envi (export "mem" (memory $mem)))
  (core instance $a (instantiate $A (with "env" (instance $envi)) (with "host" (instance $host))))
  (alias core export $a "run" (core func $arun))
  (func $run (result u32) (canon lift (core func $arun)))
  (export "run" (func $run)))
"#;

/// Instantiate `bytes` with a host `log` that returns the string's length,
/// and call `run`.
fn run(bytes: &[u8]) -> wasmtime::Result<u32> {
    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config)?;
    let component = Component::new(&engine, bytes)?;
    let mut linker = Linker::<()>::new(&engine);
    linker
        .instance("my:h/host")?
        .func_wrap("log", |_, (s,): (String,)| Ok((s.len() as u32,)))?;
    let mut store = Store::new(&engine, ());
    let instance = linker.instantiate(&mut store, &component)?;
    let f = instance.get_typed_func::<(), (u32,)>(&mut store, "run")?;
    Ok(f.call(&mut store, ())?.0)
}

fn fuse(memory_strategy: MemoryStrategy) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy,
        output_format: OutputFormat::Component,
        attestation: false,
        ..Default::default()
    });
    fuser
        .add_component(&wat::parse_str(SOURCE).expect("source parses"))
        .expect("add");
    fuser.fuse().expect("fusion")
}

// rivet: verifies SWV-155
#[test]
fn component_output_exports_the_lift_after_a_replayed_func_alias() {
    let source = wat::parse_str(SOURCE).unwrap();
    assert_eq!(run(&source).expect("the unfused component runs"), 5);
    for strategy in [MemoryStrategy::MultiMemory, MemoryStrategy::SharedMemory] {
        let fused = fuse(strategy);
        assert_eq!(
            run(&fused).unwrap_or_else(|e| panic!("{strategy:?}: fused component fails: {e:#}")),
            5,
            "{strategy:?}: fused `run` must behave like the unfused one"
        );
    }
}
