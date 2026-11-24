//! #565: meld matched a cross-component callee by its core export name
//! (`local:t/calc#add`) and ignored the core function the `canon lift`
//! names. In `lift_names_task_hook` the lift names `hook0`, which sets the
//! stack pointer global to 1000 around a call of the raw function (the shape
//! wasm32-wasip3's `__wasm_task_hook` fixup produces). Fused, `go()`
//! returned 3; the lift gives 1 + 2 + 1000 = 1003. meld now refuses.
//!
//! `lift_names_raw_export` is the control: the lift names the raw export
//! itself, so the name match is the lifted function. It fuses and `go()`
//! returns 3, which is the lift's answer there.

use std::path::Path;

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn fixture(name: &str) -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/issue_565")
        .join(name);
    wat::parse_file(&path).unwrap_or_else(|e| panic!("tracked fixture {name}: {e}"))
}

fn fuse(bytes: &[u8]) -> meld_core::Result<Vec<u8>> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component(bytes)?;
    fuser.fuse()
}

fn run_go(fused: &[u8]) -> u32 {
    let mut config = wasmtime::Config::new();
    config.wasm_multi_memory(true);
    let engine = wasmtime::Engine::new(&config).expect("engine");
    let module = wasmtime::Module::new(&engine, fused).expect("compile fused");
    assert_eq!(
        module.imports().len(),
        0,
        "the call must be wired, not left to the host"
    );
    let mut store = wasmtime::Store::new(&engine, ());
    let instance = wasmtime::Instance::new(&mut store, &module, &[]).expect("instantiate");
    let go = instance
        .get_typed_func::<(), i32>(&mut store, "go")
        .expect("go export");
    go.call(&mut store, ()).expect("go runs") as u32
}

#[test]
fn callee_matched_past_its_lift_is_refused() {
    let err = fuse(&fixture("lift_names_task_hook.wat"))
        .expect_err("calling the raw export skips the lifted wrapper: meld must refuse");
    assert!(err.to_string().contains("#565"), "unexpected error: {err}");
}

#[test]
fn callee_matched_to_its_lift_still_fuses() {
    let fused = fuse(&fixture("lift_names_raw_export.wat")).expect("the name match is the lift");
    assert_eq!(run_go(&fused), 3);
}
