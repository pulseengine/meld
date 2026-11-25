//! #666: a `stream`/`future` handle crossing a fused cross-component call
//! was passed raw. The Canonical ABI transfers the handle into the receiving
//! instance's table under a new index; fused, the receiver's built-in calls
//! named the sender's index, at exit 0. meld now refuses such an edge until
//! per-type copy adapters exist (ADR-10 step 6).
//!
//! * `stream_returned_by_sync_call`: a world-level `get: func() -> stream<u32>`.
//! * `future_param_via_interface`: an interface function taking `future<u32>`.
//! * `scalar_returned_by_sync_call`: the same shape returning `u32`, the
//!   control; it fuses and `run()` returns 42.

use std::path::Path;

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn fixture(name: &str) -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/issue_666")
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

#[test]
fn stream_or_future_across_a_fused_edge_is_refused() {
    for name in [
        "stream_returned_by_sync_call.wat",
        "future_param_via_interface.wat",
    ] {
        let err = fuse(&fixture(name)).expect_err(name);
        assert!(err.to_string().contains("#666"), "{name}: {err}");
    }
}

#[test]
fn scalar_across_a_fused_edge_still_fuses() {
    let fused = fuse(&fixture("scalar_returned_by_sync_call.wat")).expect("no handle crosses");
    let engine = wasmtime::Engine::default();
    let module = wasmtime::Module::new(&engine, &fused).expect("compile");
    assert_eq!(module.imports().len(), 0, "the call must be wired");
    let mut store = wasmtime::Store::new(&engine, ());
    let instance = wasmtime::Instance::new(&mut store, &module, &[]).expect("instantiate");
    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("run");
    assert_eq!(run.call(&mut store, ()).expect("runs"), 42);
}
