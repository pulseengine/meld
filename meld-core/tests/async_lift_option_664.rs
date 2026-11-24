//! #664: meld chose a callee's calling convention from the `[async-lift]`
//! prefix on its core export name, not from the `canon lift` options. A
//! plainly named core export lifted with `async` was wired direct, so the
//! sync caller received the callback status code (0 = EXIT) instead of the
//! value passed to task.return (107), at exit 0.
//!
//! Three fixtures share one shape and differ only in the core export name and
//! the lift's async option:
//!
//! * `plain_named_async_lift`: export `f`, lifted async. Refused.
//! * `prefixed_sync_lift`: export `[async-lift]f`, lifted sync. Refused: the
//!   adapter would drive a callback loop over a sync function.
//! * `prefixed_async_lift`: export `[async-lift]f`, lifted async. The
//!   control: name and option agree, so it fuses and `go()` returns 107.

use std::path::Path;

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn fixture(name: &str) -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/issue_664")
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

/// Run the fused module's `go`, with every import stubbed to trap: the
/// callee calls task.return synchronously and exits, so no stub is reached.
fn run_go(fused: &[u8]) -> u32 {
    let mut config = wasmtime::Config::new();
    config.wasm_multi_memory(true);
    let engine = wasmtime::Engine::new(&config).expect("engine");
    let module = wasmtime::Module::new(&engine, fused).expect("compile fused");
    let mut linker = wasmtime::Linker::new(&engine);
    for import in module.imports() {
        let wasmtime::ExternType::Func(ty) = import.ty() else {
            panic!(
                "unexpected non-function import {}::{}",
                import.module(),
                import.name()
            );
        };
        let what = format!("{}::{}", import.module(), import.name());
        linker
            .func_new(import.module(), import.name(), ty, move |_, _, _| {
                Err(wasmtime::Error::msg(format!(
                    "stub {what} must not be called"
                )))
            })
            .expect("define stub");
    }
    let mut store = wasmtime::Store::new(&engine, ());
    let instance = linker
        .instantiate(&mut store, &module)
        .expect("instantiate");
    let go = instance
        .get_typed_func::<(), i32>(&mut store, "go")
        .expect("go export");
    go.call(&mut store, ()).expect("go runs") as u32
}

#[test]
fn plainly_named_async_lift_is_refused_not_wired_direct() {
    let err = fuse(&fixture("plain_named_async_lift.wat"))
        .expect_err("an async lift wired direct returns the status code: meld must refuse");
    assert!(err.to_string().contains("#664"), "unexpected error: {err}");
}

#[test]
fn prefixed_sync_lift_is_refused() {
    let err = fuse(&fixture("prefixed_sync_lift.wat"))
        .expect_err("a sync lift driven as a callback loop: meld must refuse");
    assert!(err.to_string().contains("#664"), "unexpected error: {err}");
}

#[test]
fn prefixed_async_lift_still_fuses_and_returns_the_result() {
    let fused = fuse(&fixture("prefixed_async_lift.wat")).expect("name and option agree");
    assert_eq!(run_go(&fused), 107, "go() must return task.return's value");
}
