//! #663: a sync caller fused to an `[async-lift]` callee read its result
//! from the callee's task.return shim only when the shim's name was found in
//! the callee's FIRST core module. With a memory-only module first, the
//! adapter fell back to returning zeros, so `go()` gave 0 at exit 0 instead
//! of 107.
//!
//! The fixtures differ only in the order of the callee's core modules. Both
//! are fused and run on wasmtime with the two remaining `$root` built-ins
//! stubbed to trap: the callee calls task.return synchronously and exits,
//! so neither stub may be reached. The third fixture names its task.return
//! import `task.return` (not `[task-return]f`), so meld finds no shim and
//! must refuse instead of returning zeros.

use std::path::Path;

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn fixture(name: &str) -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/issue_663")
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

/// Run the fused module's `go`, with every `$root` import stubbed to trap.
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
fn async_result_does_not_depend_on_core_module_order() {
    for name in ["memory_module_second.wat", "memory_module_first.wat"] {
        let fused = fuse(&fixture(name)).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(
            run_go(&fused),
            107,
            "{name}: go() must return task.return's value"
        );
    }
}

#[test]
fn missing_task_return_shim_is_refused_not_zero() {
    let err = fuse(&fixture("unprefixed_task_return.wat"))
        .expect_err("no shim means no result: meld must refuse");
    assert!(err.to_string().contains("#663"), "unexpected error: {err}");
}
