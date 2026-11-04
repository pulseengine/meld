//! ADR-9: shared-everything threads are out of scope; P3 cooperative threads
//! are in scope (kiln) but not yet supported. Both must be REFUSED loudly --
//! never fused with the built-in silently dropped or mapped to `Unsupported`.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn fuse(wat: &str) -> Result<Vec<u8>, String> {
    let bytes = wat::parse_str(wat).expect("fixture parses as text");
    let mut out = Err(String::from("no strategy tried"));
    for strategy in [MemoryStrategy::MultiMemory, MemoryStrategy::SharedMemory] {
        let mut fuser = Fuser::new(FuserConfig {
            memory_strategy: strategy,
            ..Default::default()
        });
        out = fuser
            .add_component(&bytes)
            .and_then(|_| fuser.fuse())
            .map_err(|e| e.to_string());
        if out.is_ok() {
            return out;
        }
    }
    out
}

/// Shared-everything threads (ADR-9 path-T1, rejected).
// rivet: verifies SWV-120
#[test]
fn shared_everything_thread_spawn_is_refused() {
    let wat = r#"
(component
  (core module $m
    (import "" "spawn" (func $spawn (param i32 i32) (result i32)))
    (table (export "t") 1 funcref)
    (func (export "run") (result i32) (call $spawn (i32.const 0) (i32.const 0))))
  (core type $ft (shared (func (param i32))))
  (core func $sp (canon thread.spawn-ref $ft))
  (core instance $i (instantiate $m (with "" (instance (export "spawn" (func $sp))))))
  (func (export "run") (result u32) (canon lift (core func $i "run"))))
"#;
    let err = fuse(wat).expect_err("ADR-9: shared-everything threads must be refused");
    assert!(!err.is_empty(), "the refusal must say why");
}

/// P3 cooperative threads (ADR-9 path-T2, accepted, not yet implemented).
/// When the lowering lands, replace this with positive fuse-and-run tests.
// rivet: verifies SWV-120
#[test]
fn cooperative_thread_builtins_are_refused_until_supported() {
    let wat = r#"
(component
  (core module $m
    (import "" "idx" (func $idx (result i32)))
    (func (export "run") (result i32) (call $idx)))
  (core func $ti (canon thread.index))
  (core instance $i (instantiate $m (with "" (instance (export "idx" (func $ti))))))
  (func (export "run") (result u32) (canon lift (core func $i "run"))))
"#;
    let err = fuse(wat).expect_err("ADR-9: cooperative threads are not supported yet");
    assert!(
        err.contains("thread"),
        "the refusal must name threads: {err}"
    );
}

/// wasi-threads (P1): a defined `shared` memory plus `wasi:thread-spawn`.
/// meld 0.66.0 fused this at exit 0; ADR-9 makes it a refusal.
// rivet: verifies SWV-120
#[test]
fn wasi_threads_shared_memory_is_refused() {
    let wat = r#"
(component
  (core module $m
    (import "wasi" "thread-spawn" (func $spawn (param i32) (result i32)))
    (memory 1 1 shared)
    (func (export "run") (result i32) (call $spawn (i32.const 0)))
    (func (export "wasi_thread_start") (param i32 i32)))
  (core module $shim (func (export "thread-spawn") (param i32) (result i32) i32.const -1))
  (core instance $s (instantiate $shim))
  (core instance $i (instantiate $m (with "wasi" (instance $s))))
  (func (export "run") (result u32) (canon lift (core func $i "run"))))
"#;
    let err = fuse(wat).expect_err("ADR-9: wasi-threads must be refused");
    assert!(err.contains("ADR-9"), "the refusal must cite ADR-9: {err}");
}

/// An IMPORTED `shared` memory is refused the same way.
// rivet: verifies SWV-120
#[test]
fn imported_shared_memory_is_refused() {
    let wat = r#"
(component
  (core module $mem (memory (export "m") 1 1 shared))
  (core module $m
    (import "env" "m" (memory 1 1 shared))
    (func (export "run") (result i32) i32.const 7))
  (core instance $mi (instantiate $mem))
  (core instance $i (instantiate $m (with "env" (instance $mi))))
  (func (export "run") (result u32) (canon lift (core func $i "run"))))
"#;
    let err = fuse(wat).expect_err("ADR-9: an imported shared memory must be refused");
    assert!(err.contains("ADR-9"), "the refusal must cite ADR-9: {err}");
}
