//! #390 — a same-memory cross-component call that carries a record.
//!
//! `--memory shared` makes every fused boundary `Direct`, and the `Direct`
//! lowering used to assume "same memory" implied "same signature". It does not.
//! The canonical ABI switches a side to an indirect convention whenever a value
//! exceeds a flattening limit, so a record travelling through linear memory
//! leaves the two sides typed differently:
//!
//! ```text
//!   caller (lowered): (f32, f32, retptr: i32) -> ()
//!   callee (lifted):  (f32, f32)              -> i32   ; return-area pointer
//! ```
//!
//! meld forwarded the params verbatim AND (#304) wired the caller straight to
//! the callee. Both produce a type-invalid module — while meld exits 0.
//!
//! Reported by jess against a falcon flight-app + cascade composition, where it
//! left a composed application+runtime image with **no** single-address-space
//! (MCU) lowering path: `--memory multi` validated but has no MCU lowering
//! (#172), and every `--memory shared` route emitted invalid wasm.
//!
//! The fixture is deliberately hermetic (`tests/wit_bindgen/fixtures/
//! compose_record/build.sh`, wasm-tools + wac, no network): neither core module
//! declares a data segment, so the SR-56 overlap gate and the path-F relocation
//! gate stay quiet and the BOUNDARY is what these tests exercise. That
//! separation is the point — on real inputs those gates force `--address-rebase`
//! / `--pack-rebase` to be present, which is why the defect looked like a rebase
//! bug. It is not: none of these tests passes a rebase flag.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

/// The record-carrying consumer→provider composition. `run()` computes
/// `tx + ty + tz + thrust` of `tick(3, 4)` = `3 + 4 + 7 + 12` = 26.
fn composed_record_fixture() -> Option<Vec<u8>> {
    let path = format!(
        "{}/../tests/wit_bindgen/fixtures/compose_record/composed_record.wasm",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read(path).ok()
}

fn fuse_shared(bytes: &[u8]) -> (Vec<u8>, meld_core::FusionStats) {
    let mut fuser = Fuser::new(FuserConfig {
        // No rebase flag: `--memory shared` alone is enough to reproduce #390.
        memory_strategy: MemoryStrategy::SharedMemory,
        attestation: false,
        reproducible: true,
        ..Default::default()
    });
    fuser
        .add_component_named(bytes, Some("composed_record"))
        .expect("fixture parses");
    fuser.fuse_with_stats().expect("fusion succeeds")
}

/// The defect itself: the fused module must be **valid wasm**.
///
/// Before the fix this failed with `type mismatch: expected f32, found i32` —
/// the caller pushed `(f32, f32, i32)` at a callee expecting `(f32, f32)`.
#[test]
fn same_memory_record_boundary_emits_valid_wasm() {
    let Some(bytes) = composed_record_fixture() else {
        eprintln!("compose_record fixture absent — skipping");
        return;
    };
    let (fused, _stats) = fuse_shared(&bytes);

    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&fused)
        .unwrap_or_else(|e| {
            panic!("#390: fusing a record-carrying same-memory boundary produced INVALID wasm: {e}")
        });
}

/// A module that validates can still compute the wrong thing: if the bridge
/// copies the wrong bytes, or from the wrong offset, `validate` is silent and
/// the numbers are garbage. Pin the value, not just the shape.
#[test]
fn same_memory_record_boundary_computes_the_same_answer() {
    use wasmtime::{Config, Engine, Instance, Module, Store};

    let Some(bytes) = composed_record_fixture() else {
        eprintln!("compose_record fixture absent — skipping");
        return;
    };
    let (fused, _stats) = fuse_shared(&bytes);

    let mut cfg = Config::new();
    cfg.wasm_threads(true);
    cfg.shared_memory(true);
    let engine = Engine::new(&cfg).expect("engine");
    let module = Module::new(&engine, &fused).expect("fused module loads");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiate");

    let run = instance
        .get_typed_func::<(), f32>(&mut store, "golden:recapp/runner@0.1.0#run")
        .expect("run export");
    let got = run.call(&mut store, ()).expect("call run");

    // tick(3, 4) = {tx: 3, ty: 4, tz: 7, thrust: 12}; run() sums them.
    assert_eq!(
        got, 26.0,
        "#390: the return-area bridge must deliver the callee's results \
         unchanged to the caller's retptr"
    );
}

/// The #304 half. A convention bridge is NOT a pure identity forward, so the
/// caller must go through the thunk. Inlining it would wire the caller straight
/// to a differently-typed callee — which is how the invalid module was produced.
#[test]
fn a_record_carrying_boundary_is_never_inlined() {
    let Some(bytes) = composed_record_fixture() else {
        eprintln!("compose_record fixture absent — skipping");
        return;
    };
    let (_fused, stats) = fuse_shared(&bytes);

    let boundary = stats
        .boundaries
        .iter()
        .find(|b| b.function.contains("tick"))
        .expect("the tick boundary is recorded");

    assert_eq!(
        boundary.lowering, "direct",
        "same memory + same encoding is still a Direct boundary"
    );
    assert_eq!(
        boundary.wiring, "thunk",
        "#390: a return-area bridge must be wired as a thunk, never inlined away"
    );
    assert!(
        !boundary.crosses_memory,
        "the fixture is the SAME-memory case — that is what makes it #390 \
         rather than the cross-memory retptr path that already worked"
    );
    assert_eq!(
        stats.adapters_inlined, 0,
        "#390: nothing in this composition is a pure identity forward"
    );
}

/// The control row from jess's table: `--memory multi` was always valid, because
/// the cross-memory path already detects this convention mismatch
/// (`uses_retptr` → `generate_retptr_adapter`). It must stay valid — the fix
/// adds a same-memory bridge, it does not touch the cross-memory one.
#[test]
fn multi_memory_control_still_valid() {
    let Some(bytes) = composed_record_fixture() else {
        eprintln!("compose_record fixture absent — skipping");
        return;
    };
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        reproducible: true,
        ..Default::default()
    });
    fuser
        .add_component_named(&bytes, Some("composed_record"))
        .expect("fixture parses");
    let fused = fuser.fuse().expect("fusion succeeds");

    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&fused)
        .expect("the multi-memory control must remain valid");
}
