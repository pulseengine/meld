//! #423 — a `use`d record must count its real flat width, not 1.
//!
//! #393 fixed the *size* of a type reached through `use` by routing the size
//! paths through `resolve_defined_val_type`, which follows the instance-export
//! alias a `use` compiles to. The *flat count* was left on
//! `get_type_definition`, which stops at that alias, so every `use`d type
//! counted as **one** flat value.
//!
//! meld picks the calling convention from that number
//! (`resolver.rs`: `total_flat_params(..) > 16` selects params-ptr). The
//! existing `compose_record_use` fixture cannot reach the bug: its records are
//! four fields wide, so the true count is 4 and the wrong count is 1 — both
//! under the limit, same convention either way.
//!
//! This fixture crosses the limit, which is the shape jess ships: falcon's
//! `tick(state: vehicle-state, sp: setpoint)` is 14 + 4 = **18** flattened
//! params, with every record reached through `use`. meld counted 2.
//!
//! `run()` folds the whole argument tuple, so a params area that is wrongly
//! laid out shows up as a wrong number rather than only as a crash:
//!   `o1 = sum(1..14) = 105`, `o2 = sum(1..4) = 10`, `o3 = 1`, `o4 = 4` -> 120.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

const EXPECTED: f32 = 120.0;

fn fixture() -> Option<Vec<u8>> {
    let path = format!(
        "{}/../tests/wit_bindgen/fixtures/compose_record_use_wide/composed_wide_use.wasm",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read(path).ok()
}

fn fuse(bytes: &[u8], strategy: MemoryStrategy) -> Result<Vec<u8>, meld_core::Error> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: strategy,
        attestation: false,
        reproducible: true,
        ..Default::default()
    });
    fuser
        .add_component_named(bytes, Some("composed_wide_use"))
        .expect("fixture parses");
    fuser.fuse()
}

fn run(fused: &[u8]) -> f32 {
    use wasmtime::{Config, Engine, Instance, Module, Store};
    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).expect("engine");
    let module = Module::new(&engine, fused).expect("fused module loads");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiate");
    instance
        .get_typed_func::<(), f32>(&mut store, "golden:wideapp/runner@0.1.0#run")
        .expect("run export")
        .call(&mut store, ())
        .expect("call run")
}

/// The flat count meld computes decides the calling convention, so it is
/// checked directly against the emitted core signature rather than only
/// through behaviour: the provider's lift is `(param i32)`, which is what the
/// canonical ABI emits when the count is over MAX_FLAT_PARAMS.
// rivet: verifies SR-79
#[test]
fn used_records_count_their_real_flat_width() {
    let Some(bytes) = fixture() else {
        eprintln!("compose_record_use_wide fixture absent — skipping");
        return;
    };
    let parsed = meld_core::parser::ComponentParser::new()
        .parse(&bytes)
        .expect("fixture parses");

    // Find the lifted `tick` and ask meld for its flattened parameter count.
    let mut counts = Vec::new();
    for component in std::iter::once(&parsed).chain(parsed.sub_components.iter()) {
        for (_, (type_index, _)) in component.lift_info_by_core_func() {
            if let Some(def) = component.get_type_definition(type_index)
                && let meld_core::parser::ComponentTypeKind::Function { params, .. } = &def.kind
                && params.len() == 2
            {
                counts.push(component.total_flat_params(params));
            }
        }
    }

    assert!(
        !counts.is_empty(),
        "#423: the fixture's two-parameter lift was not found; the scan is broken"
    );
    assert!(
        counts.iter().all(|c| *c == 18),
        "#423: `state`(14 f32) + `setpoint`(4 f32) reached through `use` is 18 flattened \
         params, over MAX_FLAT_PARAMS; meld counted {counts:?}. The emitted core signature \
         is `(param i32)`, which the canonical ABI only produces above the limit."
    );
}

/// End to end: whatever convention meld picks, the fused module must still
/// compute the right answer. This is the test that says what the wrong count
/// actually costs.
// rivet: verifies SR-79
#[test]
fn wide_used_params_survive_fusion() {
    let Some(bytes) = fixture() else {
        eprintln!("compose_record_use_wide fixture absent — skipping");
        return;
    };
    let fused = match fuse(&bytes, MemoryStrategy::MultiMemory) {
        Ok(f) => f,
        Err(e) => panic!("#423: fusing a wide `use`d-param call failed: {e}"),
    };

    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&fused)
        .expect("#423: the fused module must validate");

    let got = run(&fused);
    assert_eq!(
        got, EXPECTED,
        "#423: an 18-flat-param call through `use`d records must be passed through the \
         params area — got {got}"
    );
}
