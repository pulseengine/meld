//! #393 — a record reached through `use` must be sized exactly, not guessed.
//!
//! WIT's `use types.{torque}` compiles to an instance-export alias:
//!
//! ```wat
//! (alias export $golden:ctrl/types@0.1.0 "torque" (type $torque (;1;)))
//! (type (;2;) (func (param "a" f32) (param "b" f32) (result $torque)))
//! ```
//!
//! `get_type_definition` followed `Defined` and `ExportAlias` chains but stopped
//! at `InstanceExportAlias`, so the type was unresolvable — and an unresolvable
//! type silently sized as **4 bytes**. That single guess produced two very
//! different failures:
//!
//!   * **cross-memory** — `return_area_byte_size.unwrap_or(8)` copied 8 bytes of
//!     a 16-byte record. The fused module validated, ran without trapping, and
//!     returned a value with its later fields zeroed. A silent wrong answer.
//!   * **same-memory** — the resolver recorded the size only `if size > 4`, and
//!     4 is not > 4, so it stayed `None` and the #390 bridge refused. Loud, and
//!     the reason this was found at all.
//!
//! Reported by jess (meld#393) against falcon's cascade, whose `types`
//! interface every component `use`s.
//!
//! The fixture returns the **second** of two exported records on purpose. A type
//! export allocates a local type index inside the instance type; an
//! implementation that resolves `use`d types but forgets to allocate for exports
//! gets the first record right and the second wrong. The single-record fixture
//! written first could not catch that, and did not — falcon did.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

/// `tick(3, 4)` returns `motor{m1:3, m2:4, m3:7, m4:12}`; `run()` sums the four
/// fields. A short 8-byte copy yields 3 + 4 + 0 + 0 = 7 — which is exactly what
/// this returned before the fix, while validating cleanly.
const EXPECTED: f32 = 26.0;

fn fixture() -> Option<Vec<u8>> {
    let path = format!(
        "{}/../tests/wit_bindgen/fixtures/compose_record_use/composed_record_use.wasm",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read(path).ok()
}

fn fuse(bytes: &[u8], strategy: MemoryStrategy) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: strategy,
        attestation: false,
        reproducible: true,
        ..Default::default()
    });
    fuser
        .add_component_named(bytes, Some("composed_record_use"))
        .expect("fixture parses");
    fuser.fuse().expect("fusion succeeds")
}

fn run(fused: &[u8], multi_memory: bool) -> f32 {
    use wasmtime::{Config, Engine, Instance, Module, Store};
    let mut cfg = Config::new();
    cfg.wasm_threads(true);
    cfg.shared_memory(true);
    cfg.wasm_multi_memory(multi_memory);
    let engine = Engine::new(&cfg).expect("engine");
    let module = Module::new(&engine, fused).expect("fused module loads");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiate");
    instance
        .get_typed_func::<(), f32>(&mut store, "golden:recapp/runner@0.1.0#run")
        .expect("run export")
        .call(&mut store, ())
        .expect("call run")
}

/// The severe half: a module that validated and ran, and returned the wrong
/// number. Nothing trapped; only the value was wrong.
// rivet: verifies SR-72
#[test]
fn used_record_is_not_truncated_across_memories() {
    let Some(bytes) = fixture() else {
        eprintln!("compose_record_use fixture absent — skipping");
        return;
    };
    let fused = fuse(&bytes, MemoryStrategy::MultiMemory);

    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&fused)
        .expect("multi-memory fusion validates");

    let got = run(&fused, true);
    assert_eq!(
        got, EXPECTED,
        "#393: a `use`d record must be copied in full across memories — \
         got {got}, which is what an 8-byte copy of a 16-byte record produces"
    );
}

/// The half jess reported: the same unresolvable type made the #390 same-memory
/// bridge refuse, because an unknown size is (correctly) never guessed.
// rivet: verifies SR-72
#[test]
fn used_record_bridges_in_one_memory() {
    let Some(bytes) = fixture() else {
        eprintln!("compose_record_use fixture absent — skipping");
        return;
    };
    let fused = fuse(&bytes, MemoryStrategy::SharedMemory);

    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&fused)
        .expect("same-memory fusion validates");

    assert_eq!(
        run(&fused, false),
        EXPECTED,
        "#393: the same-memory bridge must resolve the `use`d return type"
    );
}

/// Both strategies must agree with each other and with the unfused component.
/// Fusion is a semantics-preserving transform; a strategy that changes the
/// answer is a defect regardless of which one is "right".
// rivet: verifies SR-72
#[test]
fn both_strategies_agree() {
    let Some(bytes) = fixture() else {
        eprintln!("compose_record_use fixture absent — skipping");
        return;
    };
    let multi = run(&fuse(&bytes, MemoryStrategy::MultiMemory), true);
    let shared = run(&fuse(&bytes, MemoryStrategy::SharedMemory), false);
    assert_eq!(multi, shared, "#393: the two memory strategies disagree");
    assert_eq!(multi, EXPECTED);
}

/// The resolution itself, at the parser level: a type reached through an
/// instance-export alias must size exactly. Guards the `can_size_exactly`
/// contract the resolver depends on — if this ever returns false again, the
/// sizes go back to being unknown and both paths above fail loudly rather than
/// silently, but they still fail.
// rivet: verifies SR-72
#[test]
fn used_types_are_exactly_sizeable() {
    let Some(bytes) = fixture() else {
        eprintln!("compose_record_use fixture absent — skipping");
        return;
    };
    let parsed = meld_core::parser::ComponentParser::new()
        .parse(&bytes)
        .expect("parses");

    // Walk every sub-component; the provider is the one declaring the exports.
    fn any_exports(c: &meld_core::parser::ParsedComponent) -> bool {
        !c.instance_type_exports.is_empty() || c.sub_components.iter().any(any_exports)
    }
    assert!(
        any_exports(&parsed),
        "#393: instance-type exports must be captured, or every `use`d type is \
         unresolvable and silently sized as 4 bytes"
    );
}
