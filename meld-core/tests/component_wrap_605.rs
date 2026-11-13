//! #605: `--component` on components whose exported interface defines its own
//! types. falcon-cascade v0.13.0's `pilot` defines two records and an enum.
//! The wrapper must export them from the interface instance under their WIT
//! names, emit the enum as an `enum` (not a payload-less variant), and point
//! the lifted functions at those exported types.
//!
//! Oracle: relay's `wac plug` composition of the same three inputs. Every
//! exported function of the composition and of meld's fusion is called on
//! wasmtime with the same generated arguments; the transcripts must match.

use std::path::Path;

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasmtime::component::types::ComponentItem;
use wasmtime::component::{Component, Type};
use wasmtime::{Config, Engine};

#[path = "support/component_transcript.rs"]
mod support;
use support::transcript;

fn fixture(name: &str) -> Vec<u8> {
    std::fs::read(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/issue_605")
            .join(name),
    )
    .expect("fixture")
}

fn fuse(inputs: &[&str]) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        output_format: OutputFormat::Component,
        attestation: false,
        ..Default::default()
    });
    for n in inputs {
        fuser.add_component(&fixture(n)).unwrap();
    }
    fuser.fuse().expect("--component fuses (#605)")
}

// rivet: verifies SR-124
// rivet: verifies SWV-138
#[test]
fn three_input_component_matches_the_wac_composition() {
    let expected = transcript(&fixture("composed.wasm"));
    // Potency: all six exports run, and the estimator state that observer
    // reads back is non-trivial (it went through the internal calls).
    assert_eq!(expected.len(), 6, "{expected:#?}");
    let read_state = expected
        .iter()
        .find(|l| l.contains("#read-state"))
        .expect("observer#read-state");
    assert!(read_state.contains("Float32(0.98"), "{read_state}");

    let fused = fuse(&[
        "cascade-split.wasm",
        "cascade-estimator.wasm",
        "cascade-control.wasm",
    ]);
    assert_eq!(transcript(&fused), expected);
}

// rivet: verifies SR-124
#[test]
fn pilot_types_are_exported_named_and_the_enum_stays_an_enum() {
    let fused = fuse(&["cascade-split.wasm"]);
    let mut config = Config::new();
    config.wasm_component_model(true);
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let component = Component::new(&engine, &fused).expect("wrapped split loads");
    let ctype = component.component_type();
    let (_, pilot) = ctype
        .exports(&engine)
        .find(|(n, _)| n.starts_with("pulseengine:falcon-cascade/pilot@"))
        .expect("pilot exported");
    let ComponentItem::ComponentInstance(pilot) = pilot.ty else {
        panic!("pilot is not an instance");
    };
    let kind = |name: &str| {
        pilot
            .exports(&engine)
            .find(|(n, _)| *n == name)
            .map(|(_, i)| i.ty)
            .unwrap_or_else(|| panic!("pilot lacks {name}"))
    };
    assert!(matches!(
        kind("pilot-command"),
        ComponentItem::Type(Type::Enum(_))
    ));
    assert!(matches!(
        kind("supervisor-config"),
        ComponentItem::Type(Type::Record(_))
    ));
    assert!(matches!(
        kind("sensor-calibration"),
        ComponentItem::Type(Type::Record(_))
    ));
    assert!(matches!(kind("command"), ComponentItem::ComponentFunc(_)));
}
