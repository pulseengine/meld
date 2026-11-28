//! #709 / SR-143: the default build writes wsc-attestation 0.13's Fusion
//! schema, and records everything the hand-written schema records.
//!
//! Before #709 the wsc path was a second, hand-copied builder. It recorded
//! neither `profile`, `reproducible`, `pack_rebase`, `share_stack`, `domains`
//! nor the per-input module count, and labelled the transformation
//! `composition`. Now it is a conversion of the one `FusionAttestation`, and
//! these tests read the section back out of fused artifacts and compare it
//! with that record. The expected key sets are derived from meld's own types,
//! so a field added there is checked here without editing this file.
#![cfg(feature = "attestation")]

use meld_core::attestation::{FusionAttestationBuilder, FusionParameters};
use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use serde_json::Value;
use std::collections::BTreeSet;

fn fixture(rel: &str) -> Vec<u8> {
    let path = format!("{}/../{}", env!("CARGO_MANIFEST_DIR"), rel);
    std::fs::read(&path).unwrap_or_else(|e| panic!("tracked fixture {path} missing: {e}"))
}

fn section(fused: &[u8]) -> Vec<u8> {
    for payload in wasmparser::Parser::new(0).parse_all(fused) {
        if let wasmparser::Payload::CustomSection(r) = payload.expect("payload")
            && r.name() == "wsc.transformation.attestation"
        {
            return r.data().to_vec();
        }
    }
    panic!("fused artifact carries no attestation section");
}

fn fuse(inputs: &[(&str, Vec<u8>)]) -> (Vec<u8>, meld_core::FusionStats) {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: true,
        reproducible: true,
        ..Default::default()
    });
    for (name, bytes) in inputs {
        fuser.add_component_named(bytes, Some(name)).expect("add");
    }
    fuser.fuse_with_stats().expect("fusion")
}

fn corpus() -> Vec<Vec<(&'static str, Vec<u8>)>> {
    vec![
        vec![("composed.wasm", fixture("tests/gate/composed.wasm"))],
        vec![
            (
                "provider.wasm",
                fixture("tests/wit_bindgen/fixtures/compose/provider.wasm"),
            ),
            (
                "consumer.wasm",
                fixture("tests/wit_bindgen/fixtures/compose/consumer.wasm"),
            ),
        ],
    ]
}

fn keys(v: &Value) -> BTreeSet<String> {
    v.as_object()
        .expect("a JSON object")
        .keys()
        .cloned()
        .collect()
}

// rivet: verifies SWV-153
#[test]
fn default_build_writes_the_wsc_fusion_schema_at_parity() {
    for inputs in corpus() {
        let (fused, stats) = fuse(&inputs);
        let bytes = section(&fused);

        // wsc-attestation's own deserializer accepts it, as Fusion.
        let wsc: wsc_attestation::TransformationAttestation =
            serde_json::from_slice(&bytes).expect("wsc-attestation 0.13 parses the section");
        assert_eq!(
            wsc.transformation_type,
            wsc_attestation::TransformationType::Fusion
        );
        assert_eq!(wsc.inputs.len(), inputs.len(), "one input per caller input");

        let att: Value = serde_json::from_slice(&bytes).expect("JSON");

        // Every parameter the hand-written schema records is in
        // `tool.parameters`. `FusionParameters::default()` serializes every
        // always-present field; the optional ones are skipped when unset.
        let params = &att["tool"]["parameters"];
        let expected = keys(&serde_json::to_value(FusionParameters::default()).unwrap());
        let missing: Vec<_> = expected.difference(&keys(params)).cloned().collect();
        assert!(missing.is_empty(), "tool.parameters lacks {missing:?}");
        assert_eq!(params["reproducible"], Value::Bool(true));
        assert_eq!(params["profile"], "ecosystem");

        // Every metadata field the hand-written schema records, except
        // `parameters` (recorded once, above), is in `metadata`.
        let reference = FusionAttestationBuilder::new("meld", "x").build(&fused, &stats);
        let mut expected = keys(&serde_json::to_value(&reference.metadata).unwrap());
        expected.remove("parameters");
        let missing: Vec<_> = expected
            .difference(&keys(&att["metadata"]))
            .cloned()
            .collect();
        assert!(missing.is_empty(), "metadata lacks {missing:?}");
        assert!(
            att["metadata"].get("parameters").is_none(),
            "parameters are recorded once, in tool.parameters"
        );

        // The per-input module counts, in input order, account for every
        // merged module.
        let detail = att["metadata"]["inputs"]
            .as_array()
            .expect("metadata.inputs");
        assert_eq!(detail.len(), inputs.len());
        let counts: Vec<u64> = detail
            .iter()
            .map(|d| d["module_count"].as_u64().expect("module_count"))
            .collect();
        assert!(counts.iter().all(|c| *c > 0), "{counts:?}");
        assert_eq!(counts.iter().sum::<u64>(), stats.modules_merged as u64);
    }
}

/// `--reproducible` stays byte-stable with the wsc schema: `tool.parameters`
/// and `metadata` are `HashMap`s, which meld serializes through
/// `serde_json::Value` so their keys come out sorted.
// rivet: verifies SWV-153
#[test]
fn wsc_schema_is_byte_stable_under_reproducible() {
    for inputs in corpus() {
        let a = section(&fuse(&inputs).0);
        let b = section(&fuse(&inputs).0);
        assert_eq!(
            a, b,
            "two reproducible fusions wrote different attestations"
        );
    }
}
