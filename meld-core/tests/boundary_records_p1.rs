//! ADR-7 P1 — per-boundary strategy records: **declared, attested, observable**.
//!
//! ADR-7 made it a binding requirement that each fused boundary's strategy be
//! recorded and auditable, not inferable only from aggregate counts. meld now
//! emits one `BoundaryRecord` per entry in `DependencyGraph::adapter_sites`,
//! carrying the call-lowering class chosen for that boundary and — critically —
//! how it was ACTUALLY wired.
//!
//! The wiring field is recorded at the wiring step rather than from the lowering
//! seam's `inline_eligible`, because a widening wrapper takes precedence over
//! inlining: eligibility alone would misreport what shipped.
//!
//! Pinned here:
//!   1. one record per adapter site, in that (deterministically sorted) order;
//!   2. the record describes a real boundary (endpoints, function, lowering,
//!      wiring), and `adapters_inlined` agrees with the records;
//!   3. the records reach the fusion attestation embedded in the artifact;
//!   4. they are stable across runs (safe under `--reproducible`).

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

/// The wac-composed consumer→provider fixture (a genuine cross-component call).
fn composed_fixture() -> Option<Vec<u8>> {
    let path = format!(
        "{}/../tests/wit_bindgen/fixtures/compose/composed.wasm",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read(path).ok()
}

fn fuse(bytes: &[u8]) -> (Vec<u8>, meld_core::FusionStats) {
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        reproducible: true,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser.add_component_named(bytes, Some("composed")).unwrap();
    fuser.fuse_with_stats().expect("fusion")
}

#[test]
fn every_fused_boundary_is_recorded_with_its_strategy() {
    let Some(bytes) = composed_fixture() else {
        eprintln!("composed.wasm fixture absent — skipping");
        return;
    };
    let (_out, stats) = fuse(&bytes);

    // (1) A cross-component composition must produce at least one boundary, and
    // one record per generated adapter (records are emitted per adapter site).
    assert!(
        !stats.boundaries.is_empty(),
        "a wac-composed consumer->provider fusion must record a boundary"
    );
    assert_eq!(
        stats.boundaries.len(),
        stats.adapter_functions,
        "exactly one boundary record per generated adapter"
    );

    // (2) Each record describes a real boundary with a known strategy.
    for b in &stats.boundaries {
        assert!(
            !b.function.is_empty(),
            "boundary must name the callee function: {b:?}"
        );
        assert!(
            matches!(
                b.lowering.as_str(),
                "direct" | "memory-copy" | "transcode" | "async-lift"
            ),
            "unknown lowering label {:?}",
            b.lowering
        );
        assert!(
            matches!(
                b.wiring.as_str(),
                "inlined-direct" | "widening-wrapper" | "thunk"
            ),
            "unknown wiring label {:?}",
            b.wiring
        );
    }

    // The inline COUNT must agree with the records — this is what catches the
    // eligibility-vs-outcome confusion the wiring-step recording exists to avoid.
    let inlined_records = stats
        .boundaries
        .iter()
        .filter(|b| b.wiring == "inlined-direct")
        .count();
    assert_eq!(
        inlined_records, stats.adapters_inlined,
        "records must agree with the inlined tally (outcome, not eligibility)"
    );
}

#[test]
fn boundary_records_reach_the_attestation() {
    let Some(bytes) = composed_fixture() else {
        eprintln!("composed.wasm fixture absent — skipping");
        return;
    };
    let (out, stats) = fuse(&bytes);
    assert!(
        !stats.boundaries.is_empty(),
        "expected a boundary to attest"
    );

    // Pull the attestation custom section back out of the artifact — the
    // "auditable after the fact" half of the requirement.
    let mut attestation_json: Option<String> = None;
    for payload in wasmparser::Parser::new(0).parse_all(&out) {
        if let wasmparser::Payload::CustomSection(reader) = payload.expect("payload")
            && reader.name() == "wsc.transformation.attestation"
        {
            attestation_json = Some(String::from_utf8_lossy(reader.data()).into_owned());
        }
    }
    let json = attestation_json.expect("fused artifact carries an attestation section");
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("attestation is valid JSON");

    let boundaries = parsed
        .get("metadata")
        .and_then(|m| m.get("boundaries"))
        .and_then(|b| b.as_array())
        .expect("attestation metadata carries boundaries");
    assert_eq!(
        boundaries.len(),
        stats.boundaries.len(),
        "every recorded boundary must be attested"
    );

    let first = &boundaries[0];
    for key in [
        "from_component",
        "to_component",
        "function",
        "lowering",
        "wiring",
        "crosses_memory",
    ] {
        assert!(
            first.get(key).is_some(),
            "attested boundary must carry `{key}`: {first}"
        );
    }
}

#[test]
fn boundary_records_are_stable_across_runs() {
    let Some(bytes) = composed_fixture() else {
        eprintln!("composed.wasm fixture absent — skipping");
        return;
    };
    // `adapter_sites` is sorted into a total order by the resolver, so records
    // emitted in that order must be identical run to run — otherwise embedding
    // them in the attestation would break `--reproducible`.
    let (_, a) = fuse(&bytes);
    let (_, b) = fuse(&bytes);
    assert_eq!(
        a.boundaries, b.boundaries,
        "boundary records must be deterministic (they are serialized into the attestation)"
    );
}
