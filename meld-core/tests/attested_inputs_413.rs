//! #413 — the attestation must record the inputs the caller actually passed.
//!
//! `build_attestation` iterated `self.components`, meld's FLATTENED list, which
//! gains an entry per nested sub-component. Those synthesized entries carry no
//! source bytes, so they were attested with `hash: ""` and `size: 0`. For a
//! composed input — the pipeline the README documents — every attested input
//! hash was the empty string, and the real input's sha256 appeared nowhere in
//! the artifact. Two flat files produced four entries, two of them phantoms.
//!
//! #401 had already moved `components_fused` to the caller's input count and
//! left `inputs[]` on the flattened list, so a single attestation could report
//! `components_fused: 2` beside four input entries.
//!
//! These tests read the attestation back OUT OF THE FUSED ARTIFACT, through
//! `Fuser::fuse_with_stats`. The pre-existing input-hash test calls
//! `FusionAttestationBuilder` directly, below the defect, and so passed while
//! every shipped artifact carried empty hashes.
//!
//! All fixtures here are git-tracked, so these tests cannot silently skip in CI
//! (the failure mode of #405).

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use sha2::{Digest, Sha256};

fn fixture(rel: &str) -> Vec<u8> {
    let path = format!("{}/../{}", env!("CARGO_MANIFEST_DIR"), rel);
    std::fs::read(&path).unwrap_or_else(|e| panic!("tracked fixture {path} missing: {e}"))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    hex::encode(h.finalize())
}

/// The attestation JSON, pulled back out of the fused module's custom section.
fn attestation_of(fused: &[u8]) -> serde_json::Value {
    for payload in wasmparser::Parser::new(0).parse_all(fused) {
        if let wasmparser::Payload::CustomSection(r) = payload.expect("payload")
            && r.name() == "wsc.transformation.attestation"
        {
            return serde_json::from_slice(r.data()).expect("attestation is JSON");
        }
    }
    panic!("fused artifact carries no attestation section");
}

fn fuse(inputs: &[(&str, &[u8])], reproducible: bool) -> (Vec<u8>, meld_core::FusionStats) {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: true,
        reproducible,
        ..Default::default()
    });
    for (name, bytes) in inputs {
        fuser.add_component_named(bytes, Some(name)).expect("add");
    }
    fuser.fuse_with_stats().expect("fusion")
}

/// One attested input as read back from the artifact:
/// (name, hash, size, module_count).
type AttestedInput = (String, String, u64, Option<u64>);

/// (name, hash, size, module_count) for each attested input.
///
/// `module_count` is `Option` on purpose: the wsc attestation schema (the
/// optional `attestation` feature) has no such field. An earlier version used
/// `.unwrap_or(0)`, which silently turned "field absent" into "zero modules" —
/// a default standing in for a measurement.
fn attested_inputs(att: &serde_json::Value) -> Vec<AttestedInput> {
    att["inputs"]
        .as_array()
        .expect("inputs[] array")
        .iter()
        .map(|i| {
            (
                i["artifact"]["name"].as_str().unwrap_or("").to_string(),
                i["artifact"]["hash"].as_str().unwrap_or("").to_string(),
                i["artifact"]["size"].as_u64().unwrap_or(0),
                i.get("module_count").and_then(|m| m.as_u64()),
            )
        })
        .collect()
}

fn composed() -> Vec<(&'static str, Vec<u8>)> {
    vec![("composed.wasm", fixture("tests/gate/composed.wasm"))]
}

fn two_flat_files() -> Vec<(&'static str, Vec<u8>)> {
    vec![
        (
            "provider.wasm",
            fixture("tests/wit_bindgen/fixtures/compose/provider.wasm"),
        ),
        (
            "consumer.wasm",
            fixture("tests/wit_bindgen/fixtures/compose/consumer.wasm"),
        ),
    ]
}

fn run(
    inputs: &[(&'static str, Vec<u8>)],
    reproducible: bool,
) -> (meld_core::FusionStats, Vec<AttestedInput>) {
    let refs: Vec<(&str, &[u8])> = inputs.iter().map(|(n, b)| (*n, b.as_slice())).collect();
    let (fused, stats) = fuse(&refs, reproducible);
    (stats, attested_inputs(&attestation_of(&fused)))
}

/// The defect itself: the real input's sha256 must be in the artifact, and no
/// attested input may carry an empty hash. Checked against `sha256` of the
/// fixture file — an oracle independent of meld — for both the composed input
/// (where every hash was empty) and flat inputs (where half were).
// rivet: verifies SR-75
#[test]
fn every_attested_input_carries_the_real_input_hash() {
    for inputs in [composed(), two_flat_files()] {
        let (_, attested) = run(&inputs, false);
        for (name, hash, _, _) in &attested {
            assert!(
                !hash.is_empty(),
                "#413: attested input {name:?} has an EMPTY hash — the supply-chain \
                 record binds nothing"
            );
        }
        for (file, bytes) in &inputs {
            let want = sha256_hex(bytes);
            assert!(
                attested.iter().any(|(_, h, _, _)| *h == want),
                "#413: the sha256 of input {file} ({want}) appears nowhere in the \
                 attestation; attested: {attested:?}"
            );
        }
    }
}

/// One attested entry per file the caller passed — no phantoms from nested
/// sub-components — and sizes that match the files on disk.
// rivet: verifies SR-75
#[test]
fn inputs_are_what_the_caller_passed_with_their_real_sizes() {
    for inputs in [composed(), two_flat_files()] {
        let (stats, attested) = run(&inputs, false);
        assert_eq!(
            attested.len(),
            inputs.len(),
            "#413: one entry per input file, not per flattened sub-component: {attested:?}"
        );
        for ((file, bytes), (name, _, size, _)) in inputs.iter().zip(&attested) {
            assert_eq!(name, file, "attested in input order");
            assert_eq!(*size, bytes.len() as u64, "#413: attested size of {file}");
        }
        // The #401 sibling: the count and the list must agree within one record.
        assert_eq!(
            stats.components_fused,
            attested.len(),
            "#401/#413: components_fused and inputs[] disagree in the same attestation"
        );
    }
}

/// `input_size` feeds the attested `size_reduction_percent`. It summed the
/// flattened list and so reported 0 for a composed input.
// rivet: verifies SR-75
#[test]
fn input_size_is_the_bytes_the_caller_passed() {
    for inputs in [composed(), two_flat_files()] {
        let (stats, _) = run(&inputs, false);
        let want: usize = inputs.iter().map(|(_, b)| b.len()).sum();
        assert_eq!(
            stats.input_size, want,
            "#413: input_size must be the caller's bytes (was 0 for a composed input)"
        );
    }
}

/// Collapsing phantoms must not LOSE modules. A nested input's modules are
/// spread across its flattened children; the per-input count must sum them.
///
/// The two attestation schemas differ here, and this test asserts the truth of
/// each rather than compiling itself out of one (the pattern #408 reports). The
/// default schema records `module_count`, which must account for every merged
/// module. The wsc schema has no such field — asserted ABSENT, so if it is ever
/// added this fails and forces the count to be checked there too.
// rivet: verifies SR-75
#[test]
fn attested_module_counts_account_for_every_merged_module() {
    for inputs in [composed(), two_flat_files()] {
        let (stats, attested) = run(&inputs, false);
        let counts: Vec<Option<u64>> = attested.iter().map(|(_, _, _, m)| *m).collect();

        if cfg!(feature = "attestation") {
            assert!(
                counts.iter().all(Option::is_none),
                "the wsc schema was believed to carry no module_count; it now does, so \
                 check the per-input counts on this path too: {counts:?}"
            );
            continue;
        }

        let counts: Vec<u64> = counts
            .into_iter()
            .map(|m| m.expect("the default attestation schema records module_count"))
            .collect();
        assert_eq!(
            counts.iter().sum::<u64>(),
            stats.modules_merged as u64,
            "#413: per-input module counts must account for every merged module"
        );
        assert!(
            counts.iter().all(|m| *m > 0),
            "every real input contributes at least one module: {counts:?}"
        );
    }
}

/// Under `--reproducible` names become positional (#341) — by INPUT index —
/// and the hashes that pin the content must still be present.
// rivet: verifies SR-75
#[test]
fn reproducible_names_count_inputs_and_keep_the_hashes() {
    let inputs = two_flat_files();
    let (_, attested) = run(&inputs, true);
    let names: Vec<&str> = attested.iter().map(|(n, _, _, _)| n.as_str()).collect();
    assert_eq!(
        names,
        ["component-0", "component-1"],
        "#341/#413: input-indexed"
    );
    for ((file, bytes), (_, hash, _, _)) in inputs.iter().zip(&attested) {
        assert_eq!(
            *hash,
            sha256_hex(bytes),
            "#413: --reproducible replaces the name, never the hash ({file})"
        );
    }
}
