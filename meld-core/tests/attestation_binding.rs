//! #699 / sigil#396: the attestation's `output.hash` binds every byte of the
//! fused module except the one attestation section.
//!
//! wsc's chain check (`verify_attestation_binds_module` in sigil
//! `src/lib/src/composition/mod.rs`) parses the module into sections, removes
//! the first `wsc.transformation.attestation` section, re-serializes the rest
//! (section sizes in minimal LEB128) and compares the SHA-256 with
//! `output.hash`. Until #699 meld hashed the module without provenance and the
//! signature manifest as well, so that check failed on every meld output and
//! nothing bound the two sections hosts, kiln and scry read.
//!
//! `wsc_recompute` below mirrors that procedure. If sigil changes it, sigil's
//! own fixture (a meld-built module) is the cross-check.

use meld_core::{Fuser, FuserConfig, provenance, signature_manifest};

const ATTESTATION: &str = "wsc.transformation.attestation";
const FIXTURE: &str = "../tests/wit_bindgen/fixtures/lists.wasm";

struct Section {
    id: u8,
    /// Custom-section name, empty for other sections.
    name: String,
    /// Range of the section payload in the module bytes.
    payload: std::ops::Range<usize>,
}

fn read_leb_u32(bytes: &[u8]) -> (u32, usize) {
    let mut value = 0u32;
    for (i, &b) in bytes.iter().enumerate().take(5) {
        value |= u32::from(b & 0x7f) << (7 * i);
        if b & 0x80 == 0 {
            return (value, i + 1);
        }
    }
    panic!("unterminated LEB128");
}

fn write_leb_u32(out: &mut Vec<u8>, mut value: u32) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

fn sections(bytes: &[u8]) -> Vec<Section> {
    let mut out = Vec::new();
    let mut i = 8;
    while i < bytes.len() {
        let id = bytes[i];
        let (size, len) = read_leb_u32(&bytes[i + 1..]);
        let start = i + 1 + len;
        let end = start + size as usize;
        let name = if id == 0 {
            let (n, nlen) = read_leb_u32(&bytes[start..]);
            String::from_utf8(bytes[start + nlen..start + nlen + n as usize].to_vec())
                .expect("utf-8 custom section name")
        } else {
            String::new()
        };
        out.push(Section {
            id,
            name,
            payload: start..end,
        });
        i = end;
    }
    out
}

/// wsc's recomputation: drop the first attestation section, re-serialize the
/// others with minimal-LEB128 sizes, hash.
fn wsc_recompute(bytes: &[u8]) -> String {
    let all = sections(bytes);
    let first = all.iter().position(|s| s.id == 0 && s.name == ATTESTATION);
    let mut out = bytes[..8].to_vec();
    for (i, s) in all.iter().enumerate() {
        if Some(i) == first {
            continue;
        }
        out.push(s.id);
        write_leb_u32(&mut out, s.payload.len() as u32);
        out.extend_from_slice(&bytes[s.payload.clone()]);
    }
    provenance::sha256_hex(&out)
}

fn attested_output_hash(bytes: &[u8]) -> String {
    let all = sections(bytes);
    let att = all
        .iter()
        .find(|s| s.id == 0 && s.name == ATTESTATION)
        .expect("attestation section present");
    let payload = &bytes[att.payload.clone()];
    let (n, nlen) = read_leb_u32(payload);
    let json: serde_json::Value =
        serde_json::from_slice(&payload[nlen + n as usize..]).expect("attestation is JSON");
    json["output"]["hash"]
        .as_str()
        .expect("output.hash is a string")
        .to_string()
}

fn fuse_with_all_metadata(reproducible: bool) -> Vec<u8> {
    let bytes = std::fs::read(FIXTURE).unwrap_or_else(|e| {
        panic!("fixture {FIXTURE} must be tracked (SR-85): {e}");
    });
    let config = FuserConfig {
        signature_manifest: true,
        reproducible,
        ..FuserConfig::default()
    };
    assert!(config.attestation && config.component_provenance);
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&bytes, Some("lists"))
        .expect("add_component");
    fuser.fuse().expect("fuse")
}

// rivet: verifies SWV-151
#[test]
fn output_hash_covers_everything_but_the_attestation() {
    for reproducible in [false, true] {
        let fused = fuse_with_all_metadata(reproducible);
        let all = sections(&fused);

        // Both metadata sections a verifier must not be able to change are
        // present, so the binding below actually covers them.
        for name in [provenance::SECTION_NAME, signature_manifest::SECTION_NAME] {
            assert_eq!(
                all.iter().filter(|s| s.id == 0 && s.name == name).count(),
                1,
                "{name} present once"
            );
        }
        let attestations: Vec<usize> = all
            .iter()
            .enumerate()
            .filter(|(_, s)| s.id == 0 && s.name == ATTESTATION)
            .map(|(i, _)| i)
            .collect();
        assert_eq!(attestations, vec![all.len() - 1], "one attestation, last");

        assert_eq!(
            wsc_recompute(&fused),
            attested_output_hash(&fused),
            "output.hash must equal wsc's recomputation (reproducible={reproducible})"
        );
    }
}

/// Negative control: one flipped byte in the provenance payload, the
/// signature manifest or the code must break the binding.
// rivet: verifies SWV-151
#[test]
fn a_changed_metadata_or_code_byte_breaks_the_binding() {
    let fused = fuse_with_all_metadata(true);
    let expected = attested_output_hash(&fused);
    assert_eq!(wsc_recompute(&fused), expected, "baseline binds");

    let all = sections(&fused);
    let targets = [
        (0u8, provenance::SECTION_NAME),
        (0u8, signature_manifest::SECTION_NAME),
        (10u8, "code"),
    ];
    for (id, name) in targets {
        let s = all
            .iter()
            .find(|s| s.id == id && (id != 0 || s.name == name))
            .unwrap_or_else(|| panic!("{name} section present"));
        let mut tampered = fused.clone();
        // The last payload byte: inside the data for every target, past the
        // custom-section name.
        tampered[s.payload.end - 1] ^= 0x01;
        assert_ne!(
            wsc_recompute(&tampered),
            expected,
            "a flipped byte in {name} must fail the binding"
        );
    }
}
