//! Integration oracle for #222: under `CustomSectionHandling::Merge`
//! (the default), the fused output carries at most ONE `producers` and
//! ONE `target_features` section, with `producers` strictly before
//! `target_features` — the canonical known-custom-section order LLVM's
//! wasm object reader enforces. The observed pre-fix failure was
//! `llvm-dwarfdump: out of order section type: 0` on the whole module
//! (four duplicate `producers` sections), making meld's remapped DWARF
//! unreadable by every LLVM-based consumer.
//!
//! The merged `producers` content must also be a superset of every
//! input section's fields — merging must lose nothing.

use meld_core::{Fuser, FuserConfig};
use wasmparser::{Parser, Payload};

/// Real Rust component carrying five `producers` sections across its
/// component/module layers (the #222 repro input).
const FIXTURE: &str = "../tests/wit_bindgen/fixtures/release-0.2.0/hello_rust.wasm";

fn fixture() -> Option<Vec<u8>> {
    match std::fs::read(FIXTURE) {
        Ok(bytes) => Some(bytes),
        Err(_) => {
            eprintln!("skipping: fixture not found at {FIXTURE}");
            None
        }
    }
}

fn custom_section_names(wasm: &[u8]) -> Vec<String> {
    let mut names = Vec::new();
    for payload in Parser::new(0).parse_all(wasm) {
        if let Payload::CustomSection(reader) = payload.unwrap() {
            names.push(reader.name().to_string());
        }
    }
    names
}

#[test]
fn merge_emits_single_producers_before_target_features() {
    let Some(input) = fixture() else { return };

    let mut fuser = Fuser::new(FuserConfig::default());
    fuser
        .add_component_named(&input, Some("hello_rust"))
        .unwrap();
    let fused = fuser.fuse().unwrap();

    let names = custom_section_names(&fused);
    let producers: Vec<usize> = names
        .iter()
        .enumerate()
        .filter(|(_, n)| n.as_str() == "producers")
        .map(|(i, _)| i)
        .collect();
    let features: Vec<usize> = names
        .iter()
        .enumerate()
        .filter(|(_, n)| n.as_str() == "target_features")
        .map(|(i, _)| i)
        .collect();

    assert_eq!(
        producers.len(),
        1,
        "Merge must coalesce producers sections; got {names:?}"
    );
    assert!(
        features.len() <= 1,
        "Merge must coalesce target_features sections; got {names:?}"
    );
    if let (Some(p), Some(f)) = (producers.first(), features.first()) {
        assert!(
            p < f,
            "canonical order requires producers before target_features; got {names:?}"
        );
    }
}

/// Merging must lose no producer: every (field, value-name) pair present
/// in any input `producers` section must survive into the merged one.
/// (Version strings are NOT asserted: LLVM rejects "repeated producer"
/// for the same value name even with differing versions, so the merge
/// keeps the first-seen version per name.)
#[test]
fn merged_producers_is_superset_of_inputs() {
    let Some(input) = fixture() else { return };

    // Collect all producers payload triples from the raw input bytes
    // (component and nested module layers alike) by scanning custom
    // sections at every nesting level.
    let mut input_triples: Vec<(String, String)> = Vec::new();
    let mut stack = vec![input.clone()];
    while let Some(bytes) = stack.pop() {
        for payload in Parser::new(0).parse_all(&bytes) {
            match payload.unwrap() {
                Payload::CustomSection(reader) if reader.name() == "producers" => {
                    for (field, name, _version) in parse_producers(reader.data()) {
                        let pair = (field, name);
                        if !input_triples.contains(&pair) {
                            input_triples.push(pair);
                        }
                    }
                }
                Payload::ModuleSection {
                    unchecked_range, ..
                } => {
                    stack.push(bytes[unchecked_range].to_vec());
                }
                _ => {}
            }
        }
    }
    assert!(
        !input_triples.is_empty(),
        "fixture must carry producers metadata for this oracle to bite"
    );

    let mut fuser = Fuser::new(FuserConfig::default());
    fuser
        .add_component_named(&input, Some("hello_rust"))
        .unwrap();
    let fused = fuser.fuse().unwrap();

    let mut merged_pairs: Vec<(String, String)> = Vec::new();
    for payload in Parser::new(0).parse_all(&fused) {
        if let Payload::CustomSection(reader) = payload.unwrap()
            && reader.name() == "producers"
        {
            merged_pairs.extend(
                parse_producers(reader.data())
                    .into_iter()
                    .map(|(f, n, _v)| (f, n)),
            );
        }
    }

    for pair in &input_triples {
        assert!(
            merged_pairs.contains(pair),
            "merged producers lost {pair:?}; merged = {merged_pairs:?}"
        );
    }
}

/// Minimal tool-conventions producers parse: (field, name, version) triples.
fn parse_producers(payload: &[u8]) -> Vec<(String, String, String)> {
    fn leb(buf: &[u8], pos: &mut usize) -> Option<u32> {
        let mut r = 0u32;
        let mut s = 0;
        loop {
            let b = *buf.get(*pos)?;
            *pos += 1;
            r |= u32::from(b & 0x7f) << s;
            if b & 0x80 == 0 {
                return Some(r);
            }
            s += 7;
        }
    }
    fn string(buf: &[u8], pos: &mut usize) -> Option<String> {
        let len = leb(buf, pos)? as usize;
        let s = std::str::from_utf8(buf.get(*pos..*pos + len)?).ok()?;
        *pos += len;
        Some(s.to_string())
    }
    let mut out = Vec::new();
    let mut pos = 0;
    let Some(fields) = leb(payload, &mut pos) else {
        return out;
    };
    for _ in 0..fields {
        let Some(field) = string(payload, &mut pos) else {
            return out;
        };
        let Some(values) = leb(payload, &mut pos) else {
            return out;
        };
        for _ in 0..values {
            let (Some(name), Some(version)) =
                (string(payload, &mut pos), string(payload, &mut pos))
            else {
                return out;
            };
            out.push((field.clone(), name, version));
        }
    }
    out
}
