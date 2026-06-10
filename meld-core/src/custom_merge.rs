//! Same-name custom-section coalescing for `CustomSectionHandling::Merge`
//! (#222).
//!
//! The merger collects every input module's custom sections verbatim, so a
//! multi-module fusion (or a component whose core module already carries
//! tool metadata next to meld's own) emits several `producers` /
//! `target_features` sections. That violates both meld's documented `Merge`
//! contract ("merge custom sections with same name") and the layout LLVM's
//! wasm object reader enforces: known custom sections must appear at most
//! once, in canonical order `name` < `producers` < `target_features`
//! (unknown sections are ignored by the ranking). The observed failure is
//! `llvm-dwarfdump: out of order section type: 0` on the whole module —
//! making meld's remapped DWARF unreadable by every LLVM-based consumer.
//!
//! This module merges the two known formats per the tool-conventions spec
//! (field-wise union for `producers`, set union for `target_features`) and
//! returns the section list re-ordered so the known sections come last, in
//! canonical order — mirroring where LLVM itself places them. Payloads that
//! fail to parse are passed through unmerged (with a warning) rather than
//! risk corrupting bytes we don't understand; `name` and `.debug_*`
//! sections are not touched here (the emission layer handles those).

use std::collections::HashMap;

/// Coalesce a custom-section list for `Merge` emission.
///
/// Returns the sections with all parseable `producers` payloads merged into
/// at most one section and all parseable `target_features` payloads merged
/// into at most one section, both placed AFTER every other section in
/// canonical order (`producers` before `target_features`). The relative
/// order of all other sections is preserved.
pub fn coalesce(sections: &[(String, Vec<u8>)]) -> Vec<(String, Vec<u8>)> {
    let mut rest: Vec<(String, Vec<u8>)> = Vec::new();
    let mut producers: Vec<&[u8]> = Vec::new();
    let mut features: Vec<&[u8]> = Vec::new();

    for (name, data) in sections {
        match name.as_str() {
            "producers" => producers.push(data),
            "target_features" => features.push(data),
            _ => rest.push((name.clone(), data.clone())),
        }
    }

    if let Some(payload) = merge_producers(&producers, &mut rest) {
        rest.push(("producers".to_string(), payload));
    }
    if let Some(payload) = merge_target_features(&features, &mut rest) {
        rest.push(("target_features".to_string(), payload));
    }
    rest
}

/// Field-wise union of `producers` payloads per the tool-conventions
/// producers-section format. First-seen order of fields and values is
/// preserved. Value names are unique within a field — LLVM's reader
/// rejects "repeated producer" even when the version strings differ
/// (e.g. `rustc 1.80` + `rustc 1.81` from two input modules), so the
/// first-seen version wins and later versions are dropped with a log.
/// Unparseable payloads are pushed back into `rest` verbatim.
fn merge_producers(payloads: &[&[u8]], rest: &mut Vec<(String, Vec<u8>)>) -> Option<Vec<u8>> {
    // field name -> (insertion index, values in first-seen order)
    let mut fields: Vec<(String, Vec<(String, String)>)> = Vec::new();
    let mut index: HashMap<String, usize> = HashMap::new();
    let mut merged_any = false;

    for payload in payloads {
        match parse_producers(payload) {
            Some(parsed) => {
                merged_any = true;
                for (field, values) in parsed {
                    let slot = *index.entry(field.clone()).or_insert_with(|| {
                        fields.push((field.clone(), Vec::new()));
                        fields.len() - 1
                    });
                    for (name, version) in values {
                        match fields[slot].1.iter().find(|(n, _)| *n == name) {
                            None => fields[slot].1.push((name, version)),
                            Some((_, kept)) if *kept != version => {
                                log::debug!(
                                    "producers merge: field `{}` value `{name}` \
                                     keeps version `{kept}`, dropping `{version}`",
                                    fields[slot].0
                                );
                            }
                            Some(_) => {}
                        }
                    }
                }
            }
            None => {
                log::warn!(
                    "custom-section merge: unparseable `producers` payload \
                     ({} bytes) passed through unmerged",
                    payload.len()
                );
                rest.push(("producers".to_string(), payload.to_vec()));
            }
        }
    }

    if !merged_any {
        return None;
    }
    let mut out = Vec::new();
    write_u32(&mut out, fields.len() as u32);
    for (field, values) in &fields {
        write_str(&mut out, field);
        write_u32(&mut out, values.len() as u32);
        for (name, version) in values {
            write_str(&mut out, name);
            write_str(&mut out, version);
        }
    }
    Some(out)
}

/// Set union of `target_features` payloads (`(prefix byte, feature name)`
/// entries), preserving first-seen order. Unparseable payloads are pushed
/// back into `rest` verbatim.
fn merge_target_features(payloads: &[&[u8]], rest: &mut Vec<(String, Vec<u8>)>) -> Option<Vec<u8>> {
    let mut entries: Vec<(u8, String)> = Vec::new();
    let mut merged_any = false;

    for payload in payloads {
        match parse_target_features(payload) {
            Some(parsed) => {
                merged_any = true;
                for entry in parsed {
                    if !entries.contains(&entry) {
                        entries.push(entry);
                    }
                }
            }
            None => {
                log::warn!(
                    "custom-section merge: unparseable `target_features` payload \
                     ({} bytes) passed through unmerged",
                    payload.len()
                );
                rest.push(("target_features".to_string(), payload.to_vec()));
            }
        }
    }

    if !merged_any {
        return None;
    }
    let mut out = Vec::new();
    write_u32(&mut out, entries.len() as u32);
    for (prefix, name) in &entries {
        out.push(*prefix);
        write_str(&mut out, name);
    }
    Some(out)
}

/// One producers field: `(field-name, [(producer-name, version)])`.
type ProducersField = (String, Vec<(String, String)>);

/// `producers := count (field-name value-count (name version)*)*`
fn parse_producers(payload: &[u8]) -> Option<Vec<ProducersField>> {
    let mut pos = 0usize;
    let field_count = read_u32(payload, &mut pos)?;
    let mut fields = Vec::new();
    for _ in 0..field_count {
        let field = read_str(payload, &mut pos)?;
        let value_count = read_u32(payload, &mut pos)?;
        let mut values = Vec::new();
        for _ in 0..value_count {
            let name = read_str(payload, &mut pos)?;
            let version = read_str(payload, &mut pos)?;
            values.push((name, version));
        }
        fields.push((field, values));
    }
    (pos == payload.len()).then_some(fields)
}

/// `target_features := count (prefix-byte feature-name)*`
fn parse_target_features(payload: &[u8]) -> Option<Vec<(u8, String)>> {
    let mut pos = 0usize;
    let count = read_u32(payload, &mut pos)?;
    let mut entries = Vec::new();
    for _ in 0..count {
        let prefix = *payload.get(pos)?;
        pos += 1;
        let name = read_str(payload, &mut pos)?;
        entries.push((prefix, name));
    }
    (pos == payload.len()).then_some(entries)
}

fn read_u32(buf: &[u8], pos: &mut usize) -> Option<u32> {
    let mut result: u32 = 0;
    let mut shift = 0u32;
    loop {
        let byte = *buf.get(*pos)?;
        *pos += 1;
        if shift == 28 && byte > 0x0f {
            return None; // overflows u32
        }
        result |= u32::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Some(result);
        }
        shift += 7;
        if shift > 28 {
            return None;
        }
    }
}

fn read_str(buf: &[u8], pos: &mut usize) -> Option<String> {
    let len = read_u32(buf, pos)? as usize;
    let bytes = buf.get(*pos..*pos + len)?;
    *pos += len;
    let s = std::str::from_utf8(bytes).ok()?;
    Some(s.to_string())
}

fn write_u32(out: &mut Vec<u8>, mut value: u32) {
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

fn write_str(out: &mut Vec<u8>, s: &str) {
    write_u32(out, s.len() as u32);
    out.extend_from_slice(s.as_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;

    fn producers_payload(fields: &[(&str, &[(&str, &str)])]) -> Vec<u8> {
        let mut out = Vec::new();
        write_u32(&mut out, fields.len() as u32);
        for (field, values) in fields {
            write_str(&mut out, field);
            write_u32(&mut out, values.len() as u32);
            for (name, version) in *values {
                write_str(&mut out, name);
                write_str(&mut out, version);
            }
        }
        out
    }

    fn features_payload(entries: &[(u8, &str)]) -> Vec<u8> {
        let mut out = Vec::new();
        write_u32(&mut out, entries.len() as u32);
        for (prefix, name) in entries {
            out.push(*prefix);
            write_str(&mut out, name);
        }
        out
    }

    #[test]
    fn producers_field_wise_union_dedups_pairs() {
        let a = producers_payload(&[
            ("language", &[("Rust", "")]),
            ("processed-by", &[("rustc", "1.80")]),
        ]);
        let b = producers_payload(&[("processed-by", &[("rustc", "1.80"), ("clang", "18.0")])]);
        let sections = vec![("producers".to_string(), a), ("producers".to_string(), b)];
        let out = coalesce(&sections);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].0, "producers");
        let parsed = parse_producers(&out[0].1).expect("merged payload must parse");
        assert_eq!(
            parsed,
            vec![
                (
                    "language".to_string(),
                    vec![("Rust".to_string(), String::new())]
                ),
                (
                    "processed-by".to_string(),
                    vec![
                        ("rustc".to_string(), "1.80".to_string()),
                        ("clang".to_string(), "18.0".to_string()),
                    ]
                ),
            ]
        );
    }

    /// LLVM rejects "repeated producer" for a value name appearing twice in
    /// one field even with different versions — first-seen version wins.
    #[test]
    fn producers_same_name_different_version_keeps_first() {
        let a = producers_payload(&[("processed-by", &[("rustc", "1.80")])]);
        let b = producers_payload(&[("processed-by", &[("rustc", "1.81")])]);
        let sections = vec![("producers".to_string(), a), ("producers".to_string(), b)];
        let out = coalesce(&sections);
        assert_eq!(out.len(), 1);
        let parsed = parse_producers(&out[0].1).unwrap();
        assert_eq!(
            parsed,
            vec![(
                "processed-by".to_string(),
                vec![("rustc".to_string(), "1.80".to_string())]
            )]
        );
    }

    #[test]
    fn target_features_set_union_preserves_order() {
        let a = features_payload(&[(b'+', "bulk-memory"), (b'+', "simd128")]);
        let b = features_payload(&[(b'+', "simd128"), (b'+', "multimemory")]);
        let sections = vec![
            ("target_features".to_string(), a),
            ("target_features".to_string(), b),
        ];
        let out = coalesce(&sections);
        assert_eq!(out.len(), 1);
        let parsed = parse_target_features(&out[0].1).unwrap();
        assert_eq!(
            parsed,
            vec![
                (b'+', "bulk-memory".to_string()),
                (b'+', "simd128".to_string()),
                (b'+', "multimemory".to_string()),
            ]
        );
    }

    /// The canonical-order contract LLVM enforces: known sections last,
    /// `producers` strictly before `target_features`, everything else in
    /// original relative order.
    #[test]
    fn known_sections_emitted_last_in_canonical_order() {
        let sections = vec![
            (
                "target_features".to_string(),
                features_payload(&[(b'+', "simd128")]),
            ),
            (".debug_line".to_string(), vec![1, 2, 3]),
            (
                "producers".to_string(),
                producers_payload(&[("language", &[("Rust", "")])]),
            ),
            ("my-metadata".to_string(), vec![9]),
            (
                "producers".to_string(),
                producers_payload(&[("language", &[("C", "")])]),
            ),
        ];
        let out = coalesce(&sections);
        let names: Vec<&str> = out.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(
            names,
            vec![".debug_line", "my-metadata", "producers", "target_features"]
        );
    }

    /// Unparseable payloads must survive byte-identical (never corrupted by
    /// a half-understood merge), while parseable siblings still merge.
    #[test]
    fn unparseable_payload_passes_through_verbatim() {
        let good = producers_payload(&[("language", &[("Rust", "")])]);
        let bad = vec![0xff, 0xff, 0xff, 0xff, 0xff]; // unterminated LEB
        let sections = vec![
            ("producers".to_string(), good),
            ("producers".to_string(), bad.clone()),
        ];
        let out = coalesce(&sections);
        assert_eq!(out.len(), 2);
        assert!(out.iter().any(|(n, d)| n == "producers" && *d == bad));
        assert!(
            out.iter()
                .any(|(n, d)| n == "producers" && parse_producers(d).is_some())
        );
    }

    #[test]
    fn no_known_sections_is_identity() {
        let sections = vec![
            ("name".to_string(), vec![1]),
            (".debug_info".to_string(), vec![2]),
        ];
        assert_eq!(coalesce(&sections), sections);
    }

    #[test]
    fn single_producers_round_trips_content() {
        let payload = producers_payload(&[("sdk", &[("wasi-sdk", "20")])]);
        let sections = vec![("producers".to_string(), payload)];
        let out = coalesce(&sections);
        assert_eq!(out.len(), 1);
        assert_eq!(
            parse_producers(&out[0].1).unwrap(),
            vec![(
                "sdk".to_string(),
                vec![("wasi-sdk".to_string(), "20".to_string())]
            )]
        );
    }
}
