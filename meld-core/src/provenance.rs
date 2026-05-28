//! `component-provenance` custom section — issue #192 / scry DD-002.
//!
//! Maps every function in the fused Core Wasm module back to the
//! component + originating function index it came from, so downstream
//! consumers (notably `pulseengine/scry`'s sound abstract interpreter)
//! can project Component-Model invariants computed on the original
//! component sources onto fused-module locations.
//!
//! The data has been in-memory all along — [`crate::merger::MergedFunction::origin`]
//! is a `(component_idx, module_idx, function_idx)` triple built during
//! fusion. Prior to v0.14.0 it was discarded at emit time; this module
//! preserves it as a JSON-encoded custom section named
//! `component-provenance`.
//!
//! ## Boundary
//!
//! meld owns Core Wasm fusion correctness. scry owns Component-Model
//! semantics. The custom section is the typed contract between them.
//! This module deliberately does NOT carry:
//!
//! - Resource type names, handle shapes, capability-flow metadata
//! - WIT refinement predicates
//! - Adapter provenance (a future v2 ask)
//!
//! scry derives all of those from the original component sources
//! directly; meld only needs to provide the back-pointer.
//!
//! ## Self-referential hash
//!
//! Each provenance section carries `fused_module_sha256` to bind it to
//! a specific fused module. Because the section is itself part of the
//! module bytes, the hash is computed over the module WITHOUT the
//! provenance section (and without `wsc.transformation.attestation`).
//! Consumers verify by stripping both custom sections, hashing the
//! result, and comparing to `fused_module_sha256`. Same pattern
//! [`crate::attestation`] uses.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Custom-section name for the provenance payload. Wasm spec allows
/// arbitrary custom-section names; consumers identify by this string.
pub const SECTION_NAME: &str = "component-provenance";

/// Current section format version.
///
/// - **v1**: `{ fused_func_idx, component_id, originating_func_idx }`
///   per entry (issue #192).
/// - **v2** (DWARF Phase 2, issue #143): adds an optional
///   [`Entry::code_range`] giving the function body's byte span in
///   the fused module's code section. The field is the anchor for
///   DWARF address remapping. v1 consumers that check `version`
///   first will see `2` and can either upgrade or ignore the new
///   field (serde deserialization tolerates its absence via
///   `#[serde(default)]`, and its presence is additive — no v1 key
///   changed shape).
///
/// Consumers MUST check `version` before relying on `code_range`.
pub const VERSION: u32 = 2;

/// Byte span of a function body in the fused module's code section.
///
/// Offsets are **relative to the start of the code section's
/// contents** (the byte immediately after the code section's
/// size/count header — `wasmparser::Payload::CodeSectionStart.range.start`),
/// matching the WebAssembly-DWARF "code section relative" address
/// convention. `start` is the first byte of the function body
/// (its locals-declaration vector), `end` is one past its last
/// instruction byte — i.e. the half-open span `[start, end)` that
/// `wasmparser::FunctionBody::range()` reports, rebased to the
/// section content start.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodeRange {
    pub start: u32,
    pub end: u32,
}

/// One entry per defined function in the fused Core Wasm module.
///
/// Imported functions are *not* covered — their definition lives
/// outside meld's authorship, and there is no origin to attribute.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Entry {
    /// Absolute wasm function index in the fused output (including
    /// the leading imported-function slots; see
    /// [`crate::merger::MergedModule::defined_func`] for the
    /// imports-vs-defined arithmetic).
    pub fused_func_idx: u32,
    /// Stable component identifier — meld uses `comp.name` from the
    /// component's binary, falling back to a positional default of
    /// `component-<idx>` for nameless components.
    pub component_id: String,
    /// Function index within the originating component's flattened
    /// view (the `function_idx` field of
    /// `MergedFunction.origin: (comp_idx, mod_idx, func_idx)`).
    pub originating_func_idx: u32,
    /// v2: byte span of this function's body in the fused code
    /// section (see [`CodeRange`]). `None` when the code-offset map
    /// could not be built (e.g. the output had no code section).
    /// Serialized only when present so v1-shaped entries round-trip
    /// unchanged.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub code_range: Option<CodeRange>,
}

/// Decoded provenance section. Constructed by [`build`] at fusion
/// time; consumers should round-trip from the section bytes via
/// [`from_bytes`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComponentProvenance {
    pub version: u32,
    pub fused_module_sha256: String,
    pub entries: Vec<Entry>,
}

impl ComponentProvenance {
    /// JSON-encode for emission as the section payload. Compact (no
    /// pretty-printing) so the on-disk overhead is bounded by the
    /// number of functions; expected to be ~120 bytes per entry for
    /// typical component_id lengths.
    pub fn to_bytes(&self) -> Result<Vec<u8>, serde_json::Error> {
        serde_json::to_vec(self)
    }

    /// Inverse of [`to_bytes`]. Returns `Err` on malformed JSON; the
    /// caller is responsible for the `version` check.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, serde_json::Error> {
        serde_json::from_slice(bytes)
    }
}

/// Compute the SHA-256 hex digest of the given bytes. Lower-case hex,
/// no leading `0x`, 64 chars — same format as
/// [`crate::attestation::build_wsc_attestation`].
pub fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let out = hasher.finalize();
    hex::encode(out)
}

/// Extract the code-section-relative byte span of every defined
/// function body in `module_bytes`, in code-section order.
///
/// Returns `[(start, end); n_defined_functions]` with offsets
/// rebased to the code section content start (see [`CodeRange`]).
/// Empty if the module has no code section. The i-th entry
/// corresponds to the i-th defined function in code-section order:
/// meld writes `merged.functions` first, then adapter trampolines
/// (`meld-core/src/lib.rs` `encode_output`), so index `i` aligns
/// with `merged.functions[i]` for `i < merged.functions.len()`.
pub fn code_section_function_ranges(module_bytes: &[u8]) -> Vec<CodeRange> {
    let mut ranges = Vec::new();
    let mut content_start: Option<usize> = None;
    let parser = wasmparser::Parser::new(0);
    for payload in parser.parse_all(module_bytes) {
        match payload {
            Ok(wasmparser::Payload::CodeSectionStart { range, .. }) => {
                content_start = Some(range.start);
            }
            Ok(wasmparser::Payload::CodeSectionEntry(body)) => {
                let base = content_start.unwrap_or(0);
                let r = body.range();
                ranges.push(CodeRange {
                    start: (r.start - base) as u32,
                    end: (r.end - base) as u32,
                });
            }
            Ok(_) => {}
            Err(_) => break,
        }
    }
    ranges
}

/// Build a [`ComponentProvenance`] from the merged module + the
/// component slice. The hash binds the section to the fused module
/// without the section (call this with bytes that don't yet include
/// the `component-provenance` or `wsc.transformation.attestation`
/// custom sections — see the module-level note).
///
/// v2 (#143): each entry's [`Entry::code_range`] is populated from
/// the code section of `fused_bytes_without_extras` by index-order
/// alignment with `merged.functions`. If the parsed code section has
/// fewer bodies than `merged.functions` (should not happen for a
/// well-formed output), the missing entries get `code_range: None`
/// rather than a wrong span.
pub fn build(
    merged: &crate::merger::MergedModule,
    components: &[crate::parser::ParsedComponent],
    fused_bytes_without_extras: &[u8],
) -> ComponentProvenance {
    let import_count = merged.import_counts.func;
    let ranges = code_section_function_ranges(fused_bytes_without_extras);
    let entries: Vec<Entry> = merged
        .functions
        .iter()
        .enumerate()
        .map(|(defined_idx, mf)| {
            let (comp_idx, _mod_idx, func_idx) = mf.origin;
            let component_id = components
                .get(comp_idx)
                .and_then(|c| c.name.clone())
                .unwrap_or_else(|| format!("component-{comp_idx}"));
            Entry {
                fused_func_idx: import_count + defined_idx as u32,
                component_id,
                originating_func_idx: func_idx,
                code_range: ranges.get(defined_idx).copied(),
            }
        })
        .collect();

    ComponentProvenance {
        version: VERSION,
        fused_module_sha256: sha256_hex(fused_bytes_without_extras),
        entries,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip_preserves_payload() {
        let original = ComponentProvenance {
            version: VERSION,
            fused_module_sha256: "deadbeef".repeat(8),
            entries: vec![
                Entry {
                    fused_func_idx: 0,
                    component_id: "auth".into(),
                    originating_func_idx: 3,
                    code_range: Some(CodeRange { start: 0, end: 42 }),
                },
                Entry {
                    fused_func_idx: 1,
                    component_id: "db".into(),
                    originating_func_idx: 7,
                    code_range: Some(CodeRange {
                        start: 42,
                        end: 100,
                    }),
                },
            ],
        };
        let bytes = original.to_bytes().expect("serialize");
        let decoded = ComponentProvenance::from_bytes(&bytes).expect("deserialize");
        assert_eq!(original, decoded);
    }

    #[test]
    fn v1_shaped_entry_deserializes_with_none_code_range() {
        // A v1 producer emits entries without `code_range`. The v2
        // Entry struct must still deserialize them (serde default),
        // yielding `None`. This pins backward-compat so a v2 meld can
        // read a v1 section and a v2 consumer tolerates v1 entries.
        let v1_json = br#"{"version":1,"fused_module_sha256":"00","entries":[
            {"fused_func_idx":0,"component_id":"auth","originating_func_idx":3}
        ]}"#;
        let decoded = ComponentProvenance::from_bytes(v1_json).expect("deserialize v1");
        assert_eq!(decoded.entries.len(), 1);
        assert_eq!(decoded.entries[0].code_range, None);
    }

    #[test]
    fn code_range_omitted_from_json_when_none() {
        // v1-shaped round-trip: an entry with no code_range must not
        // emit a `code_range` key (skip_serializing_if), so a v2 meld
        // producing a None entry is byte-compatible with v1 readers.
        let cp = ComponentProvenance {
            version: VERSION,
            fused_module_sha256: "0".repeat(64),
            entries: vec![Entry {
                fused_func_idx: 0,
                component_id: "x".into(),
                originating_func_idx: 0,
                code_range: None,
            }],
        };
        let json: serde_json::Value =
            serde_json::from_slice(&cp.to_bytes().expect("serialize")).expect("parse json");
        assert!(
            json["entries"][0].get("code_range").is_none(),
            "code_range must be omitted when None; got {}",
            json["entries"][0]
        );
    }

    #[test]
    fn from_bytes_rejects_malformed_json() {
        assert!(ComponentProvenance::from_bytes(b"{not json}").is_err());
        assert!(ComponentProvenance::from_bytes(b"").is_err());
    }

    #[test]
    fn version_field_present_in_serialized_output() {
        // scry's consumer-side version check needs `version` to be a
        // top-level integer key so it can be inspected without
        // deserializing the entire payload. This pins that contract.
        let cp = ComponentProvenance {
            version: VERSION,
            fused_module_sha256: "0".repeat(64),
            entries: vec![],
        };
        let json: serde_json::Value =
            serde_json::from_slice(&cp.to_bytes().expect("serialize")).expect("parse json");
        assert_eq!(json["version"], serde_json::json!(VERSION));
    }

    #[test]
    fn empty_entries_serializes_to_empty_array() {
        let cp = ComponentProvenance {
            version: VERSION,
            fused_module_sha256: "0".repeat(64),
            entries: vec![],
        };
        let json: serde_json::Value =
            serde_json::from_slice(&cp.to_bytes().expect("serialize")).expect("parse json");
        assert_eq!(json["entries"], serde_json::json!([]));
    }

    #[test]
    fn sha256_hex_is_lowercase_64_chars() {
        let h = sha256_hex(b"hello world");
        assert_eq!(h.len(), 64);
        assert!(
            h.chars()
                .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
        );
        // Pin the canonical value for "hello world" so the hash impl
        // can't silently swap algorithms.
        assert_eq!(
            h,
            "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"
        );
    }

    #[test]
    fn code_section_ranges_are_ordered_nonoverlapping_one_per_function() {
        // Two functions of clearly different body sizes so the spans
        // are distinguishable. wat → wasm gives a real code section.
        let wasm = wat::parse_str(
            r#"(module
                (func (result i32) i32.const 1)
                (func (param i32 i32) (result i32)
                    local.get 0 local.get 1 i32.add))"#,
        )
        .expect("wat parse");

        let ranges = code_section_function_ranges(&wasm);
        assert_eq!(ranges.len(), 2, "expected one range per defined function");

        // Each span is non-empty and ordered, and consecutive spans
        // do not overlap (code-section bodies are laid out in order).
        assert!(ranges[0].start < ranges[0].end);
        assert!(ranges[1].start < ranges[1].end);
        assert!(
            ranges[0].end <= ranges[1].start,
            "function bodies must not overlap: {ranges:?}"
        );
        // The first body does NOT begin at rebased offset 0: the base
        // is `CodeSectionStart.range.start`, which points at the
        // section's count LEB. The first body content (locals + code,
        // per wasmparser's `FunctionBody::range()`) therefore starts a
        // few bytes in — past the count LEB and the body's own size
        // prefix. Assert it's small but non-zero rather than pinning
        // the exact constant (the precise base is cross-checked in
        // `code_section_ranges_rebased_to_content_start`).
        assert!(
            ranges[0].start > 0 && ranges[0].start < 16,
            "first body should start just past the count + size prefix; got {}",
            ranges[0].start
        );
    }

    #[test]
    fn code_section_ranges_empty_when_no_code_section() {
        // A module with only a type section (no functions) yields no
        // ranges — the `None` path for Entry::code_range.
        let wasm = wat::parse_str(r#"(module (type (func)))"#).expect("wat parse");
        let ranges = code_section_function_ranges(&wasm);
        assert!(
            ranges.is_empty(),
            "no code section ⇒ no ranges; got {ranges:?}"
        );
    }

    #[test]
    fn code_section_ranges_rebased_to_content_start() {
        // Cross-check the rebasing: independently re-parse the module,
        // capture the code-section content start and each body's
        // absolute range, and confirm code_section_function_ranges
        // reports exactly (absolute - content_start).
        let wasm = wat::parse_str(r#"(module (func nop) (func (result i32) i32.const 7))"#)
            .expect("wat parse");

        let mut content_start = None;
        let mut expected = Vec::new();
        for payload in wasmparser::Parser::new(0).parse_all(&wasm) {
            match payload.expect("parse") {
                wasmparser::Payload::CodeSectionStart { range, .. } => {
                    content_start = Some(range.start);
                }
                wasmparser::Payload::CodeSectionEntry(body) => {
                    let base = content_start.expect("code section started");
                    let r = body.range();
                    expected.push(CodeRange {
                        start: (r.start - base) as u32,
                        end: (r.end - base) as u32,
                    });
                }
                _ => {}
            }
        }

        assert_eq!(code_section_function_ranges(&wasm), expected);
    }
}
