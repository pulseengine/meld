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

/// Current section format version. Bumped on incompatible payload
/// changes; consumers MUST check `version` before parsing the rest.
pub const VERSION: u32 = 1;

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

/// Build a [`ComponentProvenance`] from the merged module + the
/// component slice. The hash binds the section to the fused module
/// without the section (call this with bytes that don't yet include
/// the `component-provenance` or `wsc.transformation.attestation`
/// custom sections — see the module-level note).
pub fn build(
    merged: &crate::merger::MergedModule,
    components: &[crate::parser::ParsedComponent],
    fused_bytes_without_extras: &[u8],
) -> ComponentProvenance {
    let import_count = merged.import_counts.func;
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
                },
                Entry {
                    fused_func_idx: 1,
                    component_id: "db".into(),
                    originating_func_idx: 7,
                },
            ],
        };
        let bytes = original.to_bytes().expect("serialize");
        let decoded = ComponentProvenance::from_bytes(&bytes).expect("deserialize");
        assert_eq!(original, decoded);
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
}
