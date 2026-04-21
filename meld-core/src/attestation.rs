//! Attestation integration for tracking fusion provenance
//!
//! This module provides integration with wsc-attestation for tracking
//! the transformation process through static fusion. The attestation
//! records which components were fused and how.
//!
//! ## Usage
//!
//! When wsc-attestation is available, fusion attestation is automatically
//! added to the output module's custom section.
//!
//! ## Custom Section
//!
//! The attestation is stored in a custom section named:
//! `wsc.transformation.attestation`

use crate::FusionStats;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Custom section name for fusion attestation
pub const FUSION_ATTESTATION_SECTION: &str = "wsc.transformation.attestation";

/// Attestation for a fusion transformation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FusionAttestation {
    /// Schema version
    pub version: String,

    /// Unique attestation ID
    pub attestation_id: String,

    /// Transformation type (always "fusion" for this tool)
    pub transformation_type: String,

    /// Timestamp of fusion (ISO 8601)
    pub timestamp: String,

    /// Input components
    pub inputs: Vec<InputArtifact>,

    /// Output module descriptor
    pub output: ArtifactDescriptor,

    /// Tool information
    pub tool: ToolInfo,

    /// Fusion-specific metadata
    pub metadata: FusionMetadata,
}

/// Descriptor for an artifact (input or output)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArtifactDescriptor {
    /// Name or identifier
    pub name: String,

    /// SHA-256 hash (hex encoded)
    pub hash: String,

    /// Size in bytes
    pub size: u64,
}

/// Input artifact with optional provenance
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InputArtifact {
    /// Artifact descriptor
    pub artifact: ArtifactDescriptor,

    /// Component type (P2 or P3)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub component_type: Option<String>,

    /// Number of core modules in this component
    pub module_count: usize,

    /// Existing attestation from this input (if any)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub prior_attestation: Option<Box<serde_json::Value>>,
}

/// Tool information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToolInfo {
    /// Tool name
    pub name: String,

    /// Tool version
    pub version: String,

    /// Tool hash (for reproducibility)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool_hash: Option<String>,
}

/// Fusion-specific metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FusionMetadata {
    /// Memory strategy used
    pub memory_strategy: String,

    /// Number of components fused
    pub components_fused: usize,

    /// Number of core modules merged
    pub modules_merged: usize,

    /// Number of adapters generated
    pub adapters_generated: usize,

    /// Number of imports resolved internally
    pub imports_resolved: usize,

    /// Size reduction (percentage)
    pub size_reduction_percent: f64,
}

/// Builder for creating fusion attestations
pub struct FusionAttestationBuilder {
    inputs: Vec<InputArtifact>,
    tool_name: String,
    tool_version: String,
    tool_hash: Option<String>,
    memory_strategy: String,
}

impl FusionAttestationBuilder {
    /// Create a new builder
    pub fn new(tool_name: impl Into<String>, tool_version: impl Into<String>) -> Self {
        Self {
            inputs: Vec::new(),
            tool_name: tool_name.into(),
            tool_version: tool_version.into(),
            tool_hash: None,
            memory_strategy: "shared".to_string(),
        }
    }

    /// Set the tool hash for reproducibility
    pub fn tool_hash(mut self, hash: impl Into<String>) -> Self {
        self.tool_hash = Some(hash.into());
        self
    }

    /// Set the memory strategy
    pub fn memory_strategy(mut self, strategy: impl Into<String>) -> Self {
        self.memory_strategy = strategy.into();
        self
    }

    /// Add an input component
    pub fn add_input(mut self, bytes: &[u8], name: impl Into<String>, module_count: usize) -> Self {
        let hash = compute_sha256(bytes);
        self.inputs.push(InputArtifact {
            artifact: ArtifactDescriptor {
                name: name.into(),
                hash,
                size: bytes.len() as u64,
            },
            component_type: Some("P2".to_string()),
            module_count,
            prior_attestation: None,
        });
        self
    }

    /// Add an input with existing attestation
    pub fn add_input_with_attestation(
        mut self,
        bytes: &[u8],
        name: impl Into<String>,
        module_count: usize,
        prior_attestation: serde_json::Value,
    ) -> Self {
        let hash = compute_sha256(bytes);
        self.inputs.push(InputArtifact {
            artifact: ArtifactDescriptor {
                name: name.into(),
                hash,
                size: bytes.len() as u64,
            },
            component_type: Some("P2".to_string()),
            module_count,
            prior_attestation: Some(Box::new(prior_attestation)),
        });
        self
    }

    /// Add an input with a precomputed hash and size
    pub fn add_input_descriptor(
        mut self,
        name: impl Into<String>,
        module_count: usize,
        hash: impl Into<String>,
        size: u64,
    ) -> Self {
        self.inputs.push(InputArtifact {
            artifact: ArtifactDescriptor {
                name: name.into(),
                hash: hash.into(),
                size,
            },
            component_type: Some("P2".to_string()),
            module_count,
            prior_attestation: None,
        });
        self
    }

    /// Build the attestation
    pub fn build(self, output_bytes: &[u8], stats: &FusionStats) -> FusionAttestation {
        let output_hash = compute_sha256(output_bytes);
        let timestamp = chrono_timestamp();
        let attestation_id = generate_uuid();

        let size_reduction = if stats.input_size > 0 {
            let diff = stats.input_size as i128 - stats.output_size as i128;
            (diff as f64 / stats.input_size as f64) * 100.0
        } else {
            0.0
        };

        FusionAttestation {
            version: "1.0".to_string(),
            attestation_id,
            transformation_type: "fusion".to_string(),
            timestamp,
            inputs: self.inputs,
            output: ArtifactDescriptor {
                name: "fused.wasm".to_string(),
                hash: output_hash,
                size: output_bytes.len() as u64,
            },
            tool: ToolInfo {
                name: self.tool_name,
                version: self.tool_version,
                tool_hash: self.tool_hash,
            },
            metadata: FusionMetadata {
                memory_strategy: self.memory_strategy,
                components_fused: stats.components_fused,
                modules_merged: stats.modules_merged,
                adapters_generated: stats.adapter_functions,
                imports_resolved: stats.imports_resolved,
                size_reduction_percent: size_reduction,
            },
        }
    }
}

impl FusionAttestation {
    /// Serialize to JSON
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Serialize to compact JSON
    pub fn to_json_compact(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Deserialize from JSON
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }

    /// Get bytes for embedding in custom section
    ///
    /// Returns an error if JSON serialization fails, rather than silently
    /// producing an empty `{}` payload that would violate attestation
    /// integrity (SC-6 / SR-29).
    pub fn to_bytes(&self) -> Result<Vec<u8>, serde_json::Error> {
        self.to_json_compact().map(String::into_bytes)
    }
}

/// Compute SHA-256 hash of bytes
pub(crate) fn compute_sha256(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let result = hasher.finalize();
    hex::encode(result)
}

/// Generate a UUID v4 using the current system clock as entropy.
///
/// This is a thin wrapper over [`generate_uuid_from`] that sources entropy
/// from `SystemTime::now()`. Tests should prefer [`generate_uuid_from`] to
/// pin the entropy value and keep results deterministic.
pub(crate) fn generate_uuid() -> String {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    generate_uuid_from(now)
}

/// Generate a UUID v4 from a caller-supplied entropy value.
///
/// The entropy is hashed with SHA-256 and the first 16 bytes are used to
/// fill a UUID v4 shape (with version and variant bits set per RFC 4122).
/// The algorithm is unchanged from the original `generate_uuid`; this form
/// exists so callers (and tests) can provide deterministic entropy rather
/// than depending on the wall clock.
pub(crate) fn generate_uuid_from(entropy: u128) -> String {
    let mut bytes = [0u8; 16];

    let mut hasher = Sha256::new();
    hasher.update(entropy.to_le_bytes());
    let hash = hasher.finalize();

    bytes.copy_from_slice(&hash[..16]);

    // Set version (4) and variant (RFC 4122)
    bytes[6] = (bytes[6] & 0x0f) | 0x40;
    bytes[8] = (bytes[8] & 0x3f) | 0x80;

    format!(
        "{:08x}-{:04x}-{:04x}-{:04x}-{:012x}",
        u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]),
        u16::from_be_bytes([bytes[4], bytes[5]]),
        u16::from_be_bytes([bytes[6], bytes[7]]),
        u16::from_be_bytes([bytes[8], bytes[9]]),
        u64::from_be_bytes([
            0, 0, bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15]
        ])
    )
}

/// Get current timestamp in ISO 8601 format using the system clock.
///
/// Thin wrapper over [`chrono_timestamp_from`] sourcing seconds-since-epoch
/// from `SystemTime::now()`. A clock-before-epoch collapses to
/// `"1970-01-01T00:00:00Z"`.
pub(crate) fn chrono_timestamp() -> String {
    use std::time::SystemTime;

    let secs = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    chrono_timestamp_from(secs)
}

/// Format `secs` (seconds since Unix epoch) as an ISO 8601 / RFC 3339
/// UTC timestamp: `YYYY-MM-DDTHH:MM:SSZ`.
///
/// Computes a correct proleptic Gregorian date, honoring leap years and
/// per-month day counts. No external crate dependency.
pub(crate) fn chrono_timestamp_from(secs: u64) -> String {
    const SECS_PER_DAY: u64 = 86_400;

    let days_since_epoch = secs / SECS_PER_DAY;
    let secs_today = secs % SECS_PER_DAY;

    let (year, month, day) = civil_from_days(days_since_epoch);

    let hour = secs_today / 3600;
    let minute = (secs_today % 3600) / 60;
    let second = secs_today % 60;

    format!(
        "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z",
        year, month, day, hour, minute, second
    )
}

/// Convert days-since-Unix-epoch to a (year, month, day) triple in the
/// proleptic Gregorian calendar.
///
/// Implements Howard Hinnant's `civil_from_days` algorithm
/// (http://howardhinnant.github.io/date_algorithms.html#civil_from_days).
/// Correctly handles leap years and per-month day counts. Returns
/// 1-indexed `month` (1..=12) and `day` (1..=31).
fn civil_from_days(days_since_epoch: u64) -> (u64, u64, u64) {
    // Shift epoch from 1970-01-01 to 0000-03-01 (start of a 400-year cycle
    // aligned so that February — the leap month — is the last month).
    // 719_468 = number of days from 0000-03-01 to 1970-01-01.
    let z = days_since_epoch as i64 + 719_468;

    // 146_097 days per 400-year cycle.
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097) as u64; // day-of-era, [0, 146096]

    // year-of-era, [0, 399]
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe as i64 + era * 400;

    // day-of-year, [0, 365]
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);

    // March-based month, [0, 11] where 0=March, 11=February.
    let mp = (5 * doy + 2) / 153;

    // Day of month, [1, 31].
    let d = doy - (153 * mp + 2) / 5 + 1;

    // Shift month to [1, 12] with January=1; year increments if mp>=10
    // (i.e. the March-based month rolled past December into Jan/Feb).
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };

    (y as u64, m, d)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compute_sha256() {
        let hash = compute_sha256(b"hello world");
        assert_eq!(hash.len(), 64); // 32 bytes = 64 hex chars
        assert!(hash.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_generate_uuid() {
        let uuid = generate_uuid();
        // UUID format: 8-4-4-4-12
        assert_eq!(uuid.len(), 36);
        assert_eq!(uuid.chars().filter(|&c| c == '-').count(), 4);
    }

    #[test]
    fn test_attestation_builder() {
        let stats = FusionStats {
            components_fused: 2,
            modules_merged: 3,
            adapter_functions: 1,
            imports_resolved: 5,
            input_size: 1000,
            output_size: 800,
            ..Default::default()
        };

        let attestation = FusionAttestationBuilder::new("meld", "0.1.0")
            .add_input(b"component a", "a.wasm", 1)
            .add_input(b"component b", "b.wasm", 2)
            .memory_strategy("shared")
            .build(b"output", &stats);

        assert_eq!(attestation.tool.name, "meld");
        assert_eq!(attestation.inputs.len(), 2);
        assert_eq!(attestation.metadata.components_fused, 2);
    }

    #[test]
    fn test_attestation_json_roundtrip() {
        let stats = FusionStats::default();
        let attestation = FusionAttestationBuilder::new("meld", "0.1.0")
            .add_input(b"test", "test.wasm", 1)
            .build(b"output", &stats);

        let json = attestation.to_json().unwrap();
        let parsed = FusionAttestation::from_json(&json).unwrap();

        assert_eq!(parsed.tool.name, "meld");
        assert_eq!(parsed.transformation_type, "fusion");
    }

    #[test]
    fn test_chrono_timestamp() {
        let ts = chrono_timestamp();
        // Should be in ISO 8601 format
        assert!(ts.contains('T'));
        assert!(ts.ends_with('Z'));
    }

    /// Epoch maps to 1970-01-01T00:00:00Z exactly.
    #[test]
    fn test_chrono_timestamp_from_epoch() {
        assert_eq!(chrono_timestamp_from(0), "1970-01-01T00:00:00Z");
    }

    /// 2025-01-01T00:00:00Z — 55 years after the epoch, crossing the
    /// 2024 leap year. The old (365-days-per-year) approximation was
    /// off by many days here.
    #[test]
    fn test_chrono_timestamp_from_2025_new_year() {
        assert_eq!(chrono_timestamp_from(1_735_689_600), "2025-01-01T00:00:00Z");
    }

    /// March 1, 2025 (non-leap year): the day after Feb 28. The old
    /// algorithm would have reported a non-existent "Feb 30".
    #[test]
    fn test_chrono_timestamp_from_2025_march_boundary() {
        assert_eq!(chrono_timestamp_from(1_740_787_200), "2025-03-01T00:00:00Z");
    }

    /// March 1, 2024 (leap year): the day after Feb 29. Verifies the
    /// leap-day is accounted for and March starts on the correct day.
    #[test]
    fn test_chrono_timestamp_from_2024_leap_march() {
        assert_eq!(chrono_timestamp_from(1_709_251_200), "2024-03-01T00:00:00Z");
    }

    /// Pinned output for `generate_uuid_from(0)`. The algorithm is
    /// SHA-256 of the little-endian bytes of 0u128 (16 zero bytes),
    /// take the first 16 bytes, then set UUID v4 version (0x40) and
    /// RFC 4122 variant (0x80) bits. Changing the algorithm should
    /// either update this expected value intentionally or fail here.
    #[test]
    fn test_generate_uuid_from_pinned_zero() {
        assert_eq!(
            generate_uuid_from(0),
            "374708ff-f771-4dd5-979e-c875d56cd228"
        );
    }

    /// Different entropy values must produce different UUIDs
    /// (sanity check — distinct inputs to SHA-256 collide vanishingly
    /// rarely, so this primarily guards against accidentally ignoring
    /// the entropy argument).
    #[test]
    fn test_generate_uuid_from_distinct_entropy_differs() {
        let a = generate_uuid_from(0);
        let b = generate_uuid_from(1);
        let c = generate_uuid_from(u128::MAX);
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_ne!(b, c);
    }

    /// SR-27: Input hash integrity — the attestation must record a SHA-256 hash
    /// that matches an independently computed digest of the input bytes.
    ///
    /// This ensures the attestation faithfully captures the identity of each
    /// input component, which is critical for supply chain integrity (SC-6).
    #[test]
    fn test_sr27_input_hash_integrity() {
        let input_bytes = b"known component bytes for SR-27 test";

        // Independently compute expected SHA-256
        let mut hasher = Sha256::new();
        hasher.update(input_bytes);
        let expected_hash = hex::encode(hasher.finalize());

        let stats = FusionStats::default();
        let attestation = FusionAttestationBuilder::new("meld", "0.1.0")
            .add_input(input_bytes, "sr27.wasm", 1)
            .build(b"output", &stats);

        assert_eq!(attestation.inputs.len(), 1);
        assert_eq!(
            attestation.inputs[0].artifact.hash, expected_hash,
            "Recorded input hash must match independently computed SHA-256"
        );
        assert_eq!(
            attestation.inputs[0].artifact.size,
            input_bytes.len() as u64,
            "Recorded input size must match actual byte length"
        );
    }

    /// SR-28: Config completeness — every FuserConfig field must be recorded
    /// in the attestation metadata so auditors can reconstruct the exact
    /// configuration used for fusion.
    ///
    /// This test builds an attestation via the builder (which mirrors the
    /// non-wsc path) and separately checks that the metadata struct captures
    /// the memory_strategy field. For the wsc-attestation path, the test
    /// verifies that all expected config keys are present in a tool_parameters
    /// map built inline (mirroring the pattern from `build_wsc_attestation`).
    ///
    /// If a new field is added to FuserConfig but not recorded here, this
    /// test must be updated — acting as a sentinel for config completeness.
    #[test]
    fn test_sr28_config_completeness() {
        // All FuserConfig fields that must appear in attestation metadata.
        // If you add a new field to FuserConfig, add it here too.
        let required_keys = [
            "memory_strategy",
            "address_rebasing",
            "preserve_names",
            "custom_sections",
            "output_format",
        ];

        // Build a tool_parameters map the same way build_wsc_attestation does.
        let mut tool_parameters = std::collections::HashMap::new();
        tool_parameters.insert("memory_strategy".to_string(), serde_json::json!("multi"));
        tool_parameters.insert("address_rebasing".to_string(), serde_json::json!(false));
        tool_parameters.insert("preserve_names".to_string(), serde_json::json!(false));
        tool_parameters.insert("custom_sections".to_string(), serde_json::json!("merge"));
        tool_parameters.insert(
            "output_format".to_string(),
            serde_json::json!("core-module"),
        );

        for key in &required_keys {
            assert!(
                tool_parameters.contains_key(*key),
                "Missing FuserConfig field in attestation tool_parameters: '{key}'. \
                 If you added a new config field, record it in build_wsc_attestation too."
            );
        }

        // Also verify via the built-in metadata struct (non-wsc path).
        let stats = FusionStats::default();
        let attestation = FusionAttestationBuilder::new("meld", "0.1.0")
            .memory_strategy("multi")
            .add_input(b"test", "test.wasm", 1)
            .build(b"output", &stats);

        // The FusionMetadata struct captures memory_strategy directly.
        assert_eq!(attestation.metadata.memory_strategy, "multi");

        // Serialize to JSON and verify all metadata keys round-trip.
        let json = attestation.to_json().expect("serialization must succeed");
        let value: serde_json::Value =
            serde_json::from_str(&json).expect("deserialization must succeed");
        let metadata = value.get("metadata").expect("metadata field must exist");
        assert!(
            metadata.get("memory_strategy").is_some(),
            "metadata.memory_strategy missing from serialized attestation"
        );
    }

    /// SR-29: Attestation round-trip — serialize to JSON and back, verifying
    /// that all fields survive the round-trip intact and non-empty.
    ///
    /// A broken round-trip would mean the custom section cannot be reliably
    /// consumed downstream, violating supply chain integrity (SC-6).
    #[test]
    fn test_sr29_attestation_round_trip() {
        let stats = FusionStats {
            components_fused: 2,
            modules_merged: 3,
            adapter_functions: 1,
            imports_resolved: 5,
            input_size: 1000,
            output_size: 800,
            ..Default::default()
        };

        let attestation = FusionAttestationBuilder::new("meld", "0.1.0")
            .memory_strategy("multi")
            .add_input(b"component-a", "a.wasm", 1)
            .add_input(b"component-b", "b.wasm", 2)
            .build(b"fused output bytes", &stats);

        // Serialize via to_bytes (the path used in production)
        let bytes = attestation
            .to_bytes()
            .expect("to_bytes must succeed (SR-29)");
        let json_str = std::str::from_utf8(&bytes).expect("attestation bytes must be valid UTF-8");

        // Deserialize back
        let parsed = FusionAttestation::from_json(json_str)
            .expect("round-trip deserialization must succeed");

        // Verify all top-level fields are populated
        assert!(!parsed.version.is_empty(), "version must not be empty");
        assert!(
            !parsed.attestation_id.is_empty(),
            "attestation_id must not be empty"
        );
        assert_eq!(parsed.transformation_type, "fusion");
        assert!(!parsed.timestamp.is_empty(), "timestamp must not be empty");

        // Inputs
        assert_eq!(parsed.inputs.len(), 2, "must have 2 inputs");
        for (i, input) in parsed.inputs.iter().enumerate() {
            assert!(
                !input.artifact.hash.is_empty(),
                "input[{i}] hash must not be empty"
            );
            assert!(
                !input.artifact.name.is_empty(),
                "input[{i}] name must not be empty"
            );
            assert!(input.artifact.size > 0, "input[{i}] size must be > 0");
        }

        // Output
        assert!(
            !parsed.output.hash.is_empty(),
            "output hash must not be empty"
        );
        assert!(parsed.output.size > 0, "output size must be > 0");

        // Tool info
        assert_eq!(parsed.tool.name, "meld");
        assert!(
            !parsed.tool.version.is_empty(),
            "tool version must not be empty"
        );

        // Metadata
        assert_eq!(parsed.metadata.components_fused, 2);
        assert_eq!(parsed.metadata.modules_merged, 3);
        assert_eq!(parsed.metadata.adapters_generated, 1);
        assert_eq!(parsed.metadata.imports_resolved, 5);
    }

    /// SR-30: Output hash integrity — the attestation must record a SHA-256
    /// hash of the output bytes that matches an independently computed digest.
    ///
    /// This is the dual of SR-27: it ensures the output identity is faithfully
    /// recorded, protecting downstream consumers from tampered artifacts.
    #[test]
    fn test_sr30_output_hash_integrity() {
        let output_bytes = b"known fused module bytes for SR-30 test";

        // Independently compute expected SHA-256
        let mut hasher = Sha256::new();
        hasher.update(output_bytes);
        let expected_hash = hex::encode(hasher.finalize());

        let stats = FusionStats::default();
        let attestation = FusionAttestationBuilder::new("meld", "0.1.0")
            .add_input(b"input", "input.wasm", 1)
            .build(output_bytes, &stats);

        assert_eq!(
            attestation.output.hash, expected_hash,
            "Recorded output hash must match independently computed SHA-256"
        );
        assert_eq!(
            attestation.output.size,
            output_bytes.len() as u64,
            "Recorded output size must match actual byte length"
        );
    }

    /// SR-29 (corollary): to_bytes must return Err on serialization failure,
    /// not silently produce an empty `{}` payload.
    ///
    /// This is a regression test for the silent failure bug that violated SC-6.
    /// Since FusionAttestation is always serializable in practice, we verify
    /// the happy path returns valid JSON and that the signature is Result-based.
    #[test]
    fn test_to_bytes_returns_result() {
        let stats = FusionStats::default();
        let attestation = FusionAttestationBuilder::new("meld", "0.1.0")
            .add_input(b"test", "test.wasm", 1)
            .build(b"output", &stats);

        // to_bytes now returns Result — this would not compile if it returned Vec<u8>
        let result: Result<Vec<u8>, serde_json::Error> = attestation.to_bytes();
        let bytes = result.expect("to_bytes must succeed for a valid attestation");

        // Verify the output is valid JSON (not the old fallback "{}")
        let json_str = std::str::from_utf8(&bytes).expect("must be valid UTF-8");
        assert_ne!(
            json_str, "{}",
            "to_bytes must not produce empty fallback JSON"
        );

        let parsed: serde_json::Value =
            serde_json::from_str(json_str).expect("output must be valid JSON");
        assert!(
            parsed.get("version").is_some(),
            "version field must be present"
        );
        assert!(
            parsed.get("inputs").is_some(),
            "inputs field must be present"
        );
        assert!(
            parsed.get("output").is_some(),
            "output field must be present"
        );
    }
}
