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
            ((stats.input_size - stats.output_size) as f64 / stats.input_size as f64) * 100.0
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
    pub fn to_bytes(&self) -> Vec<u8> {
        self.to_json_compact()
            .unwrap_or_else(|_| "{}".to_string())
            .into_bytes()
    }
}

/// Compute SHA-256 hash of bytes
pub(crate) fn compute_sha256(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let result = hasher.finalize();
    hex::encode(result)
}

/// Generate a UUID v4
pub(crate) fn generate_uuid() -> String {
    // Simple UUID v4 generation using random bytes
    // In production, use a proper UUID crate
    let mut bytes = [0u8; 16];

    // Use a simple hash of current time as pseudo-random
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);

    let mut hasher = Sha256::new();
    hasher.update(now.to_le_bytes());
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

/// Get current timestamp in ISO 8601 format
pub(crate) fn chrono_timestamp() -> String {
    use std::time::SystemTime;

    let now = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap_or_default();

    // Simple ISO 8601 format (without chrono dependency)
    let secs = now.as_secs();
    let days_since_epoch = secs / 86400;
    let secs_today = secs % 86400;

    // Approximate date calculation (not accounting for leap years properly)
    let years = days_since_epoch / 365;
    let year = 1970 + years;
    let day_of_year = days_since_epoch % 365;
    let month = (day_of_year / 30).min(11) + 1;
    let day = (day_of_year % 30) + 1;

    let hour = secs_today / 3600;
    let minute = (secs_today % 3600) / 60;
    let second = secs_today % 60;

    format!(
        "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z",
        year, month, day, hour, minute, second
    )
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
}
