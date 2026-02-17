//! # Meld Core
//!
//! Core library for static WebAssembly component fusion.
//!
//! This library provides the core functionality for fusing multiple P2/P3
//! WebAssembly components into a single core module, eliminating the need
//! for runtime linking.
//!
//! ## Pipeline
//!
//! ```text
//! P2/P3 Components → Parser → Resolver → Merger → Adapter Gen → Single Module
//! ```
//!
//! 1. **Parser**: Extracts core modules and type information from components
//! 2. **Resolver**: Builds import/export graph, performs topological sort
//! 3. **Merger**: Combines function/memory/table/global index spaces
//! 4. **Adapter Generator**: Creates Canonical ABI trampolines
//!
//! ## Example
//!
//! ```ignore
//! use meld_core::{Fuser, FuserConfig};
//!
//! let config = FuserConfig::default();
//! let fuser = Fuser::new(config);
//!
//! // Add components to fuse
//! fuser.add_component(&component_a_bytes)?;
//! fuser.add_component(&component_b_bytes)?;
//!
//! // Perform fusion
//! let fused_module = fuser.fuse()?;
//! ```
//!
//! ## Memory Strategy
//!
//! - **Multi-memory** (default): Each component keeps its own linear memory.
//!   Cross-component pointer-passing calls use adapters with `cabi_realloc`
//!   and `memory.copy`.
//! - **Shared memory** (legacy): All components share one memory. Broken when
//!   any component uses `memory.grow`.

pub mod adapter;
pub mod attestation;
mod error;
pub mod merger;
pub mod parser;
pub mod resolver;
pub mod rewriter;
pub mod segments;

pub use adapter::{AdapterConfig, AdapterGenerator};
pub use error::{Error, Result};
pub use merger::{MergedModule, Merger};
pub use parser::{ComponentParser, ParsedComponent};
pub use resolver::{DependencyGraph, Resolver};

#[cfg(not(feature = "attestation"))]
use crate::attestation::{FUSION_ATTESTATION_SECTION, FusionAttestationBuilder};
use wasm_encoder::Module as EncodedModule;

/// Configuration for the fusion process
#[derive(Debug, Clone)]
pub struct FuserConfig {
    /// Memory strategy for fused output
    pub memory_strategy: MemoryStrategy,

    /// Whether to generate attestation data
    pub attestation: bool,

    /// Whether to rebase per-module memory addresses into a shared memory
    pub address_rebasing: bool,

    /// Whether to preserve debug names
    pub preserve_names: bool,

    /// Custom section handling
    pub custom_sections: CustomSectionHandling,
}

impl Default for FuserConfig {
    fn default() -> Self {
        Self {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: true,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: CustomSectionHandling::Merge,
        }
    }
}

/// Memory strategy for the fused output
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryStrategy {
    /// All components share a single memory.
    /// Broken when any component uses `memory.grow` — one component's
    /// growth corrupts every other component's address space.
    SharedMemory,

    /// Each component keeps its own memory (default).
    /// Cross-component pointer-passing calls use adapters with
    /// `cabi_realloc` and `memory.copy`. Requires WebAssembly
    /// multi-memory (Core Spec 3.0).
    MultiMemory,
}

/// How to handle custom sections during fusion
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CustomSectionHandling {
    /// Merge custom sections with same name
    Merge,
    /// Prefix section names with component identifier
    Prefix,
    /// Drop all custom sections
    Drop,
}

/// Statistics about the fusion process
#[derive(Debug, Clone, Default)]
pub struct FusionStats {
    /// Number of components fused
    pub components_fused: usize,

    /// Number of core modules merged
    pub modules_merged: usize,

    /// Number of functions in output
    pub total_functions: usize,

    /// Number of adapter functions generated
    pub adapter_functions: usize,

    /// Number of imports resolved internally
    pub imports_resolved: usize,

    /// Number of exports in output
    pub total_exports: usize,

    /// Size of input components (bytes)
    pub input_size: usize,

    /// Size of fused output (bytes)
    pub output_size: usize,
}

/// Main fuser interface for static component fusion
pub struct Fuser {
    config: FuserConfig,
    components: Vec<ParsedComponent>,
}

impl Fuser {
    /// Create a new fuser with the given configuration
    pub fn new(config: FuserConfig) -> Self {
        Self {
            config,
            components: Vec::new(),
        }
    }

    /// Create a fuser with default configuration
    pub fn with_defaults() -> Self {
        Self::new(FuserConfig::default())
    }

    /// Add a component to be fused
    ///
    /// Components are parsed immediately and validated.
    pub fn add_component(&mut self, bytes: &[u8]) -> Result<()> {
        self.add_component_named(bytes, None)
    }

    /// Add a component with a name for better error messages
    pub fn add_component_named(&mut self, bytes: &[u8], name: Option<&str>) -> Result<()> {
        let parser = ComponentParser::new();
        let mut parsed = parser.parse(bytes)?;

        if let Some(n) = name {
            parsed.name = Some(n.to_string());
        }

        self.components.push(parsed);
        Ok(())
    }

    /// Get the number of components added
    pub fn component_count(&self) -> usize {
        self.components.len()
    }

    /// Perform the fusion and return the fused module bytes
    pub fn fuse(&self) -> Result<Vec<u8>> {
        let (bytes, _stats) = self.fuse_with_stats()?;
        Ok(bytes)
    }

    /// Perform fusion and return both the bytes and statistics
    pub fn fuse_with_stats(&self) -> Result<(Vec<u8>, FusionStats)> {
        if self.components.is_empty() {
            return Err(Error::NoComponents);
        }
        if self.config.address_rebasing
            && self.config.memory_strategy != MemoryStrategy::SharedMemory
        {
            return Err(Error::MemoryStrategyUnsupported(
                "address rebasing requires shared memory strategy".to_string(),
            ));
        }

        let mut stats = FusionStats {
            components_fused: self.components.len(),
            ..Default::default()
        };

        // Calculate input size
        for comp in &self.components {
            stats.input_size += comp.original_size;
            stats.modules_merged += comp.core_modules.len();
        }

        // Step 1: Resolve dependencies
        log::info!(
            "Resolving dependencies for {} components",
            self.components.len()
        );
        let resolver = Resolver::new();
        let graph = resolver.resolve(&self.components)?;
        stats.imports_resolved = graph.resolved_imports.len();

        // Step 2: Merge modules
        log::info!("Merging {} core modules", stats.modules_merged);
        let merger = Merger::new(self.config.memory_strategy, self.config.address_rebasing);
        let merged = merger.merge(&self.components, &graph)?;
        stats.total_functions = merged.functions.len();
        stats.total_exports = merged.exports.len();

        // Step 3: Generate adapters
        log::info!("Generating adapters");
        let adapter_config = AdapterConfig {
            inline_adapters: true,
            optimize_string_copies: true,
        };
        let generator = adapter::FactStyleGenerator::new(adapter_config);
        let adapters = generator.generate(&merged, &graph)?;
        stats.adapter_functions = adapters.len();

        // Step 4: Encode output module
        log::info!("Encoding fused module");
        let output_without_attestation = self.encode_output(&merged, &adapters, &[])?;
        let output = if self.config.attestation {
            // Build attestation from the output without the attestation section to avoid
            // self-referential hashing.
            let mut attestation_stats = stats.clone();
            attestation_stats.output_size = output_without_attestation.len();
            let (section_name, payload) =
                self.build_attestation_payload(&output_without_attestation, &attestation_stats);
            let extra_sections = vec![(section_name, payload)];
            self.encode_output(&merged, &adapters, &extra_sections)?
        } else {
            output_without_attestation
        };

        stats.output_size = output.len();

        log::info!(
            "Fusion complete: {} components → {} bytes ({}% of input)",
            stats.components_fused,
            stats.output_size,
            if stats.input_size > 0 {
                (stats.output_size * 100) / stats.input_size
            } else {
                100
            }
        );

        Ok((output, stats))
    }

    /// Encode the merged module to binary
    fn encode_output(
        &self,
        merged: &MergedModule,
        adapters: &[adapter::AdapterFunction],
        extra_custom_sections: &[(&str, Vec<u8>)],
    ) -> Result<Vec<u8>> {
        let mut module = EncodedModule::new();

        // Encode types
        if !merged.types.is_empty() {
            let mut types = wasm_encoder::TypeSection::new();
            for ty in &merged.types {
                types
                    .ty()
                    .function(ty.params.iter().copied(), ty.results.iter().copied());
            }
            module.section(&types);
        }

        // Encode imports (remaining unresolved imports)
        if !merged.imports.is_empty() {
            let mut imports = wasm_encoder::ImportSection::new();
            for imp in &merged.imports {
                imports.import(&imp.module, &imp.name, imp.entity_type);
            }
            module.section(&imports);
        }

        // Encode functions (type references)
        if !merged.functions.is_empty() || !adapters.is_empty() {
            let mut functions = wasm_encoder::FunctionSection::new();
            for func in &merged.functions {
                functions.function(func.type_idx);
            }
            // Add adapter function types
            for adapter in adapters {
                functions.function(adapter.type_idx);
            }
            module.section(&functions);
        }

        // Encode tables
        if !merged.tables.is_empty() {
            let mut tables = wasm_encoder::TableSection::new();
            for table in &merged.tables {
                tables.table(*table);
            }
            module.section(&tables);
        }

        // Encode memories
        if !merged.memories.is_empty() {
            let mut memories = wasm_encoder::MemorySection::new();
            for mem in &merged.memories {
                memories.memory(*mem);
            }
            module.section(&memories);
        }

        // Encode globals
        if !merged.globals.is_empty() {
            let mut globals = wasm_encoder::GlobalSection::new();
            for global in &merged.globals {
                globals.global(global.ty, &global.init_expr);
            }
            module.section(&globals);
        }

        // Encode exports
        if !merged.exports.is_empty() {
            let mut exports = wasm_encoder::ExportSection::new();
            for exp in &merged.exports {
                exports.export(&exp.name, exp.kind, exp.index);
            }
            module.section(&exports);
        }

        // Encode start function if present
        if let Some(start_idx) = merged.start_function {
            module.section(&wasm_encoder::StartSection {
                function_index: start_idx,
            });
        }

        // Encode element section (reindexed segments)
        if !merged.elements.is_empty() {
            let mut elements = wasm_encoder::ElementSection::new();
            for segment in &merged.elements {
                elements.segment(segments::encode_element_segment(segment));
            }
            module.section(&elements);
        }

        // Encode data count section before code (required by bulk memory)
        if !merged.data_segments.is_empty() {
            module.section(&wasm_encoder::DataCountSection {
                count: merged.data_segments.len() as u32,
            });
        }

        // Encode code section
        if !merged.functions.is_empty() || !adapters.is_empty() {
            let mut code = wasm_encoder::CodeSection::new();

            // Add merged function bodies
            for func in &merged.functions {
                code.function(&func.body);
            }

            // Add adapter function bodies
            for adapter in adapters {
                code.function(&adapter.body);
            }

            module.section(&code);
        }

        // Encode data section (reindexed segments)
        if !merged.data_segments.is_empty() {
            let mut data = wasm_encoder::DataSection::new();
            for segment in &merged.data_segments {
                data.segment(segments::encode_data_segment(segment));
            }
            module.section(&data);
        }

        // Handle custom sections based on config
        if self.config.custom_sections != CustomSectionHandling::Drop {
            for (name, contents) in &merged.custom_sections {
                if !self.config.preserve_names && name == "name" {
                    continue;
                }
                module.section(&wasm_encoder::CustomSection {
                    name: std::borrow::Cow::Borrowed(name),
                    data: std::borrow::Cow::Borrowed(contents),
                });
            }
        }

        for (name, contents) in extra_custom_sections {
            module.section(&wasm_encoder::CustomSection {
                name: std::borrow::Cow::Borrowed(*name),
                data: std::borrow::Cow::Borrowed(contents),
            });
        }

        Ok(module.finish())
    }

    fn build_attestation_payload(
        &self,
        output_bytes: &[u8],
        stats: &FusionStats,
    ) -> (&'static str, Vec<u8>) {
        #[cfg(feature = "attestation")]
        {
            let attestation = self.build_wsc_attestation(output_bytes, stats);
            let payload = attestation
                .to_json_compact()
                .unwrap_or_else(|_| "{}".to_string())
                .into_bytes();
            (wsc_attestation::TRANSFORMATION_ATTESTATION_SECTION, payload)
        }

        #[cfg(not(feature = "attestation"))]
        {
            let attestation = self.build_attestation(output_bytes, stats);
            (FUSION_ATTESTATION_SECTION, attestation.to_bytes())
        }
    }

    #[cfg(not(feature = "attestation"))]
    fn build_attestation(
        &self,
        output_bytes: &[u8],
        stats: &FusionStats,
    ) -> attestation::FusionAttestation {
        let mut builder = FusionAttestationBuilder::new("meld", env!("CARGO_PKG_VERSION"))
            .memory_strategy(self.memory_strategy_label());

        for (index, component) in self.components.iter().enumerate() {
            let name = component
                .name
                .clone()
                .unwrap_or_else(|| format!("component-{}", index));
            builder = builder.add_input_descriptor(
                name,
                component.core_modules.len(),
                component.original_hash.clone(),
                component.original_size as u64,
            );
        }

        builder.build(output_bytes, stats)
    }

    #[cfg(feature = "attestation")]
    fn build_wsc_attestation(
        &self,
        output_bytes: &[u8],
        stats: &FusionStats,
    ) -> wsc_attestation::TransformationAttestation {
        use std::collections::HashMap;
        use wsc_attestation::{
            ArtifactDescriptor, AttestationSignature, InputArtifact, SignatureStatus, ToolInfo,
            TransformationAttestation, TransformationType,
        };

        let output_hash = attestation::compute_sha256(output_bytes);
        let timestamp = attestation::chrono_timestamp();
        let attestation_id = attestation::generate_uuid();

        let mut inputs = Vec::new();
        for (index, component) in self.components.iter().enumerate() {
            let name = component
                .name
                .clone()
                .unwrap_or_else(|| format!("component-{}", index));
            inputs.push(InputArtifact {
                artifact: ArtifactDescriptor {
                    name,
                    hash: component.original_hash.clone(),
                    size: component.original_size as u64,
                },
                signature_status: SignatureStatus::Unsigned,
                signature_info: None,
                provenance: None,
                transformation_chain: None,
            });
        }

        let mut tool_parameters = HashMap::new();
        tool_parameters.insert(
            "memory_strategy".to_string(),
            serde_json::json!(self.memory_strategy_label()),
        );
        tool_parameters.insert(
            "address_rebasing".to_string(),
            serde_json::json!(self.config.address_rebasing),
        );
        tool_parameters.insert(
            "preserve_names".to_string(),
            serde_json::json!(self.config.preserve_names),
        );
        tool_parameters.insert(
            "custom_sections".to_string(),
            serde_json::json!(self.custom_sections_label()),
        );

        let mut metadata = HashMap::new();
        metadata.insert(
            "memory_strategy".to_string(),
            serde_json::json!(self.memory_strategy_label()),
        );
        metadata.insert(
            "components_fused".to_string(),
            serde_json::json!(stats.components_fused),
        );
        metadata.insert(
            "modules_merged".to_string(),
            serde_json::json!(stats.modules_merged),
        );
        metadata.insert(
            "adapters_generated".to_string(),
            serde_json::json!(stats.adapter_functions),
        );
        metadata.insert(
            "imports_resolved".to_string(),
            serde_json::json!(stats.imports_resolved),
        );
        let size_reduction = if stats.input_size > 0 {
            ((stats.input_size - stats.output_size) as f64 / stats.input_size as f64) * 100.0
        } else {
            0.0
        };
        metadata.insert(
            "size_reduction_percent".to_string(),
            serde_json::json!(size_reduction),
        );

        TransformationAttestation {
            version: "1.0".to_string(),
            transformation_type: TransformationType::Composition,
            attestation_id,
            timestamp: timestamp.clone(),
            output: ArtifactDescriptor {
                name: "fused.wasm".to_string(),
                hash: output_hash,
                size: output_bytes.len() as u64,
            },
            inputs,
            tool: ToolInfo {
                name: "meld".to_string(),
                version: env!("CARGO_PKG_VERSION").to_string(),
                tool_hash: None,
                parameters: tool_parameters,
            },
            attestation_signature: AttestationSignature {
                algorithm: "unsigned".to_string(),
                signature: String::new(),
                key_id: None,
                public_key: None,
                signer_identity: None,
                certificate_chain: None,
                rekor_uuid: None,
                signed_at: timestamp,
            },
            metadata,
        }
    }

    fn memory_strategy_label(&self) -> &'static str {
        match self.config.memory_strategy {
            MemoryStrategy::SharedMemory => "shared",
            MemoryStrategy::MultiMemory => "multi",
        }
    }

    #[cfg(feature = "attestation")]
    fn custom_sections_label(&self) -> &'static str {
        match self.config.custom_sections {
            CustomSectionHandling::Merge => "merge",
            CustomSectionHandling::Prefix => "prefix",
            CustomSectionHandling::Drop => "drop",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fuser_config_default() {
        let config = FuserConfig::default();
        assert_eq!(config.memory_strategy, MemoryStrategy::MultiMemory);
        assert!(config.attestation);
        assert!(!config.address_rebasing);
        assert!(!config.preserve_names);
    }

    #[test]
    fn test_fuser_empty_components_error() {
        let fuser = Fuser::with_defaults();
        let result = fuser.fuse();
        assert!(matches!(result, Err(Error::NoComponents)));
    }
}
