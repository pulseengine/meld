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
//! - **Phase 1** (current): Single shared memory space
//! - **Phase 2** (future): Multi-memory support where each component keeps its own memory

mod error;
pub mod parser;
pub mod resolver;
pub mod merger;
pub mod adapter;
pub mod attestation;

pub use error::{Error, Result};
pub use parser::{ParsedComponent, ComponentParser};
pub use resolver::{DependencyGraph, Resolver};
pub use merger::{MergedModule, Merger};
pub use adapter::{AdapterGenerator, AdapterConfig};

use wasm_encoder::Module as EncodedModule;

/// Configuration for the fusion process
#[derive(Debug, Clone)]
pub struct FuserConfig {
    /// Memory strategy for fused output
    pub memory_strategy: MemoryStrategy,

    /// Whether to generate attestation data
    pub attestation: bool,

    /// Whether to preserve debug names
    pub preserve_names: bool,

    /// Custom section handling
    pub custom_sections: CustomSectionHandling,
}

impl Default for FuserConfig {
    fn default() -> Self {
        Self {
            memory_strategy: MemoryStrategy::SharedMemory,
            attestation: true,
            preserve_names: false,
            custom_sections: CustomSectionHandling::Merge,
        }
    }
}

/// Memory strategy for the fused output
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryStrategy {
    /// All components share a single memory (Phase 1)
    /// Simpler but requires careful offset management
    SharedMemory,

    /// Each component keeps its own memory (Phase 2)
    /// Requires multi-memory support
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
        log::info!("Resolving dependencies for {} components", self.components.len());
        let resolver = Resolver::new();
        let graph = resolver.resolve(&self.components)?;
        stats.imports_resolved = graph.resolved_imports.len();

        // Step 2: Merge modules
        log::info!("Merging {} core modules", stats.modules_merged);
        let merger = Merger::new(self.config.memory_strategy);
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
        let output = self.encode_output(&merged, &adapters)?;
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
    ) -> Result<Vec<u8>> {
        let mut module = EncodedModule::new();

        // Encode types
        if !merged.types.is_empty() {
            let mut types = wasm_encoder::TypeSection::new();
            for ty in &merged.types {
                types.ty().function(
                    ty.params.iter().copied(),
                    ty.results.iter().copied(),
                );
            }
            module.section(&types);
        }

        // Encode imports (remaining unresolved imports)
        if !merged.imports.is_empty() {
            let mut imports = wasm_encoder::ImportSection::new();
            for imp in &merged.imports {
                imports.import(
                    &imp.module,
                    &imp.name,
                    imp.entity_type.clone(),
                );
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
                tables.table(table.clone());
            }
            module.section(&tables);
        }

        // Encode memories
        if !merged.memories.is_empty() {
            let mut memories = wasm_encoder::MemorySection::new();
            for mem in &merged.memories {
                memories.memory(mem.clone());
            }
            module.section(&memories);
        }

        // Encode globals
        if !merged.globals.is_empty() {
            let mut globals = wasm_encoder::GlobalSection::new();
            for global in &merged.globals {
                globals.global(
                    global.ty.clone(),
                    &global.init_expr,
                );
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
            module.section(&wasm_encoder::StartSection { function_index: start_idx });
        }

        // Encode element section (raw bytes, preserved from original modules)
        // Note: Element segments require complex reindexing which is TODO
        // For now we skip them; real implementation would reindex function refs
        let _ = &merged.elements;

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

        // Encode data section (raw bytes, preserved from original modules)
        // Note: Data segments with memory references need reindexing which is TODO
        // For now we skip them; real implementation would adjust memory indices
        let _ = &merged.data_segments;

        // Handle custom sections based on config
        if self.config.custom_sections != CustomSectionHandling::Drop {
            for (name, contents) in &merged.custom_sections {
                module.section(&wasm_encoder::CustomSection {
                    name: std::borrow::Cow::Borrowed(name),
                    data: std::borrow::Cow::Borrowed(contents),
                });
            }
        }

        Ok(module.finish())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fuser_config_default() {
        let config = FuserConfig::default();
        assert_eq!(config.memory_strategy, MemoryStrategy::SharedMemory);
        assert!(config.attestation);
        assert!(!config.preserve_names);
    }

    #[test]
    fn test_fuser_empty_components_error() {
        let fuser = Fuser::with_defaults();
        let result = fuser.fuse();
        assert!(matches!(result, Err(Error::NoComponents)));
    }
}
