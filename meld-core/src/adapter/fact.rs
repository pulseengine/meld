//! FACT-style adapter generation
//!
//! This module implements adapter generation in the style of wasmtime's FACT
//! (Fused Adapter Compiler of Trampolines). It generates adapter functions
//! that handle:
//!
//! - Cross-memory data copying
//! - String transcoding (UTF-8 ↔ UTF-16 ↔ Latin-1)
//! - List/array copying
//! - Resource handle transfer
//!
//! ## FACT Overview
//!
//! FACT in wasmtime generates adapter modules that sit between components.
//! For static fusion, we generate similar adapters but inline them directly
//! into the fused module rather than keeping them as separate adapter modules.

use super::{AdapterConfig, AdapterFunction, AdapterGenerator, AdapterOptions, StringEncoding};
use crate::merger::MergedModule;
use crate::resolver::{AdapterSite, DependencyGraph};
use crate::Result;
use wasm_encoder::{Function, Instruction};

/// FACT-style adapter generator
pub struct FactStyleGenerator {
    config: AdapterConfig,
}

impl FactStyleGenerator {
    /// Create a new generator with the given configuration
    pub fn new(config: AdapterConfig) -> Self {
        Self { config }
    }

    /// Generate an adapter for a specific call site
    fn generate_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
        _adapter_idx: usize,
    ) -> Result<AdapterFunction> {
        let name = format!(
            "$adapter_{}_{}_to_{}_{}",
            site.from_component, site.from_module, site.to_component, site.to_module
        );

        // Determine adapter options based on call site
        let options = self.analyze_call_site(site, merged);

        // Generate the adapter function body
        let (type_idx, body) = if site.crosses_memory && options.needs_transcoding() {
            self.generate_transcoding_adapter(site, merged, &options)?
        } else if site.crosses_memory {
            self.generate_memory_copy_adapter(site, merged, &options)?
        } else {
            self.generate_direct_adapter(site, merged)?
        };

        Ok(AdapterFunction {
            name,
            type_idx,
            body,
            source_component: site.from_component,
            source_module: site.from_module,
            target_component: site.to_component,
            target_module: site.to_module,
            target_function: self.resolve_target_function(site, merged)?,
        })
    }

    /// Analyze a call site to determine adapter options
    fn analyze_call_site(&self, site: &AdapterSite, merged: &MergedModule) -> AdapterOptions {
        let mut options = AdapterOptions::default();

        // Determine memory indices
        // In shared memory mode, all components use memory 0
        // In multi-memory mode, each component gets its own memory
        if let Some(&caller_mem) =
            merged
                .memory_index_map
                .get(&(site.from_component, site.from_module, 0))
        {
            options.caller_memory = caller_mem;
        }

        if let Some(&callee_mem) =
            merged
                .memory_index_map
                .get(&(site.to_component, site.to_module, 0))
        {
            options.callee_memory = callee_mem;
        }

        // For now, assume UTF-8 encoding everywhere
        // A real implementation would inspect the component's canonical options
        options.caller_string_encoding = StringEncoding::Utf8;
        options.callee_string_encoding = StringEncoding::Utf8;

        options
    }

    /// Generate a simple direct call adapter (no memory crossing)
    fn generate_direct_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
    ) -> Result<(u32, Function)> {
        let target_func = self.resolve_target_function(site, merged)?;

        // Find the target function's type
        let type_idx = merged
            .functions
            .get(target_func as usize)
            .map(|f| f.type_idx)
            .unwrap_or(0);

        let func_type = merged.types.get(type_idx as usize);
        let param_count = func_type.map(|t| t.params.len()).unwrap_or(0);

        // Generate a simple trampoline
        let mut func = Function::new([]);

        // Load all parameters
        for i in 0..param_count {
            func.instruction(&Instruction::LocalGet(i as u32));
        }

        // Call the target
        func.instruction(&Instruction::Call(target_func));

        // End
        func.instruction(&Instruction::End);

        Ok((type_idx, func))
    }

    /// Generate an adapter that copies data between memories
    fn generate_memory_copy_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
        options: &AdapterOptions,
    ) -> Result<(u32, Function)> {
        // For simple memory copying without transcoding
        // This handles cases like copying byte arrays between components

        let target_func = self.resolve_target_function(site, merged)?;
        let type_idx = merged
            .functions
            .get(target_func as usize)
            .map(|f| f.type_idx)
            .unwrap_or(0);

        let func_type = merged.types.get(type_idx as usize);
        let param_count = func_type.map(|t| t.params.len()).unwrap_or(0);

        let mut func = Function::new([]);

        // If memories are the same, just do direct call
        if options.caller_memory == options.callee_memory {
            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
        } else {
            // Need to copy data between memories
            // This is a simplified version - real implementation would:
            // 1. Allocate space in callee's memory
            // 2. Copy data from caller's memory
            // 3. Call with new pointers
            // 4. Copy results back

            // For now, generate a placeholder
            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
        }

        func.instruction(&Instruction::End);

        Ok((type_idx, func))
    }

    /// Generate an adapter with string transcoding
    fn generate_transcoding_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
        options: &AdapterOptions,
    ) -> Result<(u32, Function)> {
        let target_func = self.resolve_target_function(site, merged)?;
        let type_idx = merged
            .functions
            .get(target_func as usize)
            .map(|f| f.type_idx)
            .unwrap_or(0);

        let func_type = merged.types.get(type_idx as usize);
        let param_count = func_type.map(|t| t.params.len()).unwrap_or(0);

        let mut func = Function::new([]);

        // Generate transcoding logic
        // The actual transcoding depends on:
        // - Source encoding (caller)
        // - Target encoding (callee)
        // - Whether we need to allocate new memory

        match (
            options.caller_string_encoding,
            options.callee_string_encoding,
        ) {
            (StringEncoding::Utf8, StringEncoding::Utf8) => {
                // No transcoding needed, just copy
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
            }

            (StringEncoding::Utf8, StringEncoding::Utf16) => {
                // UTF-8 to UTF-16 transcoding
                // This would call a transcoding helper function
                self.emit_utf8_to_utf16_transcode(&mut func, param_count, target_func, options);
            }

            (StringEncoding::Utf16, StringEncoding::Utf8) => {
                // UTF-16 to UTF-8 transcoding
                self.emit_utf16_to_utf8_transcode(&mut func, param_count, target_func, options);
            }

            (StringEncoding::Latin1, StringEncoding::Utf8) => {
                // Latin-1 to UTF-8 is straightforward (single byte to potentially multi-byte)
                self.emit_latin1_to_utf8_transcode(&mut func, param_count, target_func, options);
            }

            _ => {
                // Other combinations - fall back to direct call for now
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
            }
        }

        func.instruction(&Instruction::End);

        Ok((type_idx, func))
    }

    /// Emit UTF-8 to UTF-16 transcoding
    fn emit_utf8_to_utf16_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        _options: &AdapterOptions,
    ) {
        // Placeholder - real implementation would:
        // 1. Calculate output buffer size (UTF-16 needs max 2x bytes)
        // 2. Call realloc to allocate callee memory
        // 3. Transcode byte by byte
        // 4. Call target with new pointer/length
        // 5. Free temporary buffer if needed

        for i in 0..param_count {
            func.instruction(&Instruction::LocalGet(i as u32));
        }
        func.instruction(&Instruction::Call(target_func));
    }

    /// Emit UTF-16 to UTF-8 transcoding
    fn emit_utf16_to_utf8_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        _options: &AdapterOptions,
    ) {
        // Placeholder
        for i in 0..param_count {
            func.instruction(&Instruction::LocalGet(i as u32));
        }
        func.instruction(&Instruction::Call(target_func));
    }

    /// Emit Latin-1 to UTF-8 transcoding
    fn emit_latin1_to_utf8_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        _options: &AdapterOptions,
    ) {
        // Placeholder
        for i in 0..param_count {
            func.instruction(&Instruction::LocalGet(i as u32));
        }
        func.instruction(&Instruction::Call(target_func));
    }

    /// Resolve the target function index in the merged module
    fn resolve_target_function(&self, site: &AdapterSite, merged: &MergedModule) -> Result<u32> {
        // Look up the export in the target module and find its merged index
        // For now, use a simple heuristic
        if let Some(&idx) = merged
            .function_index_map
            .get(&(site.to_component, site.to_module, 0))
        {
            return Ok(idx);
        }

        // Fallback: first function
        Ok(0)
    }
}

impl AdapterGenerator for FactStyleGenerator {
    fn generate(
        &self,
        merged: &MergedModule,
        graph: &DependencyGraph,
    ) -> Result<Vec<AdapterFunction>> {
        let mut adapters = Vec::new();

        for (idx, site) in graph.adapter_sites.iter().enumerate() {
            log::debug!(
                "Generating adapter for {} -> {}",
                site.import_name,
                site.export_name
            );

            let adapter = self.generate_adapter(site, merged, idx)?;
            adapters.push(adapter);
        }

        Ok(adapters)
    }
}

impl AdapterOptions {
    /// Check if this call site needs string transcoding
    pub fn needs_transcoding(&self) -> bool {
        self.caller_string_encoding != self.callee_string_encoding
    }

    /// Check if this call site crosses memory boundaries
    pub fn crosses_memory(&self) -> bool {
        self.caller_memory != self.callee_memory
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_adapter_options_default() {
        let options = AdapterOptions::default();
        assert_eq!(options.caller_string_encoding, StringEncoding::Utf8);
        assert_eq!(options.callee_string_encoding, StringEncoding::Utf8);
        assert!(!options.needs_transcoding());
    }

    #[test]
    fn test_adapter_options_needs_transcoding() {
        let mut options = AdapterOptions::default();
        options.callee_string_encoding = StringEncoding::Utf16;
        assert!(options.needs_transcoding());
    }

    #[test]
    fn test_adapter_options_crosses_memory() {
        let mut options = AdapterOptions::default();
        assert!(!options.crosses_memory());

        options.callee_memory = 1;
        assert!(options.crosses_memory());
    }

    #[test]
    fn test_fact_generator_creation() {
        let config = AdapterConfig::default();
        let _generator = FactStyleGenerator::new(config);
    }
}
