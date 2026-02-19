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
use crate::Result;
use crate::merger::MergedModule;
use crate::parser::CanonStringEncoding;
use crate::resolver::{AdapterSite, DependencyGraph};
use wasm_encoder::{Function, Instruction};

/// Convert a canonical string encoding from the parser to the adapter's encoding enum
fn canon_to_string_encoding(enc: CanonStringEncoding) -> StringEncoding {
    match enc {
        CanonStringEncoding::Utf8 => StringEncoding::Utf8,
        CanonStringEncoding::Utf16 => StringEncoding::Utf16,
        // CompactUTF16 is latin1+utf16 — treat as Latin1 for adapter purposes
        CanonStringEncoding::CompactUtf16 => StringEncoding::Latin1,
    }
}

/// Return the required alignment for a cabi_realloc call for the given string encoding
fn alignment_for_encoding(encoding: StringEncoding) -> i32 {
    match encoding {
        StringEncoding::Utf8 | StringEncoding::Latin1 => 1,
        StringEncoding::Utf16 => 2,
    }
}

/// FACT-style adapter generator
pub struct FactStyleGenerator {
    #[allow(dead_code)]
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

        // Look up cabi_realloc for caller and callee
        if let Some(&realloc_idx) = merged
            .realloc_map
            .get(&(site.from_component, site.from_module))
        {
            options.caller_realloc = Some(realloc_idx);
        }
        if let Some(&realloc_idx) = merged.realloc_map.get(&(site.to_component, site.to_module)) {
            options.callee_realloc = Some(realloc_idx);
        }

        // Use canonical options from the resolver if available, fall back to UTF-8
        options.caller_string_encoding = site
            .requirements
            .caller_encoding
            .map(canon_to_string_encoding)
            .unwrap_or(StringEncoding::Utf8);
        options.callee_string_encoding = site
            .requirements
            .callee_encoding
            .map(canon_to_string_encoding)
            .unwrap_or(StringEncoding::Utf8);

        // Detect whether the target function returns a (ptr, len) pair.
        // Look up the target function's type in the merged module and check
        // if the result signature is exactly [I32, I32].
        if let Some(&merged_func_idx) = merged.function_index_map.get(&(
            site.to_component,
            site.to_module,
            site.export_func_idx,
        )) && let Some(func) = merged.defined_func(merged_func_idx)
            && let Some(func_type) = merged.types.get(func.type_idx as usize)
            && func_type.results.len() == 2
            && func_type.results[0] == wasm_encoder::ValType::I32
            && func_type.results[1] == wasm_encoder::ValType::I32
        {
            options.returns_pointer_pair = true;
        }

        // Populate post-return from canonical data (remap to merged index)
        if let Some(post_return_core_idx) = site.requirements.callee_post_return
            && let Some(&merged_pr_idx) = merged.function_index_map.get(&(
                site.to_component,
                site.to_module,
                post_return_core_idx,
            ))
        {
            options.callee_post_return = Some(merged_pr_idx);
        }

        options
    }

    /// Generate a simple direct call adapter (no memory crossing)
    fn generate_direct_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
    ) -> Result<(u32, Function)> {
        let target_func = self.resolve_target_function(site, merged)?;
        let options = self.analyze_call_site(site, merged);

        // Find the target function's type (convert wasm index to array position)
        let type_idx = merged
            .defined_func(target_func)
            .map(|f| f.type_idx)
            .unwrap_or(0);

        let func_type = merged.types.get(type_idx as usize);
        let param_count = func_type.map(|t| t.params.len()).unwrap_or(0);
        let result_count = func_type.map(|t| t.results.len()).unwrap_or(0);
        let result_types: Vec<wasm_encoder::ValType> =
            func_type.map(|t| t.results.clone()).unwrap_or_default();

        // If post-return is specified, we need scratch locals to save results
        let has_post_return = options.callee_post_return.is_some();

        if has_post_return && result_count > 0 {
            // Need locals to save results across the post-return call
            let locals: Vec<(u32, wasm_encoder::ValType)> =
                result_types.iter().map(|t| (1u32, *t)).collect();
            let mut func = Function::new(locals);
            let result_base = param_count as u32;

            // Load all parameters and call target
            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));

            // Save results to locals (pop in reverse order)
            for i in (0..result_count).rev() {
                func.instruction(&Instruction::LocalSet(result_base + i as u32));
            }

            // Call post-return with the saved results
            for i in 0..result_count {
                func.instruction(&Instruction::LocalGet(result_base + i as u32));
            }
            func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));

            // Push saved results back onto stack
            for i in 0..result_count {
                func.instruction(&Instruction::LocalGet(result_base + i as u32));
            }

            func.instruction(&Instruction::End);
            Ok((type_idx, func))
        } else {
            // Simple trampoline (no post-return or no results)
            let mut func = Function::new([]);

            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));

            if has_post_return {
                // No results to save, just call post-return
                func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
            }

            func.instruction(&Instruction::End);
            Ok((type_idx, func))
        }
    }

    /// Generate an adapter that copies data between memories
    ///
    /// When caller and callee use different memories, pointer arguments must
    /// be remapped: allocate in callee's memory via `cabi_realloc`, copy the
    /// data with `memory.copy $callee $caller`, then call the target with the
    /// new pointer.  Handles the common `(ptr, len)` pair pattern.
    ///
    /// When the target function returns a `(ptr, len)` pair (detected via
    /// `AdapterOptions::returns_pointer_pair`), the adapter also copies the
    /// returned data from callee's memory back to caller's memory using
    /// `caller_realloc` and `memory.copy` in the reverse direction.
    fn generate_memory_copy_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
        options: &AdapterOptions,
    ) -> Result<(u32, Function)> {
        let target_func = self.resolve_target_function(site, merged)?;
        let type_idx = merged
            .defined_func(target_func)
            .map(|f| f.type_idx)
            .unwrap_or(0);

        let func_type = merged.types.get(type_idx as usize);
        let param_count = func_type.map(|t| t.params.len()).unwrap_or(0);
        let result_count = func_type.map(|t| t.results.len()).unwrap_or(0);
        let result_types: Vec<wasm_encoder::ValType> =
            func_type.map(|t| t.results.clone()).unwrap_or_default();

        // If memories are the same, just do direct call (with post-return if needed)
        if options.caller_memory == options.callee_memory {
            let has_post_return = options.callee_post_return.is_some();

            if has_post_return && result_count > 0 {
                // Need scratch locals to save results across post-return call
                let locals: Vec<(u32, wasm_encoder::ValType)> =
                    result_types.iter().map(|t| (1u32, *t)).collect();
                let mut func = Function::new(locals);
                let result_base = param_count as u32;

                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));

                // Save results to locals (pop in reverse order)
                for i in (0..result_count).rev() {
                    func.instruction(&Instruction::LocalSet(result_base + i as u32));
                }

                // Call post-return with saved results
                for i in 0..result_count {
                    func.instruction(&Instruction::LocalGet(result_base + i as u32));
                }
                func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));

                // Push saved results back onto stack
                for i in 0..result_count {
                    func.instruction(&Instruction::LocalGet(result_base + i as u32));
                }

                func.instruction(&Instruction::End);
                return Ok((type_idx, func));
            } else {
                let mut func = Function::new([]);
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));

                if has_post_return {
                    // No results to save, just call post-return
                    func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
                }

                func.instruction(&Instruction::End);
                return Ok((type_idx, func));
            }
        }

        // Only treat first two params as (ptr, len) when callee has realloc —
        // without realloc we cannot allocate in the callee's memory, so the
        // params are scalar values that should be passed through directly.
        let needs_outbound_copy = param_count >= 2 && options.callee_realloc.is_some();
        let needs_result_copy = options.returns_pointer_pair;

        // Post-return with scalar results needs scratch locals to save/restore
        let needs_post_return_save =
            !needs_result_copy && options.callee_post_return.is_some() && result_count > 0;

        // If no copying and no post-return save needed, direct call
        if !needs_outbound_copy && !needs_result_copy && !needs_post_return_save {
            let mut func = Function::new([]);
            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
            func.instruction(&Instruction::End);
            return Ok((type_idx, func));
        }

        // Determine scratch local count for copy operations
        let copy_scratch_count: u32 = if needs_outbound_copy && needs_result_copy {
            4 // dest_ptr + callee_ret_ptr + callee_ret_len + caller_new_ptr
        } else if needs_result_copy {
            3 // callee_ret_ptr + callee_ret_len + caller_new_ptr
        } else if needs_outbound_copy {
            1 // dest_ptr
        } else {
            0 // post-return-only path (no copy needed)
        };

        // Build local declarations: copy scratch (i32) + post-return save (typed)
        let mut local_decls: Vec<(u32, wasm_encoder::ValType)> = Vec::new();
        if copy_scratch_count > 0 {
            local_decls.push((copy_scratch_count, wasm_encoder::ValType::I32));
        }
        let post_return_base = param_count as u32 + copy_scratch_count;
        if needs_post_return_save {
            for ty in &result_types {
                local_decls.push((1, *ty));
            }
        }

        let mut func = Function::new(local_decls);

        // Assign scratch local indices (after params)
        let base = param_count as u32;
        // For outbound copy:
        let dest_ptr_local = base; // only used when needs_outbound_copy
        // For result copy:
        let result_locals_base = if needs_outbound_copy { base + 1 } else { base };
        let callee_ret_ptr_local = result_locals_base;
        let callee_ret_len_local = result_locals_base + 1;
        let caller_new_ptr_local = result_locals_base + 2;

        // --- Phase 1: Outbound argument copy (caller → callee) ---
        if needs_outbound_copy {
            // Requires callee's cabi_realloc to allocate destination buffer.
            let callee_realloc = match options.callee_realloc {
                Some(idx) => idx,
                None => {
                    log::warn!("Cross-memory copy: no callee realloc, falling back to direct call");
                    let mut func = Function::new([]);
                    for i in 0..param_count {
                        func.instruction(&Instruction::LocalGet(i as u32));
                    }
                    func.instruction(&Instruction::Call(target_func));
                    func.instruction(&Instruction::End);
                    return Ok((type_idx, func));
                }
            };

            // 1. Allocate in callee's memory: dest_ptr = cabi_realloc(0, 0, 1, len)
            func.instruction(&Instruction::I32Const(0)); // original_ptr
            func.instruction(&Instruction::I32Const(0)); // original_size
            func.instruction(&Instruction::I32Const(1)); // alignment
            func.instruction(&Instruction::LocalGet(1)); // len
            func.instruction(&Instruction::Call(callee_realloc));
            func.instruction(&Instruction::LocalSet(dest_ptr_local));

            // 2. Copy data: memory.copy $callee_mem $caller_mem (dest_ptr, src_ptr, len)
            func.instruction(&Instruction::LocalGet(dest_ptr_local)); // dst
            func.instruction(&Instruction::LocalGet(0)); // src (caller ptr)
            func.instruction(&Instruction::LocalGet(1)); // len
            func.instruction(&Instruction::MemoryCopy {
                src_mem: options.caller_memory,
                dst_mem: options.callee_memory,
            });

            // 3. Call target with (dest_ptr, len, ...remaining args)
            func.instruction(&Instruction::LocalGet(dest_ptr_local));
            func.instruction(&Instruction::LocalGet(1)); // len
            for i in 2..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
        } else {
            // No outbound copy — pass args through directly
            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
        }

        // --- Phase 2: Result copy (callee → caller) ---
        if needs_result_copy {
            let caller_realloc = match options.caller_realloc {
                Some(idx) => idx,
                None => {
                    log::warn!("Result copy: no caller realloc, returning callee pointers as-is");
                    func.instruction(&Instruction::End);
                    return Ok((type_idx, func));
                }
            };

            // After the call, stack has: [callee_ret_ptr, callee_ret_len]
            // Save them to locals (pop in reverse order: len first, then ptr)
            func.instruction(&Instruction::LocalSet(callee_ret_len_local));
            func.instruction(&Instruction::LocalSet(callee_ret_ptr_local));

            // Allocate in caller's memory:
            //   caller_new_ptr = cabi_realloc(0, 0, 1, callee_ret_len)
            func.instruction(&Instruction::I32Const(0)); // original_ptr
            func.instruction(&Instruction::I32Const(0)); // original_size
            func.instruction(&Instruction::I32Const(1)); // alignment
            func.instruction(&Instruction::LocalGet(callee_ret_len_local));
            func.instruction(&Instruction::Call(caller_realloc));
            func.instruction(&Instruction::LocalSet(caller_new_ptr_local));

            // Copy data from callee's memory to caller's memory:
            //   memory.copy $caller_mem $callee_mem (caller_new_ptr, callee_ret_ptr, len)
            func.instruction(&Instruction::LocalGet(caller_new_ptr_local)); // dst
            func.instruction(&Instruction::LocalGet(callee_ret_ptr_local)); // src
            func.instruction(&Instruction::LocalGet(callee_ret_len_local)); // size
            func.instruction(&Instruction::MemoryCopy {
                src_mem: options.callee_memory,
                dst_mem: options.caller_memory,
            });

            // Call post-return if specified (callee cleanup with original return values)
            if let Some(post_return_func) = options.callee_post_return {
                func.instruction(&Instruction::LocalGet(callee_ret_ptr_local));
                func.instruction(&Instruction::LocalGet(callee_ret_len_local));
                func.instruction(&Instruction::Call(post_return_func));
            }

            // Push results: (caller_new_ptr, callee_ret_len)
            func.instruction(&Instruction::LocalGet(caller_new_ptr_local));
            func.instruction(&Instruction::LocalGet(callee_ret_len_local));
        }

        // Post-return for non-result-copy case (callee returned scalars)
        if !needs_result_copy && let Some(post_return_func) = options.callee_post_return {
            if result_count > 0 {
                // Save return values to scratch locals (pop in reverse order)
                for i in (0..result_count).rev() {
                    func.instruction(&Instruction::LocalSet(post_return_base + i as u32));
                }
                // Pass saved return values to cabi_post_return
                for i in 0..result_count {
                    func.instruction(&Instruction::LocalGet(post_return_base + i as u32));
                }
                func.instruction(&Instruction::Call(post_return_func));
                // Push return values back onto the stack for the caller
                for i in 0..result_count {
                    func.instruction(&Instruction::LocalGet(post_return_base + i as u32));
                }
            } else {
                // No results — just call post-return
                func.instruction(&Instruction::Call(post_return_func));
            }
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
        let result_count = func_type.map(|t| t.results.len()).unwrap_or(0);
        let result_types: Vec<wasm_encoder::ValType> =
            func_type.map(|t| t.results.clone()).unwrap_or_default();
        let needs_post_return_save = options.callee_post_return.is_some() && result_count > 0;

        // Determine how many scratch locals are needed for transcoding
        let needs_transcoding_locals = !matches!(
            (
                options.caller_string_encoding,
                options.callee_string_encoding
            ),
            (StringEncoding::Utf8, StringEncoding::Utf8)
        );

        // Scratch locals: src_idx, dst_idx, out_ptr, byte (+ code_point for UTF-8/16)
        let scratch_locals: u32 = if needs_transcoding_locals { 5 } else { 0 };
        let post_return_base = param_count as u32 + scratch_locals;

        let mut local_decls: Vec<(u32, wasm_encoder::ValType)> = Vec::new();
        if scratch_locals > 0 {
            local_decls.push((scratch_locals, wasm_encoder::ValType::I32));
        }
        if needs_post_return_save {
            for ty in &result_types {
                local_decls.push((1, *ty));
            }
        }
        let mut func = Function::new(local_decls);

        // Generate transcoding logic based on encoding pair

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

        // Post-return: call cabi_post_return with the function's flat return values
        if let Some(post_return_func) = options.callee_post_return {
            if result_count > 0 {
                // Save return values to scratch locals (pop in reverse order)
                for i in (0..result_count).rev() {
                    func.instruction(&Instruction::LocalSet(post_return_base + i as u32));
                }
                // Pass saved values to cabi_post_return
                for i in 0..result_count {
                    func.instruction(&Instruction::LocalGet(post_return_base + i as u32));
                }
                func.instruction(&Instruction::Call(post_return_func));
                // Push return values back for the caller
                for i in 0..result_count {
                    func.instruction(&Instruction::LocalGet(post_return_base + i as u32));
                }
            } else {
                // No results — just call post-return
                func.instruction(&Instruction::Call(post_return_func));
            }
        }

        func.instruction(&Instruction::End);

        Ok((type_idx, func))
    }

    /// Emit UTF-8 to UTF-16 transcoding
    ///
    /// Decodes variable-length UTF-8 (1-4 bytes per code point) and encodes
    /// as UTF-16 (1-2 code units per code point, with surrogate pairs for
    /// code points >= U+10000).
    ///
    /// Assumes params start with (ptr: i32, len: i32) where len is byte count.
    /// Calls target with (out_ptr: i32, code_unit_count: i32, ...rest).
    fn emit_utf8_to_utf16_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        options: &AdapterOptions,
    ) {
        let callee_realloc = match options.callee_realloc {
            Some(idx) => idx,
            None => {
                log::warn!(
                    "UTF-8→UTF-16 transcode: no callee realloc, falling back to direct call"
                );
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
                return;
            }
        };

        // Scratch locals: src_idx, dst_idx (code units), out_ptr, byte, code_point
        let src_idx_local = param_count as u32;
        let dst_idx_local = param_count as u32 + 1;
        let out_ptr_local = param_count as u32 + 2;
        let byte_local = param_count as u32 + 3;
        let cp_local = param_count as u32 + 4;

        // Source reads use caller_memory, destination writes use callee_memory
        let src_mem8 = wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: options.caller_memory,
        };
        let dst_mem16 = wasm_encoder::MemArg {
            offset: 0,
            align: 1,
            memory_index: options.callee_memory,
        };

        // Step 1: Allocate output buffer = 2 * input_len bytes via cabi_realloc
        // (each UTF-8 byte produces at most one UTF-16 code unit = 2 bytes)
        let callee_align = alignment_for_encoding(options.callee_string_encoding);
        func.instruction(&Instruction::I32Const(0)); // original_ptr
        func.instruction(&Instruction::I32Const(0)); // original_size
        func.instruction(&Instruction::I32Const(callee_align)); // alignment
        func.instruction(&Instruction::LocalGet(1)); // input_len
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Mul); // alloc_size = 2 * input_len
        func.instruction(&Instruction::Call(callee_realloc));
        func.instruction(&Instruction::LocalSet(out_ptr_local));

        // Step 2: Initialize loop counters
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(src_idx_local));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(dst_idx_local));

        // Step 3: Transcoding loop
        func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        // if src_idx >= input_len, break
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::BrIf(1));

        // Read lead byte from caller memory
        func.instruction(&Instruction::LocalGet(0));
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Load8U(src_mem8));
        func.instruction(&Instruction::LocalSet(byte_local));

        // --- Decode UTF-8 sequence into code_point, advance src_idx ---

        // if byte < 0x80: 1-byte ASCII
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::I32Const(0x80));
        func.instruction(&Instruction::I32LtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            // code_point = byte
            func.instruction(&Instruction::LocalGet(byte_local));
            func.instruction(&Instruction::LocalSet(cp_local));
            // src_idx += 1
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(src_idx_local));
        }
        func.instruction(&Instruction::Else);
        {
            // if byte < 0xE0: 2-byte sequence
            func.instruction(&Instruction::LocalGet(byte_local));
            func.instruction(&Instruction::I32Const(0xE0));
            func.instruction(&Instruction::I32LtU);
            func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
            {
                // cp = (byte & 0x1F) << 6 | (b1 & 0x3F)
                func.instruction(&Instruction::LocalGet(byte_local));
                func.instruction(&Instruction::I32Const(0x1F));
                func.instruction(&Instruction::I32And);
                func.instruction(&Instruction::I32Const(6));
                func.instruction(&Instruction::I32Shl);
                func.instruction(&Instruction::LocalGet(0));
                func.instruction(&Instruction::LocalGet(src_idx_local));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Load8U(src_mem8));
                func.instruction(&Instruction::I32Const(0x3F));
                func.instruction(&Instruction::I32And);
                func.instruction(&Instruction::I32Or);
                func.instruction(&Instruction::LocalSet(cp_local));
                // src_idx += 2
                func.instruction(&Instruction::LocalGet(src_idx_local));
                func.instruction(&Instruction::I32Const(2));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalSet(src_idx_local));
            }
            func.instruction(&Instruction::Else);
            {
                // if byte < 0xF0: 3-byte sequence
                func.instruction(&Instruction::LocalGet(byte_local));
                func.instruction(&Instruction::I32Const(0xF0));
                func.instruction(&Instruction::I32LtU);
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                {
                    // cp = (byte & 0x0F) << 12 | (b1 & 0x3F) << 6 | (b2 & 0x3F)
                    func.instruction(&Instruction::LocalGet(byte_local));
                    func.instruction(&Instruction::I32Const(0x0F));
                    func.instruction(&Instruction::I32And);
                    func.instruction(&Instruction::I32Const(12));
                    func.instruction(&Instruction::I32Shl);
                    // b1
                    func.instruction(&Instruction::LocalGet(0));
                    func.instruction(&Instruction::LocalGet(src_idx_local));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(1));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Load8U(src_mem8));
                    func.instruction(&Instruction::I32Const(0x3F));
                    func.instruction(&Instruction::I32And);
                    func.instruction(&Instruction::I32Const(6));
                    func.instruction(&Instruction::I32Shl);
                    func.instruction(&Instruction::I32Or);
                    // b2
                    func.instruction(&Instruction::LocalGet(0));
                    func.instruction(&Instruction::LocalGet(src_idx_local));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(2));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Load8U(src_mem8));
                    func.instruction(&Instruction::I32Const(0x3F));
                    func.instruction(&Instruction::I32And);
                    func.instruction(&Instruction::I32Or);
                    func.instruction(&Instruction::LocalSet(cp_local));
                    // src_idx += 3
                    func.instruction(&Instruction::LocalGet(src_idx_local));
                    func.instruction(&Instruction::I32Const(3));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::LocalSet(src_idx_local));
                }
                func.instruction(&Instruction::Else);
                {
                    // 4-byte sequence (byte >= 0xF0)
                    // cp = (byte & 0x07) << 18 | (b1 & 0x3F) << 12 | (b2 & 0x3F) << 6 | (b3 & 0x3F)
                    func.instruction(&Instruction::LocalGet(byte_local));
                    func.instruction(&Instruction::I32Const(0x07));
                    func.instruction(&Instruction::I32And);
                    func.instruction(&Instruction::I32Const(18));
                    func.instruction(&Instruction::I32Shl);
                    // b1
                    func.instruction(&Instruction::LocalGet(0));
                    func.instruction(&Instruction::LocalGet(src_idx_local));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(1));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Load8U(src_mem8));
                    func.instruction(&Instruction::I32Const(0x3F));
                    func.instruction(&Instruction::I32And);
                    func.instruction(&Instruction::I32Const(12));
                    func.instruction(&Instruction::I32Shl);
                    func.instruction(&Instruction::I32Or);
                    // b2
                    func.instruction(&Instruction::LocalGet(0));
                    func.instruction(&Instruction::LocalGet(src_idx_local));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(2));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Load8U(src_mem8));
                    func.instruction(&Instruction::I32Const(0x3F));
                    func.instruction(&Instruction::I32And);
                    func.instruction(&Instruction::I32Const(6));
                    func.instruction(&Instruction::I32Shl);
                    func.instruction(&Instruction::I32Or);
                    // b3
                    func.instruction(&Instruction::LocalGet(0));
                    func.instruction(&Instruction::LocalGet(src_idx_local));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(3));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Load8U(src_mem8));
                    func.instruction(&Instruction::I32Const(0x3F));
                    func.instruction(&Instruction::I32And);
                    func.instruction(&Instruction::I32Or);
                    func.instruction(&Instruction::LocalSet(cp_local));
                    // src_idx += 4
                    func.instruction(&Instruction::LocalGet(src_idx_local));
                    func.instruction(&Instruction::I32Const(4));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::LocalSet(src_idx_local));
                }
                func.instruction(&Instruction::End); // end 3-byte vs 4-byte
            }
            func.instruction(&Instruction::End); // end 2-byte vs 3+byte
        }
        func.instruction(&Instruction::End); // end 1-byte vs 2+byte

        // --- Encode code_point as UTF-16 ---

        // if code_point < 0x10000: BMP, single code unit
        func.instruction(&Instruction::LocalGet(cp_local));
        func.instruction(&Instruction::I32Const(0x10000));
        func.instruction(&Instruction::I32LtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            // out[dst_idx * 2] = code_point as u16
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Shl);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Store16(dst_mem16));
            // dst_idx += 1
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(dst_idx_local));
        }
        func.instruction(&Instruction::Else);
        {
            // Supplementary plane: surrogate pair
            // high = 0xD800 + ((code_point - 0x10000) >> 10)
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Shl);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(0xD800));
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Const(0x10000));
            func.instruction(&Instruction::I32Sub);
            func.instruction(&Instruction::I32Const(10));
            func.instruction(&Instruction::I32ShrU);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Store16(dst_mem16));

            // low = 0xDC00 + ((code_point - 0x10000) & 0x3FF)
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Shl);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(2));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(0xDC00));
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Const(0x10000));
            func.instruction(&Instruction::I32Sub);
            func.instruction(&Instruction::I32Const(0x3FF));
            func.instruction(&Instruction::I32And);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Store16(dst_mem16));

            // dst_idx += 2 (two code units)
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(2));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(dst_idx_local));
        }
        func.instruction(&Instruction::End); // end BMP vs supplementary

        // Continue loop
        func.instruction(&Instruction::Br(0));

        func.instruction(&Instruction::End); // end loop
        func.instruction(&Instruction::End); // end block

        // Step 4: Call target with (out_ptr, code_unit_count, ...rest params)
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        for i in 2..param_count {
            func.instruction(&Instruction::LocalGet(i as u32));
        }
        func.instruction(&Instruction::Call(target_func));
    }

    /// Emit UTF-16 to UTF-8 transcoding
    ///
    /// Reads UTF-16 code units (2 bytes each), handles surrogate pairs for
    /// code points >= U+10000, and encodes as variable-length UTF-8 (1-4 bytes).
    ///
    /// Assumes params start with (ptr: i32, len: i32) where len is code unit count.
    /// Calls target with (out_ptr: i32, byte_len: i32, ...rest).
    fn emit_utf16_to_utf8_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        options: &AdapterOptions,
    ) {
        let callee_realloc = match options.callee_realloc {
            Some(idx) => idx,
            None => {
                log::warn!(
                    "UTF-16→UTF-8 transcode: no callee realloc, falling back to direct call"
                );
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
                return;
            }
        };

        // Scratch locals: src_idx (code units), dst_idx (bytes), out_ptr, cu, code_point
        let src_idx_local = param_count as u32;
        let dst_idx_local = param_count as u32 + 1;
        let out_ptr_local = param_count as u32 + 2;
        let cu_local = param_count as u32 + 3;
        let cp_local = param_count as u32 + 4;

        // Source reads (UTF-16) use caller_memory, destination writes (UTF-8) use callee_memory
        let src_mem16 = wasm_encoder::MemArg {
            offset: 0,
            align: 1,
            memory_index: options.caller_memory,
        };
        let dst_mem8 = wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: options.callee_memory,
        };

        // Step 1: Allocate output buffer = 3 * input_code_units bytes
        // (worst case: all BMP chars in U+0800-U+FFFF → 3 bytes UTF-8 each)
        let callee_align = alignment_for_encoding(options.callee_string_encoding);
        func.instruction(&Instruction::I32Const(0)); // original_ptr
        func.instruction(&Instruction::I32Const(0)); // original_size
        func.instruction(&Instruction::I32Const(callee_align)); // alignment
        func.instruction(&Instruction::LocalGet(1)); // input_len (code units)
        func.instruction(&Instruction::I32Const(3));
        func.instruction(&Instruction::I32Mul); // alloc_size = 3 * code_units
        func.instruction(&Instruction::Call(callee_realloc));
        func.instruction(&Instruction::LocalSet(out_ptr_local));

        // Step 2: Initialize loop counters
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(src_idx_local));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(dst_idx_local));

        // Step 3: Transcoding loop
        func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        // if src_idx >= input_len (code units), break
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::BrIf(1));

        // Read code unit: cu = mem16[ptr + src_idx * 2]
        func.instruction(&Instruction::LocalGet(0));
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Shl);
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Load16U(src_mem16));
        func.instruction(&Instruction::LocalSet(cu_local));

        // --- Detect surrogate pairs ---
        // if cu >= 0xD800 && cu < 0xDC00: high surrogate
        func.instruction(&Instruction::LocalGet(cu_local));
        func.instruction(&Instruction::I32Const(0xD800_u32 as i32));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::LocalGet(cu_local));
        func.instruction(&Instruction::I32Const(0xDC00_u32 as i32));
        func.instruction(&Instruction::I32LtU);
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            // Surrogate pair: read low surrogate
            // cu2 = mem16[ptr + (src_idx + 1) * 2]
            // code_point = 0x10000 + ((cu - 0xD800) << 10) + (cu2 - 0xDC00)
            func.instruction(&Instruction::I32Const(0x10000));
            func.instruction(&Instruction::LocalGet(cu_local));
            func.instruction(&Instruction::I32Const(0xD800_u32 as i32));
            func.instruction(&Instruction::I32Sub);
            func.instruction(&Instruction::I32Const(10));
            func.instruction(&Instruction::I32Shl);
            func.instruction(&Instruction::I32Add);
            // Load low surrogate
            func.instruction(&Instruction::LocalGet(0));
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Shl);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Load16U(src_mem16));
            func.instruction(&Instruction::I32Const(0xDC00_u32 as i32));
            func.instruction(&Instruction::I32Sub);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(cp_local));
            // src_idx += 2
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::I32Const(2));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(src_idx_local));
        }
        func.instruction(&Instruction::Else);
        {
            // BMP character: code_point = cu
            func.instruction(&Instruction::LocalGet(cu_local));
            func.instruction(&Instruction::LocalSet(cp_local));
            // src_idx += 1
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(src_idx_local));
        }
        func.instruction(&Instruction::End); // end surrogate detection

        // --- Encode code_point as UTF-8 ---

        // if code_point < 0x80: 1-byte
        func.instruction(&Instruction::LocalGet(cp_local));
        func.instruction(&Instruction::I32Const(0x80));
        func.instruction(&Instruction::I32LtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            // out[dst_idx] = code_point
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Store8(dst_mem8));
            // dst_idx += 1
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(dst_idx_local));
        }
        func.instruction(&Instruction::Else);
        {
            // if code_point < 0x800: 2-byte
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Const(0x800));
            func.instruction(&Instruction::I32LtU);
            func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
            {
                // out[dst_idx] = 0xC0 | (cp >> 6)
                func.instruction(&Instruction::LocalGet(out_ptr_local));
                func.instruction(&Instruction::LocalGet(dst_idx_local));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(0xC0));
                func.instruction(&Instruction::LocalGet(cp_local));
                func.instruction(&Instruction::I32Const(6));
                func.instruction(&Instruction::I32ShrU);
                func.instruction(&Instruction::I32Or);
                func.instruction(&Instruction::I32Store8(dst_mem8));
                // out[dst_idx+1] = 0x80 | (cp & 0x3F)
                func.instruction(&Instruction::LocalGet(out_ptr_local));
                func.instruction(&Instruction::LocalGet(dst_idx_local));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(0x80));
                func.instruction(&Instruction::LocalGet(cp_local));
                func.instruction(&Instruction::I32Const(0x3F));
                func.instruction(&Instruction::I32And);
                func.instruction(&Instruction::I32Or);
                func.instruction(&Instruction::I32Store8(dst_mem8));
                // dst_idx += 2
                func.instruction(&Instruction::LocalGet(dst_idx_local));
                func.instruction(&Instruction::I32Const(2));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalSet(dst_idx_local));
            }
            func.instruction(&Instruction::Else);
            {
                // if code_point < 0x10000: 3-byte
                func.instruction(&Instruction::LocalGet(cp_local));
                func.instruction(&Instruction::I32Const(0x10000));
                func.instruction(&Instruction::I32LtU);
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                {
                    // out[dst_idx] = 0xE0 | (cp >> 12)
                    func.instruction(&Instruction::LocalGet(out_ptr_local));
                    func.instruction(&Instruction::LocalGet(dst_idx_local));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(0xE0_u32 as i32));
                    func.instruction(&Instruction::LocalGet(cp_local));
                    func.instruction(&Instruction::I32Const(12));
                    func.instruction(&Instruction::I32ShrU);
                    func.instruction(&Instruction::I32Or);
                    func.instruction(&Instruction::I32Store8(dst_mem8));
                    // out[dst_idx+1] = 0x80 | ((cp >> 6) & 0x3F)
                    func.instruction(&Instruction::LocalGet(out_ptr_local));
                    func.instruction(&Instruction::LocalGet(dst_idx_local));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(1));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(0x80));
                    func.instruction(&Instruction::LocalGet(cp_local));
                    func.instruction(&Instruction::I32Const(6));
                    func.instruction(&Instruction::I32ShrU);
                    func.instruction(&Instruction::I32Const(0x3F));
                    func.instruction(&Instruction::I32And);
                    func.instruction(&Instruction::I32Or);
                    func.instruction(&Instruction::I32Store8(dst_mem8));
                    // out[dst_idx+2] = 0x80 | (cp & 0x3F)
                    func.instruction(&Instruction::LocalGet(out_ptr_local));
                    func.instruction(&Instruction::LocalGet(dst_idx_local));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(2));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(0x80));
                    func.instruction(&Instruction::LocalGet(cp_local));
                    func.instruction(&Instruction::I32Const(0x3F));
                    func.instruction(&Instruction::I32And);
                    func.instruction(&Instruction::I32Or);
                    func.instruction(&Instruction::I32Store8(dst_mem8));
                    // dst_idx += 3
                    func.instruction(&Instruction::LocalGet(dst_idx_local));
                    func.instruction(&Instruction::I32Const(3));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::LocalSet(dst_idx_local));
                }
                func.instruction(&Instruction::Else);
                {
                    // 4-byte: code_point >= 0x10000
                    // out[dst_idx] = 0xF0 | (cp >> 18)
                    func.instruction(&Instruction::LocalGet(out_ptr_local));
                    func.instruction(&Instruction::LocalGet(dst_idx_local));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(0xF0_u32 as i32));
                    func.instruction(&Instruction::LocalGet(cp_local));
                    func.instruction(&Instruction::I32Const(18));
                    func.instruction(&Instruction::I32ShrU);
                    func.instruction(&Instruction::I32Or);
                    func.instruction(&Instruction::I32Store8(dst_mem8));
                    // out[dst_idx+1] = 0x80 | ((cp >> 12) & 0x3F)
                    func.instruction(&Instruction::LocalGet(out_ptr_local));
                    func.instruction(&Instruction::LocalGet(dst_idx_local));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(1));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(0x80));
                    func.instruction(&Instruction::LocalGet(cp_local));
                    func.instruction(&Instruction::I32Const(12));
                    func.instruction(&Instruction::I32ShrU);
                    func.instruction(&Instruction::I32Const(0x3F));
                    func.instruction(&Instruction::I32And);
                    func.instruction(&Instruction::I32Or);
                    func.instruction(&Instruction::I32Store8(dst_mem8));
                    // out[dst_idx+2] = 0x80 | ((cp >> 6) & 0x3F)
                    func.instruction(&Instruction::LocalGet(out_ptr_local));
                    func.instruction(&Instruction::LocalGet(dst_idx_local));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(2));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(0x80));
                    func.instruction(&Instruction::LocalGet(cp_local));
                    func.instruction(&Instruction::I32Const(6));
                    func.instruction(&Instruction::I32ShrU);
                    func.instruction(&Instruction::I32Const(0x3F));
                    func.instruction(&Instruction::I32And);
                    func.instruction(&Instruction::I32Or);
                    func.instruction(&Instruction::I32Store8(dst_mem8));
                    // out[dst_idx+3] = 0x80 | (cp & 0x3F)
                    func.instruction(&Instruction::LocalGet(out_ptr_local));
                    func.instruction(&Instruction::LocalGet(dst_idx_local));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(3));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Const(0x80));
                    func.instruction(&Instruction::LocalGet(cp_local));
                    func.instruction(&Instruction::I32Const(0x3F));
                    func.instruction(&Instruction::I32And);
                    func.instruction(&Instruction::I32Or);
                    func.instruction(&Instruction::I32Store8(dst_mem8));
                    // dst_idx += 4
                    func.instruction(&Instruction::LocalGet(dst_idx_local));
                    func.instruction(&Instruction::I32Const(4));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::LocalSet(dst_idx_local));
                }
                func.instruction(&Instruction::End); // end 3-byte vs 4-byte
            }
            func.instruction(&Instruction::End); // end 2-byte vs 3+byte
        }
        func.instruction(&Instruction::End); // end 1-byte vs 2+byte

        // Continue loop
        func.instruction(&Instruction::Br(0));

        func.instruction(&Instruction::End); // end loop
        func.instruction(&Instruction::End); // end block

        // Step 4: Call target with (out_ptr, byte_count, ...rest params)
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        for i in 2..param_count {
            func.instruction(&Instruction::LocalGet(i as u32));
        }
        func.instruction(&Instruction::Call(target_func));
    }

    /// Emit Latin-1 to UTF-8 transcoding
    ///
    /// Latin-1 (ISO 8859-1) maps 1:1 to Unicode code points 0x00-0xFF.
    /// UTF-8 encoding: 0x00-0x7F → 1 byte, 0x80-0xFF → 2 bytes.
    /// Max output size = 2 * input length.
    ///
    /// Assumes params start with (ptr: i32, len: i32), followed by other params.
    fn emit_latin1_to_utf8_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        options: &AdapterOptions,
    ) {
        let callee_realloc = match options.callee_realloc {
            Some(idx) => idx,
            None => {
                // No realloc available — fall back to direct call
                log::warn!(
                    "Latin-1→UTF-8 transcode: no callee realloc, falling back to direct call"
                );
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
                return;
            }
        };

        // Scratch locals start after the function's original params.
        // We use local indices: param_count+0 = src_idx, +1 = dst_idx,
        // +2 = out_ptr, +3 = byte
        let src_idx_local = param_count as u32;
        let dst_idx_local = param_count as u32 + 1;
        let out_ptr_local = param_count as u32 + 2;
        let byte_local = param_count as u32 + 3;

        // Source reads (Latin-1) use caller_memory, destination writes (UTF-8) use callee_memory
        let src_mem = wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: options.caller_memory,
        };
        let dst_mem = wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: options.callee_memory,
        };

        // Step 1: Allocate output buffer = 2 * input_len via cabi_realloc
        let callee_align = alignment_for_encoding(options.callee_string_encoding);
        func.instruction(&Instruction::I32Const(0)); // original_ptr
        func.instruction(&Instruction::I32Const(0)); // original_size
        func.instruction(&Instruction::I32Const(callee_align)); // alignment
        func.instruction(&Instruction::LocalGet(1)); // input_len
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Mul); // alloc_size = 2 * input_len
        func.instruction(&Instruction::Call(callee_realloc));
        func.instruction(&Instruction::LocalSet(out_ptr_local));

        // Step 2: Initialize loop counters
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(src_idx_local));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(dst_idx_local));

        // Step 3: Transcoding loop
        func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        // if src_idx >= input_len, break
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::LocalGet(1)); // input_len
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::BrIf(1)); // br to outer block (done)

        // Read byte from source: memory[string_ptr + src_idx]
        func.instruction(&Instruction::LocalGet(0)); // string_ptr
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Load8U(src_mem));
        func.instruction(&Instruction::LocalSet(byte_local));

        // if byte < 0x80: ASCII — write single byte
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::I32Const(0x80));
        func.instruction(&Instruction::I32LtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));

        // ASCII path: out[dst_idx] = byte
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::I32Store8(dst_mem));
        // dst_idx += 1
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(dst_idx_local));

        func.instruction(&Instruction::Else);

        // Non-ASCII (0x80-0xFF): encode as 2-byte UTF-8
        // First byte: 0xC0 | (byte >> 6)
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Const(0xC0));
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::I32Const(6));
        func.instruction(&Instruction::I32ShrU);
        func.instruction(&Instruction::I32Or);
        func.instruction(&Instruction::I32Store8(dst_mem));

        // Second byte: 0x80 | (byte & 0x3F)
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Const(0x80));
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::I32Const(0x3F));
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::I32Or);
        func.instruction(&Instruction::I32Store8(dst_mem));

        // dst_idx += 2
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(dst_idx_local));

        func.instruction(&Instruction::End); // end if/else

        // src_idx += 1
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(src_idx_local));

        // Continue loop
        func.instruction(&Instruction::Br(0));

        func.instruction(&Instruction::End); // end loop
        func.instruction(&Instruction::End); // end block

        // Step 4: Call target with (out_ptr, dst_idx, ...rest params)
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        // Pass remaining params through
        for i in 2..param_count {
            func.instruction(&Instruction::LocalGet(i as u32));
        }
        func.instruction(&Instruction::Call(target_func));
    }

    /// Resolve the target function index in the merged module
    fn resolve_target_function(&self, site: &AdapterSite, merged: &MergedModule) -> Result<u32> {
        // Look up the exported function's merged index using the original export index.
        // If the index is missing, this indicates a bug in the resolution or merging
        // pipeline -- we must not silently fall back to an arbitrary function (such as
        // index 0) because that would cause the adapter to call the wrong function at
        // runtime with no visible error.
        merged
            .function_index_map
            .get(&(site.to_component, site.to_module, site.export_func_idx))
            .copied()
            .ok_or_else(|| {
                crate::Error::AdapterGeneration(format!(
                    "Cannot resolve target function for adapter: {} -> {} \
                     (component={}, module={}, export_func_idx={}). \
                     The export may be missing or the function index map is incomplete.",
                    site.import_name,
                    site.export_name,
                    site.to_component,
                    site.to_module,
                    site.export_func_idx,
                ))
            })
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
        let options = AdapterOptions {
            callee_string_encoding: StringEncoding::Utf16,
            ..Default::default()
        };
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
