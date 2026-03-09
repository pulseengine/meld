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

        // Populate post-return from canonical data (remap to merged index).
        // callee_post_return is pre-decomposed to (module_idx, module_local_func_idx)
        // by the resolver, so we can look up directly in function_index_map.
        if let Some((pr_mod_idx, pr_local_idx)) = site.requirements.callee_post_return
            && let Some(&merged_pr_idx) =
                merged
                    .function_index_map
                    .get(&(site.to_component, pr_mod_idx, pr_local_idx))
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
    /// When the caller uses the retptr calling convention (extra i32 param,
    /// void return) and the callee returns a return-area pointer (i32), the
    /// adapter reads flat results from the callee's return area, copies
    /// pointed-to data across memories, and writes fixed-up results at the
    /// caller's retptr.
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

        // --- Determine callee's type (what we call) ---
        let callee_type_idx = merged
            .defined_func(target_func)
            .map(|f| f.type_idx)
            .unwrap_or(0);
        let callee_type = merged.types.get(callee_type_idx as usize);
        let callee_param_count = callee_type.map(|t| t.params.len()).unwrap_or(0);
        let callee_result_count = callee_type.map(|t| t.results.len()).unwrap_or(0);
        let callee_result_types: Vec<wasm_encoder::ValType> =
            callee_type.map(|t| t.results.clone()).unwrap_or_default();

        // --- Determine caller's type (what the adapter declares) ---
        // Use the caller's import type if available; otherwise fall back to callee's type.
        let caller_type_idx = site
            .import_func_type_idx
            .and_then(|local_ti| {
                merged
                    .type_index_map
                    .get(&(site.from_component, site.from_module, local_ti))
                    .copied()
            })
            .unwrap_or(callee_type_idx);
        let caller_type = merged.types.get(caller_type_idx as usize);
        let caller_param_count = caller_type
            .map(|t| t.params.len())
            .unwrap_or(callee_param_count);
        let caller_result_count = caller_type
            .map(|t| t.results.len())
            .unwrap_or(callee_result_count);

        // --- Detect retptr calling convention ---
        // The canonical ABI uses retptr when flat results > MAX_FLAT_RESULTS:
        //   caller (lowered): params..., retptr:i32 → void
        //   callee (lifted):  params...            → i32 (return area ptr)
        let uses_retptr = caller_param_count > callee_param_count
            && caller_result_count == 0
            && callee_result_count == 1
            && callee_result_types.first() == Some(&wasm_encoder::ValType::I32);

        if uses_retptr {
            return self.generate_retptr_adapter(
                site,
                merged,
                options,
                target_func,
                caller_type_idx,
                caller_param_count,
                callee_param_count,
            );
        }

        // --- Non-retptr path: use caller's type for declared signature ---
        let adapter_type_idx = caller_type_idx;
        let param_count = callee_param_count;
        let result_count = callee_result_count;
        let result_types = callee_result_types;

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
                return Ok((adapter_type_idx, func));
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
                return Ok((adapter_type_idx, func));
            }
        }

        // Only treat first two params as (ptr, len) when callee has realloc AND
        // there are pointer pairs to copy — without realloc we cannot allocate
        // in the callee's memory.
        let has_param_pointer_pairs = !site.requirements.pointer_pair_positions.is_empty();
        let has_conditional_pairs = !site.requirements.conditional_pointer_pairs.is_empty();
        let needs_outbound_copy =
            has_param_pointer_pairs && param_count >= 2 && options.callee_realloc.is_some();
        let needs_conditional_copy = has_conditional_pairs && options.callee_realloc.is_some();
        let needs_result_copy = options.returns_pointer_pair;
        let has_conditional_result_pairs =
            !site.requirements.conditional_result_flat_pairs.is_empty();
        let needs_conditional_result_copy =
            !needs_result_copy && has_conditional_result_pairs && options.caller_realloc.is_some();

        // Post-return with scalar results needs scratch locals to save/restore
        let needs_post_return_save =
            !needs_result_copy && options.callee_post_return.is_some() && result_count > 0;

        // We need result-save locals for post-return AND/OR conditional result copy
        let needs_result_save =
            (needs_post_return_save || needs_conditional_result_copy) && result_count > 0;

        // If no copying and no post-return save needed, direct call
        if !needs_outbound_copy
            && !needs_conditional_copy
            && !needs_result_copy
            && !needs_conditional_result_copy
            && !needs_post_return_save
        {
            let mut func = Function::new([]);
            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
            func.instruction(&Instruction::End);
            return Ok((adapter_type_idx, func));
        }

        // Compute fixup depth for non-retptr path (each level needs 4 scratch locals)
        let nonretptr_fixup_depth = if needs_outbound_copy {
            Self::max_fixup_depth(&site.requirements.param_copy_layouts)
        } else {
            0
        };
        let inner_fixup_locals: u32 = 4 * nonretptr_fixup_depth;
        let copy_scratch_count: u32 = if needs_outbound_copy && needs_result_copy {
            4 + inner_fixup_locals // dest_ptr + callee_ret_ptr + callee_ret_len + caller_new_ptr + fixup
        } else if needs_result_copy {
            3 // callee_ret_ptr + callee_ret_len + caller_new_ptr
        } else if needs_outbound_copy {
            1 + inner_fixup_locals // dest_ptr + fixup
        } else if needs_conditional_copy || needs_conditional_result_copy {
            1 // dest_ptr for conditional copy (param or result side)
        } else {
            0 // post-return-only path (no copy needed)
        };

        // Build local declarations: copy scratch (i32) + result save (typed)
        let mut local_decls: Vec<(u32, wasm_encoder::ValType)> = Vec::new();
        if copy_scratch_count > 0 {
            local_decls.push((copy_scratch_count, wasm_encoder::ValType::I32));
        }
        let result_save_base = param_count as u32 + copy_scratch_count;
        if needs_result_save {
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
                    return Ok((adapter_type_idx, func));
                }
            };

            // Get the byte multiplier from copy layout (default 1 for strings)
            let byte_mult = site
                .requirements
                .param_copy_layouts
                .first()
                .map(|cl| match cl {
                    crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                    crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                })
                .unwrap_or(1);

            // 1. Compute byte_size = len * byte_multiplier
            //    Allocate in callee's memory: dest_ptr = cabi_realloc(0, 0, align, byte_size)
            func.instruction(&Instruction::I32Const(0)); // original_ptr
            func.instruction(&Instruction::I32Const(0)); // original_size
            func.instruction(&Instruction::I32Const(1)); // alignment
            func.instruction(&Instruction::LocalGet(1)); // len (element count)
            if byte_mult > 1 {
                func.instruction(&Instruction::I32Const(byte_mult as i32));
                func.instruction(&Instruction::I32Mul);
            }
            func.instruction(&Instruction::Call(callee_realloc));
            func.instruction(&Instruction::LocalSet(dest_ptr_local));

            // 2. Copy data: memory.copy $callee_mem $caller_mem (dest_ptr, src_ptr, byte_size)
            func.instruction(&Instruction::LocalGet(dest_ptr_local)); // dst
            func.instruction(&Instruction::LocalGet(0)); // src (caller ptr)
            func.instruction(&Instruction::LocalGet(1)); // len
            if byte_mult > 1 {
                func.instruction(&Instruction::I32Const(byte_mult as i32));
                func.instruction(&Instruction::I32Mul);
            }
            func.instruction(&Instruction::MemoryCopy {
                src_mem: options.caller_memory,
                dst_mem: options.callee_memory,
            });

            // 2b. Fix up inner pointers if element type contains owned data
            if let Some(crate::resolver::CopyLayout::Elements {
                element_size,
                inner_pointers,
            }) = site.requirements.param_copy_layouts.first()
                && !inner_pointers.is_empty()
            {
                let fixup_base = dest_ptr_local + 1;
                Self::emit_inner_pointer_fixup(
                    &mut func,
                    inner_pointers,
                    *element_size,
                    0,              // src_base = param 0 (caller's original ptr)
                    dest_ptr_local, // dst_base (callee's copy)
                    1,              // count = param 1 (len)
                    options.caller_memory,
                    options.callee_memory,
                    callee_realloc,
                    fixup_base,
                );
            }

            // 3. Call target with (dest_ptr, len, ...remaining args)
            func.instruction(&Instruction::LocalGet(dest_ptr_local));
            func.instruction(&Instruction::LocalGet(1)); // len
            for i in 2..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
        } else if needs_conditional_copy {
            // Conditional copy for option/result/variant params.
            // For each conditional pointer pair, check the discriminant and
            // copy the pointed-to data if the variant is active.
            let callee_realloc = options.callee_realloc.unwrap();

            // We need scratch locals: one dest_ptr per conditional pair
            // These were NOT allocated in the main scratch pool above,
            // so we extend the function with extra locals.
            // NOTE: We handle this by modifying the params in-place using
            // local.set on the original param slots.
            for cond in &site.requirements.conditional_pointer_pairs {
                let disc_local = cond.discriminant_position;
                let ptr_local = cond.ptr_position;
                let len_local = cond.ptr_position + 1;
                let byte_mult = match &cond.copy_layout {
                    crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                    crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                };

                // if (disc == expected_value) { copy and replace ptr }
                func.instruction(&Instruction::LocalGet(disc_local));
                func.instruction(&Instruction::I32Const(cond.discriminant_value as i32));
                func.instruction(&Instruction::I32Eq);
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));

                // Allocate: new_ptr = cabi_realloc(0, 0, 1, len * byte_mult)
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::LocalGet(len_local));
                if byte_mult > 1 {
                    func.instruction(&Instruction::I32Const(byte_mult as i32));
                    func.instruction(&Instruction::I32Mul);
                }
                func.instruction(&Instruction::Call(callee_realloc));
                // Save as dest_ptr (reuse a scratch local)
                func.instruction(&Instruction::LocalSet(dest_ptr_local));

                // Copy: memory.copy callee caller (dest, src, len * byte_mult)
                func.instruction(&Instruction::LocalGet(dest_ptr_local));
                func.instruction(&Instruction::LocalGet(ptr_local));
                func.instruction(&Instruction::LocalGet(len_local));
                if byte_mult > 1 {
                    func.instruction(&Instruction::I32Const(byte_mult as i32));
                    func.instruction(&Instruction::I32Mul);
                }
                func.instruction(&Instruction::MemoryCopy {
                    src_mem: options.caller_memory,
                    dst_mem: options.callee_memory,
                });

                // Replace the original ptr with the new ptr in callee memory
                func.instruction(&Instruction::LocalGet(dest_ptr_local));
                func.instruction(&Instruction::LocalSet(ptr_local));

                func.instruction(&Instruction::End); // end if
            }

            // Pass all args through (with modified ptr values)
            for i in 0..param_count {
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
                    return Ok((adapter_type_idx, func));
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

        // Post-return and/or conditional result copy for non-result-copy case
        if !needs_result_copy
            && (needs_conditional_result_copy || options.callee_post_return.is_some())
        {
            if result_count > 0 && needs_result_save {
                // Save return values to scratch locals (pop in reverse order)
                for i in (0..result_count).rev() {
                    func.instruction(&Instruction::LocalSet(result_save_base + i as u32));
                }
            }

            // Call post-return with callee's original return values
            if let Some(post_return_func) = options.callee_post_return {
                if result_count > 0 && needs_result_save {
                    for i in 0..result_count {
                        func.instruction(&Instruction::LocalGet(result_save_base + i as u32));
                    }
                }
                func.instruction(&Instruction::Call(post_return_func));
            }

            // Conditional result copy: fix up pointer pairs in callee results
            if needs_conditional_result_copy && result_count > 0 {
                let caller_realloc = options.caller_realloc.unwrap();
                for cond in &site.requirements.conditional_result_flat_pairs {
                    let disc_local = result_save_base + cond.discriminant_position;
                    let ptr_local = result_save_base + cond.ptr_position;
                    let len_local = result_save_base + cond.ptr_position + 1;
                    let byte_mult = match &cond.copy_layout {
                        crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                        crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                    };

                    // if (disc == expected_value) { allocate in caller, copy, replace ptr }
                    func.instruction(&Instruction::LocalGet(disc_local));
                    func.instruction(&Instruction::I32Const(cond.discriminant_value as i32));
                    func.instruction(&Instruction::I32Eq);
                    func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));

                    // Allocate in caller memory
                    func.instruction(&Instruction::I32Const(0));
                    func.instruction(&Instruction::I32Const(0));
                    func.instruction(&Instruction::I32Const(1));
                    func.instruction(&Instruction::LocalGet(len_local));
                    if byte_mult > 1 {
                        func.instruction(&Instruction::I32Const(byte_mult as i32));
                        func.instruction(&Instruction::I32Mul);
                    }
                    func.instruction(&Instruction::Call(caller_realloc));
                    func.instruction(&Instruction::LocalSet(dest_ptr_local));

                    // Copy from callee memory to caller memory
                    func.instruction(&Instruction::LocalGet(dest_ptr_local));
                    func.instruction(&Instruction::LocalGet(ptr_local));
                    func.instruction(&Instruction::LocalGet(len_local));
                    if byte_mult > 1 {
                        func.instruction(&Instruction::I32Const(byte_mult as i32));
                        func.instruction(&Instruction::I32Mul);
                    }
                    func.instruction(&Instruction::MemoryCopy {
                        src_mem: options.callee_memory,
                        dst_mem: options.caller_memory,
                    });

                    // Replace ptr with caller's copy
                    func.instruction(&Instruction::LocalGet(dest_ptr_local));
                    func.instruction(&Instruction::LocalSet(ptr_local));

                    func.instruction(&Instruction::End); // end if
                }
            }

            // Push (modified) return values back onto the stack
            if result_count > 0 && needs_result_save {
                for i in 0..result_count {
                    func.instruction(&Instruction::LocalGet(result_save_base + i as u32));
                }
            }
        }

        func.instruction(&Instruction::End);

        Ok((adapter_type_idx, func))
    }

    /// Generate an adapter for the retptr calling convention.
    ///
    /// In the canonical ABI, when a function returns heap-allocated types
    /// (strings, lists, records containing them), the lowered import uses:
    ///   caller: (params..., retptr: i32) → void
    /// and the lifted export uses:
    ///   callee: (params...)               → i32 (return area pointer)
    ///
    /// The adapter bridges these conventions:
    /// 1. Copy ALL input pointer pairs from caller to callee memory
    /// 2. Call callee with remapped params (excluding retptr)
    /// 3. Read flat results from callee's return area
    /// 4. Copy pointed-to data for each result pointer pair to caller memory
    /// 5. Write fixed-up flat results at caller's retptr
    /// 6. Call post-return for callee cleanup
    #[allow(clippy::too_many_arguments)]
    fn generate_retptr_adapter(
        &self,
        site: &AdapterSite,
        _merged: &MergedModule,
        options: &AdapterOptions,
        target_func: u32,
        caller_type_idx: u32,
        caller_param_count: usize,
        callee_param_count: usize,
    ) -> Result<(u32, Function)> {
        let retptr_local = (caller_param_count - 1) as u32;
        let return_area_size = site.requirements.return_area_byte_size.unwrap_or(8);

        let param_ptr_positions = &site.requirements.pointer_pair_positions;
        let result_ptr_offsets = &site.requirements.result_pointer_pair_offsets;
        let num_param_pairs = param_ptr_positions.len();
        let _num_result_pairs = result_ptr_offsets.len();

        // Compute fixup depth: each nesting level needs 4 scratch locals
        let param_fixup_depth = Self::max_fixup_depth(&site.requirements.param_copy_layouts);
        let result_fixup_depth = Self::max_fixup_depth(&site.requirements.result_copy_layouts);
        let max_fixup_depth = param_fixup_depth.max(result_fixup_depth);

        let has_cond_param_pairs = !site.requirements.conditional_pointer_pairs.is_empty();
        let has_cond_result_pairs = !site
            .requirements
            .conditional_result_pointer_pairs
            .is_empty();

        // Scratch locals layout (all i32, after caller params):
        //   [dest_ptr_0..dest_ptr_N]  (one per param pointer pair)
        //   [cond_dest_ptr]           (reused for conditional param/result copies)
        //   [result_ptr]              (return area pointer from callee)
        //   [data_ptr] [data_len] [caller_new_ptr]  (reused for each result pair)
        //   [loop_idx, inner_ptr, inner_len, new_ptr] × depth  (for nested fixup loops)
        let mut scratch_count: u32 = 0;
        let dest_ptr_base = caller_param_count as u32;
        if num_param_pairs > 0 && options.callee_realloc.is_some() {
            scratch_count += num_param_pairs as u32;
        }
        let cond_dest_ptr_local = caller_param_count as u32 + scratch_count;
        if has_cond_param_pairs || has_cond_result_pairs {
            scratch_count += 1;
        }
        let result_ptr_local = caller_param_count as u32 + scratch_count;
        scratch_count += 1;
        let data_ptr_local = caller_param_count as u32 + scratch_count;
        scratch_count += 1;
        let data_len_local = caller_param_count as u32 + scratch_count;
        scratch_count += 1;
        let caller_new_ptr_local = caller_param_count as u32 + scratch_count;
        scratch_count += 1;
        let fixup_locals_base = caller_param_count as u32 + scratch_count;
        scratch_count += 4 * max_fixup_depth; // 4 locals per nesting level

        let local_decls = vec![(scratch_count, wasm_encoder::ValType::I32)];
        let mut func = Function::new(local_decls);

        // --- Phase 1: Outbound copy of ALL pointer pairs (caller → callee) ---
        if let Some(callee_realloc) = options
            .callee_realloc
            .filter(|_| !param_ptr_positions.is_empty())
        {
            let param_layouts = &site.requirements.param_copy_layouts;
            for (pair_idx, &ptr_pos) in param_ptr_positions.iter().enumerate() {
                let len_pos = ptr_pos + 1;
                let dest_local = dest_ptr_base + pair_idx as u32;
                let byte_mult = param_layouts
                    .get(pair_idx)
                    .map(|cl| match cl {
                        crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                        crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                    })
                    .unwrap_or(1);

                // Allocate: dest = cabi_realloc(0, 0, 1, len * byte_mult)
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::LocalGet(len_pos));
                if byte_mult > 1 {
                    func.instruction(&Instruction::I32Const(byte_mult as i32));
                    func.instruction(&Instruction::I32Mul);
                }
                func.instruction(&Instruction::Call(callee_realloc));
                func.instruction(&Instruction::LocalSet(dest_local));

                // Copy: memory.copy callee_mem caller_mem (dest, src, len * byte_mult)
                func.instruction(&Instruction::LocalGet(dest_local));
                func.instruction(&Instruction::LocalGet(ptr_pos));
                func.instruction(&Instruction::LocalGet(len_pos));
                if byte_mult > 1 {
                    func.instruction(&Instruction::I32Const(byte_mult as i32));
                    func.instruction(&Instruction::I32Mul);
                }
                func.instruction(&Instruction::MemoryCopy {
                    src_mem: options.caller_memory,
                    dst_mem: options.callee_memory,
                });

                // Fix up inner pointers if element type has owned data
                if let Some(crate::resolver::CopyLayout::Elements {
                    element_size,
                    inner_pointers,
                }) = param_layouts.get(pair_idx)
                    && !inner_pointers.is_empty()
                {
                    Self::emit_inner_pointer_fixup(
                        &mut func,
                        inner_pointers,
                        *element_size,
                        ptr_pos,    // src_base (caller's original ptr)
                        dest_local, // dst_base (callee's copy)
                        len_pos,    // count (element count)
                        options.caller_memory,
                        options.callee_memory,
                        callee_realloc,
                        fixup_locals_base,
                    );
                }
            }
        }

        // --- Phase 1b: Conditional param copy (option/result/variant params) ---
        if let Some(callee_realloc) = options.callee_realloc.filter(|_| has_cond_param_pairs) {
            for cond in &site.requirements.conditional_pointer_pairs {
                let disc_local = cond.discriminant_position;
                let ptr_local = cond.ptr_position;
                let len_local = cond.ptr_position + 1;
                let byte_mult = match &cond.copy_layout {
                    crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                    crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                };

                func.instruction(&Instruction::LocalGet(disc_local));
                func.instruction(&Instruction::I32Const(cond.discriminant_value as i32));
                func.instruction(&Instruction::I32Eq);
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));

                // Allocate in callee memory
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::LocalGet(len_local));
                if byte_mult > 1 {
                    func.instruction(&Instruction::I32Const(byte_mult as i32));
                    func.instruction(&Instruction::I32Mul);
                }
                func.instruction(&Instruction::Call(callee_realloc));
                func.instruction(&Instruction::LocalSet(cond_dest_ptr_local));

                // Copy from caller to callee memory
                func.instruction(&Instruction::LocalGet(cond_dest_ptr_local));
                func.instruction(&Instruction::LocalGet(ptr_local));
                func.instruction(&Instruction::LocalGet(len_local));
                if byte_mult > 1 {
                    func.instruction(&Instruction::I32Const(byte_mult as i32));
                    func.instruction(&Instruction::I32Mul);
                }
                func.instruction(&Instruction::MemoryCopy {
                    src_mem: options.caller_memory,
                    dst_mem: options.callee_memory,
                });

                // Replace ptr with callee's copy
                func.instruction(&Instruction::LocalGet(cond_dest_ptr_local));
                func.instruction(&Instruction::LocalSet(ptr_local));

                func.instruction(&Instruction::End);
            }
        }

        // Push callee params (after all pointer remapping)
        if !param_ptr_positions.is_empty() && options.callee_realloc.is_some() {
            for i in 0..callee_param_count as u32 {
                if let Some(pair_idx) = param_ptr_positions.iter().position(|&pos| pos == i) {
                    func.instruction(&Instruction::LocalGet(dest_ptr_base + pair_idx as u32));
                } else {
                    func.instruction(&Instruction::LocalGet(i));
                }
            }
        } else {
            for i in 0..callee_param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
        }

        // --- Phase 2: Call callee → get return area pointer ---
        func.instruction(&Instruction::Call(target_func));
        func.instruction(&Instruction::LocalSet(result_ptr_local));

        // --- Phase 3+4+5: Process return area and write to retptr ---
        // For each result pointer pair, copy the pointed-to data and fix up.
        // For scalar values in the return area, copy them using correctly-sized
        // load/store instructions based on the canonical ABI memory layout.
        let result_layouts = &site.requirements.result_copy_layouts;
        let return_area_slots = &site.requirements.return_area_slots;
        if let Some(caller_realloc) = options
            .caller_realloc
            .filter(|_| !result_ptr_offsets.is_empty())
        {
            // Walk return area slots from the canonical ABI layout.
            // Pointer-pair slots trigger cross-memory data copy + fixup.
            // Scalar slots are copied with correctly-sized load/store.
            let mut result_pair_idx: usize = 0;
            for slot in return_area_slots {
                if slot.is_pointer_pair {
                    // This is a pointer pair [data_ptr, data_len] — need to copy data
                    let ptr_offset = slot.byte_offset;
                    let len_offset = slot.byte_offset + 4;
                    let byte_mult = result_layouts
                        .get(result_pair_idx)
                        .map(|cl| match cl {
                            crate::resolver::CopyLayout::Bulk { byte_multiplier } => {
                                *byte_multiplier
                            }
                            crate::resolver::CopyLayout::Elements { element_size, .. } => {
                                *element_size
                            }
                        })
                        .unwrap_or(1);

                    // Load data_ptr and data_len from callee's return area
                    func.instruction(&Instruction::LocalGet(result_ptr_local));
                    func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                        offset: ptr_offset as u64,
                        align: 2,
                        memory_index: options.callee_memory,
                    }));
                    func.instruction(&Instruction::LocalSet(data_ptr_local));

                    func.instruction(&Instruction::LocalGet(result_ptr_local));
                    func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                        offset: len_offset as u64,
                        align: 2,
                        memory_index: options.callee_memory,
                    }));
                    func.instruction(&Instruction::LocalSet(data_len_local));

                    // Allocate in caller's memory: data_len * byte_mult bytes
                    func.instruction(&Instruction::I32Const(0));
                    func.instruction(&Instruction::I32Const(0));
                    func.instruction(&Instruction::I32Const(1));
                    func.instruction(&Instruction::LocalGet(data_len_local));
                    if byte_mult > 1 {
                        func.instruction(&Instruction::I32Const(byte_mult as i32));
                        func.instruction(&Instruction::I32Mul);
                    }
                    func.instruction(&Instruction::Call(caller_realloc));
                    func.instruction(&Instruction::LocalSet(caller_new_ptr_local));

                    // Copy data bytes from callee → caller
                    func.instruction(&Instruction::LocalGet(caller_new_ptr_local));
                    func.instruction(&Instruction::LocalGet(data_ptr_local));
                    func.instruction(&Instruction::LocalGet(data_len_local));
                    if byte_mult > 1 {
                        func.instruction(&Instruction::I32Const(byte_mult as i32));
                        func.instruction(&Instruction::I32Mul);
                    }
                    func.instruction(&Instruction::MemoryCopy {
                        src_mem: options.callee_memory,
                        dst_mem: options.caller_memory,
                    });

                    // Fix up inner pointers in the result (callee → caller direction)
                    if let Some(crate::resolver::CopyLayout::Elements {
                        element_size,
                        inner_pointers,
                    }) = result_layouts.get(result_pair_idx)
                        && !inner_pointers.is_empty()
                    {
                        Self::emit_inner_pointer_fixup(
                            &mut func,
                            inner_pointers,
                            *element_size,
                            data_ptr_local,       // src_base (callee's original)
                            caller_new_ptr_local, // dst_base (caller's copy)
                            data_len_local,       // count
                            options.callee_memory,
                            options.caller_memory,
                            caller_realloc,
                            fixup_locals_base,
                        );
                    }

                    // Write fixed-up [new_ptr, data_len] to retptr
                    func.instruction(&Instruction::LocalGet(retptr_local));
                    func.instruction(&Instruction::LocalGet(caller_new_ptr_local));
                    func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                        offset: ptr_offset as u64,
                        align: 2,
                        memory_index: options.caller_memory,
                    }));

                    func.instruction(&Instruction::LocalGet(retptr_local));
                    func.instruction(&Instruction::LocalGet(data_len_local));
                    func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                        offset: len_offset as u64,
                        align: 2,
                        memory_index: options.caller_memory,
                    }));

                    result_pair_idx += 1;
                } else {
                    // Scalar value — copy with correctly-sized load/store
                    let byte_offset = slot.byte_offset;
                    func.instruction(&Instruction::LocalGet(retptr_local));
                    func.instruction(&Instruction::LocalGet(result_ptr_local));
                    match slot.byte_size {
                        8 => {
                            func.instruction(&Instruction::I64Load(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 3, // 2^3 = 8
                                memory_index: options.callee_memory,
                            }));
                            func.instruction(&Instruction::I64Store(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 3,
                                memory_index: options.caller_memory,
                            }));
                        }
                        2 => {
                            func.instruction(&Instruction::I32Load16U(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 1, // 2^1 = 2
                                memory_index: options.callee_memory,
                            }));
                            func.instruction(&Instruction::I32Store16(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 1,
                                memory_index: options.caller_memory,
                            }));
                        }
                        1 => {
                            func.instruction(&Instruction::I32Load8U(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 0, // 2^0 = 1
                                memory_index: options.callee_memory,
                            }));
                            func.instruction(&Instruction::I32Store8(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 0,
                                memory_index: options.caller_memory,
                            }));
                        }
                        _ => {
                            // 4 bytes (i32/f32) or fallback
                            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 2, // 2^2 = 4
                                memory_index: options.callee_memory,
                            }));
                            func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 2,
                                memory_index: options.caller_memory,
                            }));
                        }
                    }
                }
            }
        } else {
            // No result pointer pairs — bulk copy the entire return area
            func.instruction(&Instruction::LocalGet(retptr_local)); // dst
            func.instruction(&Instruction::LocalGet(result_ptr_local)); // src
            func.instruction(&Instruction::I32Const(return_area_size as i32)); // size
            func.instruction(&Instruction::MemoryCopy {
                src_mem: options.callee_memory,
                dst_mem: options.caller_memory,
            });
        }

        // --- Phase 5b: Conditional result copy (option/result/variant in return area) ---
        if let Some(caller_realloc) = options.caller_realloc.filter(|_| has_cond_result_pairs) {
            for cond in &site.requirements.conditional_result_pointer_pairs {
                let disc_offset = cond.discriminant_position;
                let ptr_offset = cond.ptr_position;
                let len_offset = cond.ptr_position + 4;
                let byte_mult = match &cond.copy_layout {
                    crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                    crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                };

                // Load discriminant from callee's return area using correct byte width
                func.instruction(&Instruction::LocalGet(result_ptr_local));
                match cond.discriminant_byte_size {
                    1 => func.instruction(&Instruction::I32Load8U(wasm_encoder::MemArg {
                        offset: disc_offset as u64,
                        align: 0,
                        memory_index: options.callee_memory,
                    })),
                    2 => func.instruction(&Instruction::I32Load16U(wasm_encoder::MemArg {
                        offset: disc_offset as u64,
                        align: 1,
                        memory_index: options.callee_memory,
                    })),
                    _ => func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                        offset: disc_offset as u64,
                        align: 2,
                        memory_index: options.callee_memory,
                    })),
                };
                func.instruction(&Instruction::I32Const(cond.discriminant_value as i32));
                func.instruction(&Instruction::I32Eq);
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));

                // Load ptr and len from callee's return area
                func.instruction(&Instruction::LocalGet(result_ptr_local));
                func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                    offset: ptr_offset as u64,
                    align: 2,
                    memory_index: options.callee_memory,
                }));
                func.instruction(&Instruction::LocalSet(data_ptr_local));

                func.instruction(&Instruction::LocalGet(result_ptr_local));
                func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                    offset: len_offset as u64,
                    align: 2,
                    memory_index: options.callee_memory,
                }));
                func.instruction(&Instruction::LocalSet(data_len_local));

                // Allocate in caller memory
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::LocalGet(data_len_local));
                if byte_mult > 1 {
                    func.instruction(&Instruction::I32Const(byte_mult as i32));
                    func.instruction(&Instruction::I32Mul);
                }
                func.instruction(&Instruction::Call(caller_realloc));
                func.instruction(&Instruction::LocalSet(caller_new_ptr_local));

                // Copy data from callee → caller
                func.instruction(&Instruction::LocalGet(caller_new_ptr_local));
                func.instruction(&Instruction::LocalGet(data_ptr_local));
                func.instruction(&Instruction::LocalGet(data_len_local));
                if byte_mult > 1 {
                    func.instruction(&Instruction::I32Const(byte_mult as i32));
                    func.instruction(&Instruction::I32Mul);
                }
                func.instruction(&Instruction::MemoryCopy {
                    src_mem: options.callee_memory,
                    dst_mem: options.caller_memory,
                });

                // Write fixed-up ptr to caller's retptr
                func.instruction(&Instruction::LocalGet(retptr_local));
                func.instruction(&Instruction::LocalGet(caller_new_ptr_local));
                func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                    offset: ptr_offset as u64,
                    align: 2,
                    memory_index: options.caller_memory,
                }));

                func.instruction(&Instruction::End);
            }
        }

        // --- Phase 6: Call post-return for callee cleanup ---
        if let Some(post_return_func) = options.callee_post_return {
            func.instruction(&Instruction::LocalGet(result_ptr_local));
            func.instruction(&Instruction::Call(post_return_func));
        }

        // Return void (retptr convention — results written to memory)
        func.instruction(&Instruction::End);

        Ok((caller_type_idx, func))
    }

    /// Compute the maximum nesting depth of inner pointer fixups.
    /// Each level needs 4 scratch locals (loop_idx, inner_ptr, inner_len, new_ptr).
    fn max_fixup_depth(layouts: &[crate::resolver::CopyLayout]) -> u32 {
        fn depth(layout: &crate::resolver::CopyLayout) -> u32 {
            match layout {
                crate::resolver::CopyLayout::Bulk { .. } => 0,
                crate::resolver::CopyLayout::Elements { inner_pointers, .. } => {
                    if inner_pointers.is_empty() {
                        0
                    } else {
                        1 + inner_pointers
                            .iter()
                            .map(|(_, cl)| depth(cl))
                            .max()
                            .unwrap_or(0)
                    }
                }
            }
        }
        layouts.iter().map(depth).max().unwrap_or(0)
    }

    /// Emit wasm instructions that fix up inner pointers after a bulk copy.
    ///
    /// After bulk-copying `count` elements of `element_size` bytes from one
    /// memory to another, inner (ptr, len) pairs within each element still
    /// reference the source memory. This method generates a wasm loop that:
    /// 1. Iterates over each element
    /// 2. For each inner pointer pair at a known offset:
    ///    a. Reads (ptr, len) from the destination copy
    ///    b. Allocates `len * inner_byte_mult` bytes in the destination memory
    ///    c. Copies data from source memory to destination memory
    ///    d. Writes the new pointer back into the destination element
    ///
    /// `locals_base` is the first available scratch local index (all i32).
    /// This method uses 4 scratch locals: [loop_idx, inner_ptr, inner_len, new_ptr].
    #[allow(clippy::too_many_arguments)]
    fn emit_inner_pointer_fixup(
        func: &mut Function,
        inner_pointers: &[(u32, crate::resolver::CopyLayout)],
        element_size: u32,
        _src_base_local: u32, // local holding source array base pointer (reserved for future deep copy)
        dst_base_local: u32,  // local holding destination array base pointer
        count_local: u32,     // local holding element count
        src_mem: u32,
        dst_mem: u32,
        realloc_func: u32,
        locals_base: u32,
    ) {
        if inner_pointers.is_empty() {
            return;
        }
        let loop_idx = locals_base;
        let inner_ptr = locals_base + 1;
        let inner_len = locals_base + 2;
        let new_ptr = locals_base + 3;

        // Initialize loop counter to 0
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(loop_idx));

        // block $exit { loop $cont {
        func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        // if loop_idx >= count: break
        func.instruction(&Instruction::LocalGet(loop_idx));
        func.instruction(&Instruction::LocalGet(count_local));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::BrIf(1)); // break to $exit

        // For each inner pointer pair in the element:
        for (inner_offset, inner_layout) in inner_pointers {
            let byte_mult = match inner_layout {
                crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
            };

            // elem_offset = loop_idx * element_size + inner_offset
            // Read inner_ptr from dst_base[elem_offset]
            func.instruction(&Instruction::LocalGet(dst_base_local));
            func.instruction(&Instruction::LocalGet(loop_idx));
            func.instruction(&Instruction::I32Const(element_size as i32));
            func.instruction(&Instruction::I32Mul);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(*inner_offset as i32));
            func.instruction(&Instruction::I32Add);
            // Now stack has: dst_base + loop_idx * element_size + inner_offset
            // But we need to load from the SOURCE memory (the pointer values
            // in the dst copy still point to src memory after bulk copy)
            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: 0,
                align: 2,
                memory_index: dst_mem,
            }));
            func.instruction(&Instruction::LocalSet(inner_ptr));

            // Read inner_len from dst_base[elem_offset + 4]
            func.instruction(&Instruction::LocalGet(dst_base_local));
            func.instruction(&Instruction::LocalGet(loop_idx));
            func.instruction(&Instruction::I32Const(element_size as i32));
            func.instruction(&Instruction::I32Mul);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(*inner_offset as i32 + 4));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: 0,
                align: 2,
                memory_index: dst_mem,
            }));
            func.instruction(&Instruction::LocalSet(inner_len));

            // Allocate inner data in dst memory: new_ptr = realloc(0, 0, 1, inner_len * byte_mult)
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::LocalGet(inner_len));
            if byte_mult > 1 {
                func.instruction(&Instruction::I32Const(byte_mult as i32));
                func.instruction(&Instruction::I32Mul);
            }
            func.instruction(&Instruction::Call(realloc_func));
            func.instruction(&Instruction::LocalSet(new_ptr));

            // Copy data from src memory to dst memory
            // memory.copy dst_mem src_mem (new_ptr, inner_ptr, inner_len * byte_mult)
            func.instruction(&Instruction::LocalGet(new_ptr));
            func.instruction(&Instruction::LocalGet(inner_ptr));
            func.instruction(&Instruction::LocalGet(inner_len));
            if byte_mult > 1 {
                func.instruction(&Instruction::I32Const(byte_mult as i32));
                func.instruction(&Instruction::I32Mul);
            }
            func.instruction(&Instruction::MemoryCopy { src_mem, dst_mem });

            // Recursively fix up inner-inner pointers if the inner layout
            // itself has pointer pairs (e.g., list<list<string>>).
            if let crate::resolver::CopyLayout::Elements {
                element_size: inner_elem_size,
                inner_pointers: inner_inner,
            } = inner_layout
                && !inner_inner.is_empty()
            {
                // Use the next set of 4 scratch locals for the recursive level
                Self::emit_inner_pointer_fixup(
                    func,
                    inner_inner,
                    *inner_elem_size,
                    inner_ptr, // src_base: the original source ptr
                    new_ptr,   // dst_base: the newly allocated copy
                    inner_len, // count: element count
                    src_mem,
                    dst_mem,
                    realloc_func,
                    locals_base + 4, // next level gets next 4 scratch locals
                );
            }

            // Write new_ptr back to dst element
            func.instruction(&Instruction::LocalGet(dst_base_local));
            func.instruction(&Instruction::LocalGet(loop_idx));
            func.instruction(&Instruction::I32Const(element_size as i32));
            func.instruction(&Instruction::I32Mul);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(*inner_offset as i32));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalGet(new_ptr));
            func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                offset: 0,
                align: 2,
                memory_index: dst_mem,
            }));
            // len stays the same — no need to update it
        }

        // Increment loop counter
        func.instruction(&Instruction::LocalGet(loop_idx));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(loop_idx));

        // Continue loop
        func.instruction(&Instruction::Br(0)); // br $cont

        // }} end loop, end block
        func.instruction(&Instruction::End); // end loop
        func.instruction(&Instruction::End); // end block
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
            .defined_func(target_func)
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
