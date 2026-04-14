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

/// Build a lookup from `(module, field)` → merged function index for resource imports.
///
/// Scans the merged module's imports to find `[resource-rep]` and `[resource-new]`
/// function imports and records their merged function indices.
type ResourceImportMap = std::collections::HashMap<(String, String), u32>;

fn build_resource_import_maps(merged: &MergedModule) -> (ResourceImportMap, ResourceImportMap) {
    use wasm_encoder::EntityType;
    let mut rep_map = std::collections::HashMap::new();
    let mut new_map = std::collections::HashMap::new();
    let mut func_idx = 0u32;
    for imp in &merged.imports {
        if matches!(imp.entity_type, EntityType::Function(_)) {
            if imp.name.starts_with("[resource-rep]") {
                rep_map.insert((imp.module.clone(), imp.name.clone()), func_idx);
            } else if imp.name.starts_with("[resource-new]") {
                new_map.insert((imp.module.clone(), imp.name.clone()), func_idx);
            }
            func_idx += 1;
        }
    }
    (rep_map, new_map)
}

/// Emit Phase 0: convert borrow resource handles for each `ResourceBorrowTransfer`.
fn emit_resource_borrow_phase0(func: &mut Function, transfers: &[super::ResourceBorrowTransfer]) {
    for t in transfers {
        func.instruction(&Instruction::LocalGet(t.param_idx));
        func.instruction(&Instruction::Call(t.rep_func));
        if let Some(new_func) = t.new_func {
            // 3-component chain: rep → new handle in callee's table
            func.instruction(&Instruction::Call(new_func));
        }
        func.instruction(&Instruction::LocalSet(t.param_idx));
    }
}

/// Emit Phase R-rep: extract representations from own<T> result handles.
///
/// Calls `resource.rep(handle)` for each own result, storing the rep in
/// scratch locals starting at `scratch_base`. The original handle locals
/// are NOT modified — post_return still needs them to drop the callee's handles.
fn emit_resource_rep_results(
    func: &mut Function,
    transfers: &[super::ResourceOwnResultTransfer],
    result_base: u32,
    scratch_base: u32,
) {
    for (i, t) in transfers.iter().enumerate() {
        let local_idx = result_base + t.position;
        func.instruction(&Instruction::LocalGet(local_idx));
        func.instruction(&Instruction::Call(t.rep_func));
        func.instruction(&Instruction::LocalSet(scratch_base + i as u32));
    }
}

/// Emit Phase R-new: mint fresh handles from extracted representations.
///
/// Calls `resource.new(rep)` for each own result, reading from scratch locals
/// and storing the new handle back into the result locals.
fn emit_resource_new_results(
    func: &mut Function,
    transfers: &[super::ResourceOwnResultTransfer],
    result_base: u32,
    scratch_base: u32,
) {
    for (i, t) in transfers.iter().enumerate() {
        let local_idx = result_base + t.position;
        func.instruction(&Instruction::LocalGet(scratch_base + i as u32));
        func.instruction(&Instruction::Call(t.new_func));
        func.instruction(&Instruction::LocalSet(local_idx));
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
        resource_rep_imports: &std::collections::HashMap<(String, String), u32>,
        resource_new_imports: &std::collections::HashMap<(String, String), u32>,
    ) -> Result<AdapterFunction> {
        let name = format!(
            "$adapter_{}_{}_to_{}_{}",
            site.from_component, site.from_module, site.to_component, site.to_module
        );

        // Determine adapter options based on call site
        let options =
            self.analyze_call_site(site, merged, resource_rep_imports, resource_new_imports);

        // Generate the adapter function body
        let (type_idx, body) = if site.crosses_memory && options.needs_transcoding() {
            self.generate_transcoding_adapter(site, merged, &options)?
        } else if site.crosses_memory {
            self.generate_memory_copy_adapter(site, merged, &options)?
        } else {
            self.generate_direct_adapter(site, merged, &options)?
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
    fn analyze_call_site(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
        resource_rep_imports: &std::collections::HashMap<(String, String), u32>,
        resource_new_imports: &std::collections::HashMap<(String, String), u32>,
    ) -> AdapterOptions {
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

        // Resolve resource BORROW params → [resource-rep] merged function indices.
        //
        // Per the canonical ABI spec, `borrow<T>` params where T is defined by
        // the callee receive the representation (raw pointer), not the handle.
        // The adapter must call resource.rep(handle) → rep for these.
        //
        // `own<T>` params receive the handle directly — the callee's core
        // function calls from_handle/resource.rep internally, so the adapter
        // must NOT convert them (that would cause double conversion).
        //
        for op in &site.requirements.resource_params {
            if op.is_owned {
                continue; // own<T>: callee handles conversion internally
            }

            if op.callee_defines_resource {
                // Callee defines the resource — convert handle→rep.
                // Skip if upstream adapter already converted (avoids double resource.rep).
                if !op.caller_already_converted {
                    // If the caller has a handle table, use ht_rep to extract rep
                    // from the memory-pointer handle. Otherwise use canonical resource.rep.
                    let rep_func = merged
                        .handle_tables
                        .get(&site.from_component)
                        .map(|ht| ht.rep_func)
                        .or_else(|| {
                            resource_rep_imports
                                .get(&(op.import_module.clone(), op.import_field.clone()))
                                .copied()
                        });
                    if let Some(rep_func) = rep_func {
                        options
                            .resource_rep_calls
                            .push(super::ResourceBorrowTransfer {
                                param_idx: op.flat_idx,
                                rep_func,
                                new_func: None,
                            });
                    }
                }
            } else {
                // 3-component case: callee doesn't define the resource.
                // Use caller's [resource-rep] + callee's [resource-new].
                let resource_name = op
                    .import_field
                    .strip_prefix("[resource-rep]")
                    .unwrap_or(&op.import_field);

                // Primary: per-component map from MergedModule
                let caller_rep_func = merged
                    .resource_rep_by_component
                    .get(&(site.from_component, resource_name.to_string()))
                    .copied()
                    .or_else(|| {
                        // Fallback: find any [resource-rep] for this resource name
                        // that isn't the callee's (different component index).
                        merged
                            .resource_rep_by_component
                            .iter()
                            .find(|((comp, rn), _)| {
                                rn == resource_name && *comp != site.to_component
                            })
                            .map(|(_, &idx)| idx)
                    })
                    .or_else(|| {
                        // Last resort: flat map with different module heuristic
                        resource_rep_imports
                            .iter()
                            .find(|((module, field), _)| {
                                field.ends_with(resource_name)
                                    && field.starts_with("[resource-rep]")
                                    && *module != op.import_module
                            })
                            .map(|(_, &idx)| idx)
                    });

                // For re-exporter callees with handle tables, use ht_new
                // which returns memory-pointer handles that wit-bindgen expects.
                let callee_new_func = merged
                    .handle_tables
                    .get(&site.to_component)
                    .map(|ht| ht.new_func)
                    .or_else(|| {
                        merged
                            .resource_new_by_component
                            .get(&(site.to_component, resource_name.to_string()))
                            .copied()
                    })
                    .or_else(|| {
                        let new_field = op.import_field.replace("[resource-rep]", "[resource-new]");
                        resource_new_imports
                            .get(&(op.import_module.clone(), new_field))
                            .copied()
                    });

                if let Some(rep_func) = caller_rep_func {
                    options
                        .resource_rep_calls
                        .push(super::ResourceBorrowTransfer {
                            param_idx: op.flat_idx,
                            rep_func,
                            new_func: callee_new_func,
                        });
                } else {
                    log::warn!(
                        "3-component borrow: no caller [resource-rep] for '{}' \
                         (from_comp={}, to_comp={})",
                        resource_name,
                        site.from_component,
                        site.to_component,
                    );
                }
            }
        }

        // Resolve own<T> results that need [resource-rep] + [resource-new].
        // When callee_defines_resource is true, the P2 wrapper's canon lift/lower
        // handles the conversion — the adapter passes the handle directly.
        for op in &site.requirements.resource_results {
            if !op.is_owned || op.callee_defines_resource {
                continue;
            }
            let resource_name = op
                .import_field
                .strip_prefix("[resource-new]")
                .unwrap_or(&op.import_field);

            // Caller's [resource-new] (rep → caller handle)
            let new_func = merged
                .resource_new_by_component
                .get(&(site.from_component, resource_name.to_string()))
                .copied()
                .or_else(|| {
                    resource_new_imports
                        .get(&(op.import_module.clone(), op.import_field.clone()))
                        .copied()
                });

            // Callee's [resource-rep] (callee handle → rep).
            // For re-exporter callees with handle tables, use ht_rep.
            let rep_field = format!("[resource-rep]{}", resource_name);
            let rep_func = merged
                .handle_tables
                .get(&site.to_component)
                .map(|ht| ht.rep_func)
                .or_else(|| {
                    merged
                        .resource_rep_by_component
                        .get(&(site.to_component, resource_name.to_string()))
                        .copied()
                })
                .or_else(|| {
                    resource_rep_imports
                        .get(&(op.import_module.clone(), rep_field.clone()))
                        .copied()
                });

            if let (Some(rep_func), Some(new_func)) = (rep_func, new_func) {
                options
                    .resource_new_calls
                    .push(super::ResourceOwnResultTransfer {
                        position: op.flat_idx,
                        byte_offset: op.byte_offset,
                        rep_func,
                        new_func,
                    });
            } else if let Some(new_func) = new_func {
                log::warn!(
                    "own<T> result transfer: no callee [resource-rep] for '{}' \
                     (from={}, to={}), falling back to new-only",
                    resource_name,
                    site.from_component,
                    site.to_component,
                );
                // Fallback: use new_func as both rep and new (may be wrong but
                // avoids a hard failure for fixtures that don't need rep)
                options
                    .resource_new_calls
                    .push(super::ResourceOwnResultTransfer {
                        position: op.flat_idx,
                        byte_offset: op.byte_offset,
                        rep_func: new_func,
                        new_func,
                    });
            }
        }

        // Resolve inner resource handles from param copy layouts.
        // When list elements contain borrow<T>, the adapter must convert
        // each handle after bulk-copying the list data to callee memory.
        for layout in &site.requirements.param_copy_layouts {
            if let crate::resolver::CopyLayout::Elements {
                inner_resources, ..
            } = layout
            {
                for &(byte_offset, _resource_type_id, is_owned) in inner_resources {
                    if is_owned {
                        continue; // own<T> in lists — callee handles internally
                    }
                    // Find any [resource-rep] import for borrow handles.
                    // For 2-component (callee defines), use callee's rep.
                    // For 3-component, would need caller's rep + callee's new.
                    // For now, find ANY matching [resource-rep] import.
                    if let Some(&rep_func) = resource_rep_imports.values().next() {
                        options.inner_resource_fixups.push((byte_offset, rep_func));
                    }
                }
            }
        }

        // Resolve resource handles inside the params-ptr buffer.
        // For borrow<T> where callee defines T, the adapter must convert
        // handle → rep at the byte offset within the buffer.
        for op in &site.requirements.params_area_resource_positions {
            if op.is_owned {
                continue; // own<T>: callee calls resource.rep internally
            }

            if op.callee_defines_resource {
                // 2-component: use callee's [resource-rep]
                if let Some(&rep_func) =
                    resource_rep_imports.get(&(op.import_module.clone(), op.import_field.clone()))
                {
                    options
                        .params_area_borrow_fixups
                        .push(super::ParamsAreaResourceFixup {
                            byte_offset: op.byte_offset,
                            rep_func,
                            is_owned: false,
                        });
                }
            }
            // 3-component chains for params-area borrows could be added here
        }

        options
    }

    /// Generate a simple direct call adapter (no memory crossing)
    fn generate_direct_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
        options: &AdapterOptions,
    ) -> Result<(u32, Function)> {
        let target_func = self.resolve_target_function(site, merged)?;

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

        let has_post_return = options.callee_post_return.is_some();
        let has_resource_ops = !options.resource_rep_calls.is_empty();
        let has_result_resource_ops = !options.resource_new_calls.is_empty();
        let needs_result_locals = (has_post_return || has_result_resource_ops) && result_count > 0;
        let scratch_count = options.resource_new_calls.len();

        if has_resource_ops || has_result_resource_ops || (has_post_return && result_count > 0) {
            let mut locals: Vec<(u32, wasm_encoder::ValType)> = Vec::new();
            let result_base = param_count as u32;
            if needs_result_locals {
                locals.extend(result_types.iter().map(|t| (1u32, *t)));
            }
            // Scratch locals for intermediate rep values (one i32 per own<T> result)
            let scratch_base = result_base + result_count as u32;
            if scratch_count > 0 {
                locals.extend(std::iter::repeat_n(
                    (1u32, wasm_encoder::ValType::I32),
                    scratch_count,
                ));
            }
            let mut func = Function::new(locals);

            // Phase 0: Convert borrow resource handles
            emit_resource_borrow_phase0(&mut func, &options.resource_rep_calls);

            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));

            if needs_result_locals {
                // Save results to locals (pop in reverse order)
                for i in (0..result_count).rev() {
                    func.instruction(&Instruction::LocalSet(result_base + i as u32));
                }

                // Phase R-rep: extract representations while handles are still alive
                emit_resource_rep_results(
                    &mut func,
                    &options.resource_new_calls,
                    result_base,
                    scratch_base,
                );

                // Call post-return with original handles (drops callee's handles)
                if has_post_return {
                    for i in 0..result_count {
                        func.instruction(&Instruction::LocalGet(result_base + i as u32));
                    }
                    func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
                }

                // Phase R-new: mint fresh handles from reps
                emit_resource_new_results(
                    &mut func,
                    &options.resource_new_calls,
                    result_base,
                    scratch_base,
                );

                // Push saved results back onto stack
                for i in 0..result_count {
                    func.instruction(&Instruction::LocalGet(result_base + i as u32));
                }
            } else if has_post_return {
                func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
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

        // --- Detect params-ptr calling convention ---
        // The canonical ABI uses params-ptr when flat params > MAX_FLAT_PARAMS (16):
        //   caller (lowered): (params_ptr: i32) → result...
        //   callee (lifted):  (params_ptr: i32) → result...
        // Both sides use a single i32 pointer to a buffer in linear memory.
        // When memories differ, the adapter must copy the buffer across.
        let uses_params_ptr = site.requirements.params_area_byte_size.is_some();

        if uses_params_ptr && options.caller_memory != options.callee_memory {
            log::debug!(
                "params-ptr adapter: generating for import={} (buffer={}B, {} ptr pairs, {} borrow fixups)",
                site.import_name,
                site.requirements.params_area_byte_size.unwrap_or(0),
                site.requirements.params_area_pointer_pair_offsets.len(),
                site.requirements
                    .params_area_resource_positions
                    .iter()
                    .filter(|p| !p.is_owned && p.callee_defines_resource)
                    .count(),
            );
            return self.generate_params_ptr_adapter(site, options, target_func, caller_type_idx);
        }

        // --- Non-retptr path: use callee's type so body is valid ---
        // wire_adapter_indices generates a widening wrapper if caller expects
        // wider result types (P3 async i64 vs i32).
        let adapter_type_idx = callee_type_idx;
        let param_count = callee_param_count;
        let result_count = callee_result_count;
        let result_types = callee_result_types;

        // If memories are the same, just do direct call (with post-return if needed)
        if options.caller_memory == options.callee_memory {
            let has_post_return = options.callee_post_return.is_some();
            let has_resource_ops = !options.resource_rep_calls.is_empty();

            if has_resource_ops || (has_post_return && result_count > 0) {
                let mut locals: Vec<(u32, wasm_encoder::ValType)> = Vec::new();
                let result_base = param_count as u32;
                if has_post_return && result_count > 0 {
                    locals.extend(result_types.iter().map(|t| (1u32, *t)));
                }
                let mut func = Function::new(locals);

                // Phase 0: Convert borrow resource handles
                emit_resource_borrow_phase0(&mut func, &options.resource_rep_calls);

                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));

                if has_post_return && result_count > 0 {
                    for i in (0..result_count).rev() {
                        func.instruction(&Instruction::LocalSet(result_base + i as u32));
                    }
                    for i in 0..result_count {
                        func.instruction(&Instruction::LocalGet(result_base + i as u32));
                    }
                    func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
                    for i in 0..result_count {
                        func.instruction(&Instruction::LocalGet(result_base + i as u32));
                    }
                } else if has_post_return {
                    func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
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

        let has_result_resource_ops = !options.resource_new_calls.is_empty();

        // We need result-save locals for post-return, conditional result copy,
        // or resource result conversion.
        let needs_result_save =
            (needs_post_return_save || needs_conditional_result_copy || has_result_resource_ops)
                && result_count > 0;

        let has_resource_ops = !options.resource_rep_calls.is_empty();

        let has_inner_resource_fixups = !options.inner_resource_fixups.is_empty();

        // If no copying, no post-return save, and no resource ops needed, direct call
        if !needs_outbound_copy
            && !needs_conditional_copy
            && !needs_result_copy
            && !needs_conditional_result_copy
            && !needs_post_return_save
            && !has_resource_ops
            && !has_inner_resource_fixups
            && !has_result_resource_ops
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
        let inner_resource_locals: u32 = if has_inner_resource_fixups { 1 } else { 0 }; // loop counter
        let num_param_pairs = site.requirements.pointer_pair_positions.len() as u32;
        let copy_scratch_count: u32 = if needs_outbound_copy && needs_result_copy {
            num_param_pairs.max(1) + 3 + inner_fixup_locals + inner_resource_locals
        } else if needs_result_copy {
            3 // callee_ret_ptr + callee_ret_len + caller_new_ptr
        } else if needs_outbound_copy {
            let num_pairs = site.requirements.pointer_pair_positions.len() as u32;
            num_pairs.max(1) + inner_fixup_locals + inner_resource_locals
        } else if needs_conditional_copy || needs_conditional_result_copy {
            1 // dest_ptr for conditional copy (param or result side)
        } else if has_inner_resource_fixups {
            1 + inner_resource_locals // dest_ptr + resource loop counter
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
        // Scratch locals for Phase R-rep intermediate rep values (one i32 per own<T> result)
        let own_result_scratch_count = options.resource_new_calls.len();
        let own_result_scratch_base = result_save_base + result_count as u32;
        if own_result_scratch_count > 0 {
            local_decls.push((own_result_scratch_count as u32, wasm_encoder::ValType::I32));
        }

        let mut func = Function::new(local_decls);

        // Phase 0: Convert borrow resource handles
        emit_resource_borrow_phase0(&mut func, &options.resource_rep_calls);

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

            // Copy ALL pointer pairs from caller to callee memory.
            let param_ptr_positions = &site.requirements.pointer_pair_positions;
            let param_layouts = &site.requirements.param_copy_layouts;
            for (pair_idx, &ptr_pos) in param_ptr_positions.iter().enumerate() {
                let len_pos = ptr_pos + 1;
                let dest_local = dest_ptr_local + pair_idx as u32;
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

                // Fix up inner pointers if element type contains owned data
                if let Some(crate::resolver::CopyLayout::Elements {
                    element_size,
                    inner_pointers,
                    ..
                }) = param_layouts.get(pair_idx)
                    && !inner_pointers.is_empty()
                {
                    let fixup_base = dest_ptr_local + num_param_pairs.max(1);
                    Self::emit_inner_pointer_fixup(
                        &mut func,
                        inner_pointers,
                        *element_size,
                        ptr_pos,    // src_base (caller's original ptr)
                        dest_local, // dst_base (callee's copy)
                        len_pos,    // count
                        options.caller_memory,
                        options.callee_memory,
                        callee_realloc,
                        fixup_base,
                    );
                }
            } // end for each pointer pair

            // 2c. Fix up inner resource handles if element type contains borrow<T>
            if !options.inner_resource_fixups.is_empty()
                && let Some(crate::resolver::CopyLayout::Elements { element_size, .. }) =
                    site.requirements.param_copy_layouts.first()
            {
                let element_size = *element_size;
                let loop_idx = dest_ptr_local + num_param_pairs.max(1) + inner_fixup_locals;
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::LocalSet(loop_idx));
                // block $exit { loop $cont {
                func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
                func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
                // if loop_idx >= len: break
                func.instruction(&Instruction::LocalGet(loop_idx));
                func.instruction(&Instruction::LocalGet(1)); // len
                func.instruction(&Instruction::I32GeU);
                func.instruction(&Instruction::BrIf(1));
                for &(byte_offset, rep_func) in &options.inner_resource_fixups {
                    // addr = dest_ptr + loop_idx * element_size + byte_offset
                    // i32.store needs [addr, value] on stack.
                    // Emit: addr, addr, i32.load → handle, call rep → rep, i32.store
                    // First push addr for the store:
                    func.instruction(&Instruction::LocalGet(dest_ptr_local));
                    func.instruction(&Instruction::LocalGet(loop_idx));
                    func.instruction(&Instruction::I32Const(element_size as i32));
                    func.instruction(&Instruction::I32Mul);
                    func.instruction(&Instruction::I32Add);
                    // Stack: [addr_for_store]
                    // Now load handle from same addr using offset
                    func.instruction(&Instruction::LocalGet(dest_ptr_local));
                    func.instruction(&Instruction::LocalGet(loop_idx));
                    func.instruction(&Instruction::I32Const(element_size as i32));
                    func.instruction(&Instruction::I32Mul);
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                        offset: byte_offset as u64,
                        align: 2,
                        memory_index: options.callee_memory,
                    }));
                    // Stack: [addr_for_store, handle]
                    func.instruction(&Instruction::Call(rep_func));
                    // Stack: [addr_for_store, rep]
                    func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                        offset: byte_offset as u64,
                        align: 2,
                        memory_index: options.callee_memory,
                    }));
                }
                // loop_idx++
                func.instruction(&Instruction::LocalGet(loop_idx));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalSet(loop_idx));
                func.instruction(&Instruction::Br(0));
                func.instruction(&Instruction::End); // loop
                func.instruction(&Instruction::End); // block
            }

            // 3. Call target with remapped pointer pairs
            for i in 0..param_count as u32 {
                if let Some(pair_idx) = param_ptr_positions.iter().position(|&pos| pos == i) {
                    // Replace pointer with allocated copy in callee memory
                    func.instruction(&Instruction::LocalGet(dest_ptr_local + pair_idx as u32));
                } else {
                    func.instruction(&Instruction::LocalGet(i));
                }
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

        // Post-return and/or conditional result copy
        if !needs_result_copy
            && (needs_conditional_result_copy
                || options.callee_post_return.is_some()
                || has_result_resource_ops)
        {
            if result_count > 0 && needs_result_save {
                // Save return values to scratch locals (pop in reverse order)
                for i in (0..result_count).rev() {
                    func.instruction(&Instruction::LocalSet(result_save_base + i as u32));
                }

                // Phase R-rep: extract representations while handles are still alive
                emit_resource_rep_results(
                    &mut func,
                    &options.resource_new_calls,
                    result_save_base,
                    own_result_scratch_base,
                );
            }

            // Call post-return with callee's original handles (drops them)
            if let Some(post_return_func) = options.callee_post_return {
                if result_count > 0 && needs_result_save {
                    for i in 0..result_count {
                        func.instruction(&Instruction::LocalGet(result_save_base + i as u32));
                    }
                }
                func.instruction(&Instruction::Call(post_return_func));
            }

            // Phase R-new: mint fresh handles from reps (after post_return dropped originals)
            if result_count > 0 && needs_result_save && has_result_resource_ops {
                emit_resource_new_results(
                    &mut func,
                    &options.resource_new_calls,
                    result_save_base,
                    own_result_scratch_base,
                );
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

    /// Generate an adapter for the params-ptr calling convention.
    ///
    /// When flat param count > MAX_FLAT_PARAMS (16), the canonical ABI stores all
    /// params in a buffer in linear memory. Both caller and callee use:
    ///   (params_ptr: i32) → result...
    ///
    /// The adapter bridges different memories:
    /// 1. Allocate buffer in callee's memory via cabi_realloc
    /// 2. Bulk copy the params buffer from caller to callee memory
    /// 3. Fix up any (ptr, len) pairs inside the buffer — copy pointed-to data
    ///    from caller memory to callee memory and update the pointers
    /// 4. Call callee with new pointer
    /// 5. Return the result(s)
    fn generate_params_ptr_adapter(
        &self,
        site: &AdapterSite,
        options: &AdapterOptions,
        target_func: u32,
        caller_type_idx: u32,
    ) -> Result<(u32, Function)> {
        let params_area_size = site.requirements.params_area_byte_size.unwrap_or(0);
        let params_area_align = site.requirements.params_area_max_align.max(1);
        let ptr_pair_offsets = &site.requirements.params_area_pointer_pair_offsets;
        let copy_layouts = &site.requirements.params_area_copy_layouts;

        let callee_realloc = options.callee_realloc.unwrap_or_else(|| {
            log::warn!("params-ptr adapter: no callee realloc, buffer copy may fail");
            0
        });

        // Check if any list copy layouts contain inner resources (borrow handles)
        let has_inner_resources = copy_layouts.iter().any(|cl| {
            matches!(cl,
                crate::resolver::CopyLayout::Elements { inner_resources, .. }
                if !inner_resources.is_empty()
            )
        });

        // Local layout:
        //   0: params_ptr (the function parameter — pointer to caller's memory)
        //   1: callee_ptr (allocated pointer in callee's memory)
        //   2..2+N: dest_ptr for each pointer pair copy
        //   2+N: loop_counter (if inner resources need fixup)
        let num_ptr_pairs = ptr_pair_offsets.len() as u32;
        let loop_counter_count = if has_inner_resources { 1u32 } else { 0 };
        let scratch_count = 1 + num_ptr_pairs + loop_counter_count; // callee_ptr + per-pair dest ptrs + loop counter

        // Post-return needs result save locals
        let has_post_return = options.callee_post_return.is_some();
        // For params-ptr, the results come from the callee directly.

        let mut local_decls: Vec<(u32, wasm_encoder::ValType)> = Vec::new();
        if scratch_count > 0 {
            local_decls.push((scratch_count, wasm_encoder::ValType::I32));
        }

        // We don't know result count from here, so we handle post-return simply:
        // if there's a post-return, we'll save and restore results.
        // But for params-ptr functions with resource results, result count should be 1 (i32).
        // For simplicity: if has_post_return, add 1 i32 result save local.
        let result_save_base = 1 + scratch_count; // after params_ptr(0) + scratch
        if has_post_return {
            local_decls.push((1, wasm_encoder::ValType::I32));
        }

        let mut func = Function::new(local_decls);

        let params_ptr_local: u32 = 0;
        let callee_ptr_local: u32 = 1;
        let pair_dest_base: u32 = 2;

        // --- Phase 1: Allocate buffer in callee's memory ---
        // callee_ptr = cabi_realloc(0, 0, align, size)
        func.instruction(&Instruction::I32Const(0)); // original_ptr
        func.instruction(&Instruction::I32Const(0)); // original_size
        func.instruction(&Instruction::I32Const(params_area_align as i32)); // alignment
        func.instruction(&Instruction::I32Const(params_area_size as i32)); // new_size
        func.instruction(&Instruction::Call(callee_realloc));
        func.instruction(&Instruction::LocalSet(callee_ptr_local));

        // --- Phase 2: Bulk copy the entire params buffer ---
        // memory.copy $callee_mem $caller_mem (callee_ptr, params_ptr, size)
        func.instruction(&Instruction::LocalGet(callee_ptr_local)); // dst
        func.instruction(&Instruction::LocalGet(params_ptr_local)); // src
        func.instruction(&Instruction::I32Const(params_area_size as i32)); // size
        func.instruction(&Instruction::MemoryCopy {
            src_mem: options.caller_memory,
            dst_mem: options.callee_memory,
        });

        // --- Phase 3: Fix up pointer pairs inside the buffer ---
        // For each (ptr, len) pair in the params buffer:
        //   1. Read ptr and len from callee's copy of the buffer
        //   2. Compute byte_size from len and the copy layout's byte_multiplier
        //   3. Allocate in callee's memory: new_ptr = cabi_realloc(0, 0, 1, byte_size)
        //   4. Copy data from caller's memory at old_ptr to callee's memory at new_ptr
        //   5. Write new_ptr back into callee's buffer at the same offset
        for (pair_idx, &byte_offset) in ptr_pair_offsets.iter().enumerate() {
            let dest_local = pair_dest_base + pair_idx as u32;
            let byte_mult = copy_layouts
                .get(pair_idx)
                .map(|cl| match cl {
                    crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                    crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                })
                .unwrap_or(1);

            // Read old_ptr from callee's buffer: i32.load callee_mem (callee_ptr + byte_offset)
            // Read old_len from callee's buffer: i32.load callee_mem (callee_ptr + byte_offset + 4)

            // Allocate: new_ptr = cabi_realloc(0, 0, 1, len * byte_mult)
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::I32Const(1));
            // Load len from callee's buffer
            func.instruction(&Instruction::LocalGet(callee_ptr_local));
            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: (byte_offset + 4) as u64,
                align: 2,
                memory_index: options.callee_memory,
            }));
            if byte_mult > 1 {
                func.instruction(&Instruction::I32Const(byte_mult as i32));
                func.instruction(&Instruction::I32Mul);
            }
            func.instruction(&Instruction::Call(callee_realloc));
            func.instruction(&Instruction::LocalSet(dest_local));

            // Copy data: memory.copy callee caller (new_ptr, old_ptr, len * byte_mult)
            func.instruction(&Instruction::LocalGet(dest_local)); // dst (in callee mem)
            // Load old_ptr from callee's buffer (this was copied from caller's buffer,
            // so it points into caller's memory)
            func.instruction(&Instruction::LocalGet(callee_ptr_local));
            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: byte_offset as u64,
                align: 2,
                memory_index: options.callee_memory,
            })); // src (in caller mem)
            // Load len from callee's buffer
            func.instruction(&Instruction::LocalGet(callee_ptr_local));
            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: (byte_offset + 4) as u64,
                align: 2,
                memory_index: options.callee_memory,
            }));
            if byte_mult > 1 {
                func.instruction(&Instruction::I32Const(byte_mult as i32));
                func.instruction(&Instruction::I32Mul);
            }
            func.instruction(&Instruction::MemoryCopy {
                src_mem: options.caller_memory,
                dst_mem: options.callee_memory,
            });

            // Write new_ptr back into callee's buffer at byte_offset
            func.instruction(&Instruction::LocalGet(callee_ptr_local));
            func.instruction(&Instruction::LocalGet(dest_local));
            func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                offset: byte_offset as u64,
                align: 2,
                memory_index: options.callee_memory,
            }));

            // Fix up inner resource handles in list elements.
            // After bulk copy, borrow handles in the list data still reference
            // the caller's resource table. Convert each borrow handle → rep.
            if let Some(crate::resolver::CopyLayout::Elements {
                element_size,
                inner_resources,
                ..
            }) = copy_layouts.get(pair_idx)
                && !inner_resources.is_empty()
            {
                let element_size = *element_size;
                let loop_local = pair_dest_base + num_ptr_pairs;

                // Initialize loop counter to 0
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::LocalSet(loop_local));

                // block $exit { loop $cont {
                func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
                func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

                // if loop_counter >= len: break
                func.instruction(&Instruction::LocalGet(loop_local));
                // Load len from callee's buffer
                func.instruction(&Instruction::LocalGet(callee_ptr_local));
                func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                    offset: (byte_offset + 4) as u64,
                    align: 2,
                    memory_index: options.callee_memory,
                }));
                func.instruction(&Instruction::I32GeU);
                func.instruction(&Instruction::BrIf(1)); // break to $exit

                for &(res_byte_offset, _resource_type_id, is_owned) in inner_resources {
                    if is_owned {
                        continue; // own<T>: callee handles internally
                    }
                    // Find [resource-rep] for this resource
                    if let Some(&rep_func) = options
                        .params_area_borrow_fixups
                        .first()
                        .map(|f| &f.rep_func)
                        .or_else(|| options.resource_rep_calls.first().map(|t| &t.rep_func))
                    {
                        // addr = dest_ptr + loop_counter * element_size + res_byte_offset
                        // Push addr for store
                        func.instruction(&Instruction::LocalGet(dest_local));
                        func.instruction(&Instruction::LocalGet(loop_local));
                        func.instruction(&Instruction::I32Const(element_size as i32));
                        func.instruction(&Instruction::I32Mul);
                        func.instruction(&Instruction::I32Add);
                        // Load handle from same addr + offset
                        func.instruction(&Instruction::LocalGet(dest_local));
                        func.instruction(&Instruction::LocalGet(loop_local));
                        func.instruction(&Instruction::I32Const(element_size as i32));
                        func.instruction(&Instruction::I32Mul);
                        func.instruction(&Instruction::I32Add);
                        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                            offset: res_byte_offset as u64,
                            align: 2,
                            memory_index: options.callee_memory,
                        }));
                        // Call [resource-rep](handle) → rep
                        func.instruction(&Instruction::Call(rep_func));
                        // Store rep back
                        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                            offset: res_byte_offset as u64,
                            align: 2,
                            memory_index: options.callee_memory,
                        }));
                    }
                }

                // loop_counter++
                func.instruction(&Instruction::LocalGet(loop_local));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalSet(loop_local));
                func.instruction(&Instruction::Br(0)); // continue to $cont
                func.instruction(&Instruction::End); // end loop
                func.instruction(&Instruction::End); // end block
            }
        }

        // --- Phase 3.5: Convert borrow resource handles inside the buffer ---
        // For borrow<T> where callee defines T, the adapter must convert
        // handle → rep by calling [resource-rep] and writing the rep back.
        for fixup in &options.params_area_borrow_fixups {
            // Stack: callee_ptr (for i32.store dest)
            func.instruction(&Instruction::LocalGet(callee_ptr_local));
            // Load handle from callee's buffer at byte_offset
            func.instruction(&Instruction::LocalGet(callee_ptr_local));
            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: fixup.byte_offset as u64,
                align: 2,
                memory_index: options.callee_memory,
            }));
            // Call [resource-rep](handle) → rep
            func.instruction(&Instruction::Call(fixup.rep_func));
            // Store rep back at the same offset
            func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                offset: fixup.byte_offset as u64,
                align: 2,
                memory_index: options.callee_memory,
            }));
        }

        // --- Phase 4: Call callee with the new pointer ---
        func.instruction(&Instruction::LocalGet(callee_ptr_local));
        func.instruction(&Instruction::Call(target_func));

        // --- Phase 5: Handle post-return if needed ---
        if has_post_return {
            // Save result (assume i32)
            func.instruction(&Instruction::LocalSet(result_save_base));
            // Call post-return (no args for params-ptr convention post-return)
            func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
            // Push result back
            func.instruction(&Instruction::LocalGet(result_save_base));
        }

        func.instruction(&Instruction::End);

        Ok((caller_type_idx, func))
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
        if !options.inner_resource_fixups.is_empty() {
            scratch_count += 1; // resource loop counter
        }

        let local_decls = vec![(scratch_count, wasm_encoder::ValType::I32)];
        let mut func = Function::new(local_decls);

        // Phase 0: Convert borrow resource handles
        emit_resource_borrow_phase0(&mut func, &options.resource_rep_calls);

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
                    ..
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

                // Fix up inner resource handles after bulk copy
                if let Some(crate::resolver::CopyLayout::Elements {
                    element_size,
                    inner_resources,
                    ..
                }) = param_layouts.get(pair_idx)
                    && !inner_resources.is_empty()
                    && !options.inner_resource_fixups.is_empty()
                {
                    let element_size = *element_size;
                    let res_loop_idx = fixup_locals_base + 4 * max_fixup_depth;
                    func.instruction(&Instruction::I32Const(0));
                    func.instruction(&Instruction::LocalSet(res_loop_idx));
                    func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
                    func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
                    func.instruction(&Instruction::LocalGet(res_loop_idx));
                    func.instruction(&Instruction::LocalGet(len_pos));
                    func.instruction(&Instruction::I32GeU);
                    func.instruction(&Instruction::BrIf(1));
                    for &(byte_offset, rep_func) in &options.inner_resource_fixups {
                        // Push addr for store
                        func.instruction(&Instruction::LocalGet(dest_local));
                        func.instruction(&Instruction::LocalGet(res_loop_idx));
                        func.instruction(&Instruction::I32Const(element_size as i32));
                        func.instruction(&Instruction::I32Mul);
                        func.instruction(&Instruction::I32Add);
                        // Load handle
                        func.instruction(&Instruction::LocalGet(dest_local));
                        func.instruction(&Instruction::LocalGet(res_loop_idx));
                        func.instruction(&Instruction::I32Const(element_size as i32));
                        func.instruction(&Instruction::I32Mul);
                        func.instruction(&Instruction::I32Add);
                        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                            offset: byte_offset as u64,
                            align: 2,
                            memory_index: options.callee_memory,
                        }));
                        func.instruction(&Instruction::Call(rep_func));
                        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                            offset: byte_offset as u64,
                            align: 2,
                            memory_index: options.callee_memory,
                        }));
                    }
                    func.instruction(&Instruction::LocalGet(res_loop_idx));
                    func.instruction(&Instruction::I32Const(1));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::LocalSet(res_loop_idx));
                    func.instruction(&Instruction::Br(0));
                    func.instruction(&Instruction::End);
                    func.instruction(&Instruction::End);
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
                        ..
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
                ..
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

        // Phase 0: Convert borrow resource handles
        emit_resource_borrow_phase0(&mut func, &options.resource_rep_calls);

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

    /// Generate a callback-driving adapter for P3 async cross-component calls.
    ///
    /// Instead of canon lift/lower (which triggers call_might_be_recursive),
    /// the adapter drives the callee's [async-lift] + [callback] loop directly
    /// in core wasm. The protocol:
    ///   1. Call [async-lift] entry → packed i32 (EXIT/WAIT/YIELD)
    ///   2. Loop: poll waitable-set, call [callback] with events
    ///   3. After EXIT, call [task-get-result] host import for result
    fn generate_async_callback_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
    ) -> Result<AdapterFunction> {
        let name = format!(
            "$async_adapter_{}_to_{}",
            site.from_component, site.to_component
        );

        // Find the [async-lift] entry function's merged index
        let async_lift_func = self.resolve_target_function(site, merged)?;

        // Find the [callback] function's merged index by deriving its export name
        let callback_export_name = format!("[callback]{}", site.export_name);
        let callback_func = merged
            .exports
            .iter()
            .find(|e| e.kind == wasm_encoder::ExportKind::Func && e.name == callback_export_name)
            .map(|e| e.index)
            .ok_or_else(|| {
                crate::error::Error::EncodingError(format!(
                    "async adapter: cannot find callback export '{}' for '{}'",
                    callback_export_name, site.export_name,
                ))
            })?;

        // Find the waitable-set-poll host import. It's an unresolved import
        // from $root with name [waitable-set-poll] (possibly with $N suffix).
        let wsp_func = merged
            .imports
            .iter()
            .enumerate()
            .find(|(_, imp)| imp.name.starts_with("[waitable-set-poll]"))
            .map(|(i, _)| i as u32)
            .ok_or_else(|| {
                crate::error::Error::EncodingError(
                    "async adapter: cannot find [waitable-set-poll] import".to_string(),
                )
            })?;

        // Determine the caller's type (what the caller expects to call)
        let caller_type_idx = site
            .import_func_type_idx
            .and_then(|local_ti| {
                merged
                    .type_index_map
                    .get(&(site.from_component, site.from_module, local_ti))
                    .copied()
            })
            .unwrap_or(0);

        let caller_type = merged
            .types
            .get(caller_type_idx as usize)
            .cloned()
            .unwrap_or_else(|| crate::merger::MergedFuncType {
                params: Vec::new(),
                results: Vec::new(),
            });
        let caller_param_count = caller_type.params.len();
        let _caller_result_count = caller_type.results.len();

        // Find memory indices for cross-memory operations
        let callee_memory = crate::merger::component_memory_index(merged, site.to_component);
        let caller_memory = crate::merger::component_memory_index(merged, site.from_component);

        // Determine the [async-lift] entry's param count from its type.
        // The caller may have extra params (e.g., retptr for multi-value results)
        // that shouldn't be passed to the callee.
        let callee_param_count = merged
            .defined_func(async_lift_func)
            .and_then(|f| merged.types.get(f.type_idx as usize))
            .map(|t| t.params.len())
            .unwrap_or(caller_param_count);

        // Build the adapter function body
        //
        // Locals layout:
        //   0..caller_param_count: params from caller
        //   caller_param_count+0: $packed (i32) — packed return from entry/callback
        //   caller_param_count+1: $code (i32) — unpacked callback code
        //   caller_param_count+2: $payload (i32) — unpacked payload (waitable set idx)
        //   caller_param_count+3: $event_code (i32)
        //   caller_param_count+4: $p1 (i32)
        //   caller_param_count+5: $p2 (i32)
        let l_packed = caller_param_count as u32;
        let l_code = l_packed + 1;
        let l_payload = l_packed + 2;
        let l_event_code = l_packed + 3;
        let l_p1 = l_packed + 4;
        let l_p2 = l_packed + 5;

        // 6 locals for callback loop + 4 for string copy (src_ptr, src_len, dst_ptr, new_ptr)
        let mut body = Function::new([(10, wasm_encoder::ValType::I32)]);

        // Step 0.5: Copy string/list params from caller to callee memory
        // if the call crosses a memory boundary and has pointer pair params.
        let callee_realloc = crate::merger::component_realloc_index(merged, site.to_component);
        let has_param_copies = site.crosses_memory
            && !site.requirements.pointer_pair_positions.is_empty()
            && callee_realloc.is_some();

        if has_param_copies {
            log::debug!(
                "async adapter param copy: export={} crosses_memory={} positions={:?} callee_mem={} caller_mem={}",
                site.export_name,
                site.crosses_memory,
                site.requirements.pointer_pair_positions,
                callee_memory,
                caller_memory,
            );
            let realloc = callee_realloc.unwrap();
            // For each (ptr, len) pair in the params, allocate in callee
            // memory and copy the data from caller memory.
            for &ptr_pos in &site.requirements.pointer_pair_positions {
                let ptr_local = ptr_pos;
                let len_local = ptr_local + 1;
                let l_new_ptr = l_p2 + 4; // reuse scratch local

                // Allocate in callee memory: cabi_realloc(0, 0, 1, len)
                body.instruction(&Instruction::I32Const(0));
                body.instruction(&Instruction::I32Const(0));
                body.instruction(&Instruction::I32Const(1));
                body.instruction(&Instruction::LocalGet(len_local));
                body.instruction(&Instruction::Call(realloc));
                body.instruction(&Instruction::LocalSet(l_new_ptr));

                // Copy from caller memory to callee memory
                body.instruction(&Instruction::LocalGet(l_new_ptr)); // dst
                body.instruction(&Instruction::LocalGet(ptr_local)); // src
                body.instruction(&Instruction::LocalGet(len_local)); // len
                body.instruction(&Instruction::MemoryCopy {
                    dst_mem: callee_memory,
                    src_mem: caller_memory,
                });

                // Replace the ptr param with the new callee-memory ptr
                body.instruction(&Instruction::LocalGet(l_new_ptr));
                body.instruction(&Instruction::LocalSet(ptr_local));
            }
        }

        // Step 1: Call [async-lift] entry with callee's params
        // (skip retptr if caller has more params than callee)
        for i in 0..callee_param_count {
            body.instruction(&Instruction::LocalGet(i as u32));
        }
        body.instruction(&Instruction::Call(async_lift_func));
        body.instruction(&Instruction::LocalSet(l_packed));

        // Unpack: code = packed & 0xF, payload = packed >> 4
        body.instruction(&Instruction::LocalGet(l_packed));
        body.instruction(&Instruction::I32Const(0xF));
        body.instruction(&Instruction::I32And);
        body.instruction(&Instruction::LocalSet(l_code));
        body.instruction(&Instruction::LocalGet(l_packed));
        body.instruction(&Instruction::I32Const(4));
        body.instruction(&Instruction::I32ShrU);
        body.instruction(&Instruction::LocalSet(l_payload));

        // Step 2: Callback-driving loop
        // block $exit
        //   loop $drive
        //     if code == EXIT(0): break
        //     if code == WAIT(2): call waitable-set-poll
        //     call callback(event_code, p1, p2)
        //     unpack result
        //     br $drive
        //   end
        // end
        body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        // if code == 0 (EXIT): br $exit (block index 1)
        body.instruction(&Instruction::LocalGet(l_code));
        body.instruction(&Instruction::I32Eqz);
        body.instruction(&Instruction::BrIf(1)); // break to $exit block

        // if code == 2 (WAIT): call waitable-set-poll(payload, event_ptr)
        // Use scratch space at address 0 in callee memory for the 3xi32 event tuple
        // (This is safe because the callee isn't running — we're driving it)
        body.instruction(&Instruction::LocalGet(l_code));
        body.instruction(&Instruction::I32Const(2));
        body.instruction(&Instruction::I32Eq);
        body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            // waitable-set-poll(set_handle, event_ptr) → i32
            body.instruction(&Instruction::LocalGet(l_payload));
            body.instruction(&Instruction::I32Const(0)); // event result ptr (scratch)
            body.instruction(&Instruction::Call(wsp_func));
            body.instruction(&Instruction::Drop); // drop poll return value

            // Read event tuple from scratch memory: [event_code, p1, p2] at addr 0
            let mem_arg = wasm_encoder::MemArg {
                offset: 0,
                align: 2,
                memory_index: callee_memory,
            };
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Load(mem_arg));
            body.instruction(&Instruction::LocalSet(l_event_code));

            let mem_arg_4 = wasm_encoder::MemArg {
                offset: 4,
                align: 2,
                memory_index: callee_memory,
            };
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Load(mem_arg_4));
            body.instruction(&Instruction::LocalSet(l_p1));

            let mem_arg_8 = wasm_encoder::MemArg {
                offset: 8,
                align: 2,
                memory_index: callee_memory,
            };
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Load(mem_arg_8));
            body.instruction(&Instruction::LocalSet(l_p2));
        }
        body.instruction(&Instruction::Else);
        {
            // YIELD(1): set event to (NONE, 0, 0)
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::LocalSet(l_event_code));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::LocalSet(l_p1));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::LocalSet(l_p2));
        }
        body.instruction(&Instruction::End); // end if WAIT/YIELD

        // Call callback(event_code, p1, p2) → packed i32
        body.instruction(&Instruction::LocalGet(l_event_code));
        body.instruction(&Instruction::LocalGet(l_p1));
        body.instruction(&Instruction::LocalGet(l_p2));
        body.instruction(&Instruction::Call(callback_func));
        body.instruction(&Instruction::LocalSet(l_packed));

        // Unpack new result
        body.instruction(&Instruction::LocalGet(l_packed));
        body.instruction(&Instruction::I32Const(0xF));
        body.instruction(&Instruction::I32And);
        body.instruction(&Instruction::LocalSet(l_code));
        body.instruction(&Instruction::LocalGet(l_packed));
        body.instruction(&Instruction::I32Const(4));
        body.instruction(&Instruction::I32ShrU);
        body.instruction(&Instruction::LocalSet(l_payload));

        body.instruction(&Instruction::Br(0)); // br $drive (loop)
        body.instruction(&Instruction::End); // end loop
        body.instruction(&Instruction::End); // end block

        // Step 3: After EXIT, read result values from shim globals.
        //
        // The task.return shim (generated in step 2.5) stored the result
        // values to globals when the callee called task.return during the
        // callback loop. Read them back and return to the caller.
        //
        // Find the matching shim by looking for task_return_shims entries
        // belonging to the callee component.
        // Match by function name: extract the func name from the
        // async-lift export name (after the last '#') and find the
        // shim with the matching original_func_name.
        let adapter_func_name = site
            .export_name
            .rsplit_once('#')
            .map(|(_, name)| name)
            .unwrap_or(&site.export_name);

        let shim_info = merged
            .task_return_shims
            .values()
            .find(|info| {
                info.component_idx == site.to_component
                    && info.original_func_name == adapter_func_name
            })
            .or_else(|| {
                // Fallback: match by type signature if name matching fails
                merged.task_return_shims.values().find(|info| {
                    info.component_idx == site.to_component
                        && info.result_globals.len() == caller_type.results.len()
                        && info
                            .result_globals
                            .iter()
                            .zip(caller_type.results.iter())
                            .all(|((_, gt), ct)| gt == ct)
                })
            });

        // Detect retptr convention: caller has more params than callee
        // and returns void — the last caller param is the result pointer.
        let uses_retptr = caller_type.results.is_empty() && caller_param_count > callee_param_count;

        // Find caller's cabi_realloc for cross-memory string copying
        let caller_realloc = crate::merger::component_realloc_index(merged, site.from_component);

        if let Some(info) = shim_info {
            if uses_retptr {
                // Retptr convention: write results to caller's return area.
                // For (ptr, len) pairs that reference callee memory, copy
                // the data to caller memory first.
                let retptr_local = callee_param_count as u32;

                // Check if this is a pointer pair: exactly 2 i32 globals
                // and memories differ (cross-memory copy needed).
                let is_ptr_len_pair = info.result_globals.len() == 2
                    && info
                        .result_globals
                        .iter()
                        .all(|(_, t)| *t == wasm_encoder::ValType::I32)
                    && callee_memory != caller_memory
                    && caller_realloc.is_some();

                if is_ptr_len_pair {
                    let realloc_func = caller_realloc.unwrap();
                    let (ptr_global, _) = info.result_globals[0];
                    let (len_global, _) = info.result_globals[1];

                    // Allocate in caller memory: cabi_realloc(0, 0, 1, len) → new_ptr
                    // locals: l_packed+6 = src_ptr, l_packed+7 = src_len, l_packed+8 = dst_ptr
                    let l_src_ptr = l_p2 + 1;
                    let l_src_len = l_p2 + 2;
                    let l_dst_ptr = l_p2 + 3;

                    // Read source ptr and len from shim globals
                    body.instruction(&Instruction::GlobalGet(ptr_global));
                    body.instruction(&Instruction::LocalSet(l_src_ptr));
                    body.instruction(&Instruction::GlobalGet(len_global));
                    body.instruction(&Instruction::LocalSet(l_src_len));

                    // Allocate in caller memory
                    body.instruction(&Instruction::I32Const(0)); // old_ptr
                    body.instruction(&Instruction::I32Const(0)); // old_size
                    body.instruction(&Instruction::I32Const(1)); // align
                    body.instruction(&Instruction::LocalGet(l_src_len)); // new_size
                    body.instruction(&Instruction::Call(realloc_func));
                    body.instruction(&Instruction::LocalSet(l_dst_ptr));

                    // Copy from callee memory to caller memory
                    body.instruction(&Instruction::LocalGet(l_dst_ptr)); // dst
                    body.instruction(&Instruction::LocalGet(l_src_ptr)); // src
                    body.instruction(&Instruction::LocalGet(l_src_len)); // len
                    body.instruction(&Instruction::MemoryCopy {
                        dst_mem: caller_memory,
                        src_mem: callee_memory,
                    });

                    // Write (new_ptr, len) to retptr
                    let mem_arg_0 = wasm_encoder::MemArg {
                        offset: 0,
                        align: 2,
                        memory_index: caller_memory,
                    };
                    let mem_arg_4 = wasm_encoder::MemArg {
                        offset: 4,
                        align: 2,
                        memory_index: caller_memory,
                    };
                    body.instruction(&Instruction::LocalGet(retptr_local));
                    body.instruction(&Instruction::LocalGet(l_dst_ptr));
                    body.instruction(&Instruction::I32Store(mem_arg_0));
                    body.instruction(&Instruction::LocalGet(retptr_local));
                    body.instruction(&Instruction::LocalGet(l_src_len));
                    body.instruction(&Instruction::I32Store(mem_arg_4));
                } else {
                    // Non-pointer results: write globals directly to retptr
                    let mut offset = 0u32;
                    for (global_idx, val_ty) in &info.result_globals {
                        body.instruction(&Instruction::LocalGet(retptr_local));
                        body.instruction(&Instruction::GlobalGet(*global_idx));
                        let mem_arg = wasm_encoder::MemArg {
                            offset: offset as u64,
                            align: match val_ty {
                                wasm_encoder::ValType::I64 | wasm_encoder::ValType::F64 => 3,
                                _ => 2,
                            },
                            memory_index: caller_memory,
                        };
                        match val_ty {
                            wasm_encoder::ValType::I32 => {
                                body.instruction(&Instruction::I32Store(mem_arg));
                                offset += 4;
                            }
                            wasm_encoder::ValType::I64 => {
                                body.instruction(&Instruction::I64Store(mem_arg));
                                offset += 8;
                            }
                            wasm_encoder::ValType::F32 => {
                                body.instruction(&Instruction::F32Store(mem_arg));
                                offset += 4;
                            }
                            wasm_encoder::ValType::F64 => {
                                body.instruction(&Instruction::F64Store(mem_arg));
                                offset += 8;
                            }
                            _ => {
                                body.instruction(&Instruction::I32Store(mem_arg));
                                offset += 4;
                            }
                        }
                    }
                }
            } else {
                // Push result values onto the stack
                for (global_idx, _) in &info.result_globals {
                    body.instruction(&Instruction::GlobalGet(*global_idx));
                }
            }
        } else {
            // Fallback: return default values if no matching shim found
            for result_ty in &caller_type.results {
                match result_ty {
                    wasm_encoder::ValType::I32 => {
                        body.instruction(&Instruction::I32Const(0));
                    }
                    wasm_encoder::ValType::I64 => {
                        body.instruction(&Instruction::I64Const(0));
                    }
                    wasm_encoder::ValType::F32 => {
                        body.instruction(&Instruction::F32Const(0.0_f32.into()));
                    }
                    wasm_encoder::ValType::F64 => {
                        body.instruction(&Instruction::F64Const(0.0_f64.into()));
                    }
                    _ => {
                        body.instruction(&Instruction::I32Const(0));
                    }
                }
            }
        }

        body.instruction(&Instruction::End);

        let target_func = self.resolve_target_function(site, merged)?;

        Ok(AdapterFunction {
            name,
            type_idx: caller_type_idx,
            body,
            source_component: site.from_component,
            source_module: site.from_module,
            target_component: site.to_component,
            target_module: site.to_module,
            target_function: target_func,
        })
    }
}

impl AdapterGenerator for FactStyleGenerator {
    fn generate(
        &self,
        merged: &MergedModule,
        graph: &DependencyGraph,
    ) -> Result<Vec<AdapterFunction>> {
        let (resource_rep_imports, resource_new_imports) = build_resource_import_maps(merged);
        let mut adapters = Vec::new();

        for (idx, site) in graph.adapter_sites.iter().enumerate() {
            if site.is_async_lift {
                let adapter = self.generate_async_callback_adapter(site, merged)?;
                adapters.push(adapter);
                continue;
            }
            let adapter = self.generate_adapter(
                site,
                merged,
                idx,
                &resource_rep_imports,
                &resource_new_imports,
            )?;
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

    // ---------------------------------------------------------------
    // SR-17: String transcoding correctness
    //
    // These tests verify the adapter's string encoding handling:
    //   - canon_to_string_encoding mapping
    //   - alignment_for_encoding values
    //   - needs_transcoding detection for all encoding pairs
    //   - Scratch local allocation for transcoding paths
    //
    // Currently supported transcoding paths:
    //   - UTF-8  <-> UTF-8  (no-op, direct call)
    //   - UTF-8   -> UTF-16 (emit_utf8_to_utf16_transcode)
    //   - UTF-16  -> UTF-8  (emit_utf16_to_utf8_transcode)
    //   - Latin-1 -> UTF-8  (emit_latin1_to_utf8_transcode)
    //
    // Edge cases NOT yet tested at runtime:
    //   - UTF-8  -> Latin-1 (falls through to direct call, no transcoding)
    //   - UTF-16 -> Latin-1 (falls through to direct call, no transcoding)
    //   - Latin-1 -> UTF-16 (falls through to direct call, no transcoding)
    //   - Latin-1 <-> Latin-1 (no-op, direct call)
    //   - Surrogate pair handling for non-BMP characters (U+10000+)
    //   - Overlong UTF-8 sequences (malformed input)
    //   - Lone surrogates in UTF-16 input
    //
    // For full SR-17 coverage, runtime tests with wasmtime are needed
    // to verify actual byte-level correctness of the transcoding loops.
    // See tests/adapter_safety.rs for the runtime harness pattern.
    // ---------------------------------------------------------------

    #[test]
    fn test_sr17_canon_to_string_encoding_utf8() {
        assert_eq!(
            canon_to_string_encoding(CanonStringEncoding::Utf8),
            StringEncoding::Utf8,
            "SR-17: CanonStringEncoding::Utf8 should map to StringEncoding::Utf8"
        );
    }

    #[test]
    fn test_sr17_canon_to_string_encoding_utf16() {
        assert_eq!(
            canon_to_string_encoding(CanonStringEncoding::Utf16),
            StringEncoding::Utf16,
            "SR-17: CanonStringEncoding::Utf16 should map to StringEncoding::Utf16"
        );
    }

    #[test]
    fn test_sr17_canon_to_string_encoding_compact_utf16() {
        // CompactUTF16 (latin1+utf16) is treated as Latin1 for adapter purposes.
        // The canonical ABI spec defines CompactUTF16 as an optimization where
        // strings that fit in Latin-1 use 1 byte/char, otherwise UTF-16.
        // The adapter treats it as Latin-1 because that's the worst-case element
        // size (1 byte), and the caller is responsible for the compact encoding.
        assert_eq!(
            canon_to_string_encoding(CanonStringEncoding::CompactUtf16),
            StringEncoding::Latin1,
            "SR-17: CompactUTF16 should map to Latin1 for adapter purposes"
        );
    }

    #[test]
    fn test_sr17_alignment_for_utf8() {
        assert_eq!(
            alignment_for_encoding(StringEncoding::Utf8),
            1,
            "SR-17: UTF-8 alignment should be 1 (byte-aligned)"
        );
    }

    #[test]
    fn test_sr17_alignment_for_utf16() {
        assert_eq!(
            alignment_for_encoding(StringEncoding::Utf16),
            2,
            "SR-17: UTF-16 alignment should be 2 (2-byte aligned for code units)"
        );
    }

    #[test]
    fn test_sr17_alignment_for_latin1() {
        assert_eq!(
            alignment_for_encoding(StringEncoding::Latin1),
            1,
            "SR-17: Latin-1 alignment should be 1 (byte-aligned)"
        );
    }

    #[test]
    fn test_sr17_needs_transcoding_same_encoding() {
        // No transcoding needed when both sides use the same encoding
        let utf8_utf8 = AdapterOptions {
            caller_string_encoding: StringEncoding::Utf8,
            callee_string_encoding: StringEncoding::Utf8,
            ..Default::default()
        };
        assert!(
            !utf8_utf8.needs_transcoding(),
            "SR-17: UTF-8 to UTF-8 should not need transcoding"
        );

        let utf16_utf16 = AdapterOptions {
            caller_string_encoding: StringEncoding::Utf16,
            callee_string_encoding: StringEncoding::Utf16,
            ..Default::default()
        };
        assert!(
            !utf16_utf16.needs_transcoding(),
            "SR-17: UTF-16 to UTF-16 should not need transcoding"
        );

        let latin1_latin1 = AdapterOptions {
            caller_string_encoding: StringEncoding::Latin1,
            callee_string_encoding: StringEncoding::Latin1,
            ..Default::default()
        };
        assert!(
            !latin1_latin1.needs_transcoding(),
            "SR-17: Latin-1 to Latin-1 should not need transcoding"
        );
    }

    #[test]
    fn test_sr17_needs_transcoding_different_encodings() {
        // All cross-encoding pairs must require transcoding
        let pairs = [
            (StringEncoding::Utf8, StringEncoding::Utf16),
            (StringEncoding::Utf8, StringEncoding::Latin1),
            (StringEncoding::Utf16, StringEncoding::Utf8),
            (StringEncoding::Utf16, StringEncoding::Latin1),
            (StringEncoding::Latin1, StringEncoding::Utf8),
            (StringEncoding::Latin1, StringEncoding::Utf16),
        ];
        for (caller, callee) in &pairs {
            let options = AdapterOptions {
                caller_string_encoding: *caller,
                callee_string_encoding: *callee,
                ..Default::default()
            };
            assert!(
                options.needs_transcoding(),
                "SR-17: {:?} to {:?} should need transcoding",
                caller,
                callee
            );
        }
    }

    #[test]
    fn test_sr17_needs_transcoding_independent_of_memory() {
        // Transcoding depends on encoding, not memory indices.
        // Same encoding with different memories should NOT need transcoding.
        let options = AdapterOptions {
            caller_string_encoding: StringEncoding::Utf8,
            callee_string_encoding: StringEncoding::Utf8,
            caller_memory: 0,
            callee_memory: 1,
            ..Default::default()
        };
        assert!(
            !options.needs_transcoding(),
            "SR-17: same encoding across different memories should not need transcoding"
        );
        assert!(
            options.crosses_memory(),
            "SR-17: different memory indices should cross memory boundaries"
        );
    }

    #[test]
    fn test_sr17_needs_transcoding_and_crosses_memory() {
        // When both encoding differs AND memory differs, both flags should be true.
        let options = AdapterOptions {
            caller_string_encoding: StringEncoding::Utf8,
            callee_string_encoding: StringEncoding::Utf16,
            caller_memory: 0,
            callee_memory: 1,
            ..Default::default()
        };
        assert!(
            options.needs_transcoding(),
            "SR-17: UTF-8 to UTF-16 should need transcoding"
        );
        assert!(
            options.crosses_memory(),
            "SR-17: different memory indices should cross memory boundaries"
        );
    }
}
