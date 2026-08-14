//! Handle-table allocation for resource types extracted from the merger.

use super::*;

impl Merger {
    /// Allocate per-component handle tables for re-exporter components.
    ///
    /// For each re-exporter, grows its memory by 1 page and places a handle
    /// table at the start of the new page. Adds a mutable global for the
    /// next-allocation pointer and generates ht_new/ht_rep/ht_drop functions.
    #[allow(dead_code)]
    pub(crate) fn allocate_handle_tables(
        graph: &DependencyGraph,
        merged: &mut MergedModule,
        opaque_resources: &[(String, String)],
    ) -> Result<()> {
        // Handle table capacity: 256 entries = 1024 bytes (fits in 1 page)
        const HT_CAPACITY: u32 = 256;
        const ENTRY_SIZE: u32 = 4; // i32

        for (comp_idx, iface, rn) in &graph.reexporter_resources {
            let comp_idx = *comp_idx;
            // Opaque-rep resources still get ht_* slots in handle_tables, but
            // the function bodies are pure identity (no memory storage):
            //   ht_new(rep)  → rep   (the rep IS the handle)
            //   ht_rep(h)    → h     (the handle IS the rep)
            //   ht_drop(h)   → ()    (no cleanup needed)
            // Path B's redirect routes [resource-*] imports through these
            // same ht_* functions whether opaque or not, so opaque imports
            // bypass wasmtime's canonical resource layer entirely (which
            // would otherwise reject cross-component handle passing for
            // per-component-typed resources).
            // Opaque-rep gets the same memory-backed ht_* as standard
            // resources — the rep storage semantics are the same (ht_new
            // allocates a fresh handle and stores the rep, ht_rep reads
            // it back). The DIFFERENCE with --opaque-rep is in the wrapper:
            // opaque resources use a separate-typed local_resource_types
            // entry so wasmtime's canonical resource layer doesn't conflate
            // them with standard Box-pattern reps.
            let _is_opaque = opaque_resources.iter().any(|(i, r)| i == iface && r == rn);

            // Find merged memory index for this component's memory 0
            let memory_idx = match merged.memory_index_map.get(&(comp_idx, 0, 0)) {
                Some(&idx) => idx,
                None => continue, // No memory — skip (shouldn't happen for real components)
            };

            // Determine table base: grow memory by 1 page, place table at start
            // of new page. Each (component, resource) gets its own page so the
            // tables don't collide.
            let mem_slot = (memory_idx - merged.import_counts.memory) as usize;
            let current_pages = if mem_slot < merged.memories.len() {
                merged.memories[mem_slot].minimum
            } else {
                continue;
            };
            let table_base_addr = (current_pages * WASM_PAGE_SIZE) as u32;

            // Grow memory by 1 page to accommodate the handle table
            merged.memories[mem_slot].minimum += 1;
            if let Some(max) = merged.memories[mem_slot].maximum {
                if max < merged.memories[mem_slot].minimum {
                    merged.memories[mem_slot].maximum = Some(merged.memories[mem_slot].minimum);
                }
            }

            // Add mutable i32 global for next-allocation pointer.
            // Start at base+4 to skip slot 0 (handle=0 means "no handle").
            let next_ptr_global = merged.import_counts.global + merged.globals.len() as u32;
            merged.globals.push(MergedGlobal {
                ty: EncoderGlobalType {
                    val_type: ValType::I32,
                    mutable: true,
                    shared: false,
                },
                init_expr: ConstExpr::i32_const((table_base_addr + ENTRY_SIZE) as i32),
            });

            // Register or reuse the function types we need:
            //   ht_new:  (i32) -> (i32)
            //   ht_rep:  (i32) -> (i32)
            //   ht_drop: (i32) -> ()
            let type_i32_to_i32 =
                Self::find_or_add_type(&mut merged.types, &[ValType::I32], &[ValType::I32]);
            let type_i32_to_void = Self::find_or_add_type(&mut merged.types, &[ValType::I32], &[]);

            let mem_arg = wasm_encoder::MemArg {
                offset: 0,
                align: 2, // 4-byte aligned
                memory_index: memory_idx,
            };

            // Generate ht_new: store rep at next_ptr, return next_ptr, advance by 4
            let new_func_idx = merged.import_counts.func + merged.functions.len() as u32;
            {
                let mut body = Function::new([(1, ValType::I32)]); // local $handle
                body.instruction(&Instruction::GlobalGet(next_ptr_global));
                body.instruction(&Instruction::LocalSet(1)); // handle = next_ptr
                body.instruction(&Instruction::LocalGet(1)); // [handle]
                body.instruction(&Instruction::LocalGet(0)); // [handle, rep]
                body.instruction(&Instruction::I32Store(mem_arg)); // mem[handle] = rep
                body.instruction(&Instruction::LocalGet(1)); // [handle]
                body.instruction(&Instruction::I32Const(ENTRY_SIZE as i32));
                body.instruction(&Instruction::I32Add);
                body.instruction(&Instruction::GlobalSet(next_ptr_global)); // next_ptr += 4
                body.instruction(&Instruction::LocalGet(1)); // return handle
                body.instruction(&Instruction::End);
                merged.functions.push(MergedFunction {
                    type_idx: type_i32_to_i32,
                    body,
                    origin: (comp_idx, 0, u32::MAX), // synthetic
                    synthetic_kind: Some(SyntheticKind::HandleTable),
                });
            }

            // Generate ht_rep: return mem[handle]
            let rep_func_idx = merged.import_counts.func + merged.functions.len() as u32;
            {
                let mut body = Function::new([]);
                body.instruction(&Instruction::LocalGet(0)); // [handle]
                body.instruction(&Instruction::I32Load(mem_arg)); // mem[handle] -> rep
                body.instruction(&Instruction::End);
                merged.functions.push(MergedFunction {
                    type_idx: type_i32_to_i32,
                    body,
                    origin: (comp_idx, 0, u32::MAX),
                    synthetic_kind: Some(SyntheticKind::HandleTable),
                });
            }

            // Find the resource's dtor function (if any) so ht_drop can
            // invoke it before zeroing the slot. wit-bindgen-rust emits
            // `<iface>#[dtor]<rn>` as a core export for each component that
            // owns a Box-backed rep.
            //
            // Match by EXACT `<iface>#[dtor]<rn>` (with optional `$N` dedup
            // suffix tolerance). A previous version used `name.contains(...)`
            // which collided when one component defines the same resource
            // name across multiple interfaces (e.g. `resource_floats` has
            // dtors for `exports#[dtor]float`, `imports#[dtor]float`, and
            // `test:resource-floats/test#[dtor]float` — the contains-match
            // picked the first regardless of iface). Exact match plus the
            // origin-comp filter selects the right dtor unambiguously.
            let exact_dtor_export = format!("{}#[dtor]{}", iface, rn);
            let exact_dtor_dollar = format!("{}#[dtor]{}$", iface, rn);
            let dtor_func_idx: Option<u32> = merged
                .exports
                .iter()
                .filter(|e| {
                    matches!(e.kind, EncoderExportKind::Func)
                        && (e.name == exact_dtor_export || e.name.starts_with(&exact_dtor_dollar))
                })
                .find_map(|e| {
                    let import_count = merged.import_counts.func;
                    if e.index < import_count {
                        return None;
                    }
                    let local_idx = (e.index - import_count) as usize;
                    let func = merged.functions.get(local_idx)?;
                    if func.origin.0 == comp_idx {
                        Some(e.index)
                    } else {
                        None
                    }
                });
            if let Some(idx) = dtor_func_idx {
                log::info!(
                    "ht_drop for {}/{} in component {} will invoke dtor func {}",
                    iface,
                    rn,
                    comp_idx,
                    idx,
                );
            }

            // Generate ht_drop: load rep, optionally call dtor(rep), zero slot.
            // Skip the dtor invocation when ht_drop is called with handle=0
            // (used as a sentinel by the canonical ABI). Using if-then to
            // avoid double-free if the same handle is dropped twice.
            //
            // For re-exporters whose ht stores foreign reps (placed there by
            // the own bridge), invoking the local dtor on a foreign rep is
            // undefined behavior — the dtor casts the rep as `*mut
            // _ThingRep<LocalT>` and Box::from_raw drops what it thinks is a
            // local box. When the foreign rep is actually a leaf-allocated
            // box, this misinterprets memory and leads to recursion through
            // the import drop chain. Suppress the dtor for re-exporter
            // components whose ht is also fed via own bridges (the standard
            // Box-pattern wit-bindgen design assumes the rep is always
            // owned by the component whose ht stores it, but Phase 1's
            // per-component-ht-for-definers broke that invariant).
            let invoke_dtor =
                dtor_func_idx.filter(|_| !graph.reexporter_components.contains(&comp_idx));
            let drop_func_idx = merged.import_counts.func + merged.functions.len() as u32;
            {
                let mut body = Function::new([]);
                body.instruction(&Instruction::LocalGet(0)); // [handle]
                body.instruction(&Instruction::I32Eqz); // [handle == 0]
                body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                body.instruction(&Instruction::Else);
                if let Some(dtor_idx) = invoke_dtor {
                    // Load the rep stored at this handle slot, then call dtor(rep).
                    body.instruction(&Instruction::LocalGet(0));
                    body.instruction(&Instruction::I32Load(mem_arg));
                    body.instruction(&Instruction::Call(dtor_idx));
                }
                // Zero the slot regardless of whether a dtor was called.
                body.instruction(&Instruction::LocalGet(0));
                body.instruction(&Instruction::I32Const(0));
                body.instruction(&Instruction::I32Store(mem_arg));
                body.instruction(&Instruction::End); // end if
                body.instruction(&Instruction::End); // end function
                merged.functions.push(MergedFunction {
                    type_idx: type_i32_to_void,
                    body,
                    origin: (comp_idx, 0, u32::MAX),
                    synthetic_kind: Some(SyntheticKind::HandleTable),
                });
            }

            merged.handle_tables.insert(
                (comp_idx, iface.clone(), rn.clone()),
                HandleTableInfo {
                    memory_idx,
                    next_ptr_global,
                    table_base_addr,
                    capacity: HT_CAPACITY,
                    new_func: new_func_idx,
                    rep_func: rep_func_idx,
                    drop_func: drop_func_idx,
                },
            );

            // Export handle table functions so the P2 wrapper can alias them.
            // Naming: $ht_new_{comp}_{iface_safe}_{rn} so multiple resources
            // per component don't collide.
            let suffix = ht_export_suffix(comp_idx, iface, rn);
            merged.exports.push(MergedExport {
                name: format!("$ht_new_{}", suffix),
                kind: EncoderExportKind::Func,
                index: new_func_idx,
            });
            merged.exports.push(MergedExport {
                name: format!("$ht_rep_{}", suffix),
                kind: EncoderExportKind::Func,
                index: rep_func_idx,
            });
            merged.exports.push(MergedExport {
                name: format!("$ht_drop_{}", suffix),
                kind: EncoderExportKind::Func,
                index: drop_func_idx,
            });

            log::info!(
                "handle table for component {} resource {}/{}: memory={}, base=0x{:x}, global={}, funcs=({},{},{})",
                comp_idx,
                iface,
                rn,
                memory_idx,
                table_base_addr,
                next_ptr_global,
                new_func_idx,
                rep_func_idx,
                drop_func_idx,
            );
        }

        Ok(())
    }
}
