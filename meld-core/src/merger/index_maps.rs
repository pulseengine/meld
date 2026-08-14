//! Per-module index-map construction, init-expression folding, type/ref
//! remapping, and function-body extraction helpers extracted from the merger.

use super::*;

/// Decompose a component-level core function index into (module_idx, module_local_func_idx).
///
/// The component-level core function index space is formed by concatenating
/// each core module's function space (imports + defined functions) in module
/// order. This function finds which module the given index falls in and
/// returns the module index and the module-local function index.
///
/// Returns `None` if `core_func_idx` exceeds the total number of functions
/// across all modules (it may refer to a core function created by `canon lower`
/// or an alias, which lives outside any module's function space).
pub(crate) fn decompose_component_core_func_index(
    component: &ParsedComponent,
    core_func_idx: u32,
) -> Option<(usize, u32)> {
    let mut running: u32 = 0;
    for (mod_idx, module) in component.core_modules.iter().enumerate() {
        let import_func_count = module
            .imports
            .iter()
            .filter(|i| matches!(i.kind, ImportKind::Function(_)))
            .count() as u32;
        let module_func_count = import_func_count + module.functions.len() as u32;
        if core_func_idx < running.saturating_add(module_func_count) {
            return Some((mod_idx, core_func_idx - running));
        }
        running = running.saturating_add(module_func_count);
    }
    None
}

/// Remap a concrete heap-type index embedded in a `RefType` through the
/// per-module type index map, so it points at the correct merged type.
///
/// Concrete indices on `RefType`s produced by the parser are *module-level*
/// (see `parser.rs::convert_ref_type`). When the merger renumbers types it
/// records `(comp_idx, mod_idx, old_idx) -> merged_idx` in
/// `merged.type_index_map` (built at the top of `merge_module`). This applies
/// that same mapping. Abstract heap types carry no index and are returned
/// unchanged.
///
/// This mirrors the concrete-heap-type remap already done for `ref.null` const
/// expressions (the `RefNull` arm in `convert_const_expr`); that path remaps
/// indices in *const-expression operands*, whereas this remaps the indices in
/// *type/table/global section declarations*. The two cover disjoint structures,
/// so applying this does not double-remap anything that path already handles.
fn remap_concrete_ref_type(
    rt: RefType,
    comp_idx: usize,
    mod_idx: usize,
    merged: &MergedModule,
) -> RefType {
    let heap_type = match rt.heap_type {
        wasm_encoder::HeapType::Concrete(old_idx) => {
            let new_idx = merged
                .type_index_map
                .get(&(comp_idx, mod_idx, old_idx))
                .copied()
                .unwrap_or(old_idx);
            wasm_encoder::HeapType::Concrete(new_idx)
        }
        other => other,
    };
    RefType { heap_type, ..rt }
}

/// Remap a concrete heap-type index embedded in a `ValType` (no-op for
/// non-reference value types). Used for func-signature params/results and
/// global content types. See [`remap_concrete_ref_type`].
pub(crate) fn remap_concrete_val_type(
    ty: ValType,
    comp_idx: usize,
    mod_idx: usize,
    merged: &MergedModule,
) -> ValType {
    match ty {
        ValType::Ref(rt) => ValType::Ref(remap_concrete_ref_type(rt, comp_idx, mod_idx, merged)),
        other => other,
    }
}

/// Convert parser TableType to encoder TableType.
///
/// `element_type` may be a concrete typed-ref (`(ref null $t)`); its
/// module-level type index is remapped to the merged-module index via
/// [`remap_concrete_ref_type`].
pub(crate) fn convert_table_type(
    table: &TableType,
    comp_idx: usize,
    mod_idx: usize,
    merged: &MergedModule,
) -> EncoderTableType {
    EncoderTableType {
        element_type: match table.element_type {
            ValType::Ref(rt) => remap_concrete_ref_type(rt, comp_idx, mod_idx, merged),
            _ => RefType::FUNCREF,
        },
        table64: false,
        minimum: table.initial,
        maximum: table.maximum,
        shared: false,
    }
}

/// Convert parser GlobalType to encoder GlobalType.
///
/// `content_type` may be a concrete typed-ref; its module-level type index is
/// remapped to the merged-module index via [`remap_concrete_val_type`].
pub(crate) fn convert_global_type(
    global: &GlobalType,
    comp_idx: usize,
    mod_idx: usize,
    merged: &MergedModule,
) -> EncoderGlobalType {
    EncoderGlobalType {
        val_type: remap_concrete_val_type(global.content_type, comp_idx, mod_idx, merged),
        mutable: global.mutable,
        shared: false,
    }
}

/// Build IndexMaps for a module from the merger's index maps
///
/// This creates a local view of index remappings for a specific module,
/// which is used when rewriting function bodies.
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_index_maps_for_module(
    comp_idx: usize,
    mod_idx: usize,
    module: &CoreModule,
    merged: &MergedModule,
    memory_strategy: MemoryStrategy,
    address_rebasing: bool,
    memory_base_offset: u64,
    memory64: bool,
    memory_initial_pages: Option<u64>,
    data_segment_base: u32,
    elem_segment_base: u32,
    code_addr_relocs: Option<std::collections::HashSet<u32>>,
) -> IndexMaps {
    let mut maps = IndexMaps::new();
    maps.address_rebasing = address_rebasing;
    maps.memory_base_offset = memory_base_offset;
    maps.memory64 = memory64;
    maps.memory_initial_pages = memory_initial_pages;
    maps.code_addr_relocs = code_addr_relocs;

    // Build function map (including imported functions)
    let import_func_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Function(_)))
        .count() as u32;

    // Map imported functions (they're resolved elsewhere, map to self for now)
    for i in 0..import_func_count {
        if let Some(&new_idx) = merged.function_index_map.get(&(comp_idx, mod_idx, i)) {
            maps.functions.insert(i, new_idx);
        }
    }

    // Map defined functions
    for old_idx in 0..module.functions.len() as u32 {
        let full_idx = import_func_count + old_idx;
        if let Some(&new_idx) = merged
            .function_index_map
            .get(&(comp_idx, mod_idx, full_idx))
        {
            maps.functions.insert(full_idx, new_idx);
        }
    }

    // Build type map
    for old_idx in 0..module.types.len() as u32 {
        if let Some(&new_idx) = merged.type_index_map.get(&(comp_idx, mod_idx, old_idx)) {
            maps.types.insert(old_idx, new_idx);
        }
    }

    // Build global map (including imported globals)
    let import_global_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Global(_)))
        .count() as u32;

    // Map imported globals (they may be resolved via module_resolutions)
    for i in 0..import_global_count {
        if let Some(&new_idx) = merged.global_index_map.get(&(comp_idx, mod_idx, i)) {
            maps.globals.insert(i, new_idx);
        }
    }

    // Map defined globals
    for old_idx in 0..module.globals.len() as u32 {
        let full_idx = import_global_count + old_idx;
        if let Some(&new_idx) = merged.global_index_map.get(&(comp_idx, mod_idx, full_idx)) {
            maps.globals.insert(full_idx, new_idx);
        }
    }

    // Build table map (including imported tables)
    let import_table_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Table(_)))
        .count() as u32;

    // Map imported tables (they may be resolved via module_resolutions)
    for i in 0..import_table_count {
        if let Some(&new_idx) = merged.table_index_map.get(&(comp_idx, mod_idx, i)) {
            maps.tables.insert(i, new_idx);
        }
    }

    // Map defined tables
    for old_idx in 0..module.tables.len() as u32 {
        let full_idx = import_table_count + old_idx;
        if let Some(&new_idx) = merged.table_index_map.get(&(comp_idx, mod_idx, full_idx)) {
            maps.tables.insert(full_idx, new_idx);
        }
    }

    // Build memory map
    let import_mem_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Memory(_)))
        .count() as u32;

    let total_memories = import_mem_count + module.memories.len() as u32;
    if memory_strategy == MemoryStrategy::SharedMemory {
        for idx in 0..total_memories {
            maps.memories.insert(idx, 0);
        }
    } else {
        // Multi-memory: map both imported and defined memory indices
        for idx in 0..import_mem_count {
            if let Some(&new_idx) = merged.memory_index_map.get(&(comp_idx, mod_idx, idx)) {
                maps.memories.insert(idx, new_idx);
            }
        }
        for old_idx in 0..module.memories.len() as u32 {
            let full_idx = import_mem_count + old_idx;
            if let Some(&new_idx) = merged.memory_index_map.get(&(comp_idx, mod_idx, full_idx)) {
                maps.memories.insert(full_idx, new_idx);
            }
        }
    }

    // Build data-segment and element-segment maps.
    //
    // The merger concatenates every module's segments into one shared
    // section in deterministic merge order, so this module's local segment
    // `local` lands at fused ordinal `base + local`, where `base` is the
    // number of segments contributed by all PRIOR modules. The caller
    // supplies that base (captured from `merged.data_segments.len()` /
    // `merged.elements.len()` BEFORE this module's segments are appended —
    // the same timing as `func_offset = merged.functions.len()`).
    //
    // Data/element segments are never imported in core wasm, so there is
    // no import-count adjustment as there is for funcs/globals/tables/mems.
    let data_segment_count = crate::segments::count_data_segments(module);
    for local in 0..data_segment_count {
        maps.data_segments.insert(local, data_segment_base + local);
    }
    let elem_segment_count = crate::segments::count_element_segments(module);
    for local in 0..elem_segment_count {
        maps.elements.insert(local, elem_segment_base + local);
    }

    maps
}

/// Create a default global initializer expression
pub(crate) fn create_global_init(val_type: &ValType) -> ConstExpr {
    match val_type {
        ValType::I32 => ConstExpr::i32_const(0),
        ValType::I64 => ConstExpr::i64_const(0),
        ValType::F32 => ConstExpr::f32_const(0.0_f32.into()),
        ValType::F64 => ConstExpr::f64_const(0.0_f64.into()),
        ValType::V128 => ConstExpr::v128_const(0),
        ValType::Ref(rt) => ConstExpr::ref_null(rt.heap_type),
    }
}

/// #339: fold a **defined-base** extended-const global initializer to a concrete
/// `i32.const`.
///
/// After fusion an imported `__memory_base`-style base becomes a DEFINED global.
/// A global INITIALIZER const-expr may only `global.get` an *imported* global, so
/// re-emitting a `global.get` of the now-defined base is rejected by wasmtime
/// ("constant expression required: global.get of locally defined global"). When
/// the (already index-remapped) sequence begins with a `global.get` of a global
/// whose init folds to a constant i32 (recorded in `defined_global_i32_const`),
/// evaluate `base ± N` and emit a single `i32.const`. This mirrors the #353
/// data/element-offset fold in `segments::ParsedConstExpr::reindex`, and it is
/// exactly the address rebase #339 asks for: the initializer holds `base + N`,
/// the module's own placed address, not a stale un-rebased value.
///
/// Returns `None` (leave the sequence verbatim) unless the LEADING op is a
/// `global.get` of a defined constant — an imported base (absent from the map)
/// stays a runtime-dependent `global.get` (#338), preserving the multi-memory
/// contract where the base is bound at instantiation.
fn fold_defined_base_init(
    seq: &[crate::segments::ExtConstOp],
    merged: &MergedModule,
) -> Option<ConstExpr> {
    if let Some(crate::segments::ExtConstOp::GlobalGet(g)) = seq.first()
        && let Some(&base) = merged.defined_global_i32_const.get(g)
        && let Some(folded) = crate::segments::eval_ext_const_i32_with_base(seq, base)
    {
        Some(ConstExpr::i32_const(folded))
    } else {
        None
    }
}

/// Convert stored init expression bytes into a `wasm_encoder::ConstExpr`,
/// remapping any global or function indices through the merged module maps.
///
/// Falls back to `create_global_init` (zeros) when `bytes` is empty (e.g. for
/// imported globals which have no initializer stored), and to raw byte emission
/// for any unrecognised operator pattern.
pub(crate) fn convert_init_expr(
    bytes: &[u8],
    comp_idx: usize,
    mod_idx: usize,
    merged: &MergedModule,
    val_type: &ValType,
) -> ConstExpr {
    if bytes.is_empty() {
        return create_global_init(val_type);
    }

    // Append the End opcode so wasmparser sees a complete const-expr
    let mut full = bytes.to_vec();
    full.push(0x0B);

    let bin_reader = wasmparser::BinaryReader::new(&full, 0);
    let parser_expr = wasmparser::ConstExpr::new(bin_reader);
    let mut ops = parser_expr.get_operators_reader();

    let op = match ops.read() {
        Ok(op) => op,
        Err(_) => return ConstExpr::raw(bytes.iter().copied()),
    };

    match op {
        // For an i32 / i64 const, the wasm 2.0 extended-const proposal
        // permits further `i32.add` / `i32.sub` / `i32.mul` (and i64
        // counterparts) before `end`. Fold them into a single value via
        // the shared helper so the merged global preserves the source's
        // semantic initializer. Prior versions of this function read
        // only the first op and silently dropped the rest, producing a
        // wrong-valued global (LS-A-11).
        wasmparser::Operator::I32Const { value } => {
            let remap = |idx: u32| {
                merged
                    .global_index_map
                    .get(&(comp_idx, mod_idx, idx))
                    .copied()
                    .unwrap_or(idx)
            };
            match crate::segments::fold_extended_const_i32(&mut ops, value) {
                Ok(crate::segments::ExtConstFold::Value(folded)) => ConstExpr::i32_const(folded),
                // Const-first with an embedded `global.get` (`N + __memory_base`):
                // preserve and remap the full sequence instead of falling back to
                // un-remapped raw bytes, which would emit the wrong global index in
                // genuine multi-module fusion (#338).
                Ok(crate::segments::ExtConstFold::Extended(seq)) => {
                    let remapped: Vec<_> = seq.iter().map(|o| o.remap_global(remap)).collect();
                    // #339: as in the `global.get`-first arm, fold a leading
                    // defined-base `base ± N` to a constant. A const-first
                    // embedded `global.get` (`N + base`) does NOT lead with the
                    // base, so `fold_defined_base_init` declines and it stays
                    // verbatim — CORRECT for an IMPORTED base (the #338
                    // multi-memory `N + __memory_base` contract, where the base
                    // is a live import). RESIDUAL (pre-existing, #339): if that
                    // embedded `global.get` is a now-DEFINED constant base
                    // (operand-swapped PIC form), emitting it verbatim yields
                    // `i32.const N; global.get <defined>; i32.add`, which
                    // wasm-tools accepts but wasmtime REJECTS ("constant
                    // expression required: global.get of locally defined
                    // global"). The leading-only fold does not cover it; not
                    // observed from wasm-ld (which emits base-first), so tracked
                    // as a residual rather than fixed here (would require
                    // generalising the fold to a non-leading single defined
                    // base). Fails loud at instantiation, never silent.
                    fold_defined_base_init(&remapped, merged)
                        .unwrap_or_else(|| crate::segments::ext_const_to_expr(&remapped))
                }
                Err(_) => ConstExpr::raw(bytes.iter().copied()),
            }
        }
        wasmparser::Operator::I64Const { value } => {
            let remap = |idx: u32| {
                merged
                    .global_index_map
                    .get(&(comp_idx, mod_idx, idx))
                    .copied()
                    .unwrap_or(idx)
            };
            match crate::segments::fold_extended_const_i64(&mut ops, value) {
                Ok(crate::segments::ExtConstFold::Value(folded)) => ConstExpr::i64_const(folded),
                Ok(crate::segments::ExtConstFold::Extended(seq)) => {
                    let remapped: Vec<_> = seq.iter().map(|o| o.remap_global(remap)).collect();
                    crate::segments::ext_const_to_expr(&remapped)
                }
                Err(_) => ConstExpr::raw(bytes.iter().copied()),
            }
        }
        wasmparser::Operator::F32Const { value } => {
            ConstExpr::f32_const(f32::from_bits(value.bits()).into())
        }
        wasmparser::Operator::F64Const { value } => {
            ConstExpr::f64_const(f64::from_bits(value.bits()).into())
        }
        wasmparser::Operator::V128Const { value } => {
            ConstExpr::v128_const(i128::from_le_bytes(*value.bytes()))
        }
        wasmparser::Operator::GlobalGet { global_index } => {
            let remap = |idx: u32| {
                merged
                    .global_index_map
                    .get(&(comp_idx, mod_idx, idx))
                    .copied()
                    .unwrap_or(idx)
            };
            // A `global.get`-first initializer may continue with extended-const
            // arithmetic (`__memory_base + N`). Its value is runtime-dependent,
            // so preserve and re-emit the COMPLETE operator sequence (global
            // indices remapped) rather than reading only the leading
            // `global.get` and dropping the trailing arithmetic (#338).
            match crate::segments::read_extended_const_global_get(&mut ops, global_index) {
                Ok(Some(seq)) => {
                    let remapped: Vec<_> = seq.iter().map(|o| o.remap_global(remap)).collect();
                    // #339: fold `base ± N` to `i32.const` when the base is a
                    // now-DEFINED constant (a fused `__memory_base`); rebases the
                    // global's address and avoids an invalid `global.get` of a
                    // defined global in a const-expr. Imported bases fold to None
                    // → preserved verbatim (#338).
                    fold_defined_base_init(&remapped, merged)
                        .unwrap_or_else(|| crate::segments::ext_const_to_expr(&remapped))
                }
                Ok(None) => {
                    // Bare `global.get`: if it names a now-DEFINED constant base,
                    // fold to that constant (a const-expr cannot `global.get` a
                    // defined global). Imported globals stay verbatim (#338).
                    let new_idx = remap(global_index);
                    match merged.defined_global_i32_const.get(&new_idx) {
                        Some(&value) => ConstExpr::i32_const(value),
                        None => ConstExpr::global_get(new_idx),
                    }
                }
                Err(_) => ConstExpr::raw(bytes.iter().copied()),
            }
        }
        wasmparser::Operator::RefFunc { function_index } => {
            let remapped = merged
                .function_index_map
                .get(&(comp_idx, mod_idx, function_index))
                .copied()
                .unwrap_or(function_index);
            ConstExpr::ref_func(remapped)
        }
        wasmparser::Operator::RefNull { hty } => {
            let heap_type = match hty {
                wasmparser::HeapType::Abstract { shared, ty } => wasm_encoder::HeapType::Abstract {
                    shared,
                    ty: convert_abstract_heap_type(ty),
                },
                wasmparser::HeapType::Concrete(idx) | wasmparser::HeapType::Exact(idx) => {
                    let old_idx = idx.as_module_index().unwrap_or(0);
                    let new_idx = merged
                        .type_index_map
                        .get(&(comp_idx, mod_idx, old_idx))
                        .copied()
                        .unwrap_or(old_idx);
                    wasm_encoder::HeapType::Concrete(new_idx)
                }
            };
            ConstExpr::ref_null(heap_type)
        }
        // Unrecognised pattern — emit the raw bytes as-is
        _ => ConstExpr::raw(bytes.iter().copied()),
    }
}

/// Extract and rewrite function body from module bytes
///
/// This function:
/// 1. Parses the code section from the module bytes
/// 2. Finds the function body at the specified index
/// 3. Rewrites all index references using the provided maps
pub(crate) fn extract_function_body(
    module: &CoreModule,
    func_idx: usize,
    param_count: u32,
    maps: &IndexMaps,
) -> Result<Function> {
    // If no code section, return an unreachable function
    let Some((start, end)) = module.code_section_range else {
        let mut func = Function::new([]);
        func.instruction(&wasm_encoder::Instruction::Unreachable);
        func.instruction(&wasm_encoder::Instruction::End);
        return Ok(func);
    };

    // Parse the code section to find the function body
    let code_bytes = &module.bytes[start..end];
    let binary_reader = wasmparser::BinaryReader::new(code_bytes, 0);
    let reader = wasmparser::CodeSectionReader::new(binary_reader)?;

    let mut current_func_idx = 0;
    for body in reader {
        let body = body?;
        if current_func_idx == func_idx {
            // Found the function - rewrite it with the index maps
            return rewrite_function_body(&body, param_count, maps);
        }
        current_func_idx += 1;
    }

    // Function not found - return unreachable
    Err(Error::IndexOutOfBounds {
        kind: "function",
        index: func_idx as u32,
        max: current_func_idx as u32,
    })
}

/// Pre-compute unresolved import counts and per-import index assignments.
/// Find the merged memory index for a component's first defined memory.
pub(crate) fn component_memory_index(merged: &MergedModule, comp_idx: usize) -> u32 {
    for (&(ci, _mi, mem_i), &merged_idx) in &merged.memory_index_map {
        if ci == comp_idx && mem_i == 0 {
            return merged_idx;
        }
    }
    0 // fallback: memory 0
}

/// Find the merged function index of a component's cabi_realloc.
///
/// Prefers module 0's realloc (the main module). If module 0 has no
/// realloc, falls back to the realloc bound to the **lowest** module
/// index for this component — chosen deterministically rather than via
/// HashMap iteration order, which would let the hasher state pick a
/// different module on every run and produce non-reproducible output
/// (LS-A-15).
pub(crate) fn component_realloc_index(merged: &MergedModule, comp_idx: usize) -> Option<u32> {
    // Prefer module 0's realloc (the main module)
    if let Some(&idx) = merged.realloc_map.get(&(comp_idx, 0)) {
        return Some(idx);
    }
    // Fallback: pick the smallest module index belonging to this component,
    // deterministically. HashMap.iter() returns entries in hash-seed
    // order, which varies per process; collect-and-sort gives reproducible
    // output and removes the multi-realloc race condition.
    let mut module_idxs: Vec<usize> = merged
        .realloc_map
        .keys()
        .filter(|(ci, _)| *ci == comp_idx)
        .map(|(_, mi)| *mi)
        .collect();
    module_idxs.sort_unstable();
    module_idxs
        .first()
        .and_then(|mi| merged.realloc_map.get(&(comp_idx, *mi)).copied())
}
