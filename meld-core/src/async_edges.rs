//! ADR-10 step 3: async-lower calls between fused components.
//!
//! meld owns the data plane: for each [`AsyncEdge`] the resolver found, it
//! keeps the caller's `[async-lower]` core import under its producer name,
//! generates a start adapter and a return adapter, exports them together with
//! the callee's `[callback]` under per-edge names, and describes the edge in
//! the `pulseengine:async-edges` custom section. The runtime (kiln-async) owns
//! control: it resolves the caller's import to the edge through the section,
//! runs the subtask, re-enters the callback, and routes the callee's
//! `[task-return]` to the edge's return adapter.
//!
//! The byte layout is the seam agreed with kiln on meld#548
//! (seam `meld-kiln/async-edges`, decided 2026-11-25):
//!
//! ```text
//! version            uleb32 = 1
//! max_edges          uleb32 = edge_count
//! max_subtasks       uleb32 > 0   per instance
//! max_waitable_sets  uleb32 > 0   per instance
//! max_events_per_set uleb32 > 0
//! edge_count         uleb32
//! edge[i]:
//!   caller           uleb32   component index (the import map's `component`)
//!   import_module    name     exact emitted module
//!   import_field     name     exact emitted field, including any `$N`
//!   callee           uleb32   component index
//!   start            name     export name of the start adapter
//!   callback         name     export name of the callee's `[callback]`
//!   return           name     export name of the return adapter
//!   param_kind       u8       0 = flat params, 1 = params pointer
//!   param_count      uleb32   core params of the start adapter
//!   retptr           u8       0 = none, 1 = last param of the caller import
//!   result_count     uleb32
//!   result_types     u8[result_count]   core valtype bytes
//! type_count         uleb32 = 0       (stream/future types: ADR-10 step 6)
//! ```
//!
//! A name is a uleb32 byte length followed by UTF-8.
//!
//! An edge carries primitives, UTF-8 strings and lists of primitives, at most
//! four flat parameter values (so both sides pass them flat) and at most one
//! result. A string or list is copied: the start adapter allocates in the
//! callee's memory with the callee's realloc and copies the bytes there; the
//! return adapter allocates in the caller's memory with the caller's realloc,
//! copies, and writes `(ptr, len)` at retptr. The resolver refuses every other
//! signature (`Resolver::extract_async_edges`).

use crate::merger::{self, MergedExport, MergedFunction, MergedModule, SyntheticKind};
use crate::parser::{ParsedComponent, PrimitiveValType};
use crate::resolver::{AsyncEdge, DependencyGraph, EdgeValue};
use crate::{Error, Result};
use wasm_encoder::{Function, Instruction, MemArg, ValType};

/// The custom section's name.
pub const SECTION_NAME: &str = "pulseengine:async-edges";

/// The section format version this meld writes.
pub const VERSION: u32 = 1;

/// Prefix of every per-edge export name.
pub const EXPORT_PREFIX: &str = "pulseengine:async-edge/";

/// Capacities written into the section header. kiln-async and gale use
/// fixed-capacity tables sized from these and never raise them, so each must
/// be non-zero.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AsyncBounds {
    /// Concurrent subtasks per instance.
    pub subtasks: u32,
    /// Waitable sets per instance.
    pub waitable_sets: u32,
    /// Queued events per waitable set.
    pub events_per_set: u32,
}

impl Default for AsyncBounds {
    fn default() -> Self {
        // 8 = gale's `MAX_TASKS`.
        Self {
            subtasks: 8,
            waitable_sets: 4,
            events_per_set: 16,
        }
    }
}

/// One emitted edge, as the section records it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EdgeRecord {
    pub caller: usize,
    pub import_module: String,
    pub import_field: String,
    pub callee: usize,
    pub start: String,
    pub callback: String,
    pub ret: String,
    /// Core params of the start adapter (always flat in increment 1).
    pub param_count: u32,
    pub retptr: bool,
    pub results: Vec<ValType>,
    /// Merged function indices of the three exports, in the order start,
    /// callback, return.
    funcs: [u32; 3],
}

/// The edges of one fusion. Functions are added by [`emit_adapters`]; the
/// exports by [`AsyncEdgePlan::push_exports`], after `--exports world`
/// pruning; the section bytes by [`AsyncEdgePlan::section_bytes`].
#[derive(Debug, Clone, Default)]
pub struct AsyncEdgePlan {
    pub edges: Vec<EdgeRecord>,
    pub bounds: AsyncBounds,
}

fn flat(p: PrimitiveValType) -> ValType {
    match p {
        PrimitiveValType::S64 | PrimitiveValType::U64 => ValType::I64,
        PrimitiveValType::F32 => ValType::F32,
        PrimitiveValType::F64 => ValType::F64,
        _ => ValType::I32,
    }
}

/// The store that writes primitive `p` at its Canonical ABI size.
fn store(p: PrimitiveValType, memory_index: u32) -> Instruction<'static> {
    let arg = |align| MemArg {
        offset: 0,
        align,
        target: wasm_encoder::MemArgTarget::Memory(memory_index),
        ordering: None,
    };
    match p {
        PrimitiveValType::Bool | PrimitiveValType::S8 | PrimitiveValType::U8 => {
            Instruction::I32Store8(arg(0))
        }
        PrimitiveValType::S16 | PrimitiveValType::U16 => Instruction::I32Store16(arg(1)),
        PrimitiveValType::S32 | PrimitiveValType::U32 | PrimitiveValType::Char => {
            Instruction::I32Store(arg(2))
        }
        PrimitiveValType::S64 | PrimitiveValType::U64 => Instruction::I64Store(arg(3)),
        PrimitiveValType::F32 => Instruction::F32Store(arg(2)),
        PrimitiveValType::F64 => Instruction::F64Store(arg(3)),
    }
}

/// Add each edge's start and return adapter to `merged.functions`.
///
/// Must run after every pass that adds imports (the P3 intrinsic lowering)
/// and before adapter generation, which places adapters after
/// `merged.functions`.
pub fn emit_adapters(
    merged: &mut MergedModule,
    components: &[ParsedComponent],
    graph: &DependencyGraph,
    bounds: AsyncBounds,
) -> Result<AsyncEdgePlan> {
    let mut plan = AsyncEdgePlan {
        edges: Vec::new(),
        bounds,
    };
    if graph.async_edges.is_empty() {
        return Ok(plan);
    }
    for (name, v) in [
        ("--async-subtasks", bounds.subtasks),
        ("--async-waitable-sets", bounds.waitable_sets),
        ("--async-events", bounds.events_per_set),
    ] {
        if v == 0 {
            return Err(Error::UnsupportedFeature(format!(
                "{name} is 0; the runtime sizes fixed tables from it and refuses 0 \
                 (ADR-10 step 3, #548)"
            )));
        }
    }
    let func_imports: Vec<(String, String, Option<usize>, u32)> = merged
        .imports
        .iter()
        .filter_map(|i| match i.entity_type {
            wasm_encoder::EntityType::Function(t) => {
                Some((i.module.clone(), i.name.clone(), i.component_idx, t))
            }
            _ => None,
        })
        .collect();
    for (n, edge) in graph.async_edges.iter().enumerate() {
        plan.edges
            .push(emit_one(merged, components, edge, n, &func_imports)?);
    }
    Ok(plan)
}

fn emit_one(
    merged: &mut MergedModule,
    components: &[ParsedComponent],
    edge: &AsyncEdge,
    n: usize,
    func_imports: &[(String, String, Option<usize>, u32)],
) -> Result<EdgeRecord> {
    let site = &edge.site;
    let caller = site.from_component;
    let refuse = |why: String| {
        Error::UnsupportedFeature(format!(
            "async edge {n} (component {caller} `{}` -> component {} `{}`): {why} \
             (ADR-10 step 3, #548)",
            site.import_name, site.to_component, site.export_name
        ))
    };
    // The emitted import that carries the caller's lowering.
    let key = (caller, edge.lower_core_func);
    let slot = merged
        .import_lower_sites
        .iter()
        .position(|s| s.sites.contains(&key))
        .ok_or_else(|| refuse("the caller's import was not emitted".into()))?;
    if merged.import_lower_sites[slot]
        .sites
        .iter()
        .any(|s| *s != key)
    {
        return Err(refuse(
            "the caller's import was merged with another lowering, so the edge table could \
             not name it alone"
                .into(),
        ));
    }
    let (import_module, import_field, import_comp, import_ty) = func_imports
        .get(slot)
        .cloned()
        .ok_or_else(|| refuse("the caller's import position is out of range".into()))?;
    if import_comp != Some(caller) {
        return Err(refuse(
            "the caller's import belongs to another component".into(),
        ));
    }

    // Core signatures.
    let params: Vec<ValType> = edge.params.iter().flat_map(|v| flat_of(*v)).collect();
    let retptr = edge.result.is_some();
    let mut import_params = params.clone();
    if retptr {
        import_params.push(ValType::I32);
    }
    let import_type = merged
        .types
        .get(import_ty as usize)
        .ok_or_else(|| refuse("the caller's import type is out of range".into()))?;
    if import_type.params != import_params || import_type.results != [ValType::I32] {
        return Err(refuse(format!(
            "the caller's core import has type {:?} -> {:?}, not the async-lower \
             signature {:?} -> [I32] meld derived from the function type",
            import_type.params, import_type.results, import_params
        )));
    }

    let lookup = |m: usize, f: u32, what: &str| {
        merged
            .function_index_map
            .get(&(site.to_component, m, f))
            .copied()
            .ok_or_else(|| refuse(format!("the callee's {what} was not merged")))
    };
    let lift = lookup(
        site.to_module,
        site.export_func_idx,
        "[async-lift] function",
    )?;
    let callback = lookup(edge.callback.0, edge.callback.1, "[callback] function")?;

    // The memories and allocators a copy needs, resolved only when one is.
    let is_bytes = |v: &EdgeValue| matches!(v, EdgeValue::Bytes { .. });
    let params_copy = edge.params.iter().any(is_bytes);
    let result_copy = edge.result.as_ref().is_some_and(is_bytes);
    let lower = crate::resolver::core_lower_options(&components[caller])
        .get(&edge.lower_core_func)
        .cloned()
        .ok_or_else(|| refuse("the caller's lowering options were not found".into()))?;
    let caller_mem = if params_copy || retptr {
        let mem = lower.memory.ok_or_else(|| {
            refuse("the caller's async lowering passes pointers but names no memory".into())
        })?;
        Some(
            crate::component_wrap::resolve_source_memory(
                &components[caller],
                components,
                merged,
                merged.memories.len(),
                mem,
            )
            .map_err(|e| refuse(e.to_string()))?,
        )
    } else {
        None
    };
    let callee_mem = if params_copy || result_copy {
        let mem = edge.callee_memory.ok_or_else(|| {
            refuse("the callee's lift passes a string or list but names no memory".into())
        })?;
        Some(
            crate::component_wrap::resolve_source_memory(
                &components[site.to_component],
                components,
                merged,
                merged.memories.len(),
                mem,
            )
            .map_err(|e| refuse(e.to_string()))?,
        )
    } else {
        None
    };
    let realloc = |owner: usize, idx: Option<u32>, who: &str| -> Result<u32> {
        let idx = idx.ok_or_else(|| {
            refuse(format!(
                "a string or list is copied into the {who}, whose options name no realloc"
            ))
        })?;
        crate::component_wrap::resolve_source_realloc(&components[owner], owner, merged, idx)
            .map_err(|e| refuse(e.to_string()))
    };
    let callee_realloc = if params_copy {
        Some(realloc(site.to_component, edge.callee_realloc, "callee")?)
    } else {
        None
    };
    let caller_realloc = if result_copy {
        Some(realloc(caller, lower.realloc, "caller")?)
    } else {
        None
    };

    // Start adapter: params (strings and lists copied into the callee's
    // memory with the callee's realloc) -> [async-lift] -> the packed i32,
    // unchanged.
    let start_ty = merger::Merger::find_or_add_type(&mut merged.types, &params, &[ValType::I32]);
    let n_copies = edge.params.iter().filter(|v| is_bytes(v)).count() as u32;
    let mut start = Function::new([(n_copies, ValType::I32)]);
    let mut slot = 0u32;
    let mut scratch = params.len() as u32;
    let mut args: Vec<u32> = Vec::new();
    for v in &edge.params {
        match *v {
            EdgeValue::Prim(_) => {
                args.push(slot);
                slot += 1;
            }
            EdgeValue::Bytes { elem_size, align } => {
                let (ptr, len, new) = (slot, slot + 1, scratch);
                emit_copy(
                    &mut start,
                    Copy {
                        src_ptr: ptr,
                        len,
                        dst: new,
                        elem_size,
                        align,
                        realloc: callee_realloc.expect("resolved for params_copy"),
                        src_mem: caller_mem.expect("resolved for params_copy"),
                        dst_mem: callee_mem.expect("resolved for params_copy"),
                    },
                );
                args.push(new);
                args.push(len);
                slot += 2;
                scratch += 1;
            }
        }
    }
    for a in args {
        start.instruction(&Instruction::LocalGet(a));
    }
    start.instruction(&Instruction::Call(lift));
    start.instruction(&Instruction::End);
    let start_idx = merged.import_counts.func + merged.functions.len() as u32;
    merged.functions.push(MergedFunction {
        type_idx: start_ty,
        body: start,
        origin: (site.to_component, site.to_module, u32::MAX),
        synthetic_kind: Some(SyntheticKind::AsyncEdgeAdapter),
    });

    // Return adapter: (retptr, flat results...) -> (), storing into the
    // caller's memory at retptr (a string or list first copied into the
    // caller's memory with the caller's realloc).
    let results: Vec<ValType> = edge.result.into_iter().flat_map(flat_of).collect();
    let mut ret_params = vec![ValType::I32];
    ret_params.extend(results.iter().copied());
    let ret_ty = merger::Merger::find_or_add_type(&mut merged.types, &ret_params, &[]);
    let mut ret = Function::new([(u32::from(result_copy), ValType::I32)]);
    match edge.result {
        None => {}
        Some(EdgeValue::Prim(p)) => {
            let memory = caller_mem.expect("resolved for retptr");
            ret.instruction(&Instruction::LocalGet(0));
            ret.instruction(&Instruction::LocalGet(1));
            ret.instruction(&store(p, memory));
        }
        Some(EdgeValue::Bytes { elem_size, align }) => {
            let memory = caller_mem.expect("resolved for retptr");
            // locals: 0 retptr, 1 ptr, 2 len, 3 new ptr
            emit_copy(
                &mut ret,
                Copy {
                    src_ptr: 1,
                    len: 2,
                    dst: 3,
                    elem_size,
                    align,
                    realloc: caller_realloc.expect("resolved for result_copy"),
                    src_mem: callee_mem.expect("resolved for result_copy"),
                    dst_mem: memory,
                },
            );
            let at = |offset| MemArg {
                offset,
                align: 2,
                target: wasm_encoder::MemArgTarget::Memory(memory),
                ordering: None,
            };
            ret.instruction(&Instruction::LocalGet(0));
            ret.instruction(&Instruction::LocalGet(3));
            ret.instruction(&Instruction::I32Store(at(0)));
            ret.instruction(&Instruction::LocalGet(0));
            ret.instruction(&Instruction::LocalGet(2));
            ret.instruction(&Instruction::I32Store(at(4)));
        }
    }
    ret.instruction(&Instruction::End);
    let ret_idx = merged.import_counts.func + merged.functions.len() as u32;
    merged.functions.push(MergedFunction {
        type_idx: ret_ty,
        body: ret,
        origin: (caller, site.from_module, u32::MAX),
        synthetic_kind: Some(SyntheticKind::AsyncEdgeAdapter),
    });

    Ok(EdgeRecord {
        caller,
        import_module,
        import_field,
        callee: site.to_component,
        start: format!("{EXPORT_PREFIX}{n}/start"),
        callback: format!("{EXPORT_PREFIX}{n}/callback"),
        ret: format!("{EXPORT_PREFIX}{n}/return"),
        param_count: params.len() as u32,
        retptr,
        results,
        funcs: [start_idx, callback, ret_idx],
    })
}

/// The flat core values of an edge value.
fn flat_of(v: EdgeValue) -> Vec<ValType> {
    match v {
        EdgeValue::Prim(p) => vec![flat(p)],
        EdgeValue::Bytes { .. } => vec![ValType::I32, ValType::I32],
    }
}

/// One `(ptr, len)` copy between memories: locals and fused indices.
struct Copy {
    src_ptr: u32,
    len: u32,
    /// Local that receives the new pointer.
    dst: u32,
    elem_size: u32,
    align: u32,
    realloc: u32,
    src_mem: u32,
    dst_mem: u32,
}

/// Allocate `len * elem_size` bytes with `realloc` in the destination
/// memory, copy them from the source memory, and leave the new pointer in
/// `c.dst`. Traps when the byte length overflows u32, as the Canonical ABI
/// does.
fn emit_copy(f: &mut Function, c: Copy) {
    if c.elem_size > 1 {
        f.instruction(&Instruction::LocalGet(c.len));
        f.instruction(&Instruction::I32Const((u32::MAX / c.elem_size) as i32));
        f.instruction(&Instruction::I32GtU);
        f.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        f.instruction(&Instruction::Unreachable);
        f.instruction(&Instruction::End);
    }
    let byte_len = |f: &mut Function| {
        f.instruction(&Instruction::LocalGet(c.len));
        if c.elem_size > 1 {
            f.instruction(&Instruction::I32Const(c.elem_size as i32));
            f.instruction(&Instruction::I32Mul);
        }
    };
    f.instruction(&Instruction::I32Const(0));
    f.instruction(&Instruction::I32Const(0));
    f.instruction(&Instruction::I32Const(c.align as i32));
    byte_len(f);
    f.instruction(&Instruction::Call(c.realloc));
    f.instruction(&Instruction::LocalSet(c.dst));
    f.instruction(&Instruction::LocalGet(c.dst));
    f.instruction(&Instruction::LocalGet(c.src_ptr));
    byte_len(f);
    f.instruction(&Instruction::MemoryCopy {
        src_mem: c.src_mem,
        dst_mem: c.dst_mem,
    });
}

impl AsyncEdgePlan {
    /// Export each edge's start adapter, callback and return adapter.
    pub fn push_exports(&self, merged: &mut MergedModule) -> Result<()> {
        for e in &self.edges {
            for (name, index) in [&e.start, &e.callback, &e.ret].into_iter().zip(e.funcs) {
                if merged.exports.iter().any(|x| &x.name == name) {
                    return Err(Error::ConflictingExports { name: name.clone() });
                }
                merged.exports.push(MergedExport {
                    name: name.clone(),
                    kind: wasm_encoder::ExportKind::Func,
                    index,
                });
            }
        }
        Ok(())
    }

    /// The `pulseengine:async-edges` payload; `None` when there are no edges.
    pub fn section_bytes(&self) -> Option<Vec<u8>> {
        if self.edges.is_empty() {
            return None;
        }
        let mut out = Vec::new();
        uleb(&mut out, VERSION);
        uleb(&mut out, self.edges.len() as u32);
        uleb(&mut out, self.bounds.subtasks);
        uleb(&mut out, self.bounds.waitable_sets);
        uleb(&mut out, self.bounds.events_per_set);
        uleb(&mut out, self.edges.len() as u32);
        for e in &self.edges {
            uleb(&mut out, e.caller as u32);
            name(&mut out, &e.import_module);
            name(&mut out, &e.import_field);
            uleb(&mut out, e.callee as u32);
            name(&mut out, &e.start);
            name(&mut out, &e.callback);
            name(&mut out, &e.ret);
            out.push(0); // param_kind: flat
            uleb(&mut out, e.param_count);
            out.push(u8::from(e.retptr));
            uleb(&mut out, e.results.len() as u32);
            for r in &e.results {
                out.push(valtype_byte(*r));
            }
        }
        uleb(&mut out, 0); // type_count
        Some(out)
    }
}

fn valtype_byte(v: ValType) -> u8 {
    match v {
        ValType::I32 => 0x7f,
        ValType::I64 => 0x7e,
        ValType::F32 => 0x7d,
        ValType::F64 => 0x7c,
        // Edge values flatten to the four numeric types only.
        other => unreachable!("async edge result type {other:?}"),
    }
}

fn uleb(out: &mut Vec<u8>, mut v: u32) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

fn name(out: &mut Vec<u8>, s: &str) {
    uleb(out, s.len() as u32);
    out.extend_from_slice(s.as_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uleb_matches_the_wasm_encoding() {
        for (v, bytes) in [
            (0u32, vec![0x00]),
            (127, vec![0x7f]),
            (128, vec![0x80, 0x01]),
            (624_485, vec![0xe5, 0x8e, 0x26]),
        ] {
            let mut out = Vec::new();
            uleb(&mut out, v);
            assert_eq!(out, bytes, "{v}");
        }
    }

    #[test]
    fn no_edges_means_no_section() {
        assert_eq!(AsyncEdgePlan::default().section_bytes(), None);
    }
}
