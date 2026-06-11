//! # Cross-component stream-bridge emitter (#141, SR-33, ADR-3 follow-up)
//!
//! When two fused components share a `stream<T>` end-to-end (one holds the
//! writable end, the other the readable end), both sides previously lowered
//! to `pulseengine:async` **host** imports — every byte crossed the host
//! boundary twice even though both ends live in the same merged module.
//! This module emits the in-module bridge that removes the double host
//! round-trip.
//!
//! ## Design (issue #141, "shim-dispatch bridge")
//!
//! The pairing is static ([`crate::p3_stream::StreamPairGraph`]) but handle
//! identity is runtime — `stream_new` mints handles at run time. So the
//! bridge takes over the stream plane for handles minted **in-module** and
//! forwards everything else to the retained host intrinsics:
//!
//! * A **bridge memory** is appended to the merged module: a slot header
//!   table plus ring storage (layout constants below).
//! * Per component that imports any of the five stream intrinsics
//!   (`stream_new` / `stream_read` / `stream_write` /
//!   `stream_drop_readable` / `stream_drop_writable`), meld emits **shim
//!   functions** with that component's merged memory index hardwired as an
//!   instruction immediate (wasm memory indices are immediates, so the
//!   host ABI's dynamic `mem_idx` parameter cannot be honoured in-module —
//!   the caller always passes its own memory by construction). Same-memory
//!   fusion is the identical codegen with all caller-memory immediates 0.
//! * **Handle tagging**: the shim `stream_new` allocates a bridge slot and
//!   returns handles with bit 31 set ([`LOCAL_TAG`]). Host handles are
//!   assumed `< 2^31` (recorded invariant from ADR-2's small-int handle
//!   convention). Each shim dispatches on the tag: tagged → ring ops
//!   against the bridge memory; untagged → call the original host import
//!   (which stays imported as the foreign-handle fallback path).
//! * **Slot exhaustion** falls back to host `stream_new` — graceful,
//!   never an error.
//! * Call sites are **rewired**: every call to a component's
//!   `pulseengine:async` `stream_*` import is redirected to that
//!   component's shim (same body-re-rewrite mechanism as
//!   `wire_adapter_indices` in `lib.rs`).
//!
//! ## Ring protocol (single-threaded interleaved semantics)
//!
//! Per-slot header at `HEADER_BASE + slot * SLOT_HEADER_STRIDE`:
//!
//! | offset | field | meaning |
//! |---|---|---|
//! | +0 | `state: u32` | 0 free, 1 open, 2 writer-dropped, 3 fully-closed |
//! | +4 | `rd: u32` | monotonic read cursor (wrapping) |
//! | +8 | `wr: u32` | monotonic write cursor (wrapping) |
//! | +12 | reserved | — |
//!
//! Ring data for slot `s` lives at `RINGS_BASE + s * RING_CAP`. Cursors
//! are **u32 wrapping monotonic counters**: `wr - rd` is the fill level
//! and `cursor & (RING_CAP - 1)` the ring offset (`RING_CAP` is a power
//! of two), so full ([`RING_CAP`]) and empty (0) are distinguishable
//! without a spare byte.
//!
//! * **write**: `avail = RING_CAP - (wr - rd)`; `n = min(len, avail)`;
//!   two-part wrapping `memory.copy` caller-mem → bridge; `wr += n`;
//!   return `n`. `n == 0` is backpressure per ADR-2 (never an error).
//! * **read**: if `wr == rd`, return `0` iff `state == 2`
//!   (writer-dropped ⇒ EOF after drain) else `-5`
//!   ([`crate::p3_async::AbiError::Pending`] — open and empty). Otherwise
//!   `n = min(len, wr - rd)`; two-part wrapping copy bridge → caller-mem;
//!   `rd += n`; return `n`.
//! * **drop_writable** (local): `state = 2`. The reader drains remaining
//!   bytes and then observes EOF — the ADR-2 "EOF only after writer
//!   dropped AND drained" contract.
//! * **drop_readable** (local): `state = 3`. The slot is **not reused**
//!   in v0.29.0 — reclamation would require proving no live writable end
//!   remains, which the single-pass emitter does not track. With
//!   [`SLOT_COUNT`] slots exhausted, `stream_new` falls back to the host,
//!   so the failure mode is "loses the optimisation", never "loses data".
//! * **stream_new**: scan for a `state == 0` slot; none → call host
//!   `stream_new` and return its `i64` unchanged. Otherwise `state = 1`,
//!   `rd = wr = 0`, and return an `i64` whose low half (readable end) and
//!   high half (writable end) are both `slot | LOCAL_TAG` — the same slot
//!   id for both ends; the ops distinguish ends by which function is
//!   called, exactly like the host ABI.
//!
//! ## ADR-3 amendment (recorded on landing, falsification-driven)
//!
//! The original "zero-copy same-memory ring" sketch drops to "**no host
//! crossing, single copy**": the ABI's caller-buffer contract
//! (`stream_read(handle, buf_ptr, …)`) requires a copy into the caller's
//! buffer regardless; what fusion removes is the double host round-trip
//! per chunk.
//!
//! ## Pipeline placement
//!
//! [`emit_stream_bridge`] runs after merging, P3 intrinsic lowering and
//! task-return shims, but **before** FACT adapter generation/wiring:
//! adapters are encoded *after* `merged.functions`, so their merged
//! indices are `import_count + functions.len() + offset` — appending shim
//! functions after `wire_adapter_indices` had baked those indices into
//! call sites would shift every adapter call off-target. Emitting the
//! shims first keeps every later index computation correct, and the
//! shared `function_index_map` carries the rewires through the later
//! re-extractions.

use std::collections::{BTreeMap, HashMap};

use wasm_encoder::{BlockType, EntityType, Function, Instruction, MemArg, MemoryType, ValType};

use crate::merger::{MergedFuncType, MergedFunction, MergedModule, SyntheticKind};
use crate::p3_async::{self, HOST_INTRINSIC_MODULE};
use crate::p3_stream::StreamPairGraph;
use crate::parser::{ImportKind, ParsedComponent};
use crate::{MemoryStrategy, Result};

// ─── Bridge memory layout ──────────────────────────────────────────────
//
// Page 0: slot header table (SLOT_COUNT * SLOT_HEADER_STRIDE bytes used,
//         rest reserved). Page 1: ring storage, SLOT_COUNT rings of
//         RING_CAP bytes each (8 * 4096 = 32 KiB, within one 64 KiB page).
// Total: 2 pages, fixed (min == max — the bridge never grows).

/// Number of bridge stream slots. Exhaustion falls back to the host.
pub const SLOT_COUNT: u32 = 8;
/// Ring capacity in bytes per slot. MUST be a power of two (cursor
/// arithmetic uses `& (RING_CAP - 1)` masking).
pub const RING_CAP: u32 = 4096;
/// Byte offset of the slot header table in the bridge memory.
pub const HEADER_BASE: u32 = 0;
/// Bytes per slot header entry: `{state u32, rd u32, wr u32, reserved}`.
pub const SLOT_HEADER_STRIDE: u32 = 16;
/// Byte offset of the ring storage (start of page 1).
pub const RINGS_BASE: u32 = 65536;
/// Fixed size of the bridge memory in 64 KiB wasm pages.
pub const BRIDGE_MEMORY_PAGES: u64 = 2;

/// Bit 31 marks a handle as bridge-local. Host handles are `< 2^31`
/// (ADR-2 small-int handle convention), so the tag is unambiguous.
pub const LOCAL_TAG: u32 = 0x8000_0000;

/// Slot state: unallocated.
pub const STATE_FREE: i32 = 0;
/// Slot state: both ends live.
pub const STATE_OPEN: i32 = 1;
/// Slot state: writable end dropped — reader drains, then sees EOF.
pub const STATE_WRITER_DROPPED: i32 = 2;
/// Slot state: readable end dropped. Slot is retired, not reused.
pub const STATE_CLOSED: i32 = 3;

/// The five stream intrinsics the bridge takes over. Cancel ops are NOT
/// bridged: a bridged op never blocks (it returns Pending / a partial
/// count immediately), so there is never a pending op to cancel; cancel
/// calls keep routing to the host import untouched.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum StreamOp {
    /// `stream_new() -> i64`
    New,
    /// `stream_read(handle, buf_ptr, buf_len, mem_idx) -> i32`
    Read,
    /// `stream_write(handle, data_ptr, data_len, mem_idx) -> i32`
    Write,
    /// `stream_drop_readable(handle)`
    DropReadable,
    /// `stream_drop_writable(handle)`
    DropWritable,
}

impl StreamOp {
    /// Map a `pulseengine:async` import field name to the op, if it is
    /// one of the five bridged intrinsics.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            n if n == p3_async::stream::NEW => Some(Self::New),
            n if n == p3_async::stream::READ => Some(Self::Read),
            n if n == p3_async::stream::WRITE => Some(Self::Write),
            n if n == p3_async::stream::DROP_READABLE => Some(Self::DropReadable),
            n if n == p3_async::stream::DROP_WRITABLE => Some(Self::DropWritable),
            _ => None,
        }
    }
}

/// One emitted bridge shim.
#[derive(Debug, Clone)]
pub struct BridgeShim {
    /// Source component the shim belongs to (memory immediate origin).
    pub component: usize,
    /// Source core module within the component.
    pub module: usize,
    /// Which intrinsic this shim replaces at the component's call sites.
    pub op: StreamOp,
    /// Merged function index of the shim.
    pub merged_index: u32,
}

/// Result of [`emit_stream_bridge`]: what was added to the module.
#[derive(Debug, Clone, Default)]
pub struct BridgePlan {
    /// Merged memory index of the appended bridge memory.
    pub bridge_memory: u32,
    /// All emitted shims.
    pub shims: Vec<BridgeShim>,
}

/// `MemArg` against the bridge memory (i32 alignment).
fn bridge_arg(offset: u64, bridge_mem: u32) -> MemArg {
    MemArg {
        offset,
        align: 2,
        memory_index: bridge_mem,
    }
}

/// Emit the cross-component stream bridge into `merged`.
///
/// Gated by the caller on a non-empty [`StreamPairGraph`] — the
/// detection foundation (ADR-3 path N) is the authority on *whether* the
/// fused module contains a cross-component stream pairing; this emitter
/// then takes over the stream plane module-wide (every component that
/// imports a stream intrinsic gets shims, because handles minted by one
/// participant may be observed by any other).
///
/// Returns `Ok(None)` when no component actually imports any of the
/// five intrinsics (pairs detected from canonical entries alone, with
/// no core-level call surface to rewire — nothing to do).
pub fn emit_stream_bridge(
    merged: &mut MergedModule,
    components: &[ParsedComponent],
    stream_pairs: &StreamPairGraph,
    memory_strategy: MemoryStrategy,
    address_rebasing: bool,
) -> Result<Option<BridgePlan>> {
    if stream_pairs.is_empty() {
        return Ok(None);
    }

    // ── 1. Locate the host intrinsic imports in the merged module. ────
    //
    // `intrinsic_imports` maps EVERY merged function-import index that is
    // a bridged stream intrinsic to its op (the merger's dedup and the
    // lowering pass can each contribute an import of the same name);
    // `host_idx` records one canonical index per op — the shims' foreign-
    // handle fallback target.
    let mut intrinsic_imports: HashMap<u32, StreamOp> = HashMap::new();
    let mut host_idx: BTreeMap<StreamOp, u32> = BTreeMap::new();
    let mut func_import_pos = 0u32;
    for imp in &merged.imports {
        if let EntityType::Function(_) = imp.entity_type {
            if imp.module == HOST_INTRINSIC_MODULE
                && let Some(op) = StreamOp::from_name(&imp.name)
            {
                intrinsic_imports.insert(func_import_pos, op);
                host_idx.entry(op).or_insert(func_import_pos);
            }
            func_import_pos += 1;
        }
    }
    if intrinsic_imports.is_empty() {
        return Ok(None);
    }

    // ── 2. Which (component, module) calls which intrinsic? ───────────
    //
    // A module "uses" an op when one of its function-import positions is
    // mapped (via function_index_map) to an intrinsic import index. This
    // covers both direct `pulseengine:async` core imports and canonical-
    // entry imports that earlier passes pointed at the lowered imports.
    type Usage = BTreeMap<(usize, usize), BTreeMap<StreamOp, Vec<u32>>>;
    let mut usage: Usage = BTreeMap::new();
    for (c, comp) in components.iter().enumerate() {
        for (m, module) in comp.core_modules.iter().enumerate() {
            let mut pos = 0u32;
            for imp in &module.imports {
                if matches!(imp.kind, ImportKind::Function(_)) {
                    if let Some(&merged_idx) = merged.function_index_map.get(&(c, m, pos))
                        && let Some(&op) = intrinsic_imports.get(&merged_idx)
                    {
                        usage
                            .entry((c, m))
                            .or_default()
                            .entry(op)
                            .or_default()
                            .push(pos);
                    }
                    pos += 1;
                }
            }
        }
    }
    if usage.is_empty() {
        return Ok(None);
    }

    // ── 3. Append the bridge memory (fixed 2 pages, never grows). ─────
    merged.memories.push(MemoryType {
        minimum: BRIDGE_MEMORY_PAGES,
        maximum: Some(BRIDGE_MEMORY_PAGES),
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    let bridge_mem = merged.import_counts.memory + merged.memories.len() as u32 - 1;

    // ── 4. Shim function types (find-or-append, indices are stable). ──
    let type_for =
        |merged: &mut MergedModule, params: Vec<ValType>, results: Vec<ValType>| match merged
            .types
            .iter()
            .position(|t| t.params == params && t.results == results)
        {
            Some(idx) => idx as u32,
            None => {
                merged.types.push(MergedFuncType { params, results });
                merged.types.len() as u32 - 1
            }
        };
    let ty_new = type_for(merged, vec![], vec![ValType::I64]);
    let ty_rw = type_for(merged, vec![ValType::I32; 4], vec![ValType::I32]);
    let ty_drop = type_for(merged, vec![ValType::I32], vec![]);

    // ── 5. Emit one shim per (component module, used op). ─────────────
    let mut plan = BridgePlan {
        bridge_memory: bridge_mem,
        shims: Vec::new(),
    };
    let mut shim_index: HashMap<(usize, usize, StreamOp), u32> = HashMap::new();

    for (&(c, m), ops) in &usage {
        // The component's own memory, as a hardwired immediate. Local
        // memory index 0 is the module's first memory (imported or
        // defined); modules with no memory at all cannot pass buffers,
        // so 0 is a safe default for their (drop/new-only) shims.
        let caller_mem = merged
            .memory_index_map
            .get(&(c, m, 0))
            .copied()
            .unwrap_or(0);

        for &op in ops.keys() {
            let host = host_idx[&op];
            let (type_idx, body) = match op {
                StreamOp::New => (ty_new, emit_new_shim(bridge_mem, host)),
                StreamOp::Read => (ty_rw, emit_read_shim(bridge_mem, caller_mem, host)),
                StreamOp::Write => (ty_rw, emit_write_shim(bridge_mem, caller_mem, host)),
                StreamOp::DropReadable => (ty_drop, emit_drop_shim(bridge_mem, STATE_CLOSED, host)),
                StreamOp::DropWritable => (
                    ty_drop,
                    emit_drop_shim(bridge_mem, STATE_WRITER_DROPPED, host),
                ),
            };
            let merged_index = merged.import_counts.func + merged.functions.len() as u32;
            merged.functions.push(MergedFunction {
                type_idx,
                body,
                origin: (c, m, u32::MAX),
                synthetic_kind: Some(SyntheticKind::StreamBridge),
            });
            shim_index.insert((c, m, op), merged_index);
            plan.shims.push(BridgeShim {
                component: c,
                module: m,
                op,
                merged_index,
            });
        }
    }

    // ── 6. Rewire call sites: import position → shim. ─────────────────
    for (&(c, m), ops) in &usage {
        for (&op, positions) in ops {
            let shim = shim_index[&(c, m, op)];
            for &pos in positions {
                merged.function_index_map.insert((c, m, pos), shim);
            }
        }
    }

    // ── 7. Re-extract function bodies of affected modules so already-
    //       encoded `call` instructions pick up the shim indices (same
    //       mechanism as `wire_adapter_indices`). ──────────────────────
    for &(c, m) in usage.keys() {
        let module = &components[c].core_modules[m];

        let module_memory = if address_rebasing {
            crate::merger::module_memory_type(module)?
        } else {
            None
        };
        let memory64 = module_memory
            .as_ref()
            .map(|mem| mem.memory64)
            .unwrap_or(false);
        let memory_initial_pages = module_memory.as_ref().map(|mem| mem.initial);

        let index_maps = crate::merger::build_index_maps_for_module(
            c,
            m,
            module,
            merged,
            memory_strategy,
            address_rebasing,
            0, // memory_base_offset — matches wire_adapter_indices
            memory64,
            memory_initial_pages,
        );

        let import_func_count = module
            .imports
            .iter()
            .filter(|i| matches!(i.kind, ImportKind::Function(_)))
            .count() as u32;

        for (old_idx, &type_idx) in module.functions.iter().enumerate() {
            let old_func_idx = import_func_count + old_idx as u32;
            let param_count = module
                .types
                .get(type_idx as usize)
                .map(|ty| ty.params.len() as u32)
                .unwrap_or(0);

            let body =
                crate::merger::extract_function_body(module, old_idx, param_count, &index_maps)?;

            if let Some(mf) = merged
                .functions
                .iter_mut()
                .find(|f| f.origin == (c, m, old_func_idx))
            {
                mf.body = body;
            }
        }
    }

    log::info!(
        "Stream bridge (#141): memory {} ({} slots × {} B rings) + {} shim(s) across {} module(s)",
        bridge_mem,
        SLOT_COUNT,
        RING_CAP,
        plan.shims.len(),
        usage.len(),
    );

    Ok(Some(plan))
}

// ─── Shim codegen ───────────────────────────────────────────────────────
//
// Locals layout convention for read/write shims (params l0..l3 =
// handle, ptr, len, mem_idx — mem_idx is accepted for ABI compatibility
// and forwarded on the host path, but the local path uses the hardwired
// memory immediates):
//   l4 = slot, then header address  (slot * SLOT_HEADER_STRIDE)
//   l5 = ring base address          (RINGS_BASE + slot * RING_CAP)
//   l6 = rd cursor   l7 = wr cursor
//   l8 = scratch → avail/fill → n   l9 = ring offset   l10 = first-part len

/// Dispatch prologue shared by read/write/drop shims: if the handle is
/// NOT bit-31-tagged, forward all params to the host import and return
/// its results (the host call's results are exactly the shim's results).
fn emit_host_fallback(f: &mut Function, host: u32, param_count: u32) {
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I32Const(LOCAL_TAG as i32));
    f.instruction(&Instruction::I32And);
    f.instruction(&Instruction::I32Eqz);
    f.instruction(&Instruction::If(BlockType::Empty));
    for i in 0..param_count {
        f.instruction(&Instruction::LocalGet(i));
    }
    f.instruction(&Instruction::Call(host));
    f.instruction(&Instruction::Return);
    f.instruction(&Instruction::End);
}

/// Decode `l0 = handle` into `l4 = header address`, `l5 = ring base`.
fn emit_slot_decode(f: &mut Function) {
    // l4 = handle & !LOCAL_TAG  (the slot id)
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I32Const(0x7FFF_FFFF));
    f.instruction(&Instruction::I32And);
    f.instruction(&Instruction::LocalSet(4));
    // l5 = RINGS_BASE + slot * RING_CAP
    f.instruction(&Instruction::LocalGet(4));
    f.instruction(&Instruction::I32Const(RING_CAP as i32));
    f.instruction(&Instruction::I32Mul);
    f.instruction(&Instruction::I32Const(RINGS_BASE as i32));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::LocalSet(5));
    // l4 = HEADER_BASE + slot * SLOT_HEADER_STRIDE (overwrites the slot id)
    f.instruction(&Instruction::LocalGet(4));
    f.instruction(&Instruction::I32Const(SLOT_HEADER_STRIDE as i32));
    f.instruction(&Instruction::I32Mul);
    f.instruction(&Instruction::I32Const(HEADER_BASE as i32));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::LocalSet(4));
}

/// `min(a_local, b_local)` (unsigned) left on the stack via `select`.
fn emit_min_u(f: &mut Function, a: u32, b: u32) {
    f.instruction(&Instruction::LocalGet(a));
    f.instruction(&Instruction::LocalGet(b));
    f.instruction(&Instruction::LocalGet(a));
    f.instruction(&Instruction::LocalGet(b));
    f.instruction(&Instruction::I32LtU);
    f.instruction(&Instruction::Select);
}

/// `stream_new() -> i64` shim: claim a free slot (state=1, rd=wr=0) and
/// return `(slot|LOCAL_TAG)` in both i64 halves; on exhaustion fall back
/// to the host `stream_new` and return its result unchanged.
fn emit_new_shim(bridge_mem: u32, host_new: u32) -> Function {
    // locals: l0 = slot scan cursor, l1 = header address
    let mut f = Function::new([(2, ValType::I32)]);

    f.instruction(&Instruction::Block(BlockType::Empty)); // $exhausted (depth 2 from loop)
    f.instruction(&Instruction::Block(BlockType::Empty)); // $have (depth 1 from loop)
    f.instruction(&Instruction::Loop(BlockType::Empty)); // $scan (depth 0)
    // if slot >= SLOT_COUNT → exhausted
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I32Const(SLOT_COUNT as i32));
    f.instruction(&Instruction::I32GeU);
    f.instruction(&Instruction::BrIf(2));
    // if state[slot] == FREE → have
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I32Const(SLOT_HEADER_STRIDE as i32));
    f.instruction(&Instruction::I32Mul);
    f.instruction(&Instruction::I32Load(bridge_arg(
        HEADER_BASE as u64,
        bridge_mem,
    )));
    f.instruction(&Instruction::I32Eqz);
    f.instruction(&Instruction::BrIf(1));
    // slot += 1; continue scan
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I32Const(1));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::LocalSet(0));
    f.instruction(&Instruction::Br(0));
    f.instruction(&Instruction::End); // loop
    f.instruction(&Instruction::End); // $have lands here

    // claim: l1 = header address
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I32Const(SLOT_HEADER_STRIDE as i32));
    f.instruction(&Instruction::I32Mul);
    f.instruction(&Instruction::LocalSet(1));
    // state = OPEN
    f.instruction(&Instruction::LocalGet(1));
    f.instruction(&Instruction::I32Const(STATE_OPEN));
    f.instruction(&Instruction::I32Store(bridge_arg(0, bridge_mem)));
    // rd = 0
    f.instruction(&Instruction::LocalGet(1));
    f.instruction(&Instruction::I32Const(0));
    f.instruction(&Instruction::I32Store(bridge_arg(4, bridge_mem)));
    // wr = 0
    f.instruction(&Instruction::LocalGet(1));
    f.instruction(&Instruction::I32Const(0));
    f.instruction(&Instruction::I32Store(bridge_arg(8, bridge_mem)));
    // tagged = slot | LOCAL_TAG; result = tagged | (tagged << 32)
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I32Const(LOCAL_TAG as i32));
    f.instruction(&Instruction::I32Or);
    f.instruction(&Instruction::LocalSet(0));
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I64ExtendI32U);
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I64ExtendI32U);
    f.instruction(&Instruction::I64Const(32));
    f.instruction(&Instruction::I64Shl);
    f.instruction(&Instruction::I64Or);
    f.instruction(&Instruction::Return);

    f.instruction(&Instruction::End); // $exhausted lands here
    f.instruction(&Instruction::Call(host_new));
    f.instruction(&Instruction::End);
    f
}

/// `stream_write(handle, ptr, len, mem_idx) -> i32` shim.
fn emit_write_shim(bridge_mem: u32, caller_mem: u32, host_write: u32) -> Function {
    let mut f = Function::new([(7, ValType::I32)]);
    emit_host_fallback(&mut f, host_write, 4);
    emit_slot_decode(&mut f);

    // l6 = rd, l7 = wr
    f.instruction(&Instruction::LocalGet(4));
    f.instruction(&Instruction::I32Load(bridge_arg(4, bridge_mem)));
    f.instruction(&Instruction::LocalSet(6));
    f.instruction(&Instruction::LocalGet(4));
    f.instruction(&Instruction::I32Load(bridge_arg(8, bridge_mem)));
    f.instruction(&Instruction::LocalSet(7));

    // l8 = avail = RING_CAP - (wr - rd)   (wrapping u32 arithmetic)
    f.instruction(&Instruction::I32Const(RING_CAP as i32));
    f.instruction(&Instruction::LocalGet(7));
    f.instruction(&Instruction::LocalGet(6));
    f.instruction(&Instruction::I32Sub);
    f.instruction(&Instruction::I32Sub);
    f.instruction(&Instruction::LocalSet(8));
    // l8 = n = min(len, avail)
    emit_min_u(&mut f, 2, 8);
    f.instruction(&Instruction::LocalSet(8));
    // n == 0 → backpressure: return 0 (ADR-2: 0 is Partial, never EOF)
    f.instruction(&Instruction::LocalGet(8));
    f.instruction(&Instruction::I32Eqz);
    f.instruction(&Instruction::If(BlockType::Empty));
    f.instruction(&Instruction::I32Const(0));
    f.instruction(&Instruction::Return);
    f.instruction(&Instruction::End);

    // l9 = off = wr & (RING_CAP - 1)
    f.instruction(&Instruction::LocalGet(7));
    f.instruction(&Instruction::I32Const((RING_CAP - 1) as i32));
    f.instruction(&Instruction::I32And);
    f.instruction(&Instruction::LocalSet(9));
    // l10 = first = min(n, RING_CAP - off)
    f.instruction(&Instruction::I32Const(RING_CAP as i32));
    f.instruction(&Instruction::LocalGet(9));
    f.instruction(&Instruction::I32Sub);
    f.instruction(&Instruction::LocalSet(10));
    emit_min_u(&mut f, 8, 10);
    f.instruction(&Instruction::LocalSet(10));

    // copy 1: bridge[ring + off] ← caller[ptr], first bytes
    f.instruction(&Instruction::LocalGet(5));
    f.instruction(&Instruction::LocalGet(9));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::LocalGet(1));
    f.instruction(&Instruction::LocalGet(10));
    f.instruction(&Instruction::MemoryCopy {
        src_mem: caller_mem,
        dst_mem: bridge_mem,
    });
    // copy 2 (wrap): bridge[ring] ← caller[ptr + first], n - first bytes
    f.instruction(&Instruction::LocalGet(8));
    f.instruction(&Instruction::LocalGet(10));
    f.instruction(&Instruction::I32GtU);
    f.instruction(&Instruction::If(BlockType::Empty));
    f.instruction(&Instruction::LocalGet(5));
    f.instruction(&Instruction::LocalGet(1));
    f.instruction(&Instruction::LocalGet(10));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::LocalGet(8));
    f.instruction(&Instruction::LocalGet(10));
    f.instruction(&Instruction::I32Sub);
    f.instruction(&Instruction::MemoryCopy {
        src_mem: caller_mem,
        dst_mem: bridge_mem,
    });
    f.instruction(&Instruction::End);

    // wr += n
    f.instruction(&Instruction::LocalGet(4));
    f.instruction(&Instruction::LocalGet(7));
    f.instruction(&Instruction::LocalGet(8));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::I32Store(bridge_arg(8, bridge_mem)));
    // return n (accepted count)
    f.instruction(&Instruction::LocalGet(8));
    f.instruction(&Instruction::End);
    f
}

/// `stream_read(handle, ptr, len, mem_idx) -> i32` shim.
fn emit_read_shim(bridge_mem: u32, caller_mem: u32, host_read: u32) -> Function {
    let mut f = Function::new([(7, ValType::I32)]);
    emit_host_fallback(&mut f, host_read, 4);
    emit_slot_decode(&mut f);

    // l6 = rd, l7 = wr
    f.instruction(&Instruction::LocalGet(4));
    f.instruction(&Instruction::I32Load(bridge_arg(4, bridge_mem)));
    f.instruction(&Instruction::LocalSet(6));
    f.instruction(&Instruction::LocalGet(4));
    f.instruction(&Instruction::I32Load(bridge_arg(8, bridge_mem)));
    f.instruction(&Instruction::LocalSet(7));

    // empty (wr == rd): EOF (0) iff writer dropped, else Pending (-5)
    f.instruction(&Instruction::LocalGet(7));
    f.instruction(&Instruction::LocalGet(6));
    f.instruction(&Instruction::I32Eq);
    f.instruction(&Instruction::If(BlockType::Empty));
    f.instruction(&Instruction::LocalGet(4));
    f.instruction(&Instruction::I32Load(bridge_arg(0, bridge_mem)));
    f.instruction(&Instruction::I32Const(STATE_WRITER_DROPPED));
    f.instruction(&Instruction::I32Eq);
    f.instruction(&Instruction::If(BlockType::Result(ValType::I32)));
    f.instruction(&Instruction::I32Const(0));
    f.instruction(&Instruction::Else);
    f.instruction(&Instruction::I32Const(p3_async::AbiError::Pending.as_i32()));
    f.instruction(&Instruction::End);
    f.instruction(&Instruction::Return);
    f.instruction(&Instruction::End);

    // l8 = fill = wr - rd; n = min(len, fill)
    f.instruction(&Instruction::LocalGet(7));
    f.instruction(&Instruction::LocalGet(6));
    f.instruction(&Instruction::I32Sub);
    f.instruction(&Instruction::LocalSet(8));
    emit_min_u(&mut f, 2, 8);
    f.instruction(&Instruction::LocalSet(8));

    // l9 = off = rd & (RING_CAP - 1)
    f.instruction(&Instruction::LocalGet(6));
    f.instruction(&Instruction::I32Const((RING_CAP - 1) as i32));
    f.instruction(&Instruction::I32And);
    f.instruction(&Instruction::LocalSet(9));
    // l10 = first = min(n, RING_CAP - off)
    f.instruction(&Instruction::I32Const(RING_CAP as i32));
    f.instruction(&Instruction::LocalGet(9));
    f.instruction(&Instruction::I32Sub);
    f.instruction(&Instruction::LocalSet(10));
    emit_min_u(&mut f, 8, 10);
    f.instruction(&Instruction::LocalSet(10));

    // copy 1: caller[ptr] ← bridge[ring + off], first bytes
    f.instruction(&Instruction::LocalGet(1));
    f.instruction(&Instruction::LocalGet(5));
    f.instruction(&Instruction::LocalGet(9));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::LocalGet(10));
    f.instruction(&Instruction::MemoryCopy {
        src_mem: bridge_mem,
        dst_mem: caller_mem,
    });
    // copy 2 (wrap): caller[ptr + first] ← bridge[ring], n - first bytes
    f.instruction(&Instruction::LocalGet(8));
    f.instruction(&Instruction::LocalGet(10));
    f.instruction(&Instruction::I32GtU);
    f.instruction(&Instruction::If(BlockType::Empty));
    f.instruction(&Instruction::LocalGet(1));
    f.instruction(&Instruction::LocalGet(10));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::LocalGet(5));
    f.instruction(&Instruction::LocalGet(8));
    f.instruction(&Instruction::LocalGet(10));
    f.instruction(&Instruction::I32Sub);
    f.instruction(&Instruction::MemoryCopy {
        src_mem: bridge_mem,
        dst_mem: caller_mem,
    });
    f.instruction(&Instruction::End);

    // rd += n
    f.instruction(&Instruction::LocalGet(4));
    f.instruction(&Instruction::LocalGet(6));
    f.instruction(&Instruction::LocalGet(8));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::I32Store(bridge_arg(4, bridge_mem)));
    // return n (bytes read)
    f.instruction(&Instruction::LocalGet(8));
    f.instruction(&Instruction::End);
    f
}

/// `stream_drop_readable` / `stream_drop_writable` shim: tagged handle →
/// set the slot state; host handle → forward to the host import.
fn emit_drop_shim(bridge_mem: u32, new_state: i32, host_drop: u32) -> Function {
    let mut f = Function::new([]);
    emit_host_fallback(&mut f, host_drop, 1);
    // header address = (handle & !LOCAL_TAG) * SLOT_HEADER_STRIDE
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I32Const(0x7FFF_FFFF));
    f.instruction(&Instruction::I32And);
    f.instruction(&Instruction::I32Const(SLOT_HEADER_STRIDE as i32));
    f.instruction(&Instruction::I32Mul);
    f.instruction(&Instruction::I32Const(new_state));
    f.instruction(&Instruction::I32Store(bridge_arg(0, bridge_mem)));
    f.instruction(&Instruction::End);
    f
}

// Layout invariants the codegen masks/offsets rely on, checked at
// compile time: RING_CAP must be a power of two (mask arithmetic), the
// header table must fit below the ring storage, the rings must fit in
// the fixed bridge memory, and LOCAL_TAG must be exactly bit 31 (so
// `handle as i32 >= 0` means "host handle").
const _: () = {
    assert!(RING_CAP.is_power_of_two());
    assert!(SLOT_COUNT * SLOT_HEADER_STRIDE <= RINGS_BASE - HEADER_BASE);
    assert!(
        (RINGS_BASE as u64) + (SLOT_COUNT as u64) * (RING_CAP as u64)
            <= BRIDGE_MEMORY_PAGES * 65536
    );
    assert!(LOCAL_TAG == 1 << 31);
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stream_op_name_round_trip() {
        for (name, op) in [
            ("stream_new", StreamOp::New),
            ("stream_read", StreamOp::Read),
            ("stream_write", StreamOp::Write),
            ("stream_drop_readable", StreamOp::DropReadable),
            ("stream_drop_writable", StreamOp::DropWritable),
        ] {
            assert_eq!(StreamOp::from_name(name), Some(op));
        }
        // Cancel ops are deliberately NOT bridged.
        assert_eq!(StreamOp::from_name("stream_cancel_read"), None);
        assert_eq!(StreamOp::from_name("stream_cancel_write"), None);
        assert_eq!(StreamOp::from_name("future_read"), None);
    }
}
