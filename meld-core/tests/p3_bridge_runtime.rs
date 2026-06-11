//! Runtime oracles for the cross-component stream-bridge emitter
//! (#141, SR-33, LS-ST-1).
//!
//! Two hand-built components are fused through the REAL pipeline and the
//! fused core module is executed under wasmtime:
//!
//! * **producer** — core module importing `pulseengine:async`
//!   `stream_new` / `stream_write` / `stream_drop_writable`, with driver
//!   exports (`p_new`, `p_write`, `p_drop`) and its own memory.
//! * **consumer** — core module importing `stream_read` /
//!   `stream_drop_readable`, with driver exports (`c_read`, `c_get`,
//!   `c_drop`) and its own (distinct) memory.
//!
//! ## How the pair detector is triggered (honest construction note)
//!
//! `p3_stream::build_stream_pair_graph` needs two things that a bare
//! module-in-component wrapper does not have:
//!
//! 1. **Stream roles** — `CanonicalEntry::StreamWrite` / `StreamRead`
//!    entries whose type resolves to a `stream`. We attach a component
//!    type section defining an UNTYPED `stream` (payload `None`) plus a
//!    canonical section with `stream.write` / `stream.read` against it.
//!    The untyped stream is deliberate: the component-model validator
//!    only demands a `memory` canonical option when the element type is
//!    concrete, and a memory option would require instantiating a core
//!    module inside the component (which would internalise the very
//!    host imports this test must keep). `StreamElement::Untyped`
//!    matches `Untyped`, so the detector pairs them.
//! 2. **Fusion connection** — `resolved_imports` is keyed on
//!    *component-level* import/export names. The producer component
//!    exports its core module as `"link"` and the consumer component
//!    imports a core module named `"link"`; the resolver matches them,
//!    making the two components fusion-connected without disturbing the
//!    core-level stream imports.
//!
//! This drives the emitter through `Fuser::fuse()` itself — no test-only
//! entry point — so these tests cover detection→emission→rewiring→runtime
//! end to end. (The fallback sanctioned by the #141 plan — driving the
//! emitter directly with a constructed `StreamPairGraph` — was NOT
//! needed.)
//!
//! ## The host-crossing proof
//!
//! The wasmtime host stubs for every `pulseengine:async` intrinsic TRAP
//! when invoked with a bit-31-tagged (bridge-local) handle, and the
//! tests additionally assert the stubs' call counters stay zero on the
//! bridged paths. Any mis-dispatch of a local stream op to the host
//! fails loudly.

use meld_core::p3_bridge::{LOCAL_TAG, RING_CAP, SLOT_COUNT};
use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CanonicalFunctionSection, CodeSection, Component, ComponentExportKind, ComponentExportSection,
    ComponentImportSection, ComponentTypeRef, ComponentTypeSection, CoreTypeSection, ExportKind,
    ExportSection, Function, FunctionSection, ImportSection, Instruction, MemArg, MemorySection,
    MemoryType, Module, ModuleSection, ModuleType, TypeSection, ValType,
};
use wasmtime::{Caller, Config, Engine, Instance, Linker, Module as RuntimeModule, Store};

const ASYNC_MOD: &str = "pulseengine:async";

/// Producer buffer base address (in producer memory).
const P_BUF: i32 = 16;
/// Consumer buffer base address (in consumer memory).
const C_BUF: i32 = 32;

fn mem8(memory_index: u32) -> MemArg {
    MemArg {
        offset: 0,
        align: 0,
        memory_index,
    }
}

/// Producer core module.
///
/// imports: f0 `stream_new` `()->i64`, f1 `stream_write`
/// `(i32,i32,i32,i32)->i32`, f2 `stream_drop_writable` `(i32)->()`.
///
/// exports:
/// * `p_new() -> i64` — mint a stream pair.
/// * `p_write(handle, count) -> i32` — fill its OWN memory at `P_BUF`
///   with bytes `(i+1) & 0xff` for `i in 0..count`, then
///   `stream_write(handle, P_BUF, count, 0)`.
/// * `p_drop(handle)` — drop the writable end.
fn build_producer_module() -> Module {
    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I64]); // t0: stream_new / p_new
    types.ty().function([ValType::I32; 4], [ValType::I32]); // t1: stream_write
    types.ty().function([ValType::I32], []); // t2: drop / p_drop
    types
        .ty()
        .function([ValType::I32, ValType::I32], [ValType::I32]); // t3: p_write

    let mut imports = ImportSection::new();
    imports.import(
        ASYNC_MOD,
        "stream_new",
        wasm_encoder::EntityType::Function(0),
    );
    imports.import(
        ASYNC_MOD,
        "stream_write",
        wasm_encoder::EntityType::Function(1),
    );
    imports.import(
        ASYNC_MOD,
        "stream_drop_writable",
        wasm_encoder::EntityType::Function(2),
    );

    let mut functions = FunctionSection::new();
    functions.function(0); // f3: p_new
    functions.function(3); // f4: p_write
    functions.function(2); // f5: p_drop

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export("p_new", ExportKind::Func, 3);
    exports.export("p_write", ExportKind::Func, 4);
    exports.export("p_drop", ExportKind::Func, 5);

    let mut code = CodeSection::new();

    // p_new: call stream_new
    let mut f = Function::new([]);
    f.instruction(&Instruction::Call(0));
    f.instruction(&Instruction::End);
    code.function(&f);

    // p_write(handle l0, count l1), local l2 = i
    let mut f = Function::new([(1, ValType::I32)]);
    f.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
    f.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
    f.instruction(&Instruction::LocalGet(2));
    f.instruction(&Instruction::LocalGet(1));
    f.instruction(&Instruction::I32GeU);
    f.instruction(&Instruction::BrIf(1));
    // mem[P_BUF + i] = (i + 1) (store8 truncates to & 0xff)
    f.instruction(&Instruction::LocalGet(2));
    f.instruction(&Instruction::I32Const(P_BUF));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::LocalGet(2));
    f.instruction(&Instruction::I32Const(1));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::I32Store8(mem8(0)));
    f.instruction(&Instruction::LocalGet(2));
    f.instruction(&Instruction::I32Const(1));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::LocalSet(2));
    f.instruction(&Instruction::Br(0));
    f.instruction(&Instruction::End);
    f.instruction(&Instruction::End);
    // stream_write(handle, P_BUF, count, 0)
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I32Const(P_BUF));
    f.instruction(&Instruction::LocalGet(1));
    f.instruction(&Instruction::I32Const(0));
    f.instruction(&Instruction::Call(1));
    f.instruction(&Instruction::End);
    code.function(&f);

    // p_drop(handle)
    let mut f = Function::new([]);
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::Call(2));
    f.instruction(&Instruction::End);
    code.function(&f);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&imports)
        .section(&functions)
        .section(&memory)
        .section(&exports)
        .section(&code);
    module
}

/// Consumer core module.
///
/// imports: f0 `stream_read` `(i32,i32,i32,i32)->i32`,
/// f1 `stream_drop_readable` `(i32)->()`.
///
/// exports:
/// * `c_read(handle, count) -> i32` — `stream_read(handle, C_BUF, count, 0)`
///   into its OWN memory.
/// * `c_get(i) -> i32` — `mem[C_BUF + i]` (u8 load) to verify integrity.
/// * `c_drop(handle)` — drop the readable end.
fn build_consumer_module() -> Module {
    let mut types = TypeSection::new();
    types.ty().function([ValType::I32; 4], [ValType::I32]); // t0: stream_read
    types.ty().function([ValType::I32], []); // t1: drop / c_drop
    types
        .ty()
        .function([ValType::I32, ValType::I32], [ValType::I32]); // t2: c_read
    types.ty().function([ValType::I32], [ValType::I32]); // t3: c_get

    let mut imports = ImportSection::new();
    imports.import(
        ASYNC_MOD,
        "stream_read",
        wasm_encoder::EntityType::Function(0),
    );
    imports.import(
        ASYNC_MOD,
        "stream_drop_readable",
        wasm_encoder::EntityType::Function(1),
    );

    let mut functions = FunctionSection::new();
    functions.function(2); // f2: c_read
    functions.function(3); // f3: c_get
    functions.function(1); // f4: c_drop

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export("c_read", ExportKind::Func, 2);
    exports.export("c_get", ExportKind::Func, 3);
    exports.export("c_drop", ExportKind::Func, 4);

    let mut code = CodeSection::new();

    // c_read(handle l0, count l1)
    let mut f = Function::new([]);
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I32Const(C_BUF));
    f.instruction(&Instruction::LocalGet(1));
    f.instruction(&Instruction::I32Const(0));
    f.instruction(&Instruction::Call(0));
    f.instruction(&Instruction::End);
    code.function(&f);

    // c_get(i)
    let mut f = Function::new([]);
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I32Const(C_BUF));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::I32Load8U(mem8(0)));
    f.instruction(&Instruction::End);
    code.function(&f);

    // c_drop(handle)
    let mut f = Function::new([]);
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::Call(1));
    f.instruction(&Instruction::End);
    code.function(&f);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&imports)
        .section(&functions)
        .section(&memory)
        .section(&exports)
        .section(&code);
    module
}

/// Producer component: untyped `stream` type + `canon stream.write`
/// (StreamWrite role for the pair detector), the core module, and a
/// component-level export of that module as `"link"` (the fusion
/// connection anchor).
fn producer_component() -> Vec<u8> {
    let mut component = Component::new();

    let mut ctypes = ComponentTypeSection::new();
    ctypes.defined_type().stream(None); // component type 0: stream (untyped)
    component.section(&ctypes);

    let mut canon = CanonicalFunctionSection::new();
    canon.stream_write(0, []);
    component.section(&canon);

    component.section(&ModuleSection(&build_producer_module()));

    let mut exports = ComponentExportSection::new();
    exports.export("link", ComponentExportKind::Module, 0, None);
    component.section(&exports);

    component.finish()
}

/// Consumer component: a core-module-typed import named `"link"` (the
/// fusion connection anchor), untyped `stream` type + `canon
/// stream.read` (StreamRead role), and the core module.
fn consumer_component() -> Vec<u8> {
    let mut component = Component::new();

    let mut core_types = CoreTypeSection::new();
    core_types.ty().module(&ModuleType::new()); // core type 0: (module)
    component.section(&core_types);

    let mut imports = ComponentImportSection::new();
    imports.import("link", ComponentTypeRef::Module(0));
    component.section(&imports);

    let mut ctypes = ComponentTypeSection::new();
    ctypes.defined_type().stream(None); // component type 0: stream (untyped)
    component.section(&ctypes);

    let mut canon = CanonicalFunctionSection::new();
    canon.stream_read(0, []);
    component.section(&canon);

    component.section(&ModuleSection(&build_consumer_module()));

    component.finish()
}

/// Fuse producer + consumer through the real pipeline (multi-memory —
/// the cross-memory bridge shape; same-memory is the identical codegen
/// with caller-memory immediates 0).
fn fuse_pair() -> Vec<u8> {
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&producer_component(), Some("producer"))
        .expect("add producer");
    fuser
        .add_component_named(&consumer_component(), Some("consumer"))
        .expect("add consumer");
    fuser.fuse().expect("fuse")
}

/// Host-stub call counters — the "no host crossing" witness.
#[derive(Default)]
struct HostCounters {
    new: u32,
    read: u32,
    write: u32,
    drops: u32,
}

/// `Err` (→ wasm trap) on any bit-31-tagged handle reaching the host.
fn guard(handle: i32, op: &str) -> wasmtime::Result<()> {
    if (handle as u32) & LOCAL_TAG != 0 {
        anyhow::bail!("bridge-local handle {handle:#x} crossed the host boundary via {op}");
    }
    Ok(())
}

/// Instantiate the fused core module with trapping host stubs.
///
/// Host `stream_new` mints untagged handles (readable = 1, writable = 2;
/// then 3/4, …) — exercised only by the slot-exhaustion fallback test.
/// Host `stream_write` accepts everything; host `stream_read` returns 0.
fn instantiate(fused: &[u8]) -> (Store<HostCounters>, Instance) {
    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).expect("engine");
    let module = RuntimeModule::new(&engine, fused).expect("fused module must validate");
    let mut store = Store::new(&engine, HostCounters::default());

    let mut linker: Linker<HostCounters> = Linker::new(&engine);
    linker
        .func_wrap(
            ASYNC_MOD,
            "stream_new",
            |mut caller: Caller<'_, HostCounters>| -> wasmtime::Result<i64> {
                let n = caller.data().new;
                caller.data_mut().new = n + 1;
                let readable = i64::from(2 * n + 1);
                let writable = i64::from(2 * n + 2);
                Ok((writable << 32) | readable)
            },
        )
        .unwrap();
    linker
        .func_wrap(
            ASYNC_MOD,
            "stream_read",
            |mut caller: Caller<'_, HostCounters>,
             h: i32,
             _ptr: i32,
             _len: i32,
             _mem: i32|
             -> wasmtime::Result<i32> {
                guard(h, "stream_read")?;
                caller.data_mut().read += 1;
                Ok(0)
            },
        )
        .unwrap();
    linker
        .func_wrap(
            ASYNC_MOD,
            "stream_write",
            |mut caller: Caller<'_, HostCounters>,
             h: i32,
             _ptr: i32,
             len: i32,
             _mem: i32|
             -> wasmtime::Result<i32> {
                guard(h, "stream_write")?;
                caller.data_mut().write += 1;
                Ok(len)
            },
        )
        .unwrap();
    for name in ["stream_drop_readable", "stream_drop_writable"] {
        linker
            .func_wrap(
                ASYNC_MOD,
                name,
                move |mut caller: Caller<'_, HostCounters>, h: i32| -> wasmtime::Result<()> {
                    guard(h, "stream_drop_*")?;
                    caller.data_mut().drops += 1;
                    Ok(())
                },
            )
            .unwrap();
    }

    let instance = linker
        .instantiate(&mut store, &module)
        .expect("instantiate");
    (store, instance)
}

struct Drivers {
    p_new: wasmtime::TypedFunc<(), i64>,
    p_write: wasmtime::TypedFunc<(i32, i32), i32>,
    p_drop: wasmtime::TypedFunc<i32, ()>,
    c_read: wasmtime::TypedFunc<(i32, i32), i32>,
    c_get: wasmtime::TypedFunc<i32, i32>,
}

fn drivers(store: &mut Store<HostCounters>, instance: &Instance) -> Drivers {
    Drivers {
        p_new: instance.get_typed_func(&mut *store, "p_new").unwrap(),
        p_write: instance.get_typed_func(&mut *store, "p_write").unwrap(),
        p_drop: instance.get_typed_func(&mut *store, "p_drop").unwrap(),
        c_read: instance.get_typed_func(&mut *store, "c_read").unwrap(),
        c_get: instance.get_typed_func(&mut *store, "c_get").unwrap(),
    }
}

/// Split a packed `stream_new` result: low 32 = readable, high 32 = writable.
fn split(pair: i64) -> (i32, i32) {
    ((pair & 0xFFFF_FFFF) as i32, (pair >> 32) as i32)
}

fn assert_no_host_calls(store: &Store<HostCounters>) {
    let c = store.data();
    assert_eq!(
        (c.new, c.read, c.write, c.drops),
        (0, 0, 0, 0),
        "bridged stream ops must never cross the host boundary"
    );
}

/// Count the memories declared by the fused core module (independent
/// wasmparser derivation).
fn count_memories(fused: &[u8]) -> usize {
    let mut count = 0;
    for payload in wasmparser::Parser::new(0).parse_all(fused) {
        if let wasmparser::Payload::MemorySection(reader) = payload.unwrap() {
            count += reader.into_iter().count();
        }
    }
    count
}

/// Oracle (a) — round-trip: the producer writes `[1, 2, 3, 4]` through a
/// bridge-local stream and the consumer reads the same bytes back, with
/// ZERO host intrinsic calls. (`ls_st_1_` prefix: LS-ST-1 gate fixture.)
#[test]
fn ls_st_1_round_trip_local_stream_never_crosses_host() {
    let fused = fuse_pair();
    let (mut store, instance) = instantiate(&fused);
    let d = drivers(&mut store, &instance);

    let pair = d.p_new.call(&mut store, ()).unwrap();
    let (readable, writable) = split(pair);
    assert_ne!(
        (readable as u32) & LOCAL_TAG,
        0,
        "in-module stream_new must mint a bridge-local (tagged) readable end"
    );
    assert_ne!(
        (writable as u32) & LOCAL_TAG,
        0,
        "writable end must be tagged"
    );

    let written = d.p_write.call(&mut store, (writable, 4)).unwrap();
    assert_eq!(written, 4, "ring has space: all 4 bytes accepted");

    let read = d.c_read.call(&mut store, (readable, 8)).unwrap();
    assert_eq!(
        read, 4,
        "read returns the buffered byte count, not the request"
    );

    for i in 0..4 {
        let byte = d.c_get.call(&mut store, i).unwrap();
        assert_eq!(byte, i + 1, "byte {i} must survive the bridge intact");
    }

    assert_no_host_calls(&store);
}

/// Oracle (b) — cross-memory chain: producer memory ≠ consumer memory
/// (multi-memory fusion keeps one memory per component, plus the bridge
/// memory), and data still arrives intact across the two `memory.copy`
/// hops (producer mem → bridge ring → consumer mem).
#[test]
fn cross_memory_chain_preserves_data_across_distinct_memories() {
    let fused = fuse_pair();
    assert_eq!(
        count_memories(&fused),
        3,
        "fused module must carry producer memory + consumer memory + bridge memory"
    );

    let (mut store, instance) = instantiate(&fused);
    let d = drivers(&mut store, &instance);

    let (readable, writable) = split(d.p_new.call(&mut store, ()).unwrap());

    // 300 bytes exercises multi-byte copies and the (i+1) & 0xff wrap.
    assert_eq!(d.p_write.call(&mut store, (writable, 300)).unwrap(), 300);
    assert_eq!(d.c_read.call(&mut store, (readable, 4096)).unwrap(), 300);
    for i in 0..300 {
        let expected = (i + 1) & 0xff;
        let byte = d.c_get.call(&mut store, i).unwrap();
        assert_eq!(byte, expected, "byte {i} corrupted crossing memories");
    }

    assert_no_host_calls(&store);
}

/// Oracle (c) — backpressure: a write larger than RING_CAP returns the
/// accepted count (= RING_CAP, ADR-2 Partial); once the consumer drains
/// the ring, a follow-up write accepts the rest.
#[test]
fn backpressure_partial_write_then_drain_then_resume() {
    let fused = fuse_pair();
    let (mut store, instance) = instantiate(&fused);
    let d = drivers(&mut store, &instance);

    let (readable, writable) = split(d.p_new.call(&mut store, ()).unwrap());

    let requested = RING_CAP as i32 + 904; // 5000 > ring capacity
    let accepted = d.p_write.call(&mut store, (writable, requested)).unwrap();
    assert_eq!(
        accepted, RING_CAP as i32,
        "write > capacity must return the accepted count, not trap or queue"
    );

    // Ring is full now: another write is pure backpressure (0 ≠ EOF).
    assert_eq!(
        d.p_write.call(&mut store, (writable, 1)).unwrap(),
        0,
        "full ring must report 0 accepted (ADR-2: 0 from write is backpressure)"
    );

    // Drain everything the ring holds.
    let drained = d
        .c_read
        .call(&mut store, (readable, RING_CAP as i32 + 904))
        .unwrap();
    assert_eq!(
        drained, RING_CAP as i32,
        "drain returns exactly the fill level"
    );
    assert_eq!(d.c_get.call(&mut store, 0).unwrap(), 1);
    assert_eq!(
        d.c_get.call(&mut store, RING_CAP as i32 - 1).unwrap(),
        (RING_CAP as i32) & 0xff,
        "last drained byte must match the producer pattern"
    );

    // Producer retries the unaccepted tail (ADR-2: producer is the retry
    // authority). The wrap-around copy path is exercised here: the write
    // starts at ring offset 4096 & 4095 = 0 after one full cycle… and a
    // second partial cycle below crosses the ring boundary.
    let resumed = d.p_write.call(&mut store, (writable, 904)).unwrap();
    assert_eq!(
        resumed, 904,
        "after drain the ring must accept the remainder"
    );
    let read2 = d.c_read.call(&mut store, (readable, 8192)).unwrap();
    assert_eq!(read2, 904);
    assert_eq!(d.c_get.call(&mut store, 0).unwrap(), 1);
    assert_eq!(d.c_get.call(&mut store, 903).unwrap(), 904 & 0xff);

    // Cross the ring boundary mid-write: both cursors sit at 5000, so the
    // ring offset is 5000 & 4095 = 904 and a 3500-byte transfer splits
    // into 3192 + 308 — the two-part wrapping memory.copy path runs with
    // both parts non-empty, on the write AND the read side.
    assert_eq!(d.p_write.call(&mut store, (writable, 3500)).unwrap(), 3500);
    assert_eq!(d.c_read.call(&mut store, (readable, 8192)).unwrap(), 3500);
    for i in [0, 3191, 3192, 3499] {
        assert_eq!(
            d.c_get.call(&mut store, i).unwrap(),
            (i + 1) & 0xff,
            "byte {i} corrupted across the ring wrap boundary"
        );
    }

    assert_no_host_calls(&store);
}

/// Oracle (d) — EOF: while the stream is open and empty, read returns
/// `-5` (ADR-2 Pending); after `drop_writable` the reader drains the
/// remaining bytes and only THEN observes `0` (EOF), which is sticky.
/// (`ls_st_1_` prefix: LS-ST-1 gate fixture.)
#[test]
fn ls_st_1_eof_only_after_writer_drop_and_drain() {
    let fused = fuse_pair();
    let (mut store, instance) = instantiate(&fused);
    let d = drivers(&mut store, &instance);

    let (readable, writable) = split(d.p_new.call(&mut store, ()).unwrap());

    // Open + empty ⇒ Pending, NOT EOF.
    assert_eq!(
        d.c_read.call(&mut store, (readable, 8)).unwrap(),
        -5,
        "open+empty must be Pending (-5), distinguishable from EOF"
    );

    assert_eq!(d.p_write.call(&mut store, (writable, 4)).unwrap(), 4);
    d.p_drop.call(&mut store, writable).unwrap();

    // Buffered bytes drain first — dropping the writer must not lose data.
    assert_eq!(d.c_read.call(&mut store, (readable, 2)).unwrap(), 2);
    assert_eq!(d.c_get.call(&mut store, 0).unwrap(), 1);
    assert_eq!(d.c_get.call(&mut store, 1).unwrap(), 2);
    assert_eq!(d.c_read.call(&mut store, (readable, 8)).unwrap(), 2);
    assert_eq!(d.c_get.call(&mut store, 0).unwrap(), 3);
    assert_eq!(d.c_get.call(&mut store, 1).unwrap(), 4);

    // Drained + writer-dropped ⇒ EOF (0), and it stays EOF.
    assert_eq!(d.c_read.call(&mut store, (readable, 8)).unwrap(), 0);
    assert_eq!(
        d.c_read.call(&mut store, (readable, 8)).unwrap(),
        0,
        "EOF is sticky"
    );

    assert_no_host_calls(&store);
}

/// Fallback dispatch: exhausting all bridge slots makes `stream_new`
/// fall back to the HOST intrinsic (untagged handles), and ops on those
/// handles route to the host imports — the stubs see them and accept
/// them (the guard only rejects TAGGED handles).
#[test]
fn slot_exhaustion_falls_back_to_host_stream() {
    let fused = fuse_pair();
    let (mut store, instance) = instantiate(&fused);
    let d = drivers(&mut store, &instance);

    for i in 0..SLOT_COUNT {
        let (readable, _writable) = split(d.p_new.call(&mut store, ()).unwrap());
        assert_ne!(
            (readable as u32) & LOCAL_TAG,
            0,
            "slot {i} must still be bridge-local"
        );
    }
    assert_eq!(store.data().new, 0, "no host fallback before exhaustion");

    // Ninth stream: bridge slots exhausted → host mints it.
    let (readable, writable) = split(d.p_new.call(&mut store, ()).unwrap());
    assert_eq!(
        store.data().new,
        1,
        "exhaustion must fall back to host stream_new"
    );
    assert_eq!(
        (readable as u32) & LOCAL_TAG,
        0,
        "host-minted readable end must be untagged"
    );
    assert_eq!((writable as u32) & LOCAL_TAG, 0);

    // Ops on the host handle cross to the host import (and only those).
    assert_eq!(d.p_write.call(&mut store, (writable, 4)).unwrap(), 4);
    assert_eq!(
        store.data().write,
        1,
        "foreign-handle write must reach the host"
    );
    assert_eq!(d.c_read.call(&mut store, (readable, 4)).unwrap(), 0);
    assert_eq!(
        store.data().read,
        1,
        "foreign-handle read must reach the host"
    );
    d.p_drop.call(&mut store, writable).unwrap();
    assert_eq!(
        store.data().drops,
        1,
        "foreign-handle drop must reach the host"
    );
}
