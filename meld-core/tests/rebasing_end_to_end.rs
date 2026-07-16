use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, CustomSection, DataCountSection, DataSection, DataSegment,
    DataSegmentMode, ExportKind, ExportSection, Function, FunctionSection, Instruction, MemArg,
    MemorySection, MemoryType, Module, ModuleSection, TypeSection, ValType,
};
use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};

const WASM_PAGE_SIZE: usize = 65_536;

fn build_component(module: Module) -> Vec<u8> {
    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

fn shared_memory_section() -> MemorySection {
    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: Some(2),
        memory64: false,
        shared: true,
        page_size_log2: None,
    });
    memory
}

fn build_module_a() -> Module {
    let mut types = TypeSection::new();
    types.ty().function([], []);

    let mut functions = FunctionSection::new();
    functions.function(0);

    let mut exports = ExportSection::new();
    exports.export("a_fill", ExportKind::Func, 0);
    exports.export("memory", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    let mut func = Function::new([]);
    func.instruction(&Instruction::I32Const(0));
    func.instruction(&Instruction::I32Const(0x11));
    func.instruction(&Instruction::I32Const(4));
    func.instruction(&Instruction::MemoryFill(0));
    func.instruction(&Instruction::End);
    code.function(&func);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&shared_memory_section())
        .section(&exports)
        .section(&code);

    module
}

fn build_module_b() -> Module {
    let mut types = TypeSection::new();
    types.ty().function([], []);

    let mut functions = FunctionSection::new();
    functions.function(0);
    functions.function(0);
    functions.function(0);

    let mut exports = ExportSection::new();
    exports.export("b_init", ExportKind::Func, 0);
    exports.export("b_copy", ExportKind::Func, 1);
    exports.export("b_fill", ExportKind::Func, 2);

    let mut code = CodeSection::new();

    let mut init = Function::new([]);
    init.instruction(&Instruction::I32Const(0));
    init.instruction(&Instruction::I32Const(0));
    init.instruction(&Instruction::I32Const(4));
    init.instruction(&Instruction::MemoryInit {
        mem: 0,
        data_index: 0,
    });
    init.instruction(&Instruction::DataDrop(0));
    init.instruction(&Instruction::End);
    code.function(&init);

    let mut copy = Function::new([]);
    copy.instruction(&Instruction::I32Const(4));
    copy.instruction(&Instruction::I32Const(0));
    copy.instruction(&Instruction::I32Const(4));
    copy.instruction(&Instruction::MemoryCopy {
        src_mem: 0,
        dst_mem: 0,
    });
    copy.instruction(&Instruction::End);
    code.function(&copy);

    let mut fill = Function::new([]);
    fill.instruction(&Instruction::I32Const(8));
    fill.instruction(&Instruction::I32Const(0xBB));
    fill.instruction(&Instruction::I32Const(4));
    fill.instruction(&Instruction::MemoryFill(0));
    fill.instruction(&Instruction::End);
    code.function(&fill);

    let mut data = DataSection::new();
    data.segment(DataSegment {
        mode: DataSegmentMode::Passive,
        data: [1u8, 2, 3, 4],
    });

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&shared_memory_section())
        .section(&exports)
        .section(&DataCountSection { count: 1 })
        .section(&code)
        .section(&data);

    module
}

fn read_shared(memory: &wasmtime::SharedMemory, offset: usize, len: usize) -> Vec<u8> {
    let data = memory.data();
    (0..len)
        // Safe for this test: we read after all writes, with no concurrent access.
        .map(|idx| unsafe { *data[offset + idx].get() })
        .collect()
}

#[test]
fn test_address_rebasing_end_to_end() {
    let component_a = build_component(build_module_a());
    let component_b = build_component(build_module_b());

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        ..Default::default()
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component_a, Some("component-a"))
        .unwrap();
    fuser
        .add_component_named(&component_b, Some("component-b"))
        .unwrap();

    let fused = fuser.fuse().unwrap();

    let mut engine_config = Config::new();
    engine_config.wasm_threads(true);
    engine_config.shared_memory(true);
    engine_config.wasm_bulk_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let a_fill = instance
        .get_typed_func::<(), ()>(&mut store, "a_fill")
        .unwrap();
    let b_init = instance
        .get_typed_func::<(), ()>(&mut store, "b_init")
        .unwrap();
    let b_copy = instance
        .get_typed_func::<(), ()>(&mut store, "b_copy")
        .unwrap();
    let b_fill = instance
        .get_typed_func::<(), ()>(&mut store, "b_fill")
        .unwrap();

    a_fill.call(&mut store, ()).unwrap();
    b_init.call(&mut store, ()).unwrap();
    b_copy.call(&mut store, ()).unwrap();
    b_fill.call(&mut store, ()).unwrap();

    let memory = instance
        .get_shared_memory(&mut store, "memory")
        .expect("shared memory export not found");

    assert!(memory.data_size() >= 2 * WASM_PAGE_SIZE);

    let a_region = read_shared(&memory, 0, 4);
    assert_eq!(a_region, vec![0x11, 0x11, 0x11, 0x11]);

    let base = WASM_PAGE_SIZE;
    let b_init_region = read_shared(&memory, base, 4);
    assert_eq!(b_init_region, vec![1, 2, 3, 4]);

    let b_copy_region = read_shared(&memory, base + 4, 4);
    assert_eq!(b_copy_region, vec![1, 2, 3, 4]);

    let b_fill_region = read_shared(&memory, base + 8, 4);
    assert_eq!(b_fill_region, vec![0xBB, 0xBB, 0xBB, 0xBB]);
}

/// #298 real-artifact blocker — grounds the synthetic kill-criterion oracle
/// (`merger::tests::test_298_vestigial_grow_blocks_shared_rebase_fusion`) on a
/// **real** wit-bindgen component.
///
/// Stock wit-bindgen output links a growing allocator behind `cabi_realloc`
/// (`cabi_realloc → … → $sbrk → memory.grow`). Every fixture in the corpus
/// carries it: `strings-simple.wasm` exports `cabi_realloc` and contains
/// `memory.grow`. So fusing it in the single-address-space MCU config
/// (`SharedMemory` ⟹ `address_rebasing`) must currently hard-fail when the
/// rebase rewriter reaches that `memory.grow` — exactly the blocker the fork's
/// `cabi-realloc-extern` (arena-backed, no-grow) build removes, after which
/// `test_298_fork_arena_realloc_fuses_under_shared_rebase_today` shows meld
/// fuses the result.
///
/// This is the real-bytes proof that the embedded no-grow story is needed and
/// that meld's blocker fires on actual wit-bindgen output, not just hand-built
/// WAT. When #298's dead-allocator handling lands, this stays red until updated
/// to assert the (now grow-free) success.
#[test]
fn test_298_real_wit_bindgen_component_blocks_shared_rebase() {
    let path = format!(
        "{}/../tests/wit_bindgen/fixtures/strings-simple.wasm",
        env!("CARGO_MANIFEST_DIR")
    );
    let component = std::fs::read(&path).expect("strings-simple fixture present");

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component, Some("strings-simple"))
        .unwrap();

    let err = fuser
        .fuse()
        .expect_err("a real wit-bindgen component must not fuse under shared+rebase");
    let msg = err.to_string();
    // The invariant this pins is that a real wit-bindgen artifact is REJECTED
    // under shared+rebase — the corruption meld must not silently emit. There
    // are now two hard-fail gates and either satisfies the invariant:
    //   * the #298 `memory.grow` rebase rejection (the vestigial allocator), or
    //   * #326's path-F `MissingRelocMetadata`: this artifact's non-base module
    //     carries no relocation metadata yet does direct memory access, so its
    //     absolute addresses cannot be rebased safely. That gate is checked at
    //     merge time, *before* the rewriter reaches the `memory.grow`, so on
    //     this fixture #326 now fires first.
    assert!(
        msg.contains("memory.grow") || msg.contains("relocation metadata"),
        "expected shared+rebase to reject the real wit-bindgen artifact \
         (memory.grow or missing-reloc-metadata), got: {msg}"
    );
}

// ─── #326: relocation-driven address rebasing ──────────────────────────────

const RELOC_ADDR: i32 = 0x100;
const RELOC_VAL: i32 = 0xAB;

/// The base module (component-a): a 1-page shared memory exported as "memory".
/// It occupies window `[0, 64KiB)`, so the reloc module below is placed at base
/// 64KiB. No code ⟹ no direct memory access ⟹ no relocs required (base 0).
fn build_reloc_base_module() -> Module {
    let mut exports = ExportSection::new();
    exports.export("memory", ExportKind::Memory, 0);

    let mut module = Module::new();
    module.section(&shared_memory_section()).section(&exports);
    module
}

/// Add the sections of the reloc module: a 1-page shared memory and three
/// functions. `b_store` writes `RELOC_VAL` through the **absolute** address
/// `RELOC_ADDR`; `b_load` reads it back; `b_get_addr` simply RETURNS the
/// absolute address literal. Every `i32.const RELOC_ADDR` is a site the
/// synthetic `reloc.CODE` MEMORY_ADDR entry flags.
///
/// `b_get_addr` is the real discriminator: it uses the address as a *value*
/// (as canonical-ABI code does when it takes `&BUF` to hand to `memcpy`), where
/// there is no load/store `memarg` for the legacy access-point rebasing to
/// "accidentally" compensate. Pre-fix it returns the un-rebased `RELOC_ADDR`
/// (pointing into component-a's window); post-fix it returns `base+RELOC_ADDR`.
/// The store/load `memarg` offsets are 0 (genuine, not addresses) so they must
/// NOT be rebased — proving const-rebase and (conditional) memarg-rebase do not
/// double-count.
fn add_reloc_module_sections(module: &mut Module) {
    let mut types = TypeSection::new();
    types.ty().function([], []); // type 0: b_store: () -> ()
    types.ty().function([], [ValType::I32]); // type 1: () -> i32

    let mut functions = FunctionSection::new();
    functions.function(0);
    functions.function(1);
    functions.function(1);

    let mut exports = ExportSection::new();
    exports.export("b_store", ExportKind::Func, 0);
    exports.export("b_load", ExportKind::Func, 1);
    exports.export("b_get_addr", ExportKind::Func, 2);

    let zero_memarg = MemArg {
        offset: 0,
        align: 0,
        memory_index: 0,
    };

    let mut code = CodeSection::new();
    let mut store = Function::new([]);
    store.instruction(&Instruction::I32Const(RELOC_ADDR)); // absolute address (reloc-flagged)
    store.instruction(&Instruction::I32Const(RELOC_VAL));
    store.instruction(&Instruction::I32Store8(zero_memarg));
    store.instruction(&Instruction::End);
    code.function(&store);

    let mut load = Function::new([]);
    load.instruction(&Instruction::I32Const(RELOC_ADDR)); // absolute address (reloc-flagged)
    load.instruction(&Instruction::I32Load8U(zero_memarg));
    load.instruction(&Instruction::End);
    code.function(&load);

    let mut get_addr = Function::new([]);
    get_addr.instruction(&Instruction::I32Const(RELOC_ADDR)); // returned as a VALUE (reloc-flagged)
    get_addr.instruction(&Instruction::End);
    code.function(&get_addr);

    module
        .section(&types)
        .section(&functions)
        .section(&shared_memory_section())
        .section(&exports)
        .section(&code);
}

fn write_uleb(out: &mut Vec<u8>, mut v: u32) {
    loop {
        let mut byte = (v & 0x7f) as u8;
        v >>= 7;
        if v != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if v == 0 {
            break;
        }
    }
}

/// Parse `module_bytes` and return the code-section-content byte offset of the
/// immediate of every `i32.const flag_value` — the coordinate space a
/// `reloc.CODE` MEMORY_ADDR entry uses (`opcode_pos - code_content_start + 1`,
/// matching how meld's rewriter walks operators over the sliced code section).
fn find_i32const_reloc_offsets(module_bytes: &[u8], flag_value: i32) -> Vec<u32> {
    let mut code_start = None;
    let mut offsets = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(module_bytes) {
        match payload.expect("payload") {
            wasmparser::Payload::CodeSectionStart { range, .. } => code_start = Some(range.start),
            wasmparser::Payload::CodeSectionEntry(body) => {
                let cs = code_start.expect("code section start seen first");
                for item in body
                    .get_operators_reader()
                    .expect("operators")
                    .into_iter_with_offsets()
                {
                    let (op, pos) = item.expect("operator");
                    if let wasmparser::Operator::I32Const { value } = op
                        && value == flag_value
                    {
                        offsets.push((pos - cs + 1) as u32);
                    }
                }
            }
            _ => {}
        }
    }
    offsets
}

/// Build a `reloc.CODE` custom-section body flagging each offset as a
/// `MemoryAddrSleb` site (`type=4, offset, index=0, addend=0`).
fn build_reloc_code_body(offsets: &[u32]) -> Vec<u8> {
    let mut body = Vec::new();
    write_uleb(&mut body, 3); // target section index (cosmetic — consumer ignores it)
    write_uleb(&mut body, offsets.len() as u32);
    for &off in offsets {
        body.push(4u8); // R_WASM_MEMORY_ADDR_SLEB
        write_uleb(&mut body, off);
        write_uleb(&mut body, 0); // symbol index
        body.push(0u8); // addend = 0 (sleb)
    }
    body
}

/// The reloc module wrapped as a component. Built in two passes: a dry build to
/// locate the address-literal offsets, then the real build with a `linking`
/// (version 2) and `reloc.CODE` custom section appended. Custom sections sit
/// after the code section, so appending them does not shift the offsets found
/// in the dry pass.
fn build_reloc_component() -> Vec<u8> {
    let mut dry = Module::new();
    add_reloc_module_sections(&mut dry);
    let dry_bytes = dry.finish();
    let offsets = find_i32const_reloc_offsets(&dry_bytes, RELOC_ADDR);
    assert_eq!(offsets.len(), 3, "three i32.const address literals to flag");
    let reloc_code = build_reloc_code_body(&offsets);

    let mut module = Module::new();
    add_reloc_module_sections(&mut module);
    module.section(&CustomSection {
        name: "linking".into(),
        data: vec![0x02].into(), // version 2, no subsections
    });
    module.section(&CustomSection {
        name: "reloc.CODE".into(),
        data: reloc_code.into(),
    });
    build_component(module)
}

/// True if the core module `bytes` carries a top-level custom section `name`.
fn has_custom_section(bytes: &[u8], name: &str) -> bool {
    wasmparser::Parser::new(0)
        .parse_all(bytes)
        .any(|p| matches!(p, Ok(wasmparser::Payload::CustomSection(r)) if r.name() == name))
}

/// #326 behavioural oracle: fusing a relocatable module into shared memory at a
/// non-zero base must rebase its absolute `i32.const` addresses.
///
/// The discriminator is `b_get_addr`, which returns the absolute address of the
/// module's `BUF` as a *value* (what canonical-ABI code does when it takes
/// `&BUF` to pass to `memcpy`). `b_store` first writes `0xAB` at that address.
///
/// * BEFORE the reloc-consumer fix the `i32.const RELOC_ADDR` is left
///   un-rebased, so `b_get_addr` returns `RELOC_ADDR` (0x100) — an address in
///   component-a's window. `read_shared` at that returned address reads `0`
///   (component-a never wrote there): the two assertions below FAIL.
///   (Note: `b_store`'s own byte still lands at `base+RELOC_ADDR` even pre-fix
///   because the legacy *access-point* rebasing rebases the store's `memarg`
///   offset — which is exactly why a store-and-read-back oracle would NOT
///   distinguish, and why the discriminator uses the address as a value.)
/// * AFTER the fix `b_get_addr` returns `base+RELOC_ADDR`, and `read_shared` at
///   that address reads back the `0xAB` written by `b_store`.
#[test]
fn test_326_reloc_const_rebasing_end_to_end() {
    let component_a = build_component(build_reloc_base_module());
    let component_b = build_reloc_component();

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component_a, Some("component-a"))
        .unwrap();
    fuser
        .add_component_named(&component_b, Some("component-b"))
        .unwrap();

    let fused = fuser.fuse().unwrap();

    // Part C: the consumed reloc/linking metadata must not survive fusion.
    assert!(
        !has_custom_section(&fused, "reloc.CODE"),
        "reloc.CODE must be stripped from the fused output"
    );
    assert!(
        !has_custom_section(&fused, "linking"),
        "linking must be stripped from the fused output"
    );

    let mut engine_config = Config::new();
    engine_config.wasm_threads(true);
    engine_config.shared_memory(true);
    engine_config.wasm_bulk_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let b_store = instance
        .get_typed_func::<(), ()>(&mut store, "b_store")
        .unwrap();
    let b_load = instance
        .get_typed_func::<(), i32>(&mut store, "b_load")
        .unwrap();
    let b_get_addr = instance
        .get_typed_func::<(), i32>(&mut store, "b_get_addr")
        .unwrap();

    b_store.call(&mut store, ()).unwrap();

    let memory = instance
        .get_shared_memory(&mut store, "memory")
        .expect("shared memory export not found");
    let base = WASM_PAGE_SIZE; // component-b is placed at page 1

    // DISCRIMINATOR 1: the address literal, used as a value, must be rebased.
    let addr = b_get_addr.call(&mut store, ()).unwrap();
    assert_eq!(
        addr,
        (base + RELOC_ADDR as usize) as i32,
        "b_get_addr must return the REBASED address base+0x100 (pre-fix: 0x100)"
    );

    // DISCRIMINATOR 2 (behavioural): the address the module computes for BUF
    // must actually point at the byte `b_store` wrote. Pre-fix `addr` is 0x100
    // (component-a's window, never written) so this reads 0.
    let via_addr = read_shared(&memory, addr as usize, 1);
    assert_eq!(
        via_addr,
        vec![RELOC_VAL as u8],
        "the module's computed BUF address must point at the written byte"
    );

    // Sanity: the store landed at the rebased window and `b_load` reads it back.
    // (These pass pre-fix too, via the legacy access-point memarg rebasing.)
    assert_eq!(
        read_shared(&memory, base + RELOC_ADDR as usize, 1),
        vec![RELOC_VAL as u8]
    );
    assert_eq!(b_load.call(&mut store, ()).unwrap(), RELOC_VAL);
}

/// #326 Part A (path-F): a module doing direct memory access, placed at a
/// non-zero shared-memory base but carrying NO relocation metadata, cannot have
/// its absolute addresses rebased safely, so fusion must hard-fail with
/// `MissingRelocMetadata` rather than silently emit a colliding module.
#[test]
fn test_326_shared_rebase_without_relocs_hard_errors() {
    let component_a = build_component(build_reloc_base_module());

    // Same direct-memory module as the oracle, but WITHOUT the reloc.CODE /
    // linking custom sections.
    let mut module = Module::new();
    add_reloc_module_sections(&mut module);
    let component_b = build_component(module);

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component_a, Some("component-a"))
        .unwrap();
    fuser
        .add_component_named(&component_b, Some("non-relocatable"))
        .unwrap();

    let err = fuser
        .fuse()
        .expect_err("shared+rebase of a non-relocatable direct-memory module must fail");
    assert!(
        matches!(err, meld_core::Error::MissingRelocMetadata { .. }),
        "expected MissingRelocMetadata, got: {err:?}"
    );
}

/// #351 backstop: real-world components whose `reloc.CODE` offsets are STALE
/// relative to the emitted (minimal-LEB) code — produced by clang 22.1.4 +
/// wit-component 0.245.1, which relaxed the address immediates 5-byte→3-byte
/// without rewriting the reloc offsets (drift +2 per preceding memory-address
/// reloc; upstream pulseengine/wasm-tools#3).
///
/// The trailing `ptr-b` `i32.const` site (`SLEB@42`) drifts PAST its operator's
/// byte range, so pre-backstop meld silently left it un-rebased and `ptr-b`
/// returned `0x10000` (aliasing component-a's window) — grounded runtime bug on
/// v0.41.1. meld must now hard-fail with `MisalignedReloc` rather than emit a
/// plausible-but-wrong module. Fixtures are the exact bytes from the issue
/// (`b.wasm` sha256 `481c36…d3a3`).
#[test]
fn test_351_stale_reloc_offsets_hard_error() {
    let component_a =
        std::fs::read("../tests/reloc351/a.wasm").expect("meld#351 fixture a.wasm missing");
    let component_b =
        std::fs::read("../tests/reloc351/b.wasm").expect("meld#351 fixture b.wasm missing");

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component_a, Some("a.wasm"))
        .unwrap();
    fuser
        .add_component_named(&component_b, Some("b.wasm"))
        .unwrap();

    let err = fuser
        .fuse()
        .expect_err("stale-reloc module must hard-fail, not silently miscompile");
    match err {
        meld_core::Error::MisalignedReloc { offset, .. } => {
            assert_eq!(
                offset, 42,
                "the drifted ptr-b SLEB site is at code offset 42"
            );
        }
        other => panic!("expected MisalignedReloc at offset 42, got: {other:?}"),
    }
}
