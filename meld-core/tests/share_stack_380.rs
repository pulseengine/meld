//! SR-66 / #380 oracle: shared shadow-stack packing (`--share-stack`).
//!
//! `--pack-rebase` (SR-57) already compacts each provider to
//! `align16(__heap_base)`, but under a stack-first layout that still keeps every
//! provider's dead `[0, __stack_pointer)` shadow-stack reservation inside its
//! packed extent — N providers reserve N stacks for state only ONE of them uses
//! at a time (gale's F100 8 KiB budget misses by ~140 B on exactly this). This
//! is meld's LAST MCU-fit gap.
//!
//! `--share-stack` reserves ONE shadow-stack region of `max_i(sp_i)` at fused
//! base 0 and packs each provider's data (which begins at `sp_i`) immediately
//! above it — `stride = align16(extent_i - sp_i)`, `base_i = align16(max sp) -
//! sp_i` — coalescing every `__stack_pointer` onto one survivor initialised to
//! the region top.
//!
//! Differential oracle (Part-A overlap passing is necessary but not sufficient):
//!   1. SIZE — the actual claim: three providers that stride to 2 pages under
//!      `--pack-rebase` pack into 1 under `--share-stack` (both numbers asserted).
//!   2. DATA isolation on wasmtime — each provider reads back ITS OWN data
//!      sentinel; a `base_i` that placed the shared stack over data, or an
//!      under-subtracted extent, surfaces as a wrong read.
//!   3. STACK sharing — each provider writes+reads its own sentinel through the
//!      coalesced SP into the shared region, and a subsequent data read is still
//!      intact (the stack region and the data region do not collide).
//!   4. STRUCTURE — exactly one mutable-`i32` (`__stack_pointer`) global survives,
//!      initialised to the shared region top `S_raw`.
//!   5. GATES — a provider missing the `__stack_pointer` marker, or one whose
//!      data sits BELOW its stack pointer (not stack-first), hard-fails loudly.

// rivet: verifies SR-90

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, ConstExpr, CustomSection, DataSection, DataSegment, DataSegmentMode,
    ExportKind, ExportSection, Function, FunctionSection, GlobalSection, GlobalType, Instruction,
    MemArg, MemorySection, MemoryType, Module, ModuleSection, NameMap, NameSection, TypeSection,
    ValType,
};
use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};

/// Shared shadow-stack top each provider's `__stack_pointer` initialises to.
/// Deliberately large (not a few KiB) so the packed size claim discriminates at
/// PAGE granularity: a tiny sp would fit one page either way.
const SP_INIT: i32 = 30_000;
/// Provider data lives ABOVE the stack pointer (stack-first layout), at
/// `SP_INIT + 0x100`. A `base_i` bug that overlapped the stack region with data
/// would corrupt this.
const DATA_ADDR: i32 = SP_INIT + 0x100; // 30256
/// `__heap_base` = top of static data ([DATA_ADDR, DATA_ADDR+1)).
const HEAP_BASE: i32 = DATA_ADDR + 1; // 30257
/// Per-call scratch slot the stack exercise touches, `[sp-16]`.
const STACK_SLOT_DELTA: i32 = 16;

/// What `__stack_pointer` a provider carries (#446).
#[derive(Clone, Copy, PartialEq, Debug)]
enum Sp {
    /// A DEFINED, mutable `i32` global with a single `i32.const` init, named in
    /// the `name` section — the gale-shaped signal meld can read and place.
    Usable,
    /// NO `__stack_pointer` global at all, which is how `wasm-ld` leaves a
    /// module whose code never touches the shadow stack. Genuinely stackless.
    Absent,
    /// A global NAMED `__stack_pointer` that meld cannot read as a marker —
    /// immutable here. This case must keep failing loud, and it is what stops
    /// "absence means stackless" from swallowing a real marker meld merely
    /// failed to interpret. Without this control, the #446 change would be
    /// indistinguishable from deleting the check.
    Unusable,
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

/// Code-section byte offsets of every `i32.const flag_value` immediate — the
/// coordinate a `reloc.CODE` MEMORY_ADDR entry uses.
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

fn build_reloc_code_body(offsets: &[u32]) -> Vec<u8> {
    let mut body = Vec::new();
    write_uleb(&mut body, 3); // target section index (consumer ignores it)
    write_uleb(&mut body, offsets.len() as u32);
    for &off in offsets {
        body.push(4u8); // R_WASM_MEMORY_ADDR_SLEB
        write_uleb(&mut body, off);
        write_uleb(&mut body, 0); // symbol index
        body.push(0u8); // addend = 0 (sleb)
    }
    body
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

/// A stack-first provider: shared 1-page memory; a mutable `__stack_pointer`
/// global (named in the `name` section, the gale-shaped signal) initialised to
/// `sp_init`; an immutable exported `__heap_base` marker; a `data_addr` sentinel
/// ABOVE the stack; `read_<tag>` loads it through a reloc-flagged absolute
/// address; `stack_<tag>` writes+reads `stack_sentinel` at `[sp-16]` through the
/// SP and restores it. `has_sp` / `data_addr` let the negative controls drop the
/// marker or place data below the stack.
fn build_stack_provider(
    tag: &str,
    data_sentinel: u8,
    stack_sentinel: i32,
    sp_init: i32,
    export_memory: bool,
    sp_kind: Sp,
    data_addr: i32,
) -> Vec<u8> {
    let byte_memarg = MemArg {
        offset: 0,
        align: 0, // i32.load8_u — natural alignment of a 1-byte access is 0
        memory_index: 0,
    };
    let word_memarg = MemArg {
        offset: 0,
        align: 2, // i32.load/store — natural alignment of a 4-byte access is 2
        memory_index: 0,
    };

    let add_sections = |module: &mut Module| {
        let mut types = TypeSection::new();
        types.ty().function([], [ValType::I32]); // () -> i32

        let mut functions = FunctionSection::new();
        functions.function(0); // read_<tag>
        functions.function(0); // stack_<tag>

        // global 0: immutable `__heap_base` (exported — supplier precondition).
        // global 1: mutable `__stack_pointer` (named, not exported) when has_sp.
        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: false,
                shared: false,
            },
            &ConstExpr::i32_const(HEAP_BASE),
        );
        // Absent: no global at all. Unusable: present and named, but IMMUTABLE,
        // so meld's marker read rejects it while the name lookup still finds it.
        if sp_kind != Sp::Absent {
            globals.global(
                GlobalType {
                    val_type: ValType::I32,
                    mutable: sp_kind == Sp::Usable,
                    shared: false,
                },
                &ConstExpr::i32_const(sp_init),
            );
        }

        let mut exports = ExportSection::new();
        exports.export(&format!("read_{tag}"), ExportKind::Func, 0);
        exports.export(&format!("stack_{tag}"), ExportKind::Func, 1);
        exports.export("__heap_base", ExportKind::Global, 0);
        if export_memory {
            exports.export("memory", ExportKind::Memory, 0);
        }

        let mut code = CodeSection::new();
        // read_<tag>: load the data sentinel at a reloc-flagged absolute addr.
        let mut read = Function::new([]);
        read.instruction(&Instruction::I32Const(data_addr));
        read.instruction(&Instruction::I32Load8U(byte_memarg));
        read.instruction(&Instruction::End);
        code.function(&read);
        // stack_<tag>: sp -= 16; mem[sp] = stack_sentinel; load it back; sp += 16.
        // With a Usable SP the pointer is global 1. Otherwise the body is a
        // no-op returning 0 — which is what a genuinely stackless thin
        // forwarder looks like, and it now EXECUTES (#446) rather than only
        // feeding a control that errored before instantiation.
        let mut stack = Function::new([]);
        if sp_kind == Sp::Usable {
            stack.instruction(&Instruction::GlobalGet(1));
            stack.instruction(&Instruction::I32Const(STACK_SLOT_DELTA));
            stack.instruction(&Instruction::I32Sub);
            stack.instruction(&Instruction::GlobalSet(1));
            stack.instruction(&Instruction::GlobalGet(1));
            stack.instruction(&Instruction::I32Const(stack_sentinel));
            stack.instruction(&Instruction::I32Store(word_memarg));
            stack.instruction(&Instruction::GlobalGet(1));
            stack.instruction(&Instruction::I32Load(word_memarg));
            stack.instruction(&Instruction::GlobalGet(1));
            stack.instruction(&Instruction::I32Const(STACK_SLOT_DELTA));
            stack.instruction(&Instruction::I32Add);
            stack.instruction(&Instruction::GlobalSet(1));
        } else {
            stack.instruction(&Instruction::I32Const(0));
        }
        stack.instruction(&Instruction::End);
        code.function(&stack);

        let mut data = DataSection::new();
        data.segment(DataSegment {
            mode: DataSegmentMode::Active {
                memory_index: 0,
                offset: &ConstExpr::i32_const(data_addr),
            },
            data: [data_sentinel],
        });

        module.section(&types).section(&functions);
        module.section(&shared_memory_section());
        module.section(&globals).section(&exports).section(&code);
        module.section(&data);
        // name section: name the SP global `__stack_pointer` (the gale signal).
        // Named for Unusable too — that is the whole point of the control: the
        // name resolves, the marker read does not.
        if sp_kind != Sp::Absent {
            let mut gnames = NameMap::new();
            gnames.append(1, "__stack_pointer");
            let mut names = NameSection::new();
            names.globals(&gnames);
            module.section(&names);
        }
    };

    // Dry build to locate the reloc-able address literal (data read), then the
    // real build with linking + reloc.CODE appended after the code section.
    let mut dry = Module::new();
    add_sections(&mut dry);
    let offsets = find_i32const_reloc_offsets(&dry.finish(), data_addr);
    assert_eq!(
        offsets.len(),
        1,
        "one address literal to flag in read_{tag}"
    );
    let reloc_code = build_reloc_code_body(&offsets);

    let mut module = Module::new();
    add_sections(&mut module);
    module.section(&CustomSection {
        name: "linking".into(),
        data: vec![0x02].into(),
    });
    module.section(&CustomSection {
        name: "reloc.CODE".into(),
        data: reloc_code.into(),
    });

    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

/// A normal stack-first provider with equal `sp_init = SP_INIT`.
fn provider(tag: &str, data_sentinel: u8, stack_sentinel: i32, export_memory: bool) -> Vec<u8> {
    build_stack_provider(
        tag,
        data_sentinel,
        stack_sentinel,
        SP_INIT,
        export_memory,
        Sp::Usable,
        DATA_ADDR,
    )
}

/// A minimal stack-first provider for the byte-level F100 budget check: SP +
/// heap-base markers, a `data_len`-byte data segment starting AT `sp` (data-only,
/// no code memory access → no reloc needed), `__heap_base = sp + data_len`. Used
/// to verify the actual size CLAIM (not just the page-granular mechanism): the
/// packed footprint of thin drivers crosses the 8 KiB SRAM budget while the
/// shared-stack footprint stays under it.
fn build_f100_provider(tag: &str, sp: i32, data_len: usize) -> Vec<u8> {
    let heap_base = sp + data_len as i32;

    let mut types = TypeSection::new();
    types.ty().function([], []); // nop: () -> ()
    let mut functions = FunctionSection::new();
    functions.function(0);

    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: false,
            shared: false,
        },
        &ConstExpr::i32_const(heap_base),
    );
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(sp),
    );

    let mut exports = ExportSection::new();
    exports.export(&format!("nop_{tag}"), ExportKind::Func, 0);
    exports.export("__heap_base", ExportKind::Global, 0);

    let mut code = CodeSection::new();
    let mut nop = Function::new([]);
    nop.instruction(&Instruction::End);
    code.function(&nop);

    let mut data = DataSection::new();
    data.segment(DataSegment {
        mode: DataSegmentMode::Active {
            memory_index: 0,
            offset: &ConstExpr::i32_const(sp), // data AT sp (stack-first, start == sp)
        },
        data: std::iter::repeat_n(0xCDu8, data_len),
    });

    let mut module = Module::new();
    module.section(&types).section(&functions);
    module.section(&shared_memory_section());
    module.section(&globals).section(&exports).section(&code);
    module.section(&data);
    let mut gnames = NameMap::new();
    gnames.append(1, "__stack_pointer");
    let mut names = NameSection::new();
    names.globals(&gnames);
    module.section(&names);

    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

/// A stack-first provider with the SP + heap-base markers and a data segment,
/// but whose only memory access is a BULK op (`memory.fill`) with an sp-derived
/// destination, and which carries NO reloc metadata. This is the Mythos SR-66
/// finding: `rewriter::append_rebased_address` would shift the sp-derived operand
/// by `base_i` on the no-reloc path, silently corrupting it under the shared
/// stack. `--share-stack` must reject it (the fix gates on
/// `has_bulk_op && !has_reloc`).
fn build_bulk_noreloc_provider(tag: &str) -> Vec<u8> {
    let mut types = TypeSection::new();
    types.ty().function([], []); // fill_<tag>: () -> ()

    let mut functions = FunctionSection::new();
    functions.function(0);

    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: false,
            shared: false,
        },
        &ConstExpr::i32_const(HEAP_BASE),
    );
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(SP_INIT),
    );

    let mut exports = ExportSection::new();
    exports.export(&format!("fill_{tag}"), ExportKind::Func, 0);
    exports.export("__heap_base", ExportKind::Global, 0);

    let mut code = CodeSection::new();
    let mut fill = Function::new([]);
    // dst = sp - 64 (an sp-derived address that must NOT be rebased)
    fill.instruction(&Instruction::GlobalGet(1));
    fill.instruction(&Instruction::I32Const(64));
    fill.instruction(&Instruction::I32Sub);
    fill.instruction(&Instruction::I32Const(0xEE)); // value
    fill.instruction(&Instruction::I32Const(4)); // n
    fill.instruction(&Instruction::MemoryFill(0));
    fill.instruction(&Instruction::End);
    code.function(&fill);

    let mut data = DataSection::new();
    data.segment(DataSegment {
        mode: DataSegmentMode::Active {
            memory_index: 0,
            offset: &ConstExpr::i32_const(DATA_ADDR),
        },
        data: [0xAB],
    });

    let mut module = Module::new();
    module.section(&types).section(&functions);
    module.section(&shared_memory_section());
    module.section(&globals).section(&exports).section(&code);
    module.section(&data);
    // name the SP global — but NO linking / reloc.CODE sections.
    let mut gnames = NameMap::new();
    gnames.append(1, "__stack_pointer");
    let mut names = NameSection::new();
    names.globals(&gnames);
    module.section(&names);

    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

fn fuse_three(
    providers: [Vec<u8>; 3],
    pack_rebase: bool,
    share_stack: bool,
) -> Result<Vec<u8>, String> {
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        pack_rebase,
        share_stack,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    let [a, b, c] = providers;
    fuser.add_component_named(&a, Some("comp-a")).unwrap();
    fuser.add_component_named(&b, Some("comp-b")).unwrap();
    fuser.add_component_named(&c, Some("comp-c")).unwrap();
    fuser.fuse().map_err(|e| e.to_string())
}

fn fused_memory_min_pages(bytes: &[u8]) -> u64 {
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::MemorySection(reader) = payload.expect("payload") {
            let mem = reader
                .into_iter()
                .next()
                .expect("a memory")
                .expect("memory");
            return mem.initial;
        }
    }
    panic!("fused module has no memory section");
}

/// Every defined global's `(mutable, i32.const init)` in the fused module.
fn fused_globals(bytes: &[u8]) -> Vec<(bool, Option<i32>)> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::GlobalSection(reader) = payload.expect("payload") {
            for g in reader {
                let g = g.expect("global");
                let mutable = g.ty.mutable && g.ty.content_type == wasmparser::ValType::I32;
                let init = g
                    .init_expr
                    .get_operators_reader()
                    .into_iter()
                    .flatten()
                    .find_map(|op| match op {
                        wasmparser::Operator::I32Const { value } => Some(value),
                        _ => None,
                    });
                out.push((mutable, init));
            }
        }
    }
    out
}

/// Active data-segment absolute offsets (constant i32) in the fused module.
fn fused_data_offsets(bytes: &[u8]) -> Vec<i32> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::DataSection(reader) = payload.expect("payload") {
            for seg in reader {
                let seg = seg.expect("data segment");
                if let wasmparser::DataKind::Active { offset_expr, .. } = seg.kind {
                    for op in offset_expr.get_operators_reader() {
                        if let Ok(wasmparser::Operator::I32Const { value }) = op {
                            out.push(value);
                        }
                    }
                }
            }
        }
    }
    out.sort_unstable();
    out
}

fn instantiate(bytes: &[u8]) -> (Store<()>, Instance) {
    let mut cfg = Config::new();
    cfg.wasm_threads(true);
    cfg.shared_memory(true);
    cfg.wasm_bulk_memory(true);
    let engine = Engine::new(&cfg).unwrap();
    let module = RuntimeModule::new(&engine, bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();
    (store, instance)
}

fn call(store: &mut Store<()>, instance: &Instance, name: &str) -> i32 {
    instance
        .get_typed_func::<(), i32>(&mut *store, name)
        .unwrap_or_else(|e| panic!("export {name}: {e}"))
        .call(&mut *store, ())
        .unwrap()
}

#[test]
fn share_stack_reclaims_and_reads_own_data() {
    let mk = || {
        [
            provider("a", 0xA1, 0x1111, true),
            provider("b", 0xB2, 0x2222, false),
            provider("c", 0xC3, 0x3333, false),
        ]
    };
    let packed = fuse_three(mk(), true, false).expect("pack-rebase fusion");
    let shared = fuse_three(mk(), false, true).expect("share-stack fusion");

    // (1) SIZE — the claim. Under --pack-rebase each provider strides
    // align16(30257)=30272, so 3 span 2 pages; under --share-stack the shared
    // 30000-byte stack + 3×align16(257)=272 = 30816 fits ONE page.
    let packed_pages = fused_memory_min_pages(&packed);
    let shared_pages = fused_memory_min_pages(&shared);
    eprintln!(
        "SR-66: --pack-rebase = {packed_pages} page(s), --share-stack = {shared_pages} page(s)"
    );
    assert_eq!(
        packed_pages, 2,
        "pack-rebase keeps N dead stack reservations"
    );
    assert_eq!(shared_pages, 1, "share-stack reclaims them into one page");
    assert!(
        shared_pages < packed_pages,
        "sharing must shrink the reservation"
    );

    // (4) STRUCTURE — exactly one mutable-i32 (__stack_pointer) global survives,
    // initialised to the shared region top S_raw = SP_INIT.
    let muts: Vec<_> = fused_globals(&shared)
        .into_iter()
        .filter(|(m, _)| *m)
        .collect();
    assert_eq!(
        muts.len(),
        1,
        "the three SPs coalesce to one survivor, got {muts:?}"
    );
    assert_eq!(
        muts[0].1,
        Some(SP_INIT),
        "survivor SP init must be the shared region top"
    );

    // Byte-exact layout: data at align16(S_raw) + (DATA_ADDR - sp) + i*stride.
    let offsets = fused_data_offsets(&shared);
    assert_eq!(
        offsets,
        vec![30256, 30528, 30800],
        "packed data offsets above the shared stack"
    );

    // (2)+(3) Execution: shared stack is usable per-provider AND data isolated.
    let (mut store, instance) = instantiate(&shared);
    for (stack_fn, want_stack, read_fn, want_data) in [
        ("stack_a", 0x1111, "read_a", 0xA1),
        ("stack_b", 0x2222, "read_b", 0xB2),
        ("stack_c", 0x3333, "read_c", 0xC3),
    ] {
        let got_stack = call(&mut store, &instance, stack_fn);
        assert_eq!(
            got_stack, want_stack,
            "{stack_fn} must read back its own stack sentinel"
        );
        let got_data = call(&mut store, &instance, read_fn);
        assert_eq!(
            got_data, want_data,
            "{read_fn} must still read its own data sentinel — the shared stack write must not touch data"
        );
    }
    // Data intact after all stack traffic.
    for (read_fn, want) in [("read_a", 0xA1), ("read_b", 0xB2), ("read_c", 0xC3)] {
        assert_eq!(
            call(&mut store, &instance, read_fn),
            want,
            "{read_fn} corrupted post-hoc"
        );
    }
}

#[test]
fn share_stack_unequal_inits_coalesce_to_max() {
    // Providers with DIFFERENT sp inits (30000/29000/28000). --share-stack
    // coalesces them regardless of init (unlike the equal-init-only default
    // coalescer) onto one survivor initialised to the MAX = the shared top.
    let a = build_stack_provider("a", 0xA1, 0x1111, 30_000, true, Sp::Usable, 30_000 + 0x100);
    let b = build_stack_provider("b", 0xB2, 0x2222, 29_000, false, Sp::Usable, 29_000 + 0x100);
    let c = build_stack_provider("c", 0xC3, 0x3333, 28_000, false, Sp::Usable, 28_000 + 0x100);
    let shared = fuse_three([a, b, c], false, true).expect("share-stack fusion");

    let muts: Vec<_> = fused_globals(&shared)
        .into_iter()
        .filter(|(m, _)| *m)
        .collect();
    assert_eq!(
        muts.len(),
        1,
        "unequal SPs still coalesce to one survivor, got {muts:?}"
    );
    assert_eq!(
        muts[0].1,
        Some(30_000),
        "survivor init must be max(sp_i) = the shared region top"
    );

    let (mut store, instance) = instantiate(&shared);
    for (read_fn, want) in [("read_a", 0xA1), ("read_b", 0xB2), ("read_c", 0xC3)] {
        assert_eq!(
            call(&mut store, &instance, read_fn),
            want,
            "{read_fn} must read own data"
        );
    }
}

#[test]
fn share_stack_proceeds_for_a_stackless_provider() {
    // #446: provider "b" has NO `__stack_pointer` global at all — the shape
    // `wasm-ld` leaves when a module's code never touches the shadow stack
    // (gale's thin seam forwarders). It contributes no stack, so there is
    // nothing for --share-stack to collapse in it and nothing to relocate;
    // including it is a no-op and the fuse must PROCEED.
    //
    // This test previously asserted the opposite. It also passed for the wrong
    // reason: its only assertion was `err.contains("stack")`, which every
    // error from `share_stack_entry` satisfies via the `--share-stack:` prefix.
    // The error it was actually observing was neither the one it named nor the
    // sp gate — it was the dissolve's `found N __stack_pointer global(s) but M
    // rebased memory provider(s)` drift detector. Hence the specific
    // assertions below.
    let a = provider("a", 0xA1, 0x1111, true);
    let b = build_stack_provider("b", 0xB2, 0x2222, SP_INIT, false, Sp::Absent, DATA_ADDR);
    let c = provider("c", 0xC3, 0x3333, false);
    let fused = fuse_three([a, b, c], false, true)
        .expect("a provider with no __stack_pointer global at all must not fail the fuse");

    // RECORDED, not silently handled. A component that contributed nothing to
    // a safety envelope without saying so is how the envelope stops meaning
    // anything, so the attestation has to name it.
    let text = String::from_utf8_lossy(&fused);
    assert!(
        text.contains("shared-stack-stackless"),
        "the stackless provider must be recorded as such in the attestation \
         placements, so --explain can say which modules brought no stack"
    );
    // And the stack-carrying providers must still be recorded plainly, or the
    // assertion above could be satisfied by labelling everything stackless.
    assert_eq!(
        text.matches("\"strategy\":\"shared-stack\"").count(),
        2,
        "exactly the two stack-carrying providers keep the plain shared-stack \
         strategy; got: {}",
        text.matches("\"strategy\":\"shared-stack").count()
    );

    // DATA isolation still holds with a stackless module in the set: each
    // provider reads back ITS OWN sentinel. A base that overlapped the
    // stackless module's window with a neighbour's surfaces as a wrong read.
    let (mut store, instance) = instantiate(&fused);
    assert_eq!(
        call(&mut store, &instance, "read_a"),
        0xA1,
        "a reads its own"
    );
    assert_eq!(
        call(&mut store, &instance, "read_b"),
        0xB2,
        "b reads its own"
    );
    assert_eq!(
        call(&mut store, &instance, "read_c"),
        0xC3,
        "c reads its own"
    );
    // The stack-carrying providers still share the one region correctly, and a
    // data read afterwards is intact (stack and data did not collide).
    assert_eq!(call(&mut store, &instance, "stack_a"), 0x1111);
    assert_eq!(call(&mut store, &instance, "stack_c"), 0x3333);
    assert_eq!(
        call(&mut store, &instance, "read_b"),
        0xB2,
        "the stackless provider's data must survive the others' stack traffic"
    );
}

#[test]
fn share_stack_rejects_an_unusable_stack_pointer() {
    // The control that keeps #446 honest. Provider "b" HAS a global named
    // `__stack_pointer`, so the name lookup finds it, but it is immutable and
    // therefore not a marker meld can place. "Absence means stackless" must
    // not swallow a real marker meld merely failed to interpret, so this still
    // fails loud.
    //
    // Without this test the #446 change would be indistinguishable from
    // deleting the gate.
    let a = provider("a", 0xA1, 0x1111, true);
    let b = build_stack_provider("b", 0xB2, 0x2222, SP_INIT, false, Sp::Unusable, DATA_ADDR);
    let c = provider("c", 0xC3, 0x3333, false);
    let err = fuse_three([a, b, c], false, true)
        .expect_err("a present-but-unreadable __stack_pointer must still be refused");
    // Specific: not `contains("stack")`, which every error from this path
    // satisfies through the `--share-stack:` prefix — the exact looseness that
    // let the old version of this test pass on an unrelated error.
    assert!(
        err.contains("HAS a") && err.contains("cannot read it as a marker"),
        "the error must say the marker is PRESENT and unusable, distinguishing \
         it from the stackless case, got: {err}"
    );
}

#[test]
fn share_stack_rejects_an_all_stackless_set() {
    // Every provider stackless: there is no shadow stack to collapse, so the
    // flag cannot do what it was asked. Refuse with that reason rather than
    // emit a fused artifact whose --share-stack did nothing.
    let a = build_stack_provider("a", 0xA1, 0x1111, SP_INIT, true, Sp::Absent, DATA_ADDR);
    let b = build_stack_provider("b", 0xB2, 0x2222, SP_INIT, false, Sp::Absent, DATA_ADDR);
    let c = build_stack_provider("c", 0xC3, 0x3333, SP_INIT, false, Sp::Absent, DATA_ADDR);
    let err = fuse_three([a, b, c], false, true)
        .expect_err("--share-stack over an all-stackless set must be refused");
    assert!(
        err.contains("all 3 fused module(s) are stackless"),
        "the error must say the whole set is stackless and the flag has nothing \
         to do, got: {err}"
    );
}

#[test]
fn share_stack_rejects_data_below_stack_pointer() {
    // Provider "b" places its data BELOW the stack pointer (not stack-first):
    // subtracting the [0, sp) stack region would cut into data → hard-fail.
    let a = provider("a", 0xA1, 0x1111, true);
    let b = build_stack_provider("b", 0xB2, 0x2222, SP_INIT, false, Sp::Usable, 0x40); // data at 64 < sp
    let c = provider("c", 0xC3, 0x3333, false);
    let err =
        fuse_three([a, b, c], false, true).expect_err("must reject a non-stack-first provider");
    assert!(
        err.contains("stack") || err.contains("below") || err.contains("data"),
        "error must explain the data-below-stack layout, got: {err}"
    );
}

#[test]
fn share_stack_rejects_bulk_op_without_relocs() {
    // Mythos SR-66 delta-pass finding: a bulk-only, NO-reloc provider whose
    // memory.fill uses an sp-derived destination would have that operand shifted
    // by base_i on the legacy no-reloc rebasing path (append_rebased_address),
    // silently writing base_i bytes off target into a neighbour's window — while
    // the shared stack is un-rebased. --share-stack must reject it (reloc-covered
    // providers skip that path and are sound; the fix gates on
    // has_bulk_op && !has_reloc). Confirmed at runtime by the review (the fill
    // landed at s_raw-64 + base_i instead of s_raw-64); this asserts the loud
    // refusal that replaces the corruption.
    let a = provider("a", 0xA1, 0x1111, true);
    let b = build_bulk_noreloc_provider("b");
    let c = provider("c", 0xC3, 0x3333, false);
    let err = fuse_three([a, b, c], false, true)
        .expect_err("must reject a bulk-only, no-reloc provider under --share-stack");
    assert!(
        err.contains("bulk") || err.contains("reloc"),
        "error must name the bulk-op / missing-reloc hazard, got: {err}"
    );

    // Control: the SAME provider is fine under plain --pack-rebase (the stack is
    // rebased with the module there, so append's +base_i is correct) — the
    // rejection is specific to --share-stack.
    let a2 = provider("a", 0xA1, 0x1111, true);
    let b2 = build_bulk_noreloc_provider("b");
    let c2 = provider("c", 0xC3, 0x3333, false);
    fuse_three([a2, b2, c2], true, false).expect("--pack-rebase accepts the bulk-only provider");
}

#[test]
fn share_stack_closes_the_f100_8kib_budget() {
    // The actual size CLAIM behind SR-66/#380, at the REAL shape (not the
    // page-discriminating SP_INIT=30000 used elsewhere): three thin drivers with
    // sp = 2048 and ~729 B of data each. The footprint is sub-page, so the wasm
    // memory minimum is 1 page either way — the F100 (8 KiB SRAM) budget is a
    // BYTE bound the downstream placer enforces on the packed extent. Assert it
    // byte-granularly from the fused data layout.
    const SP: i32 = 2048;
    const DATA_LEN: usize = 729; // align16 = 736; align16(SP+DATA_LEN=2777) = 2784
    const F100_SRAM: i32 = 8192;

    let mk = || {
        [
            build_f100_provider("a", SP, DATA_LEN),
            build_f100_provider("b", SP, DATA_LEN),
            build_f100_provider("c", SP, DATA_LEN),
        ]
    };
    let packed = fuse_three(mk(), true, false).expect("pack-rebase fusion");
    let shared = fuse_three(mk(), false, true).expect("share-stack fusion");

    // Footprint top = highest byte any provider's data reaches (data is the top
    // of each provider's window; the shared stack sits below at [0, sp)).
    let top = |bytes: &[u8]| -> i32 {
        fused_data_offsets(bytes).into_iter().max().unwrap() + DATA_LEN as i32
    };
    let packed_top = top(&packed);
    let shared_top = top(&shared);
    eprintln!(
        "SR-66 F100: --pack-rebase footprint = {packed_top} B, --share-stack = {shared_top} B (budget {F100_SRAM} B)"
    );

    // --pack-rebase strides each provider by align16(2777)=2784 → 3rd provider's
    // data reaches ~8345 B: OVER the 8 KiB budget (gale's blocker).
    assert!(
        packed_top > F100_SRAM,
        "--pack-rebase footprint {packed_top} B must exceed the {F100_SRAM} B budget (the gap #380 closes)"
    );
    // --share-stack reserves one 2048 B stack + 3×align16(729)=2208 B data →
    // ~4256 B: UNDER budget with margin.
    assert!(
        shared_top < F100_SRAM,
        "--share-stack footprint {shared_top} B must fit the {F100_SRAM} B budget"
    );
}
