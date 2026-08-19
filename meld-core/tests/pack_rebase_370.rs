//! SR-57 / #370 oracle: compact used-extent rebasing (`--pack-rebase`).
//!
//! Page-granular `--address-rebase` places each component at its declared
//! page count (≥ 64 KiB), so three thin drivers need ≥ 3 pages of address
//! space even though each uses a few hundred bytes — 16× too big for an 8 KiB
//! MCU (gale's blocker, #370). `--pack-rebase` strides by each component's
//! actual used data extent (16-byte aligned) and sizes the merged memory to
//! the packed total.
//!
//! This is a differential-execution oracle. Part A's overlap check passing is
//! necessary but NOT sufficient, so we additionally assert:
//!   1. the packed combined memory is materially smaller than page-granular
//!      (1 page vs 3) — the actual claim of the feature, both numbers printed;
//!   2. on wasmtime, each component reads back ITS OWN sentinel — a stride
//!      that were one `min_start` too short would surface here as a wrong read
//!      (the data lives well above address 0, at 0x100), not a silent pass.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, ConstExpr, CustomSection, DataCountSection, DataSection, DataSegment,
    DataSegmentMode, EntityType, ExportKind, ExportSection, Function, FunctionSection,
    GlobalSection, GlobalType, ImportSection, Instruction, MemArg, MemorySection, MemoryType,
    Module, ModuleSection, TypeSection, ValType,
};
use wasmtime::{
    Config, Engine, Instance, Linker, MemoryType as RuntimeMemoryType, Module as RuntimeModule,
    SharedMemory, Store,
};

/// Absolute address of each component's 1-byte sentinel data segment. Well
/// above 0 so a min_start bug reads wrong rather than passing by luck.
const DATA_ADDR: i32 = 0x100;

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

/// Code-section-content byte offset of the immediate of every
/// `i32.const flag_value` — the coordinate a `reloc.CODE` MEMORY_ADDR entry
/// uses. (Copied from `rebasing_end_to_end.rs`, the #326 reloc harness.)
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

/// `reloc.CODE` body flagging each offset as a `MemoryAddrSleb` site.
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

/// A component whose core module: defines a 1-page shared memory; seeds
/// `sentinel` at `DATA_ADDR` via an ACTIVE data segment (so it contributes to
/// the used extent); and exports `read_<tag>` which loads that byte through a
/// reloc-flagged absolute `i32.const DATA_ADDR`. `export_memory` makes exactly
/// one of the three expose the merged memory as "memory".
fn build_pack_component(tag: &str, sentinel: u8, export_memory: bool) -> Vec<u8> {
    let zero_memarg = MemArg {
        offset: 0,
        align: 0,
        memory_index: 0,
    };

    let add_sections = |module: &mut Module| {
        let mut types = TypeSection::new();
        types.ty().function([], [ValType::I32]); // () -> i32

        let mut functions = FunctionSection::new();
        functions.function(0);

        // Immutable-const `__heap_base` marker = top of static data ([DATA_ADDR,
        // DATA_ADDR+1) → DATA_ADDR+1). SR-57 compacts below the declared page
        // count ONLY with this marker (a supplier's `-Wl,--export=__heap_base`);
        // without it the module packs page-granular. #370.
        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: false,
                shared: false,
            },
            &ConstExpr::i32_const(DATA_ADDR + 1),
        );

        let mut exports = ExportSection::new();
        exports.export(&format!("read_{tag}"), ExportKind::Func, 0);
        exports.export("__heap_base", ExportKind::Global, 0);
        if export_memory {
            exports.export("memory", ExportKind::Memory, 0);
        }

        let mut code = CodeSection::new();
        let mut read = Function::new([]);
        read.instruction(&Instruction::I32Const(DATA_ADDR)); // reloc-flagged absolute address
        read.instruction(&Instruction::I32Load8U(zero_memarg));
        read.instruction(&Instruction::End);
        code.function(&read);

        let mut data = DataSection::new();
        data.segment(DataSegment {
            mode: DataSegmentMode::Active {
                memory_index: 0,
                offset: &ConstExpr::i32_const(DATA_ADDR),
            },
            data: [sentinel],
        });

        module
            .section(&types)
            .section(&functions)
            .section(&shared_memory_section())
            .section(&globals)
            .section(&exports)
            .section(&code)
            .section(&data);
    };

    // Dry build to locate the address literal, then the real build with the
    // linking + reloc.CODE custom sections appended (they sit after the code
    // section, so appending them does not shift the found offset).
    let mut dry = Module::new();
    add_sections(&mut dry);
    let offsets = find_i32const_reloc_offsets(&dry.finish(), DATA_ADDR);
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
        data: vec![0x02].into(), // version 2, no subsections
    });
    module.section(&CustomSection {
        name: "reloc.CODE".into(),
        data: reloc_code.into(),
    });

    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

/// Minimum size (in wasm pages) of the first memory declared by the fused core
/// module.
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

fn fuse(pack_rebase: bool) -> Vec<u8> {
    let a = build_pack_component("a", 0xA1, true);
    let b = build_pack_component("b", 0xB2, false);
    let c = build_pack_component("c", 0xC3, false);
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: !pack_rebase, // pack implies rebasing; keep page-granular explicit
        pack_rebase,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser.add_component_named(&a, Some("comp-a")).unwrap();
    fuser.add_component_named(&b, Some("comp-b")).unwrap();
    fuser.add_component_named(&c, Some("comp-c")).unwrap();
    fuser.fuse().expect("fusion")
}

#[test]
fn pack_rebase_is_compact_and_reads_own_data() {
    let page_granular = fuse(false);
    let packed = fuse(true);

    let pg_pages = fused_memory_min_pages(&page_granular);
    let packed_pages = fused_memory_min_pages(&packed);
    eprintln!(
        "SR-57: combined memory minimum — page-granular = {pg_pages} page(s), packed = {packed_pages} page(s)"
    );

    // (1) The size claim: three 1-page components stride to 3 pages page-
    // granular but pack into 1. Assert the hard inequality, not just "smaller".
    assert_eq!(pg_pages, 3, "page-granular reserves one page per component");
    assert_eq!(
        packed_pages, 1,
        "packed fits three thin components in one page"
    );
    assert!(
        packed_pages < pg_pages,
        "packing must shrink the reservation"
    );

    // (2) Differential execution: each component reads back ITS OWN sentinel.
    let mut engine_config = Config::new();
    engine_config.wasm_threads(true);
    engine_config.shared_memory(true);
    engine_config.wasm_bulk_memory(true);
    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &packed).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    for (name, want) in [("read_a", 0xA1), ("read_b", 0xB2), ("read_c", 0xC3)] {
        let f = instance
            .get_typed_func::<(), i32>(&mut store, name)
            .unwrap_or_else(|e| panic!("export {name}: {e}"));
        let got = f.call(&mut store, ()).unwrap();
        assert_eq!(
            got, want,
            "{name} must read its own sentinel {want:#x}, got {got:#x} — packed stride placed it over a neighbor"
        );
    }
}

/// A component whose sentinel lives in a PASSIVE data segment, written into
/// memory at `DATA_ADDR` at runtime by `init_<tag>` (`memory.init`) and read
/// back by `read_<tag>`. Both `i32.const DATA_ADDR` sites are reloc-flagged.
fn build_passive_component(tag: &str, sentinel: u8, export_memory: bool) -> Vec<u8> {
    let zero_memarg = MemArg {
        offset: 0,
        align: 0,
        memory_index: 0,
    };

    let add_sections = |module: &mut Module| {
        let mut types = TypeSection::new();
        types.ty().function([], []); // type 0: init: () -> ()
        types.ty().function([], [ValType::I32]); // type 1: read: () -> i32

        let mut functions = FunctionSection::new();
        functions.function(0);
        functions.function(1);

        let mut exports = ExportSection::new();
        exports.export(&format!("init_{tag}"), ExportKind::Func, 0);
        exports.export(&format!("read_{tag}"), ExportKind::Func, 1);
        if export_memory {
            exports.export("memory", ExportKind::Memory, 0);
        }

        let mut code = CodeSection::new();
        let mut init = Function::new([]);
        init.instruction(&Instruction::I32Const(DATA_ADDR)); // dst (reloc-flagged)
        init.instruction(&Instruction::I32Const(0)); // src offset in passive data
        init.instruction(&Instruction::I32Const(1)); // n bytes
        init.instruction(&Instruction::MemoryInit {
            mem: 0,
            data_index: 0,
        });
        init.instruction(&Instruction::DataDrop(0));
        init.instruction(&Instruction::End);
        code.function(&init);

        let mut read = Function::new([]);
        read.instruction(&Instruction::I32Const(DATA_ADDR)); // addr (reloc-flagged)
        read.instruction(&Instruction::I32Load8U(zero_memarg));
        read.instruction(&Instruction::End);
        code.function(&read);

        let mut data = DataSection::new();
        data.segment(DataSegment {
            mode: DataSegmentMode::Passive,
            data: [sentinel],
        });

        module
            .section(&types)
            .section(&functions)
            .section(&shared_memory_section())
            .section(&exports)
            .section(&DataCountSection { count: 1 })
            .section(&code)
            .section(&data);
    };

    let mut dry = Module::new();
    add_sections(&mut dry);
    let offsets = find_i32const_reloc_offsets(&dry.finish(), DATA_ADDR);
    assert_eq!(offsets.len(), 2, "init dst + read addr are reloc sites");
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

/// Regression (Mythos SR-57 finding): passive data + `memory.init` is a
/// supported placement under `--address-rebase`, but its used region is
/// invisible to an active-data-segment extent scan. Packing such modules by
/// their active extent (0) placed them all at base 0, so each `memory.init`
/// clobbered the last and all three read 0xC3. The fix treats a passive-
/// carrying module as unpackable and falls back to the page-granular stride,
/// keeping the components isolated. This test read a=b=c=0xC3 before the fix.
#[test]
fn pack_rebase_passive_init_does_not_clobber() {
    let a = build_passive_component("a", 0xA1, true);
    let b = build_passive_component("b", 0xB2, false);
    let c = build_passive_component("c", 0xC3, false);
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        pack_rebase: true,
        share_stack: false,
        profile: meld_core::Profile::Ecosystem,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser.add_component_named(&a, Some("comp-a")).unwrap();
    fuser.add_component_named(&b, Some("comp-b")).unwrap();
    fuser.add_component_named(&c, Some("comp-c")).unwrap();
    let fused = fuser.fuse().expect("fusion");

    let mut engine_config = Config::new();
    engine_config.wasm_threads(true);
    engine_config.shared_memory(true);
    engine_config.wasm_bulk_memory(true);
    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // Run every init (last-write-wins if they share a destination), then read.
    for init in ["init_a", "init_b", "init_c"] {
        instance
            .get_typed_func::<(), ()>(&mut store, init)
            .unwrap_or_else(|e| panic!("export {init}: {e}"))
            .call(&mut store, ())
            .unwrap();
    }
    for (read, want) in [("read_a", 0xA1), ("read_b", 0xB2), ("read_c", 0xC3)] {
        let got = instance
            .get_typed_func::<(), i32>(&mut store, read)
            .unwrap_or_else(|e| panic!("export {read}: {e}"))
            .call(&mut store, ())
            .unwrap();
        assert_eq!(
            got, want,
            "{read} must read its own sentinel {want:#x}, got {got:#x} — passive-init clobber (packed to base 0)"
        );
    }
}

/// A component with a memory but NO data segments: `store_<tag>` writes
/// `sentinel` at `DATA_ADDR` at runtime and `load_<tag>` reads it back, both
/// through reloc-flagged absolute `i32.const DATA_ADDR`. Its used region
/// (address `DATA_ADDR`) lives above its data extent (0) — the exact shape the
/// #326 reloc harness uses, supported under `--address-rebase`.
fn build_nodata_component(tag: &str, sentinel: i32, export_memory: bool) -> Vec<u8> {
    let zero_memarg = MemArg {
        offset: 0,
        align: 0,
        memory_index: 0,
    };

    let add_sections = |module: &mut Module| {
        let mut types = TypeSection::new();
        types.ty().function([], []); // type 0: store: () -> ()
        types.ty().function([], [ValType::I32]); // type 1: load: () -> i32

        let mut functions = FunctionSection::new();
        functions.function(0);
        functions.function(1);

        let mut exports = ExportSection::new();
        exports.export(&format!("store_{tag}"), ExportKind::Func, 0);
        exports.export(&format!("load_{tag}"), ExportKind::Func, 1);
        if export_memory {
            exports.export("memory", ExportKind::Memory, 0);
        }

        let mut code = CodeSection::new();
        let mut store = Function::new([]);
        store.instruction(&Instruction::I32Const(DATA_ADDR)); // dst (reloc-flagged)
        store.instruction(&Instruction::I32Const(sentinel));
        store.instruction(&Instruction::I32Store8(zero_memarg));
        store.instruction(&Instruction::End);
        code.function(&store);

        let mut load = Function::new([]);
        load.instruction(&Instruction::I32Const(DATA_ADDR)); // addr (reloc-flagged)
        load.instruction(&Instruction::I32Load8U(zero_memarg));
        load.instruction(&Instruction::End);
        code.function(&load);

        // No data section — this module has a memory but no static data.
        module
            .section(&types)
            .section(&functions)
            .section(&shared_memory_section())
            .section(&exports)
            .section(&code);
    };

    let mut dry = Module::new();
    add_sections(&mut dry);
    let offsets = find_i32const_reloc_offsets(&dry.finish(), DATA_ADDR);
    assert_eq!(offsets.len(), 2, "store dst + load addr are reloc sites");
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

/// Regression (CI auto-Mythos SR-57 finding): a module with a memory but NO
/// data segments reported extent Some(0), so its pack stride was
/// align16(0) = 0 and `next_base` never advanced — every such module packed to
/// base 0, aliasing their memories (both write+read DATA_ADDR → the second
/// store clobbers the first). The fix treats a zero-static-extent module as
/// unpackable (its real usage is invisible to a data-segment scan) and falls
/// back to page-granular, keeping the components isolated. Before the fix both
/// loads returned 0xB2.
#[test]
fn pack_rebase_nodata_module_does_not_alias() {
    let a = build_nodata_component("a", 0xA1, true);
    let b = build_nodata_component("b", 0xB2, false);
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        pack_rebase: true,
        share_stack: false,
        profile: meld_core::Profile::Ecosystem,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser.add_component_named(&a, Some("comp-a")).unwrap();
    fuser.add_component_named(&b, Some("comp-b")).unwrap();
    let fused = fuser.fuse().expect("fusion");

    let mut engine_config = Config::new();
    engine_config.wasm_threads(true);
    engine_config.shared_memory(true);
    engine_config.wasm_bulk_memory(true);
    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    for s in ["store_a", "store_b"] {
        instance
            .get_typed_func::<(), ()>(&mut store, s)
            .unwrap_or_else(|e| panic!("export {s}: {e}"))
            .call(&mut store, ())
            .unwrap();
    }
    for (load, want) in [("load_a", 0xA1), ("load_b", 0xB2)] {
        let got = instance
            .get_typed_func::<(), i32>(&mut store, load)
            .unwrap_or_else(|e| panic!("export {load}: {e}"))
            .call(&mut store, ())
            .unwrap();
        assert_eq!(
            got, want,
            "{load} must read its own value {want:#x}, got {got:#x} — no-data modules aliased at base 0"
        );
    }
}

// ---------------------------------------------------------------------------
// #370 (escalated): a `.bss`/arena region ABOVE the last data segment.
//
// A component seeds a tiny 1-byte data segment at `DATA_ADDR` (so its
// active-data extent D ≈ DATA_ADDR+1 is SMALL) but its real working set is a
// zero-init arena at `ARENA_ADDR` (well above D) that it `memory.fill`s with its
// own sentinel and reads back near the top — exactly relay#327's shape (a
// growing allocator replaced by a bounded static arena that lives in `.bss`,
// invisible to a data-segment scan).
//
// v0.43.0 packed by D, UNDER-reserving the arena: three components strided ~272
// bytes apart while each uses [ARENA_ADDR, ARENA_ADDR+ARENA_LEN) ≈ 6 KiB, so the
// arenas overlap and the last writer wins — a component reads a NEIGHBOUR's
// sentinel. SR-56 is active-data-only and cannot catch this. Before the #370
// extent fix, `read_a` returned 0xC3 (C's fill, the last writer over the
// overlap) instead of 0xA1.
//
// The fix makes compaction below the declared page count require an
// authoritative `__heap_base` marker:
//   * NO marker  → page-granular fallback (safe: each arena in its own page).
//   * marker present → compact to clamp(__heap_base, D..=declared), which
//     reserves the whole arena, so arenas stay disjoint AND the reservation
//     still shrinks below page-granular.

/// 1-byte data segment address — makes the visible active-data extent small.
const ARENA_DATA_ADDR: i32 = 0x100;
/// Zero-init arena base, far above the data extent (a `.bss` region).
const ARENA_ADDR: i32 = 0x1000;
/// Arena length in bytes (6 KiB > 1 page/16 would be too big; keep it inside a
/// page so page-granular still isolates it, but far larger than the ~272-byte
/// data stride so an under-reservation overlaps).
const ARENA_LEN: i32 = 0x1800;

/// Build an arena component. `marker` = `Some(top)` exports an immutable-const
/// `__heap_base` global (the supplier signal that enables compaction); `None`
/// omits it (forcing the safe page-granular fallback).
fn build_arena_component(
    tag: &str,
    sentinel: u8,
    export_memory: bool,
    marker: Option<i32>,
) -> Vec<u8> {
    let read_memarg = MemArg {
        offset: (ARENA_LEN - 1) as u64, // read the TOP byte of the arena
        align: 0,
        memory_index: 0,
    };

    let add_sections = |module: &mut Module| {
        let mut types = TypeSection::new();
        types.ty().function([], []); // type 0: fill: () -> ()
        types.ty().function([], [ValType::I32]); // type 1: read: () -> i32

        let mut functions = FunctionSection::new();
        functions.function(0);
        functions.function(1);

        let mut globals = GlobalSection::new();
        if let Some(top) = marker {
            globals.global(
                GlobalType {
                    val_type: ValType::I32,
                    mutable: false,
                    shared: false,
                },
                &ConstExpr::i32_const(top),
            );
        }

        let mut exports = ExportSection::new();
        exports.export(&format!("fill_{tag}"), ExportKind::Func, 0);
        exports.export(&format!("read_{tag}"), ExportKind::Func, 1);
        if marker.is_some() {
            exports.export("__heap_base", ExportKind::Global, 0);
        }
        if export_memory {
            exports.export("memory", ExportKind::Memory, 0);
        }

        let mut code = CodeSection::new();
        // fill: memory.fill(dst = ARENA_ADDR, val = sentinel, len = ARENA_LEN)
        let mut fill = Function::new([]);
        fill.instruction(&Instruction::I32Const(ARENA_ADDR)); // dst (reloc-flagged)
        fill.instruction(&Instruction::I32Const(i32::from(sentinel)));
        fill.instruction(&Instruction::I32Const(ARENA_LEN));
        fill.instruction(&Instruction::MemoryFill(0));
        fill.instruction(&Instruction::End);
        code.function(&fill);
        // read: load8_u the TOP byte of the arena (ARENA_ADDR + ARENA_LEN-1)
        let mut read = Function::new([]);
        read.instruction(&Instruction::I32Const(ARENA_ADDR)); // base (reloc-flagged)
        read.instruction(&Instruction::I32Load8U(read_memarg));
        read.instruction(&Instruction::End);
        code.function(&read);

        // Tiny active data segment → gives a SMALL visible extent D. The module
        // never reads it; it exists only to reproduce "has data, but uses memory
        // above it". Its offset is rebased structurally (not via reloc.CODE).
        let mut data = DataSection::new();
        data.segment(DataSegment {
            mode: DataSegmentMode::Active {
                memory_index: 0,
                offset: &ConstExpr::i32_const(ARENA_DATA_ADDR),
            },
            data: [sentinel],
        });

        module.section(&types).section(&functions).section(&{
            let mut m = MemorySection::new();
            // Declare 1 page so the arena (< 1 page) fits; page-granular strides
            // by this. (Shared: matches the other fixtures / wasmtime config.)
            m.memory(MemoryType {
                minimum: 1,
                maximum: Some(4),
                memory64: false,
                shared: true,
                page_size_log2: None,
            });
            m
        });
        module
            .section(&globals)
            .section(&exports)
            .section(&DataCountSection { count: 1 })
            .section(&code)
            .section(&data);
    };

    // Locate the two `i32.const ARENA_ADDR` literals (fill dst + read base) and
    // flag them as MEMORY_ADDR reloc sites so meld rebases them.
    let mut dry = Module::new();
    add_sections(&mut dry);
    let offsets = find_i32const_reloc_offsets(&dry.finish(), ARENA_ADDR);
    assert_eq!(offsets.len(), 2, "fill dst + read base are the reloc sites");
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

fn fuse_arena(a: &[u8], b: &[u8], c: &[u8]) -> Vec<u8> {
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        pack_rebase: true,
        share_stack: false,
        profile: meld_core::Profile::Ecosystem,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser.add_component_named(a, Some("comp-a")).unwrap();
    fuser.add_component_named(b, Some("comp-b")).unwrap();
    fuser.add_component_named(c, Some("comp-c")).unwrap();
    fuser.fuse().expect("fusion")
}

fn run_arena(fused: &[u8]) {
    let mut engine_config = Config::new();
    engine_config.wasm_threads(true);
    engine_config.shared_memory(true);
    engine_config.wasm_bulk_memory(true);
    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // Every component fills its arena (order A,B,C — the last writer wins on any
    // overlap), THEN every component reads back the top byte of its OWN arena.
    for fill in ["fill_a", "fill_b", "fill_c"] {
        instance
            .get_typed_func::<(), ()>(&mut store, fill)
            .unwrap_or_else(|e| panic!("export {fill}: {e}"))
            .call(&mut store, ())
            .unwrap();
    }
    for (read, want) in [("read_a", 0xA1), ("read_b", 0xB2), ("read_c", 0xC3)] {
        let got = instance
            .get_typed_func::<(), i32>(&mut store, read)
            .unwrap_or_else(|e| panic!("export {read}: {e}"))
            .call(&mut store, ())
            .unwrap();
        assert_eq!(
            got, want,
            "{read} must read its OWN arena sentinel {want:#x}, got {got:#x} — the arena above \
             the data extent was under-reserved and a neighbour's fill clobbered it (#370)"
        );
    }
}

/// RED→GREEN: arena components with NO `__heap_base` marker. Before the #370
/// extent fix, packing by the small data extent under-reserved the arena and a
/// neighbour clobbered it. The fix declines to compact without a marker and
/// falls back to the page-granular stride, keeping the arenas disjoint.
#[test]
fn pack_rebase_bss_arena_without_marker_falls_back_no_clobber() {
    let a = build_arena_component("a", 0xA1, true, None);
    let b = build_arena_component("b", 0xB2, false, None);
    let c = build_arena_component("c", 0xC3, false, None);
    let fused = fuse_arena(&a, &b, &c);

    // Safe fallback: three 1-page components stride page-granular (3 pages), NOT
    // compacted — the honest, sound behaviour absent a marker.
    assert_eq!(
        fused_memory_min_pages(&fused),
        3,
        "no __heap_base marker → page-granular fallback (no compaction)"
    );
    run_arena(&fused);
}

/// GREEN + compaction: the SAME arena components, now each exporting an
/// immutable-const `__heap_base = ARENA_ADDR + ARENA_LEN` marker (the top of the
/// arena). The fix compacts to that extent — arenas stay disjoint AND the
/// reservation shrinks below the page-granular 3 pages.
#[test]
fn pack_rebase_bss_arena_with_marker_compacts_no_clobber() {
    let top = ARENA_ADDR + ARENA_LEN;
    let a = build_arena_component("a", 0xA1, true, Some(top));
    let b = build_arena_component("b", 0xB2, false, Some(top));
    let c = build_arena_component("c", 0xC3, false, Some(top));
    let fused = fuse_arena(&a, &b, &c);

    let packed = fused_memory_min_pages(&fused);
    eprintln!(
        "SR-57 arena: marker-compacted memory minimum = {packed} page(s) (page-granular = 3)"
    );
    assert!(
        packed < 3,
        "with __heap_base the arena packs below page-granular (got {packed} pages)"
    );
    run_arena(&fused);
}

// ---------------------------------------------------------------------------
// #370 delta-pass regression: IMPORTED memory, where `initial` is a FLOOR, not
// a cap.
//
// A dylink/PIC dylib legally imports `(memory 1 8)` and addresses far above
// page 1, so `max_end` (its visible static extent) can EXCEED `initial*PAGE`.
// The first #370 fix treated `declared = initial*PAGE` as an upper bound in
// both branches:
//   * marker branch clamped `heap_base.max(max_end).min(declared)` — shrinking a
//     legit extent DOWN to `declared`;
//   * no-marker branch guarded `if max_end < declared` — false when
//     `max_end >= declared`, so it silently returned `None` → page-granular
//     stride `= declared`.
// Both UNDER-reserve for an imported memory, re-opening the exact silent
// cross-component corruption SR-56 cannot catch. The delta-pass confirmed it at
// runtime (`read_a == 0xB2`). The corrected rule: the reservation is always
// `>= max_end`, and `declared` may only lower it for a DEFINED memory.
//
// These modules import `(memory 1 8 shared)` (declared floor = 65536) but their
// static data reaches `IMP_ARENA_TOP = 98560 > 65536`, and each `memory.fill`s
// a working-set range that OVERLAPS a neighbour's under the (buggy) 65536
// stride, so a neighbour's fill clobbers the readback. The fused module imports
// its memory, provisioned at runtime via a `Linker`.

const IMP_MEM_MIN_PAGES: u64 = 1; // declared floor = 65536 bytes
const IMP_MEM_MAX_PAGES: u64 = 8;
/// Top of static data (a 1-byte segment sits just below it) — ABOVE the 1-page
/// declared floor, the shape only an imported memory can legally present.
const IMP_ARENA_TOP: i32 = 0x18100; // 98560
/// `memory.fill` destination (base of the working-set range).
const IMP_FILL_BASE: i32 = 0x100; // 256
/// Readback address, chosen inside the neighbour-overlap zone under the buggy
/// 65536 stride (>= 65536 above the fill base) but in the component's OWN range
/// under the correct 98560 stride.
const IMP_READ_ADDR: i32 = IMP_FILL_BASE + 80000; // 80256

/// Build a component whose core module IMPORTS `(memory 1 8 shared)` from
/// `env/memory`, seeds a 1-byte data segment at `IMP_ARENA_TOP-1` (so its
/// visible extent is 98560 > the 65536 floor), `memory.fill`s
/// `[IMP_FILL_BASE, IMP_ARENA_TOP)` with `sentinel`, and reads `IMP_READ_ADDR`
/// back. `marker` optionally exports an immutable-const `__heap_base`.
fn build_imported_arena_component(tag: &str, sentinel: u8, marker: Option<i32>) -> Vec<u8> {
    let zero_memarg = MemArg {
        offset: 0,
        align: 0,
        memory_index: 0,
    };

    let add_sections = |module: &mut Module| {
        let mut types = TypeSection::new();
        types.ty().function([], []); // type 0: fill: () -> ()
        types.ty().function([], [ValType::I32]); // type 1: read: () -> i32

        // Imported shared memory — `initial` here is a FLOOR the dylib declares,
        // NOT a cap on the addresses it uses.
        let mut imports = ImportSection::new();
        imports.import(
            "env",
            "memory",
            EntityType::Memory(MemoryType {
                minimum: IMP_MEM_MIN_PAGES,
                maximum: Some(IMP_MEM_MAX_PAGES),
                memory64: false,
                shared: true,
                page_size_log2: None,
            }),
        );

        let mut functions = FunctionSection::new();
        functions.function(0);
        functions.function(1);

        let mut globals = GlobalSection::new();
        if let Some(top) = marker {
            globals.global(
                GlobalType {
                    val_type: ValType::I32,
                    mutable: false,
                    shared: false,
                },
                &ConstExpr::i32_const(top),
            );
        }

        let mut exports = ExportSection::new();
        exports.export(&format!("fill_{tag}"), ExportKind::Func, 0);
        exports.export(&format!("read_{tag}"), ExportKind::Func, 1);
        if marker.is_some() {
            exports.export("__heap_base", ExportKind::Global, 0);
        }

        let mut code = CodeSection::new();
        // fill: memory.fill(dst = IMP_FILL_BASE, val = sentinel, len)
        let mut fill = Function::new([]);
        fill.instruction(&Instruction::I32Const(IMP_FILL_BASE)); // dst (reloc-flagged)
        fill.instruction(&Instruction::I32Const(i32::from(sentinel)));
        fill.instruction(&Instruction::I32Const(IMP_ARENA_TOP - IMP_FILL_BASE));
        fill.instruction(&Instruction::MemoryFill(0));
        fill.instruction(&Instruction::End);
        code.function(&fill);
        // read: load8_u at IMP_READ_ADDR
        let mut read = Function::new([]);
        read.instruction(&Instruction::I32Const(IMP_READ_ADDR)); // addr (reloc-flagged)
        read.instruction(&Instruction::I32Load8U(zero_memarg));
        read.instruction(&Instruction::End);
        code.function(&read);

        // 1-byte active data segment at IMP_ARENA_TOP-1 → visible extent 98560,
        // above the 65536 floor. Distinct per-component after rebasing (no SR-56
        // active-data overlap). Offset is rebased structurally, not via reloc.
        let mut data = DataSection::new();
        data.segment(DataSegment {
            mode: DataSegmentMode::Active {
                memory_index: 0,
                offset: &ConstExpr::i32_const(IMP_ARENA_TOP - 1),
            },
            data: [sentinel],
        });

        module
            .section(&types)
            .section(&imports)
            .section(&functions)
            .section(&globals)
            .section(&exports)
            .section(&DataCountSection { count: 1 })
            .section(&code)
            .section(&data);
    };

    // Flag both address literals (fill dst + read addr) as reloc sites.
    let mut dry = Module::new();
    add_sections(&mut dry);
    let dry_bytes = dry.finish();
    let mut offsets = find_i32const_reloc_offsets(&dry_bytes, IMP_FILL_BASE);
    offsets.extend(find_i32const_reloc_offsets(&dry_bytes, IMP_READ_ADDR));
    assert_eq!(offsets.len(), 2, "fill dst + read addr are the reloc sites");
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

/// The (min, max) pages of the fused module's IMPORTED memory.
fn fused_imported_memory_pages(bytes: &[u8]) -> (u64, u64) {
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::ImportSection(reader) = payload.expect("payload") {
            for import in reader.into_imports() {
                if let wasmparser::TypeRef::Memory(mem) = import.expect("import").ty {
                    return (mem.initial, mem.maximum.unwrap_or(mem.initial));
                }
            }
        }
    }
    panic!("fused module has no imported memory");
}

/// Fuse three imported-memory arena components under `--pack-rebase`, provision
/// the shared memory via a `Linker`, run every fill then every readback, and
/// assert each component reads its OWN sentinel.
fn run_imported_arena(marker: Option<i32>) {
    let a = build_imported_arena_component("a", 0xA1, marker);
    let b = build_imported_arena_component("b", 0xB2, marker);
    let c = build_imported_arena_component("c", 0xC3, marker);
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        pack_rebase: true,
        share_stack: false,
        profile: meld_core::Profile::Ecosystem,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser.add_component_named(&a, Some("comp-a")).unwrap();
    fuser.add_component_named(&b, Some("comp-b")).unwrap();
    fuser.add_component_named(&c, Some("comp-c")).unwrap();
    let fused = fuser.fuse().expect("fusion");

    let (min_pages, max_pages) = fused_imported_memory_pages(&fused);

    let mut engine_config = Config::new();
    engine_config.wasm_threads(true);
    engine_config.shared_memory(true);
    engine_config.wasm_bulk_memory(true);
    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();

    let shared = SharedMemory::new(
        &engine,
        RuntimeMemoryType::shared(min_pages as u32, max_pages as u32),
    )
    .unwrap();
    let mut store = Store::new(&engine, ());
    let mut linker = Linker::new(&engine);
    linker
        .define(&store, "env", "memory", shared.clone())
        .unwrap();

    let instance = linker.instantiate(&mut store, &module).unwrap();

    for fill in ["fill_a", "fill_b", "fill_c"] {
        instance
            .get_typed_func::<(), ()>(&mut store, fill)
            .unwrap_or_else(|e| panic!("export {fill}: {e}"))
            .call(&mut store, ())
            .unwrap();
    }
    for (read, want) in [("read_a", 0xA1), ("read_b", 0xB2), ("read_c", 0xC3)] {
        let got = instance
            .get_typed_func::<(), i32>(&mut store, read)
            .unwrap_or_else(|e| panic!("export {read}: {e}"))
            .call(&mut store, ())
            .unwrap();
        assert_eq!(
            got,
            want,
            "{read} must read its OWN sentinel {want:#x}, got {got:#x} — imported memory \
             (declared floor {}) addressing above it was under-reserved and a neighbour's fill \
             clobbered it (#370 delta-pass)",
            IMP_MEM_MIN_PAGES * 65536
        );
    }
}

/// RED→GREEN: imported memory, NO marker, `max_end (98560) > declared (65536)`.
/// The buggy no-marker guard returned `None` → 65536 stride; the fix reserves
/// `max_end`.
#[test]
fn pack_rebase_imported_memory_above_floor_no_marker_no_clobber() {
    run_imported_arena(None);
}

/// RED→GREEN: imported memory WITH a `__heap_base` marker. The buggy marker
/// branch clamped `.min(declared)` down to 65536; the fix does NOT clamp for an
/// imported memory, reserving the true `__heap_base` top.
#[test]
fn pack_rebase_imported_memory_marker_not_clamped_to_floor_no_clobber() {
    run_imported_arena(Some(IMP_ARENA_TOP));
}
