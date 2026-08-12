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
    CodeSection, Component, CustomSection, DataSection, DataSegment, DataSegmentMode, ExportKind,
    ExportSection, Function, FunctionSection, Instruction, MemArg, MemorySection, MemoryType,
    Module, ModuleSection, TypeSection, ValType,
};
use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};

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

        let mut exports = ExportSection::new();
        exports.export(&format!("read_{tag}"), ExportKind::Func, 0);
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
                offset: &wasm_encoder::ConstExpr::i32_const(DATA_ADDR),
            },
            data: [sentinel],
        });

        module
            .section(&types)
            .section(&functions)
            .section(&shared_memory_section())
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
