//! Element/data SEGMENT-index remap regression tests.
//!
//! # The bug (Mythos discovery pass)
//!
//! The merger concatenates every module's passive/active data segments into a
//! SINGLE shared data section (and likewise for element segments), in
//! deterministic module order. So module B's local segment 0 lands at fused
//! ordinal 1, B's local segment 1 at ordinal 2, and so on.
//!
//! The rewriter, however, used to pass the SEGMENT operand of
//! `memory.init` / `data.drop` / `table.init` / `elem.drop` through
//! verbatim. After fusion, module B's `memory.init … data_index:0` therefore
//! read module A's segment 0 instead of its own. The fused module VALIDATES
//! and RUNS — it just returns the wrong bytes (proven below: `probe_b`
//! returned `0xAAAAAAAA`, want `0xBBBBBBBB`).
//!
//! The fix adds `data_segments` / `elements` index maps to `IndexMaps`
//! (mirroring the existing function/type/global/table/memory maps) and remaps
//! the segment operands through them. The base offset for a module equals the
//! number of segments contributed by all PRIOR modules in the concatenated
//! section.
//!
//! # Tests
//!
//! - `segidx_data_two_modules_distinct_segments` — the core PoC. Two modules,
//!   each with its own passive data segment + `memory.init data_index:0`.
//!   `probe_b` must return `0xBBBBBBBB`, `probe_a` must return `0xAAAAAAAA`.
//!   FAILS pre-fix (probe_b reads A's segment).
//! - `segidx_elem_two_modules_distinct_segments` — element-segment analogue
//!   via `table.init` from a passive elem segment.
//! - `segidx_data_three_modules_base_offset_gt_one` — exercises base offset
//!   > 1 (module C's segment maps to ordinal 2).
//! - `segidx_single_module_identity` — regression: one segment, base 0,
//!   identity remap still works.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, DataCountSection, DataSection, DataSegment, DataSegmentMode,
    ElementSection, Elements, ExportKind, ExportSection, Function, FunctionSection, Instruction,
    MemArg, MemorySection, MemoryType, Module, ModuleSection, RefType, TableSection, TableType,
    TypeSection,
};
use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};

fn fuser_config() -> FuserConfig {
    FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Merge,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    }
}

fn engine() -> Engine {
    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    cfg.wasm_bulk_memory(true);
    Engine::new(&cfg).unwrap()
}

// ---------------------------------------------------------------------------
// Data-segment PoC
// ---------------------------------------------------------------------------

/// Build a standalone single-module component whose probe function copies its
/// OWN passive data segment 0 into memory via `memory.init data_index:0`, then
/// loads the i32 back. The 4-byte segment is `fill` (little-endian).
///
/// The segment is PASSIVE, so the only way its bytes reach memory is through
/// `memory.init` — which is exactly the operator whose segment operand the
/// merger must remap. If the operand is not remapped, after fusion this
/// module's `memory.init data_index:0` reads whichever module landed at fused
/// segment 0 instead.
fn build_data_probe_component(fill: u32, export_name: &str) -> Vec<u8> {
    let bytes = fill.to_le_bytes();

    let mut types = TypeSection::new();
    types.ty().function([], [wasm_encoder::ValType::I32]); // type 0: () -> i32

    let mut functions = FunctionSection::new();
    functions.function(0); // probe: type 0

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export(export_name, ExportKind::Func, 0);
    exports.export("memory", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    let mut probe = Function::new([]);
    // memory.init data_index:0 mem:0  (dst=0, src_off=0, len=4)
    probe.instruction(&Instruction::I32Const(0)); // dst addr
    probe.instruction(&Instruction::I32Const(0)); // src offset in segment
    probe.instruction(&Instruction::I32Const(4)); // len
    probe.instruction(&Instruction::MemoryInit {
        mem: 0,
        data_index: 0,
    });
    // load the freshly-copied i32 back
    probe.instruction(&Instruction::I32Const(0));
    probe.instruction(&Instruction::I32Load(MemArg {
        offset: 0,
        align: 2,
        memory_index: 0,
    }));
    probe.instruction(&Instruction::End);
    code.function(&probe);

    // One PASSIVE data segment (index 0).
    let mut data = DataSection::new();
    data.segment(DataSegment {
        mode: DataSegmentMode::Passive,
        data: bytes.to_vec(),
    });

    // `memory.init` requires a DataCount section; it must precede the code
    // section in the binary.
    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&exports)
        .section(&DataCountSection { count: 1 })
        .section(&code)
        .section(&data);

    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

#[test]
fn segidx_data_two_modules_distinct_segments() {
    // Module A's segment is filled 0xAAAAAAAA; module B's is 0xBBBBBBBB.
    // After fusion the concatenated data section is [A.seg0, B.seg0]. B's
    // probe does `memory.init data_index:0`; without remapping it reads
    // ordinal 0 (= A's segment) and returns 0xAAAAAAAA. With the fix it must
    // read ordinal 1 (its own) and return 0xBBBBBBBB.
    let comp_a = build_data_probe_component(0xAAAA_AAAA, "probe_a");
    let comp_b = build_data_probe_component(0xBBBB_BBBB, "probe_b");

    let mut fuser = Fuser::new(fuser_config());
    fuser.add_component_named(&comp_a, Some("comp-a")).unwrap();
    fuser.add_component_named(&comp_b, Some("comp-b")).unwrap();
    let fused = fuser.fuse().unwrap();

    let engine = engine();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let probe_b = instance
        .get_typed_func::<(), i32>(&mut store, "probe_b")
        .expect("probe_b export present");
    let got_b = probe_b.call(&mut store, ()).unwrap() as u32;
    assert_eq!(
        got_b, 0xBBBB_BBBB,
        "probe_b must read its OWN data segment (0xBBBBBBBB), not module A's \
         (0xAAAAAAAA) — segment-index remap regression"
    );

    let probe_a = instance
        .get_typed_func::<(), i32>(&mut store, "probe_a")
        .expect("probe_a export present");
    let got_a = probe_a.call(&mut store, ()).unwrap() as u32;
    assert_eq!(
        got_a, 0xAAAA_AAAA,
        "probe_a must read its own data segment (0xAAAAAAAA)"
    );
}

#[test]
fn segidx_data_three_modules_base_offset_gt_one() {
    // Three modules force a base offset > 1: module C's local segment 0 must
    // map to fused ordinal 2.
    let comp_a = build_data_probe_component(0x1111_1111, "probe_a");
    let comp_b = build_data_probe_component(0x2222_2222, "probe_b");
    let comp_c = build_data_probe_component(0x3333_3333, "probe_c");

    let mut fuser = Fuser::new(fuser_config());
    fuser.add_component_named(&comp_a, Some("comp-a")).unwrap();
    fuser.add_component_named(&comp_b, Some("comp-b")).unwrap();
    fuser.add_component_named(&comp_c, Some("comp-c")).unwrap();
    let fused = fuser.fuse().unwrap();

    let engine = engine();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    for (name, want) in [
        ("probe_a", 0x1111_1111u32),
        ("probe_b", 0x2222_2222u32),
        ("probe_c", 0x3333_3333u32),
    ] {
        let f = instance
            .get_typed_func::<(), i32>(&mut store, name)
            .unwrap_or_else(|_| panic!("{name} export present"));
        let got = f.call(&mut store, ()).unwrap() as u32;
        assert_eq!(
            got, want,
            "{name} must read its own data segment ({want:#010x})"
        );
    }
}

#[test]
fn segidx_single_module_identity() {
    // Single-module component: one segment, base 0. The remap is the identity
    // (local 0 -> fused 0); this guards against a fix that breaks the trivial
    // case.
    let comp = build_data_probe_component(0xDEAD_BEEF, "probe");

    let mut fuser = Fuser::new(fuser_config());
    fuser.add_component_named(&comp, Some("solo")).unwrap();
    let fused = fuser.fuse().unwrap();

    let engine = engine();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let probe = instance
        .get_typed_func::<(), i32>(&mut store, "probe")
        .unwrap();
    let got = probe.call(&mut store, ()).unwrap() as u32;
    assert_eq!(got, 0xDEAD_BEEF, "single-module identity remap must hold");
}

// ---------------------------------------------------------------------------
// Element-segment PoC (table.init from a passive elem segment)
// ---------------------------------------------------------------------------

/// Build a single-module component that proves element-segment remapping.
///
/// The module has:
/// - a funcref table (1 slot),
/// - a constant function `konst() -> i32` returning `marker`,
/// - a PASSIVE element segment (index 0) holding `[konst]`,
/// - a probe that does `table.init elem_index:0` into table slot 0, then
///   `call_indirect`s slot 0 and returns the result.
///
/// As with the data case, the passive elem segment is only realized through
/// `table.init`, whose elem operand must be remapped after the merger
/// concatenates every module's element segments.
fn build_elem_probe_component(marker: i32, export_name: &str) -> Vec<u8> {
    let mut types = TypeSection::new();
    types.ty().function([], [wasm_encoder::ValType::I32]); // type 0: () -> i32

    let mut functions = FunctionSection::new();
    functions.function(0); // konst: type 0
    functions.function(0); // probe: type 0

    let mut tables = TableSection::new();
    tables.table(TableType {
        element_type: RefType::FUNCREF,
        minimum: 1,
        maximum: None,
        table64: false,
        shared: false,
    });

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    // func 0 = konst, func 1 = probe
    exports.export(export_name, ExportKind::Func, 1);
    exports.export("memory", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    // konst() -> i32
    {
        let mut f = Function::new([]);
        f.instruction(&Instruction::I32Const(marker));
        f.instruction(&Instruction::End);
        code.function(&f);
    }
    // probe() -> i32
    {
        let mut f = Function::new([]);
        // table.init elem_index:0 table:0  (dst=0, src=0, len=1)
        f.instruction(&Instruction::I32Const(0)); // dst in table
        f.instruction(&Instruction::I32Const(0)); // src in segment
        f.instruction(&Instruction::I32Const(1)); // len
        f.instruction(&Instruction::TableInit {
            elem_index: 0,
            table: 0,
        });
        // call_indirect table slot 0, type 0
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::CallIndirect {
            type_index: 0,
            table_index: 0,
        });
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // One PASSIVE element segment (index 0) holding [konst] (func 0).
    let mut elements = ElementSection::new();
    let func_indices = [0u32];
    elements.segment(wasm_encoder::ElementSegment {
        mode: wasm_encoder::ElementMode::Passive,
        elements: Elements::Functions(std::borrow::Cow::Borrowed(&func_indices)),
    });

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&tables)
        .section(&memory)
        .section(&exports)
        .section(&elements)
        .section(&code);

    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

#[test]
fn segidx_elem_two_modules_distinct_segments() {
    // Module A's elem segment references its konst (returns 0x0A0A);
    // module B's references its konst (returns 0x0B0B). After fusion the
    // element sections concatenate; without elem-index remap, B's
    // `table.init elem_index:0` installs A's konst into B's table and
    // returns 0x0A0A. With the fix, probe_b returns 0x0B0B.
    let comp_a = build_elem_probe_component(0x0A0A, "probe_a");
    let comp_b = build_elem_probe_component(0x0B0B, "probe_b");

    let mut fuser = Fuser::new(fuser_config());
    fuser.add_component_named(&comp_a, Some("comp-a")).unwrap();
    fuser.add_component_named(&comp_b, Some("comp-b")).unwrap();
    let fused = fuser.fuse().unwrap();

    let engine = engine();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let probe_b = instance
        .get_typed_func::<(), i32>(&mut store, "probe_b")
        .expect("probe_b export present");
    let got_b = probe_b.call(&mut store, ()).unwrap();
    assert_eq!(
        got_b, 0x0B0B,
        "probe_b must install its OWN element segment's funcref (0x0B0B), \
         not module A's (0x0A0A) — elem-index remap regression"
    );

    let probe_a = instance
        .get_typed_func::<(), i32>(&mut store, "probe_a")
        .expect("probe_a export present");
    let got_a = probe_a.call(&mut store, ()).unwrap();
    assert_eq!(
        got_a, 0x0A0A,
        "probe_a must install its own funcref (0x0A0A)"
    );
}
