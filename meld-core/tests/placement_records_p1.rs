//! ADR-7 P1 increment 2 (SR-70) — per-module memory placement is attested and
//! observable: where each module landed in the fused address space, and by which
//! rule.
//!
//! This is the memory-axis twin of the boundary records. It matters most for the
//! case it makes visible: under `--pack-rebase` a module that cannot be compacted
//! (no `__heap_base` marker, or a passive/no-data region) silently falls back to
//! a page-granular stride. That fallback is sound but invisible — a user asking
//! for compaction could get none and never know. The placement record reports the
//! rule that actually applied, per module.
//!
//! Pinned here:
//!   1. `--pack-rebase` with markers → `packed`, with a compact reservation;
//!   2. the same shape WITHOUT markers → `page-granular` (the honest label for
//!      the declined-compaction fallback), reserving a full page;
//!   3. records reach the artifact's attestation;
//!   4. `--memory multi` records none (there is no placement decision to make).

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, ConstExpr, DataSection, DataSegment, DataSegmentMode, ExportKind,
    ExportSection, Function, FunctionSection, GlobalSection, GlobalType, Instruction,
    MemorySection, MemoryType, Module, ModuleSection, TypeSection, ValType,
};

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

/// A thin provider. `with_marker` decides whether it publishes the
/// `__heap_base` marker that licenses compaction (SR-65).
fn build_provider(tag: &str, sentinel: u8, export_memory: bool, with_marker: bool) -> Vec<u8> {
    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0);

    let mut globals = GlobalSection::new();
    if with_marker {
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: false,
                shared: false,
            },
            &ConstExpr::i32_const(DATA_ADDR + 1),
        );
    }

    let mut exports = ExportSection::new();
    exports.export(&format!("read_{tag}"), ExportKind::Func, 0);
    if with_marker {
        exports.export("__heap_base", ExportKind::Global, 0);
    }
    if export_memory {
        exports.export("memory", ExportKind::Memory, 0);
    }

    // Deliberately NO memory access: a no-reloc module that does a direct
    // load/store is (correctly) rejected by the path-F gate, and placement is
    // decided from the module's memory + data segments, not from its code.
    let mut code = CodeSection::new();
    let mut read = Function::new([]);
    read.instruction(&Instruction::I32Const(DATA_ADDR));
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

    let mut module = Module::new();
    module.section(&types).section(&functions);
    module.section(&shared_memory_section());
    module.section(&globals).section(&exports).section(&code);
    module.section(&data);

    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

fn fuse(
    with_marker: bool,
    memory_strategy: MemoryStrategy,
    pack_rebase: bool,
) -> (Vec<u8>, meld_core::FusionStats) {
    let config = FuserConfig {
        memory_strategy,
        address_rebasing: memory_strategy == MemoryStrategy::SharedMemory && !pack_rebase,
        pack_rebase,
        reproducible: true,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(
            &build_provider("a", 0xA1, true, with_marker),
            Some("comp-a"),
        )
        .unwrap();
    fuser
        .add_component_named(
            &build_provider("b", 0xB2, false, with_marker),
            Some("comp-b"),
        )
        .unwrap();
    fuser.fuse_with_stats().expect("fusion")
}

#[test]
fn pack_rebase_with_markers_reports_packed_placement() {
    let (_out, stats) = fuse(true, MemoryStrategy::SharedMemory, true);
    assert_eq!(stats.placements.len(), 2, "both modules placed");
    for p in &stats.placements {
        assert_eq!(
            p.strategy, "packed",
            "a marker-carrying module under --pack-rebase must report `packed`: {p:?}"
        );
        assert!(
            p.reserved < 65536,
            "packed reservation must be compact, got {} bytes",
            p.reserved
        );
    }
    // Bases must be distinct and ascending — the placements describe a real,
    // non-overlapping layout.
    assert!(
        stats.placements[0].base < stats.placements[1].base,
        "placements must describe distinct ascending bases: {:?}",
        stats.placements
    );
}

#[test]
fn pack_rebase_without_markers_reports_the_page_granular_fallback() {
    // The case this record exists for: `--pack-rebase` was REQUESTED, but with
    // no `__heap_base` marker meld cannot compact and silently strides
    // page-granular (SR-65). Sound, but previously invisible — a user could ask
    // for compaction, receive none, and have no way to see it.
    let (_out, stats) = fuse(false, MemoryStrategy::SharedMemory, true);
    assert_eq!(stats.placements.len(), 2, "both modules placed");
    for p in &stats.placements {
        assert_eq!(
            p.strategy, "page-granular",
            "declined compaction must be reported honestly as page-granular: {p:?}"
        );
        assert_eq!(
            p.reserved, 65536,
            "the fallback reserves a full page, got {}",
            p.reserved
        );
    }
}

#[test]
fn placement_records_reach_the_attestation() {
    let (out, stats) = fuse(true, MemoryStrategy::SharedMemory, true);
    assert!(!stats.placements.is_empty());

    let mut attestation_json: Option<String> = None;
    for payload in wasmparser::Parser::new(0).parse_all(&out) {
        if let wasmparser::Payload::CustomSection(reader) = payload.expect("payload")
            && reader.name() == "wsc.transformation.attestation"
        {
            attestation_json = Some(String::from_utf8_lossy(reader.data()).into_owned());
        }
    }
    let json = attestation_json.expect("artifact carries an attestation");
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
    let placements = parsed
        .get("metadata")
        .and_then(|m| m.get("placements"))
        .and_then(|p| p.as_array())
        .expect("attestation records placements");
    assert_eq!(placements.len(), stats.placements.len());
    for key in ["component", "module", "strategy", "base", "reserved"] {
        assert!(
            placements[0].get(key).is_some(),
            "attested placement must carry `{key}`: {}",
            placements[0]
        );
    }
}

#[test]
fn multi_memory_records_no_placement() {
    // Not an omission: with one memory per component nothing is placed, and the
    // attested `memory_strategy` already says which model is in force.
    let (_out, stats) = fuse(true, MemoryStrategy::MultiMemory, false);
    assert!(
        stats.placements.is_empty(),
        "multi-memory has no placement decision to record, got {:?}",
        stats.placements
    );
}
