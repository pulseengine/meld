//! #386 — the shared+rebase "no relocation metadata" warning fires only when it
//! actually applies.
//!
//! `--memory shared --address-rebase` used to warn "UNSOUND" unconditionally.
//! That predates the reloc CONSUMER (#326→#340): a reloc-covered input is rebased
//! at the SOURCE point (every reloc-flagged `i32.const` address is relocated at
//! its origin), so a pointer computed from it is correct by construction — proven
//! by `rebasing_end_to_end::test_326_reloc_const_rebasing_end_to_end`, which
//! executes on wasmtime. Warning on that path is inaccurate, and it is the path
//! `--pack-rebase` (SR-57) and `--share-stack` (SR-66) are built on and that the
//! falcon supplier validated on real components (#370). A safety tool that cries
//! wolf on its supported path trains users to ignore the warnings that matter.
//!
//! Contract pinned here: reloc-covered inputs fuse QUIETLY; an input WITHOUT
//! reloc metadata still warns (the residual #339 risk is real there).

use std::sync::Mutex;

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, ConstExpr, CustomSection, DataSection, DataSegment, DataSegmentMode,
    ExportKind, ExportSection, Function, FunctionSection, Instruction, MemArg, MemorySection,
    MemoryType, Module, ModuleSection, TypeSection, ValType,
};

/// The substring unique to the #386 warning (distinct from the per-module
/// `address_strategy` warning, which reports a placement failure instead).
///
/// The phrase this used to key on — "at least one input" — was removed: it was
/// inaccurate. The check walks the FLATTENED component list, which includes
/// components synthesized from an input's nested structure, so a caller whose
/// every input carried relocs could still be told an *input* lacked them. The
/// warning now names the offenders; see `the_warning_names_which_components`.
const WARN_MARKER: &str = "carry NO relocation metadata";

static CAPTURED: Mutex<Vec<String>> = Mutex::new(Vec::new());

/// Serializes the tests that CAPTURE warnings.
///
/// `CAPTURED` is process-global and `drain()` empties it, so two such tests
/// running concurrently steal each other's records. That is not hypothetical:
/// adding a second capturing test made this file pass under `--workspace` and
/// fail under `--all-features`, purely on scheduling order — a flaky test, which
/// is worse than a missing one because it teaches people to re-run.
///
/// Tests that do not capture warnings need not take this.
static CAPTURE_LOCK: Mutex<()> = Mutex::new(());
static LOGGER: CaptureLogger = CaptureLogger;

struct CaptureLogger;

impl log::Log for CaptureLogger {
    fn enabled(&self, _: &log::Metadata<'_>) -> bool {
        true
    }
    fn log(&self, record: &log::Record<'_>) {
        if record.level() == log::Level::Warn {
            CAPTURED.lock().unwrap().push(format!("{}", record.args()));
        }
    }
    fn flush(&self) {}
}

const DATA_ADDR: i32 = 0x100;

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
    write_uleb(&mut body, 3);
    write_uleb(&mut body, offsets.len() as u32);
    for &off in offsets {
        body.push(4u8); // R_WASM_MEMORY_ADDR_SLEB
        write_uleb(&mut body, off);
        write_uleb(&mut body, 0);
        body.push(0u8);
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

/// A component that reads a sentinel through a reloc-flagged absolute address.
/// `with_relocs` decides whether the `linking` + `reloc.CODE` sections are
/// emitted — i.e. whether meld can rebase that address.
fn build_component(tag: &str, sentinel: u8, export_memory: bool, with_relocs: bool) -> Vec<u8> {
    let memarg = MemArg {
        offset: 0,
        align: 0,
        memory_index: 0,
    };

    let add_sections = |module: &mut Module| {
        let mut types = TypeSection::new();
        types.ty().function([], [ValType::I32]);

        let mut functions = FunctionSection::new();
        functions.function(0);

        let mut exports = ExportSection::new();
        exports.export(&format!("read_{tag}"), ExportKind::Func, 0);
        if export_memory {
            exports.export("memory", ExportKind::Memory, 0);
        }

        let mut code = CodeSection::new();
        let mut read = Function::new([]);
        read.instruction(&Instruction::I32Const(DATA_ADDR));
        read.instruction(&Instruction::I32Load8U(memarg));
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
            .section(&exports)
            .section(&code)
            .section(&data);
    };

    let mut module = Module::new();
    add_sections(&mut module);

    if with_relocs {
        let mut dry = Module::new();
        add_sections(&mut dry);
        let offsets = find_i32const_reloc_offsets(&dry.finish(), DATA_ADDR);
        assert_eq!(
            offsets.len(),
            1,
            "one address literal to flag in read_{tag}"
        );
        let reloc_code = build_reloc_code_body(&offsets);
        module.section(&CustomSection {
            name: "linking".into(),
            data: vec![0x02].into(),
        });
        module.section(&CustomSection {
            name: "reloc.CODE".into(),
            data: reloc_code.into(),
        });
    }

    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

fn fuse_shared_rebase(a: Vec<u8>, b: Vec<u8>) -> Result<Vec<u8>, String> {
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser.add_component_named(&a, Some("comp-a")).unwrap();
    fuser.add_component_named(&b, Some("comp-b")).unwrap();
    fuser.fuse().map_err(|e| e.to_string())
}

fn drain() -> Vec<String> {
    std::mem::take(&mut *CAPTURED.lock().unwrap())
}

/// Both phases live in ONE test so the process-global capture buffer is not
/// raced by parallel test threads.
#[test]
fn shared_rebase_warns_only_when_an_input_lacks_relocs() {
    let _guard = CAPTURE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let _ = log::set_logger(&LOGGER);
    log::set_max_level(log::LevelFilter::Warn);

    // Phase 1 — every input is reloc-covered: meld can rebase every address at
    // its source, so the fuse must be QUIET (the #386 regression: it used to
    // print "UNSOUND" here, on the very path pack-rebase/share-stack ship).
    drain();
    fuse_shared_rebase(
        build_component("a", 0xA1, true, true),
        build_component("b", 0xB2, false, true),
    )
    .expect("reloc-covered shared+rebase fusion");
    let warnings = drain();
    assert!(
        !warnings.iter().any(|w| w.contains(WARN_MARKER)),
        "reloc-covered inputs must not draw the no-reloc warning, got: {warnings:?}"
    );
    assert!(
        !warnings.iter().any(|w| w.contains("UNSOUND")),
        "reloc-covered shared+rebase is not unsound — no UNSOUND warning, got: {warnings:?}"
    );

    // Phase 2 — one input carries no reloc metadata: its absolute address cannot
    // be rebased, so the warning is real and must fire. (This input does a direct
    // load, so path-F also hard-errors — the warning fires first, which is the
    // observability contract being pinned.)
    drain();
    let _ = fuse_shared_rebase(
        build_component("a", 0xA1, true, true),
        build_component("b", 0xB2, false, false),
    );
    let warnings = drain();
    assert!(
        warnings.iter().any(|w| w.contains(WARN_MARKER)),
        "an input without reloc metadata must draw the warning, got: {warnings:?}"
    );
}

/// The warning must NAME the components it is complaining about.
///
/// Reported by a downstream consumer: every one of their inputs was built with
/// `--emit-relocs`, and meld still said "at least one input ... carries NO
/// relocation metadata". The offender was a component synthesized from an
/// input's nested structure, not a file they had passed — so the message sent
/// them auditing artifacts that were fine. A safety tool's false alarm costs
/// exactly the trust its true alarms depend on.
// rivet: verifies SR-68
#[test]
fn the_warning_names_which_components() {
    let _guard = CAPTURE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let _ = log::set_logger(&LOGGER);
    log::set_max_level(log::LevelFilter::Warn);
    let _ = drain();

    // `b` has no relocs, so the warning must fire — and say so by name.
    let a = build_component("aa", 0x11, true, true);
    let b = build_component("bb", 0x22, false, false);
    let _ = fuse_shared_rebase(a, b);

    let warnings = drain();
    let warning = warnings
        .iter()
        .find(|w| w.contains(WARN_MARKER))
        .unwrap_or_else(|| panic!("expected the #386 warning; got {warnings:?}"));

    assert!(
        warning.contains("component"),
        "the warning must identify what is missing relocs, not just that something is: {warning}"
    );
    // The old phrasing asserted something the check cannot know.
    assert!(
        !warning.contains("at least one input"),
        "the warning must not claim an INPUT lacks relocs — it walks the flattened \
         component list, which includes components the caller never passed: {warning}"
    );
}

/// `input_count()` reports what the caller ADDED, not the flattened total.
///
/// Two input files were reported as "Fusing 4 components", which sends a reader
/// looking for inputs they never passed — the same false-trail problem as the
/// warning above, in the line printed directly before it.
// rivet: verifies SR-68
#[test]
fn input_count_reports_inputs_not_flattened_components() {
    let a = build_component("aa", 0x11, true, true);
    let b = build_component("bb", 0x22, false, true);

    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component_named(&a, Some("a")).expect("add a");
    assert_eq!(fuser.input_count(), 1, "one component added");
    fuser.add_component_named(&b, Some("b")).expect("add b");
    assert_eq!(
        fuser.input_count(),
        2,
        "two components added — not the flattened count"
    );
    // `component_count` keeps its existing meaning: nested_component asserts
    // flattening through it, so this is an addition, not a redefinition.
    assert!(
        fuser.component_count() >= fuser.input_count(),
        "the flattened count is never smaller than the number of inputs"
    );
}
