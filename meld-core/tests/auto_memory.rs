//! `MemoryStrategy::Auto` resolution — integration oracle for #172 / #326.
//!
//! The default memory strategy is `Auto`. It resolves to **multi-memory**:
//! shared memory + address rebasing was previously auto-selected for grow-free
//! multi-memory inputs, but that path is UNSOUND (#326 — rebasing does not
//! relocate the dynamic address operand of ordinary loads/stores, so
//! computed-pointer access silently collides across components), so Auto no
//! longer selects it. Shared+rebase remains reachable only via explicit
//! `--memory shared --address-rebase`, which warns loudly. (Historically Auto
//! also always avoided shared under `memory.grow` — merger Bug #7.)
//!
//! The oracle here mirrors the issue's repro: `wasm-opt` (and any
//! standards-default validator) rejects multi-memory modules. So the fused
//! output of grow-free inputs must validate with `WasmFeatures::default()`
//! with MULTI_MEMORY explicitly cleared — exactly the feature set
//! `wasm-opt -Os` enforces — and must still behave correctly at runtime.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, DataCountSection, DataSection, DataSegment, DataSegmentMode,
    ExportKind, ExportSection, Function, FunctionSection, Instruction, MemorySection, MemoryType,
    Module, ModuleSection, TypeSection,
};

fn build_component(module: Module) -> Vec<u8> {
    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

fn plain_memory_section() -> MemorySection {
    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: Some(2),
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    memory
}

/// Module A: fills its first 4 bytes with 0x11 and exports its memory.
/// No `memory.grow` anywhere.
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
        .section(&plain_memory_section())
        .section(&exports)
        .section(&code);
    module
}

/// Module B: initialises its first 4 bytes from a passive data segment.
/// Under address rebasing, B's writes must land at its rebased base
/// (one page in), not at absolute 0 where they would clobber A.
fn build_module_b(with_grow: bool) -> Module {
    let mut types = TypeSection::new();
    types.ty().function([], []);
    types.ty().function([], [wasm_encoder::ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0);
    if with_grow {
        functions.function(1);
    }

    let mut exports = ExportSection::new();
    exports.export("b_init", ExportKind::Func, 0);
    if with_grow {
        exports.export("b_grow", ExportKind::Func, 1);
    }

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

    if with_grow {
        let mut grow = Function::new([]);
        grow.instruction(&Instruction::I32Const(1));
        grow.instruction(&Instruction::MemoryGrow(0));
        grow.instruction(&Instruction::End);
        code.function(&grow);
    }

    let mut data = DataSection::new();
    data.segment(DataSegment {
        mode: DataSegmentMode::Passive,
        data: [1u8, 2, 3, 4],
    });

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&plain_memory_section())
        .section(&exports)
        .section(&DataCountSection { count: 1 })
        .section(&code)
        .section(&data);
    module
}

fn fuse_default(components: &[Vec<u8>]) -> (Vec<u8>, meld_core::FusionStats) {
    // FuserConfig::default() carries MemoryStrategy::Auto — the point of
    // these tests is the *default* behavior, so no explicit strategy here.
    let config = FuserConfig::default();
    assert_eq!(config.memory_strategy, MemoryStrategy::Auto);
    let mut fuser = Fuser::new(config);
    for (idx, bytes) in components.iter().enumerate() {
        fuser
            .add_component_named(bytes, Some(&format!("component-{idx}")))
            .unwrap();
    }
    fuser.fuse_with_stats().unwrap()
}

/// Count memories the output carries: defined entries plus memory imports.
fn output_memory_count(wasm: &[u8]) -> usize {
    let mut count = 0;
    for payload in wasmparser::Parser::new(0).parse_all(wasm) {
        match payload.unwrap() {
            wasmparser::Payload::MemorySection(reader) => {
                count += reader.into_iter().count();
            }
            wasmparser::Payload::ImportSection(reader) => {
                for imp in reader.into_imports() {
                    if matches!(imp.unwrap().ty, wasmparser::TypeRef::Memory(_)) {
                        count += 1;
                    }
                }
            }
            _ => {}
        }
    }
    count
}

/// The issue-#172 oracle: validate with the standards-default feature set,
/// multi-memory explicitly cleared — the same gate `wasm-opt -Os` applies.
fn validates_without_multimemory(wasm: &[u8]) -> bool {
    let mut features = wasmparser::WasmFeatures::default();
    features.set(wasmparser::WasmFeatures::MULTI_MEMORY, false);
    wasmparser::Validator::new_with_features(features)
        .validate_all(wasm)
        .is_ok()
}

/// #326: address rebasing does not relocate the dynamic address operand of
/// ordinary loads/stores, so shared-memory fusion silently corrupts any
/// component that addresses memory via a computed pointer. Auto therefore no
/// longer selects shared+rebase even for grow-free inputs — it falls back to
/// multi-memory, the sound strategy (LS-D-1: correct output, never a
/// plausible-but-wrong one). Shared remains reachable only via explicit
/// `--memory shared --address-rebase`, which warns loudly.
#[test]
fn auto_gates_shared_for_growfree_inputs_326() {
    let component_a = build_component(build_module_a());
    let component_b = build_component(build_module_b(false));

    let (fused, stats) = fuse_default(&[component_a, component_b]);

    assert_eq!(
        stats.memory_strategy, "multi",
        "auto must gate the unsound shared+rebase path (#326) and select multi"
    );
    assert_eq!(
        output_memory_count(&fused),
        2,
        "multi-memory keeps each component's memory separate — no silent \
         cross-component collision (the correctness #326 protects)"
    );
    assert!(
        !validates_without_multimemory(&fused),
        "sanity: the multi-memory form is the one a no-flags validator rejects"
    );
}

/// One input contains `memory.grow` → shared memory is unsound (merger
/// Bug #7), so Auto must keep multi-memory: both memories preserved.
/// (`ls_m_7_` prefix: regression test for the approved LS-M-7 scenario,
/// run by the LS-N verification gate.)
#[test]
fn ls_m_7_auto_keeps_multi_when_input_grows() {
    let component_a = build_component(build_module_a());
    let component_b = build_component(build_module_b(true));

    let (fused, stats) = fuse_default(&[component_a, component_b]);

    assert_eq!(
        stats.memory_strategy, "multi",
        "memory.grow in any input must force multi-memory"
    );
    assert_eq!(output_memory_count(&fused), 2);
    assert!(
        !validates_without_multimemory(&fused),
        "sanity: the multi-memory form is the one a no-flags validator \
         rejects — confirming the shared path is what fixes #172"
    );
}

/// A single component with one memory → nothing to merge; Auto stays on
/// multi-memory (the output is single-memory anyway) rather than running
/// the rebasing path for no benefit.
#[test]
fn auto_keeps_multi_for_single_memory_input() {
    let component_a = build_component(build_module_a());

    let (fused, stats) = fuse_default(&[component_a]);

    assert_eq!(stats.memory_strategy, "multi");
    assert_eq!(output_memory_count(&fused), 1);
    assert!(validates_without_multimemory(&fused));
}

/// Mythos finding A (PR #220): Auto resolution must be re-derived from the
/// CURRENT component set on every fuse. Post-#326 Auto always resolves to
/// multi-memory (shared+rebase is gated off as unsound), so re-probing is
/// verified by the memory layout re-deriving: a grow-free pair fuses to 2
/// memories, and after adding a third component the next fuse re-derives to
/// 3 — not a stale 2. (`ls_m_7_` prefix: LS-M-7 / UCA-M-11 regression, run by
/// the LS-N verification gate.)
#[test]
fn ls_m_7_auto_reprobes_after_add_component() {
    let component_a = build_component(build_module_a());
    let component_b = build_component(build_module_b(false));
    let component_grow = build_component(build_module_b(true));

    let mut fuser = Fuser::new(FuserConfig::default());
    fuser.add_component_named(&component_a, Some("a")).unwrap();
    fuser.add_component_named(&component_b, Some("b")).unwrap();

    let (fused1, stats) = fuser.fuse_with_stats().unwrap();
    assert_eq!(
        stats.memory_strategy, "multi",
        "grow-free pair → multi (#326 gates the unsound shared+rebase path)"
    );
    assert_eq!(
        output_memory_count(&fused1),
        2,
        "grow-free pair fuses to 2 memories"
    );

    fuser
        .add_component_named(&component_grow, Some("grower"))
        .unwrap();
    let (fused, stats) = fuser
        .fuse_with_stats()
        .expect("second fuse must re-resolve against the current component set");
    assert_eq!(stats.memory_strategy, "multi");
    assert_eq!(
        output_memory_count(&fused),
        3,
        "the added component must be re-probed: 3 memories, not a stale 2"
    );
}

/// Explicit strategies are untouched by Auto: `MultiMemory` still produces
/// the multi-memory form even for grow-free inputs.
#[test]
fn explicit_multi_is_not_overridden() {
    let component_a = build_component(build_module_a());
    let component_b = build_component(build_module_b(false));

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser.add_component_named(&component_a, Some("a")).unwrap();
    fuser.add_component_named(&component_b, Some("b")).unwrap();
    let (fused, stats) = fuser.fuse_with_stats().unwrap();

    assert_eq!(stats.memory_strategy, "multi");
    assert_eq!(output_memory_count(&fused), 2);
}
