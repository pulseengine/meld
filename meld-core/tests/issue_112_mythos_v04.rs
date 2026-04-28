//! Regression tests for issue #112 (Mythos v0.4 follow-up, items 4 and 5).
//!
//! Item 4: `graph.adapter_sites` was populated by iterating
//! `graph.resolved_imports` (a `HashMap`) and never sorted. Since
//! `lib.rs:413-414` and `merger.rs:1500` make first-match decisions over
//! `adapter_sites`, the same input could produce byte-different output
//! across processes (LS-CP-3 / SR-19).
//!
//! Item 5: `identify_intra_component_adapter_sites` set
//! `import_module = res.import_name` (the field name) when promoting an
//! intra-component module resolution to an adapter site. This dropped
//! the `from_import_module` disambiguator that `merger.rs:1500`'s
//! disjunctive match
//! `(imp.module == site.import_module || imp.name == site.import_module)`
//! relies on, so a module that imports two functions with the same `name`
//! from different `module`s would route both calls to the same upstream
//! export when intra-component adapter promotion fired (LS-R-10 /
//! UCA-R-3).
//!
//! Both fixtures here build a synthetic single-component component with
//! three core modules and an explicit `InstanceSection` so the
//! instance-graph resolver wires each `(module, name)` import to a
//! distinct provider. Each provider module owns its own memory so
//! MultiMemory mode forces intra-component adapter promotion, which is
//! the exact path that exposes both bugs.

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasm_encoder::{
    CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection, ImportSection,
    InstanceSection, Instruction, MemorySection, MemoryType, Module, ModuleArg, ModuleSection,
    TypeSection,
};

const PROVIDER_A: &str = "providerA";
const PROVIDER_B: &str = "providerB";

/// Provider module: exports `f() -> i32` returning `constant`, and exports
/// its own memory (so MultiMemory mode forces an adapter at every
/// cross-module call boundary).
fn build_provider_module(constant: i32) -> Module {
    let mut types = TypeSection::new();
    types.ty().function([], [wasm_encoder::ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0);

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export("f", ExportKind::Func, 0);
    exports.export("memory", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    {
        let mut func = Function::new([]);
        func.instruction(&Instruction::I32Const(constant));
        func.instruction(&Instruction::End);
        code.function(&func);
    }

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&exports)
        .section(&code);
    module
}

/// Consumer module: imports `f` from each of `providerA` and `providerB`,
/// and exports `run() -> f_A() + f_B() * 10`.
///
/// The asymmetric mixing makes the result sensitive to which import gets
/// routed where. With providers returning 1 and 2, the correct result is
/// `1 + 2 * 10 = 21`. If the merger collapses both calls to the same
/// upstream export (the item-5 bug), the result is either `1 + 1*10 = 11`
/// or `2 + 2*10 = 22`.
fn build_consumer_module() -> Module {
    let mut types = TypeSection::new();
    // type 0: () -> i32 — signature of imported `f`
    types.ty().function([], [wasm_encoder::ValType::I32]);
    // type 1: () -> i32 — signature of `run`
    types.ty().function([], [wasm_encoder::ValType::I32]);

    let mut imports = ImportSection::new();
    imports.import(PROVIDER_A, "f", wasm_encoder::EntityType::Function(0));
    imports.import(PROVIDER_B, "f", wasm_encoder::EntityType::Function(0));

    let mut functions = FunctionSection::new();
    functions.function(1); // `run` — function index 2 (after 2 imports)

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export("run", ExportKind::Func, 2);
    exports.export("consumer_memory", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    {
        let mut func = Function::new([]);
        // f_A() + f_B() * 10
        func.instruction(&Instruction::Call(0)); // f from providerA
        func.instruction(&Instruction::Call(1)); // f from providerB
        func.instruction(&Instruction::I32Const(10));
        func.instruction(&Instruction::I32Mul);
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::End);
        code.function(&func);
    }

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

/// Build a P2 component with two provider modules and one consumer
/// module, wired through `InstanceSection` so the instance-graph resolver
/// produces two `ModuleResolution`s sharing `import_name = "f"` but with
/// different `from_import_module`s.
fn build_two_provider_component() -> Vec<u8> {
    let provider_a = build_provider_module(1);
    let provider_b = build_provider_module(2);
    let consumer = build_consumer_module();

    let mut component = Component::new();
    component.section(&ModuleSection(&provider_a));
    component.section(&ModuleSection(&provider_b));
    component.section(&ModuleSection(&consumer));

    let mut inst = InstanceSection::new();
    let no_args: Vec<(&str, ModuleArg)> = vec![];
    // instance 0 = provider A, instance 1 = provider B
    inst.instantiate(0, no_args.clone());
    inst.instantiate(1, no_args);
    // instance 2 = consumer wired with providerA = inst 0, providerB = inst 1
    inst.instantiate(
        2,
        vec![
            (PROVIDER_A, ModuleArg::Instance(0)),
            (PROVIDER_B, ModuleArg::Instance(1)),
        ],
    );
    component.section(&inst);

    component.finish()
}

fn fuse_config() -> FuserConfig {
    FuserConfig {
        // MultiMemory + each module has its own memory =>
        // every cross-module call needs an intra-component adapter,
        // exercising the buggy promotion path in
        // `identify_intra_component_adapter_sites`.
        memory_strategy: MemoryStrategy::MultiMemory,
        output_format: OutputFormat::CoreModule,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        opaque_resources: Vec::new(),
    }
}

/// Item 5 PoC: with two intra-component imports sharing the same field
/// name but different `module` strings, the merger must route each call
/// to its correct upstream export. Pre-fix, both calls collapsed to the
/// same export and `run()` returned `11` or `22` instead of `21`.
#[test]
fn issue112_item5_intra_component_same_name_different_module() {
    let component_bytes = build_two_provider_component();

    let mut fuser = Fuser::new(fuse_config());
    fuser
        .add_component_named(&component_bytes, Some("issue-112-item5"))
        .expect("add_component");
    let fused = fuser.fuse().expect("fuse");

    let mut features = wasmparser::WasmFeatures::default();
    features.set(wasmparser::WasmFeatures::MULTI_MEMORY, true);
    let mut validator = wasmparser::Validator::new_with_features(features);
    validator
        .validate_all(&fused)
        .expect("issue112 item5: fused module must validate");

    let mut engine_config = wasmtime::Config::new();
    engine_config.wasm_multi_memory(true);
    let engine = wasmtime::Engine::new(&engine_config).unwrap();
    let module = wasmtime::Module::new(&engine, &fused).unwrap();
    let mut store = wasmtime::Store::new(&engine, ());
    let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();

    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap();
    let result = run.call(&mut store, ()).unwrap();

    // Correct routing: f_A() + f_B()*10 = 1 + 2*10 = 21.
    // Buggy routing collapses both calls to the same upstream export:
    //   1 + 1*10 = 11  or  2 + 2*10 = 22.
    assert_eq!(
        result, 21,
        "run() must resolve providerA.f -> 1 and providerB.f -> 2 \
         distinctly. Got {result}: the merger routed both imports to the \
         same upstream export (LS-R-10 / UCA-R-3 regression: \
         identify_intra_component_adapter_sites dropped \
         from_import_module disambiguator)."
    );
}

/// Item 4 PoC: fusing the same input twice must produce byte-equal
/// output. Even though `graph.resolved_imports` (a HashMap) is
/// non-deterministically iterated when populating `adapter_sites`, the
/// final adapter ordering must be stable across processes.
///
/// We use the same two-provider fixture to give the cross-component and
/// intra-component adapter paths something to enumerate, and run the full
/// fuse pipeline five times in fresh `Fuser`s (each Fuser has its own
/// HashMap instances with independently-randomised seeds).
#[test]
fn issue112_item4_adapter_sites_determinism() {
    let component_bytes = build_two_provider_component();
    let config = fuse_config();

    let mut reference_fuser = Fuser::new(config.clone());
    reference_fuser
        .add_component_named(&component_bytes, Some("issue-112-item4"))
        .expect("add_component");
    let reference = reference_fuser.fuse().expect("reference fuse");

    for iteration in 1..=5 {
        let mut fuser = Fuser::new(config.clone());
        fuser
            .add_component_named(&component_bytes, Some("issue-112-item4"))
            .expect("add_component");
        let output = fuser.fuse().expect("repeat fuse");

        assert_eq!(
            reference, output,
            "fusion output diverged on iteration {iteration} \
             (LS-CP-3 / SR-19 regression: graph.adapter_sites was not \
             sorted after collection from a HashMap-iterated source)."
        );
    }
}
