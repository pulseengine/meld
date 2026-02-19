//! Cross-component call integration test
//!
//! Verifies the full pipeline: parser → resolver (import/export matching) →
//! merger (index remapping of call targets) → encoder.
//!
//! Component A's module exports `add(i32, i32) -> i32`.
//! Component B's module imports `add`, defines `run() -> i32` that calls
//! `add(3, 4)`, and exports `run`.
//!
//! After fusion, calling `run()` must return 7.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection, ImportSection,
    Instruction, MemorySection, MemoryType, Module, ModuleSection, TypeSection,
};
use wasmtime::{Config, Engine, Instance, Linker, Module as RuntimeModule, Store};

/// Build a component containing both core modules (A and B).
///
/// Module A (index 0): exports `add(i32, i32) -> i32` and `memory`.
/// Module B (index 1): imports `add` from module "A", exports `run() -> i32`
///   which calls `add(3, 4)`.
fn build_two_module_component() -> Vec<u8> {
    let mut component = Component::new();
    component.section(&ModuleSection(&build_module_a()));
    component.section(&ModuleSection(&build_module_b()));
    component.finish()
}

/// Core module A: defines `add` and a shared memory.
fn build_module_a() -> Module {
    let mut types = TypeSection::new();
    // type 0: (i32, i32) -> i32
    types.ty().function(
        [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
        [wasm_encoder::ValType::I32],
    );

    let mut functions = FunctionSection::new();
    functions.function(0); // add: type 0

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: Some(2),
        memory64: false,
        shared: true,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export("add", ExportKind::Func, 0);
    exports.export("memory", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    let mut add_fn = Function::new([]);
    add_fn.instruction(&Instruction::LocalGet(0));
    add_fn.instruction(&Instruction::LocalGet(1));
    add_fn.instruction(&Instruction::I32Add);
    add_fn.instruction(&Instruction::End);
    code.function(&add_fn);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&exports)
        .section(&code);

    module
}

/// Core module B: imports `add`, defines `run` that calls `add(3, 4)`.
fn build_module_b() -> Module {
    let mut types = TypeSection::new();
    // type 0: (i32, i32) -> i32  — signature of the imported `add`
    types.ty().function(
        [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
        [wasm_encoder::ValType::I32],
    );
    // type 1: () -> i32  — signature of `run`
    types.ty().function([], [wasm_encoder::ValType::I32]);

    let mut imports = ImportSection::new();
    imports.import("A", "add", wasm_encoder::EntityType::Function(0));

    let mut functions = FunctionSection::new();
    functions.function(1); // run: type 1

    let mut exports = ExportSection::new();
    // run is at function index 1 (index 0 is the imported `add`)
    exports.export("run", ExportKind::Func, 1);

    let mut code = CodeSection::new();
    let mut run_fn = Function::new([]);
    // call add(3, 4) — `add` is function index 0 (the import)
    run_fn.instruction(&Instruction::I32Const(3));
    run_fn.instruction(&Instruction::I32Const(4));
    run_fn.instruction(&Instruction::Call(0));
    run_fn.instruction(&Instruction::End);
    code.function(&run_fn);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&imports)
        .section(&functions)
        .section(&exports)
        .section(&code);

    module
}

#[test]
fn test_cross_module_call() {
    let component = build_two_module_component();

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        attestation: false,
        ..Default::default()
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component, Some("cross-call-test"))
        .unwrap();

    let fused = fuser.fuse().unwrap();

    // Set up wasmtime to run the fused module
    let mut engine_config = Config::new();
    engine_config.wasm_threads(true);
    engine_config.shared_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // Call run(), which internally calls add(3, 4)
    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap();
    let result = run.call(&mut store, ()).unwrap();
    assert_eq!(result, 7, "run() should return add(3, 4) = 7");
}

#[test]
fn test_cross_module_call_with_different_args() {
    // Same structure but verify the actual function, not just a constant
    let component = build_two_module_component();

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        attestation: false,
        ..Default::default()
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component, Some("cross-call-test"))
        .unwrap();

    let (fused, stats) = fuser.fuse_with_stats().unwrap();

    // The resolver should have matched B's import to A's export
    assert!(
        stats.imports_resolved > 0 || stats.modules_merged == 2,
        "expected resolved imports or two merged modules"
    );

    let mut engine_config = Config::new();
    engine_config.wasm_threads(true);
    engine_config.shared_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // Verify the `add` function is directly callable too
    let add = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "add")
        .unwrap();
    let sum = add.call(&mut store, (10, 20)).unwrap();
    assert_eq!(sum, 30, "add(10, 20) should return 30");
}

// ---------------------------------------------------------------------------
// Test: unresolved host import + intra-component call
// ---------------------------------------------------------------------------

/// Module A: defines `add(i32, i32) -> i32`, exports it and `memory`.
fn build_module_a_provider() -> Module {
    let mut types = TypeSection::new();
    // type 0: (i32, i32) -> i32
    types.ty().function(
        [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
        [wasm_encoder::ValType::I32],
    );

    let mut functions = FunctionSection::new();
    functions.function(0); // add: type 0

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export("add", ExportKind::Func, 0);
    exports.export("memory", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    let mut add_fn = Function::new([]);
    add_fn.instruction(&Instruction::LocalGet(0));
    add_fn.instruction(&Instruction::LocalGet(1));
    add_fn.instruction(&Instruction::I32Add);
    add_fn.instruction(&Instruction::End);
    code.function(&add_fn);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&exports)
        .section(&code);
    module
}

/// Module B:
///   imports `env.get_value() -> i32` (unresolved — provided by host)
///   imports `A.add(i32, i32) -> i32` (resolved intra-component)
///   defines `run() -> i32` which calls `add(get_value(), 10)`
///   exports `run`
fn build_module_b_with_host_import() -> Module {
    let mut types = TypeSection::new();
    // type 0: () -> i32   — signature of imported get_value and of run
    types.ty().function([], [wasm_encoder::ValType::I32]);
    // type 1: (i32, i32) -> i32  — signature of imported add
    types.ty().function(
        [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
        [wasm_encoder::ValType::I32],
    );

    let mut imports = ImportSection::new();
    // Function index 0: host-provided get_value (unresolved)
    imports.import("env", "get_value", wasm_encoder::EntityType::Function(0));
    // Function index 1: intra-component add (resolved to module A's export)
    imports.import("A", "add", wasm_encoder::EntityType::Function(1));

    let mut functions = FunctionSection::new();
    // Function index 2: run (type 0)
    functions.function(0);

    let mut exports = ExportSection::new();
    exports.export("run", ExportKind::Func, 2);

    let mut code = CodeSection::new();
    let mut run_fn = Function::new([]);
    // result = add(get_value(), 10)
    run_fn.instruction(&Instruction::Call(0)); // get_value() -> i32
    run_fn.instruction(&Instruction::I32Const(10));
    run_fn.instruction(&Instruction::Call(1)); // add(get_value_result, 10) -> i32
    run_fn.instruction(&Instruction::End);
    code.function(&run_fn);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&imports)
        .section(&functions)
        .section(&exports)
        .section(&code);
    module
}

/// Regression test for Doubt 5: function_index_map values must be absolute
/// wasm indices (offset by import count), not 0-based array positions.
///
/// Without the fix, module B's `run` would call the wrong function:
/// `call 0` (get_value) works by coincidence, but `call 1` (add) gets
/// rewritten to `call 0` (the array position of add), which actually calls
/// the import `get_value` instead of the defined function `add`.
#[test]
fn test_unresolved_import_index_offset() {
    let mut component = Component::new();
    component.section(&ModuleSection(&build_module_a_provider()));
    component.section(&ModuleSection(&build_module_b_with_host_import()));
    let component_bytes = component.finish();

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component_bytes, Some("host-import-test"))
        .unwrap();

    let fused = fuser.fuse().unwrap();

    // The fused module should have one unresolved import (env.get_value).
    // Set up wasmtime with a Linker to provide that import.
    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());

    let mut linker = Linker::new(&engine);
    // Provide get_value() -> 32
    linker
        .func_wrap("env", "get_value", || -> i32 { 32 })
        .unwrap();

    let instance = linker.instantiate(&mut store, &module).unwrap();

    // run() should call add(get_value(), 10) = add(32, 10) = 42
    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap();
    let result = run.call(&mut store, ()).unwrap();
    assert_eq!(
        result, 42,
        "run() should return add(get_value(), 10) = add(32, 10) = 42"
    );
}
