//! Multi-memory integration tests
//!
//! Verifies that the fusion pipeline preserves per-component memory isolation
//! when using `MemoryStrategy::MultiMemory`.
//!
//! Test 1 (`test_multi_memory_separate_memories`):
//!   A single component with two core modules, each owning its own memory.
//!   Module A exports `get_value() -> i32` (loads from offset 0 of its memory)
//!   and its memory. Module B imports `get_value` from "A" and exports
//!   `run() -> i32` which calls `get_value`. After fusion the output must
//!   contain two memories and `run()` must return 0 (zero-initialized memory).
//!
//! Test 2 (`test_multi_memory_preserves_isolation`):
//!   Two separate components, each with one core module and its own memory.
//!   Component A exports `get_a() -> i32`, Component B exports `get_b() -> i32`.
//!   After fusion both memories must be present and both exports callable.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection, ImportSection,
    Instruction, MemorySection, MemoryType, Module, ModuleSection, TypeSection,
};
use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};

// ---------------------------------------------------------------------------
// Helpers for test 1: single component, two core modules
// ---------------------------------------------------------------------------

/// Core module A: defines its own memory (1 page, not shared), exports
/// `get_value() -> i32` which does `i32.load offset=0` from memory 0, and
/// exports `memory`.
fn build_module_a_with_memory() -> Module {
    let mut types = TypeSection::new();
    // type 0: () -> i32
    types.ty().function([], [wasm_encoder::ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0); // get_value: type 0

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export("get_value", ExportKind::Func, 0);
    exports.export("memory", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    let mut get_value_fn = Function::new([]);
    // i32.load offset=0 from memory 0 address 0
    get_value_fn.instruction(&Instruction::I32Const(0));
    get_value_fn.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
        offset: 0,
        align: 2, // 4-byte alignment
        memory_index: 0,
    }));
    get_value_fn.instruction(&Instruction::End);
    code.function(&get_value_fn);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&exports)
        .section(&code);

    module
}

/// Core module B: defines its own memory (1 page, not shared), imports
/// `get_value` from "A", and exports `run() -> i32` which calls `get_value`.
fn build_module_b_calls_a() -> Module {
    let mut types = TypeSection::new();
    // type 0: () -> i32  -- signature of imported `get_value` and of `run`
    types.ty().function([], [wasm_encoder::ValType::I32]);

    let mut imports = ImportSection::new();
    imports.import("A", "get_value", wasm_encoder::EntityType::Function(0));

    let mut functions = FunctionSection::new();
    functions.function(0); // run: type 0

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    // run is function index 1 (index 0 is the imported `get_value`)
    exports.export("run", ExportKind::Func, 1);
    exports.export("memory_b", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    let mut run_fn = Function::new([]);
    // call get_value() -- function index 0 (the import)
    run_fn.instruction(&Instruction::Call(0));
    run_fn.instruction(&Instruction::End);
    code.function(&run_fn);

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

/// Build a single component containing modules A and B.
fn build_two_module_component_multi_memory() -> Vec<u8> {
    let mut component = Component::new();
    component.section(&ModuleSection(&build_module_a_with_memory()));
    component.section(&ModuleSection(&build_module_b_calls_a()));
    component.finish()
}

// ---------------------------------------------------------------------------
// Helpers for test 2: two separate components, each with one module + memory
// ---------------------------------------------------------------------------

/// Build a standalone component wrapping a single core module that defines
/// its own memory and exports a function that loads i32 from offset 0.
fn build_single_module_component(func_export_name: &str, mem_export_name: &str) -> Vec<u8> {
    let mut types = TypeSection::new();
    // type 0: () -> i32
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
    exports.export(func_export_name, ExportKind::Func, 0);
    exports.export(mem_export_name, ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    let mut func = Function::new([]);
    func.instruction(&Instruction::I32Const(0));
    func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
        offset: 0,
        align: 2,
        memory_index: 0,
    }));
    func.instruction(&Instruction::End);
    code.function(&func);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&exports)
        .section(&code);

    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

/// Count the number of memory exports on a wasmtime instance.
fn count_memory_exports(instance: &Instance, store: &mut Store<()>) -> usize {
    instance
        .exports(&mut *store)
        .filter(|e| e.clone().into_memory().is_some())
        .count()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn test_multi_memory_separate_memories() {
    let component = build_two_module_component_multi_memory();

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Merge,
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component, Some("multi-mem-test"))
        .unwrap();

    let fused = fuser.fuse().unwrap();

    // The fused module must validate and be instantiable with multi-memory.
    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // Verify the output contains 2 memories (one per original module).
    let mem_count = count_memory_exports(&instance, &mut store);
    assert_eq!(
        mem_count, 2,
        "fused module should export 2 memories (one per original core module)"
    );

    // Call run(), which internally calls get_value(). Memory is zero-initialized
    // so we expect 0.
    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap();
    let result = run.call(&mut store, ()).unwrap();
    assert_eq!(
        result, 0,
        "run() should return 0 (zero-initialized memory at offset 0)"
    );
}

#[test]
fn test_multi_memory_preserves_isolation() {
    // Two separate components, each with its own memory.
    let component_a = build_single_module_component("get_a", "memory_a");
    let component_b = build_single_module_component("get_b", "memory_b");

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Merge,
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component_a, Some("component-a"))
        .unwrap();
    fuser
        .add_component_named(&component_b, Some("component-b"))
        .unwrap();

    let fused = fuser.fuse().unwrap();

    // Multi-memory support required for the fused output.
    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // Verify the output contains 2 memories.
    let mem_count = count_memory_exports(&instance, &mut store);
    assert_eq!(
        mem_count, 2,
        "fused module should export 2 memories (one per component)"
    );

    // Both exports must be callable and return 0 (zero-initialized memory).
    let get_a = instance
        .get_typed_func::<(), i32>(&mut store, "get_a")
        .unwrap();
    let result_a = get_a.call(&mut store, ()).unwrap();
    assert_eq!(
        result_a, 0,
        "get_a() should return 0 (zero-initialized memory)"
    );

    let get_b = instance
        .get_typed_func::<(), i32>(&mut store, "get_b")
        .unwrap();
    let result_b = get_b.call(&mut store, ()).unwrap();
    assert_eq!(
        result_b, 0,
        "get_b() should return 0 (zero-initialized memory)"
    );
}
