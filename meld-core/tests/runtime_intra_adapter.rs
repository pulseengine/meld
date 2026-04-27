//! Runtime test for intra-component adapter wiring and multi-memory isolation.
//!
//! Builds a synthetic component with 3 core modules that exercise:
//! - Intra-component module resolution (Module 1 imports from Module 0)
//! - Multi-memory isolation (Module 0+1 share a memory, Module 2 has its own)
//! - Cross-module function calls through the fusion pipeline
//!
//! Module 0 (`$main`):
//!   - Defines memory, exports `memory`, `transform(i32, i32) -> i32` (adds args)
//!
//! Module 1 (`$helper`):
//!   - Imports memory from Module 0, imports `transform` from Module 0
//!   - Exports `process(i32) -> i32` which calls `transform(arg, 100)`
//!   - Exports `cabi_realloc`
//!
//! Module 2 (`$consumer`):
//!   - Imports `process` from Module 1, defines own memory
//!   - Exports `run() -> i32` which calls `process(42)`
//!
//! After fusion: `run()` should return 142 (transform(42, 100) = 42 + 100).

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection, ImportSection,
    Instruction, MemorySection, MemoryType, Module, ModuleSection, TypeSection,
};
use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};

/// Core Module 0: defines memory and `transform(a, b) -> a + b`
fn build_module_main() -> Module {
    let mut types = TypeSection::new();
    // type 0: (i32, i32) -> i32
    types.ty().function(
        [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
        [wasm_encoder::ValType::I32],
    );

    let mut functions = FunctionSection::new();
    functions.function(0); // transform: type 0

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export("transform", ExportKind::Func, 0);
    exports.export("memory", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    let mut f = Function::new([]);
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::LocalGet(1));
    f.instruction(&Instruction::I32Add);
    f.instruction(&Instruction::End);
    code.function(&f);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&exports)
        .section(&code);
    module
}

/// Core Module 1: imports memory + transform from Module 0,
/// exports `process(x) -> transform(x, 100)` and `cabi_realloc`
fn build_module_helper() -> Module {
    let mut types = TypeSection::new();
    // type 0: (i32, i32) -> i32  (transform signature)
    types.ty().function(
        [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
        [wasm_encoder::ValType::I32],
    );
    // type 1: (i32) -> i32  (process signature)
    types
        .ty()
        .function([wasm_encoder::ValType::I32], [wasm_encoder::ValType::I32]);
    // type 2: (i32, i32, i32, i32) -> i32  (cabi_realloc signature)
    types.ty().function(
        [
            wasm_encoder::ValType::I32,
            wasm_encoder::ValType::I32,
            wasm_encoder::ValType::I32,
            wasm_encoder::ValType::I32,
        ],
        [wasm_encoder::ValType::I32],
    );

    let mut imports = ImportSection::new();
    imports.import("main", "transform", wasm_encoder::EntityType::Function(0));
    imports.import(
        "main",
        "memory",
        wasm_encoder::EntityType::Memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        }),
    );

    let mut functions = FunctionSection::new();
    functions.function(1); // process: type 1 (func index 1, since import is 0)
    functions.function(2); // cabi_realloc: type 2 (func index 2)

    let mut exports = ExportSection::new();
    exports.export("process", ExportKind::Func, 1);
    exports.export("cabi_realloc", ExportKind::Func, 2);

    let mut code = CodeSection::new();

    // func 1: process(x) -> transform(x, 100)
    {
        let mut f = Function::new([]);
        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::I32Const(100));
        f.instruction(&Instruction::Call(0)); // call transform (import at idx 0)
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 2: cabi_realloc — trivial stub returning 0
    {
        let mut f = Function::new([]);
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    let mut module = Module::new();
    module
        .section(&types)
        .section(&imports)
        .section(&functions)
        .section(&exports)
        .section(&code);
    module
}

/// Core Module 2: imports `process` from Module 1, defines own memory,
/// exports `run() -> process(42)`
fn build_module_consumer() -> Module {
    let mut types = TypeSection::new();
    // type 0: (i32) -> i32  (process signature)
    types
        .ty()
        .function([wasm_encoder::ValType::I32], [wasm_encoder::ValType::I32]);
    // type 1: () -> i32  (run signature)
    types.ty().function([], [wasm_encoder::ValType::I32]);

    let mut imports = ImportSection::new();
    imports.import("helper", "process", wasm_encoder::EntityType::Function(0));

    let mut functions = FunctionSection::new();
    functions.function(1); // run: type 1 (func index 1, since import is 0)

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export("run", ExportKind::Func, 1);
    exports.export("consumer_memory", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    let mut f = Function::new([]);
    f.instruction(&Instruction::I32Const(42));
    f.instruction(&Instruction::Call(0)); // call process (import at idx 0)
    f.instruction(&Instruction::End);
    code.function(&f);

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

/// Build a component with all 3 modules
fn build_three_module_component() -> Vec<u8> {
    let mut component = Component::new();
    component.section(&ModuleSection(&build_module_main()));
    component.section(&ModuleSection(&build_module_helper()));
    component.section(&ModuleSection(&build_module_consumer()));
    component.finish()
}

#[test]
fn test_intra_component_three_module_fusion() {
    let component = build_three_module_component();

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component, Some("three-module-test"))
        .unwrap();

    let (fused, stats) = fuser.fuse_with_stats().unwrap();

    eprintln!(
        "Fused: {} bytes, {} functions, {} adapters, {} imports resolved",
        stats.output_size, stats.total_functions, stats.adapter_functions, stats.imports_resolved
    );

    // Validate the output
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("fused output should validate");

    // Execute with wasmtime
    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // run() should return 142: transform(42, 100) = 42 + 100
    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap();
    let result = run.call(&mut store, ()).unwrap();
    assert_eq!(
        result, 142,
        "run() should return 142 (transform(42, 100) = 42 + 100)"
    );
}

#[test]
fn test_intra_component_memory_count() {
    let component = build_three_module_component();

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component, Some("mem-count-test"))
        .unwrap();

    let fused = fuser.fuse().unwrap();

    // Count memories in the fused output
    let parser = wasmparser::Parser::new(0);
    let mut memory_count = 0u32;
    for payload in parser.parse_all(&fused) {
        if let Ok(wasmparser::Payload::MemorySection(reader)) = payload {
            memory_count += reader.count();
        }
    }

    // Module 0 defines memory, Module 1 imports it (shares), Module 2 has own
    // So we expect 2 memories: one shared by Module 0+1, one for Module 2
    assert!(
        memory_count <= 2,
        "Expected at most 2 memories (shared + consumer), got {}",
        memory_count
    );
    assert!(
        memory_count >= 1,
        "Expected at least 1 memory, got {}",
        memory_count
    );

    eprintln!("Memory count in fused output: {}", memory_count);
}
