//! Runtime test for FromExports-style instance resolution.
//!
//! Builds a synthetic 2-module component where Module 1 imports a function
//! from Module 0 via an indirect wiring path (Module 0 exports, Module 1
//! imports by name). This verifies that the entity provenance system and
//! flat name-matching resolution correctly resolve indirect references.
//!
//! Module 0 (`$provider`):
//!   - Defines memory, exports `compute(i32) -> i32` (doubles the arg)
//!   - Exports `memory`
//!
//! Module 1 (`$caller`):
//!   - Imports `compute` from Module 0
//!   - Defines own memory
//!   - Exports `run() -> i32` which calls `compute(21)`
//!
//! After fusion: `run()` should return 42 (compute(21) = 21 * 2).

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection, ImportSection,
    Instruction, MemorySection, MemoryType, Module, ModuleSection, TypeSection,
};
use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};

/// Core Module 0: defines `compute(x) -> x * 2` and memory
fn build_provider_module() -> Module {
    let mut types = TypeSection::new();
    // type 0: (i32) -> i32
    types
        .ty()
        .function([wasm_encoder::ValType::I32], [wasm_encoder::ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0); // compute: type 0

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export("compute", ExportKind::Func, 0);
    exports.export("memory", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    let mut f = Function::new([]);
    f.instruction(&Instruction::LocalGet(0));
    f.instruction(&Instruction::I32Const(2));
    f.instruction(&Instruction::I32Mul);
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

/// Core Module 1: imports `compute` from Module 0,
/// exports `run() -> compute(21)`
fn build_caller_module() -> Module {
    let mut types = TypeSection::new();
    // type 0: (i32) -> i32 (compute signature)
    types
        .ty()
        .function([wasm_encoder::ValType::I32], [wasm_encoder::ValType::I32]);
    // type 1: () -> i32 (run signature)
    types.ty().function([], [wasm_encoder::ValType::I32]);

    let mut imports = ImportSection::new();
    imports.import("provider", "compute", wasm_encoder::EntityType::Function(0));

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
    exports.export("caller_memory", ExportKind::Memory, 0);

    let mut code = CodeSection::new();
    let mut f = Function::new([]);
    f.instruction(&Instruction::I32Const(21));
    f.instruction(&Instruction::Call(0)); // call compute (import at idx 0)
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

/// Build a component with provider and caller modules
fn build_two_module_component() -> Vec<u8> {
    let mut component = Component::new();
    component.section(&ModuleSection(&build_provider_module()));
    component.section(&ModuleSection(&build_caller_module()));
    component.finish()
}

#[test]
fn test_from_exports_resolution_runtime() {
    let component = build_two_module_component();

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
        .add_component_named(&component, Some("from-exports-test"))
        .unwrap();

    let (fused, stats) = fuser.fuse_with_stats().unwrap();

    eprintln!(
        "Fused: {} bytes, {} functions, {} adapters",
        stats.output_size, stats.total_functions, stats.adapter_functions
    );

    // Validate
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("fused output should validate");

    // Execute
    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // run() should return 42: compute(21) = 21 * 2
    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap();
    let result = run.call(&mut store, ()).unwrap();
    assert_eq!(result, 42, "run() should return 42 (compute(21) = 21 * 2)");
}

#[test]
fn test_from_exports_shared_memory_strategy() {
    let component = build_two_module_component();

    // Also test with shared memory strategy
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component, Some("from-exports-shared-test"))
        .unwrap();

    let (fused, stats) = fuser.fuse_with_stats().unwrap();

    eprintln!(
        "Fused (shared): {} bytes, {} functions",
        stats.output_size, stats.total_functions
    );

    // Validate
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("fused output should validate");

    // Execute — shared memory doesn't need multi-memory engine flag
    let engine = Engine::default();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap();
    let result = run.call(&mut store, ()).unwrap();
    assert_eq!(
        result, 42,
        "run() should return 42 (compute(21) = 21 * 2) with shared memory"
    );
}

/// Verify the function count is reasonable: the two modules' defined functions
/// should be merged without duplication.
#[test]
fn test_from_exports_function_count() {
    let component = build_two_module_component();

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
        .add_component_named(&component, Some("func-count-test"))
        .unwrap();

    let (fused, stats) = fuser.fuse_with_stats().unwrap();

    // Module 0 has 1 defined function (compute)
    // Module 1 has 1 defined function (run) + 1 import (compute)
    // After fusion: 2 defined functions, 0 unresolved imports
    assert_eq!(
        stats.total_functions, 2,
        "Expected 2 defined functions (compute + run)"
    );
    assert_eq!(
        stats.imports_resolved, 0,
        "No component-level imports to resolve"
    );

    // Verify no imports in the fused output
    let parser = wasmparser::Parser::new(0);
    let mut import_count = 0u32;
    for payload in parser.parse_all(&fused) {
        if let Ok(wasmparser::Payload::ImportSection(reader)) = payload {
            for _ in reader {
                import_count += 1;
            }
        }
    }
    assert_eq!(import_count, 0, "No imports should remain after fusion");
}
