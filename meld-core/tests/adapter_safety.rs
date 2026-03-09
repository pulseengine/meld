//! Adapter safety tests (SR-12, SR-13, SR-15, SR-16)
//!
//! These tests verify the correctness of adapter generation for cross-component
//! calls involving pointer-passing types (strings, lists) in multi-memory mode.
//!
//! Each test builds two P2 components programmatically, fuses them with
//! `MemoryStrategy::MultiMemory`, then runs the fused output through wasmtime
//! to verify correctness at runtime.
//!
//! ## Safety Requirement Coverage
//!
//! - **SR-12**: Adapter generation for all pointer-passing cross-component calls.
//!   A string parameter is passed across components and the adapter correctly
//!   allocates, copies, and invokes the callee.
//!
//! - **SR-13**: Correct cabi_realloc targeting. Each component's allocator is
//!   called in the correct memory — the adapter allocates in the callee's memory
//!   (not the caller's) for outbound argument copy.
//!
//! - **SR-15**: Correct list copy length. A `list<u32>` of known length is passed
//!   across components and the adapter copies `len * 4` bytes.
//!
//! - **SR-16**: Recursive inner pointer fixup. A `list<string>` is passed across
//!   components and the adapter fixes up inner string pointers after the bulk copy.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    Alias, CanonicalFunctionSection, CanonicalOption, CodeSection, Component,
    ComponentAliasSection, ComponentExportKind, ComponentExportSection, ComponentImportSection,
    ComponentTypeRef, ComponentTypeSection, ConstExpr, DataSection, DataSegment, DataSegmentMode,
    ExportKind, ExportSection, Function, FunctionSection, GlobalSection, GlobalType, ImportSection,
    InstanceSection, Instruction, MemorySection, MemoryType, Module, ModuleArg, ModuleSection,
    TypeSection,
};
use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};

// ===========================================================================
// Shared helper: build a core module with cabi_realloc (bump allocator)
// ===========================================================================

/// Build a minimal `cabi_realloc(orig_ptr, orig_size, align, new_size) -> ptr`
/// as a bump allocator using a mutable global. The memory index and global index
/// are parameterized so the module can be self-contained.
fn emit_cabi_realloc(func: &mut Function, bump_global: u32) {
    // return current bump; bump += new_size
    func.instruction(&Instruction::GlobalGet(bump_global));
    func.instruction(&Instruction::GlobalGet(bump_global));
    func.instruction(&Instruction::LocalGet(3)); // new_size
    func.instruction(&Instruction::I32Add);
    func.instruction(&Instruction::GlobalSet(bump_global));
    func.instruction(&Instruction::End);
}

// ===========================================================================
// SR-12: Adapter generation for string-passing cross-component call
// ===========================================================================

/// Build a callee P2 component that exports a function taking a string param.
///
/// The callee's core function signature is `(i32, i32) -> i32` representing
/// `(ptr, len) -> sum_of_bytes`. The component-level type is
/// `(func (param "s" string) (result u32))`.
///
/// The core module:
///   - Defines memory (1 page)
///   - Exports `cabi_realloc` (bump allocator)
///   - Exports `test:api/api#process-string` which sums bytes from its memory
fn build_callee_string_component() -> Vec<u8> {
    // --- Build core module ---
    let core_module = {
        let mut types = TypeSection::new();
        // type 0: (i32, i32, i32, i32) -> i32 -- cabi_realloc
        types.ty().function(
            [
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
            ],
            [wasm_encoder::ValType::I32],
        );
        // type 1: (i32, i32) -> i32 -- process-string (ptr, len) -> sum
        types.ty().function(
            [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            [wasm_encoder::ValType::I32],
        );

        let mut functions = FunctionSection::new();
        functions.function(0); // func 0: cabi_realloc
        functions.function(1); // func 1: process-string

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        // global 0: mutable i32 bump pointer (starts at 1024 to avoid data segment area)
        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: wasm_encoder::ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(1024),
        );

        let mut exports = ExportSection::new();
        exports.export("cabi_realloc", ExportKind::Func, 0);
        exports.export("test:api/api#process-string", ExportKind::Func, 1);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();

        // func 0: cabi_realloc
        {
            let mut f = Function::new([]);
            emit_cabi_realloc(&mut f, 0);
            code.function(&f);
        }

        // func 1: process-string(ptr: i32, len: i32) -> i32
        // Sums all bytes from memory[ptr..ptr+len]
        {
            // locals: param 0=ptr, param 1=len, local 2=sum, local 3=index
            let mut f = Function::new(vec![(2, wasm_encoder::ValType::I32)]);
            f.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
            f.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

            // if index >= len, break
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::LocalGet(1));
            f.instruction(&Instruction::I32GeU);
            f.instruction(&Instruction::BrIf(1));

            // sum += load_u8(memory 0, ptr + index)
            f.instruction(&Instruction::LocalGet(0));
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::I32Load8U(wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: 0,
            }));
            f.instruction(&Instruction::LocalGet(2));
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::LocalSet(2));

            // index += 1
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::I32Const(1));
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::LocalSet(3));

            f.instruction(&Instruction::Br(0));
            f.instruction(&Instruction::End); // loop
            f.instruction(&Instruction::End); // block

            f.instruction(&Instruction::LocalGet(2));
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        let mut module = Module::new();
        module
            .section(&types)
            .section(&functions)
            .section(&memory)
            .section(&globals)
            .section(&exports)
            .section(&code);
        module
    };

    // --- Build P2 component ---
    let mut component = Component::new();

    // 1. Embed core module (core module index 0)
    component.section(&ModuleSection(&core_module));

    // 2. Define component function type: (func (param "s" string) (result u32))
    //    This is component type index 0.
    {
        let mut types = ComponentTypeSection::new();
        types
            .function()
            .params([(
                "s",
                wasm_encoder::ComponentValType::Primitive(wasm_encoder::PrimitiveValType::String),
            )])
            .result(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            ));
        component.section(&types);
    }

    // 3. Instantiate the core module (core instance 0)
    {
        let mut inst = InstanceSection::new();
        let no_args: Vec<(&str, ModuleArg)> = vec![];
        inst.instantiate(0, no_args);
        component.section(&inst);
    }

    // 4. Alias core exports from instance 0
    //    This creates core function indices in the component's core function space.
    //    core func 0 = cabi_realloc, core func 1 = process-string, core memory 0 = memory
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Func,
            name: "cabi_realloc",
        });
        component.section(&aliases);
    }
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Func,
            name: "test:api/api#process-string",
        });
        component.section(&aliases);
    }
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Memory,
            name: "memory",
        });
        component.section(&aliases);
    }

    // 5. Canon lift: lift core func 1 (process-string) as component func type 0
    //    with UTF-8 encoding + memory 0 + realloc 0
    {
        let mut canon = CanonicalFunctionSection::new();
        canon.lift(
            1, // core func index: process-string
            0, // component type index: the function type we defined
            [
                CanonicalOption::UTF8,
                CanonicalOption::Memory(0),
                CanonicalOption::Realloc(0), // cabi_realloc
            ],
        );
        component.section(&canon);
    }

    // 6. Export the lifted function
    {
        let mut exp = ComponentExportSection::new();
        exp.export(
            "test:api/api",
            ComponentExportKind::Func,
            0, // component func index 0 (the lifted function)
            None,
        );
        component.section(&exp);
    }

    component.finish()
}

/// Build a caller P2 component that imports a string-processing function and calls it.
///
/// The core module:
///   - Defines memory with "Hello" at offset 0
///   - Imports `test:api/api#process-string` as `(i32, i32) -> i32`
///   - Exports `run() -> i32` which calls process-string(0, 5)
///   - Exports `cabi_realloc` (needed for result copy if any)
fn build_caller_string_component() -> Vec<u8> {
    let core_module = {
        let mut types = TypeSection::new();
        // type 0: (i32, i32) -> i32  -- imported process-string
        types.ty().function(
            [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            [wasm_encoder::ValType::I32],
        );
        // type 1: () -> i32  -- run
        types.ty().function([], [wasm_encoder::ValType::I32]);
        // type 2: (i32, i32, i32, i32) -> i32  -- cabi_realloc
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
        imports.import(
            "test:api/api",
            "process-string",
            wasm_encoder::EntityType::Function(0),
        );

        let mut functions = FunctionSection::new();
        functions.function(1); // func 1: run (func 0 is the import)
        functions.function(2); // func 2: cabi_realloc

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        // global 0: bump pointer for cabi_realloc (start at 1024)
        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: wasm_encoder::ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(1024),
        );

        let mut exports = ExportSection::new();
        exports.export("run", ExportKind::Func, 1);
        exports.export("cabi_realloc", ExportKind::Func, 2);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();

        // func 1: run() -> i32
        // Call process-string(0, 5) -- "Hello" is at offset 0, length 5
        {
            let mut f = Function::new([]);
            f.instruction(&Instruction::I32Const(0)); // ptr
            f.instruction(&Instruction::I32Const(5)); // len
            f.instruction(&Instruction::Call(0)); // process-string (import)
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        // func 2: cabi_realloc
        {
            let mut f = Function::new([]);
            emit_cabi_realloc(&mut f, 0);
            code.function(&f);
        }

        // Data segment: "Hello" at offset 0 in memory 0
        let mut data = DataSection::new();
        data.segment(DataSegment {
            mode: DataSegmentMode::Active {
                memory_index: 0,
                offset: &ConstExpr::i32_const(0),
            },
            data: b"Hello".to_vec(),
        });

        let mut module = Module::new();
        module
            .section(&types)
            .section(&imports)
            .section(&functions)
            .section(&memory)
            .section(&globals)
            .section(&exports)
            .section(&code)
            .section(&data);
        module
    };

    let mut component = Component::new();

    // Component type 0: (func (param "s" string) (result u32))
    {
        let mut types = ComponentTypeSection::new();
        types
            .function()
            .params([(
                "s",
                wasm_encoder::ComponentValType::Primitive(wasm_encoder::PrimitiveValType::String),
            )])
            .result(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            ));
        component.section(&types);
    }

    // Component import: "test:api/api" as Func(0)
    {
        let mut imports = ComponentImportSection::new();
        imports.import("test:api/api", ComponentTypeRef::Func(0));
        component.section(&imports);
    }

    // Core module
    component.section(&ModuleSection(&core_module));

    component.finish()
}

/// SR-12: Verify adapter generation for string-passing cross-component call.
///
/// Component A (callee) exports a function `process-string(s: string) -> u32`
/// that sums the bytes of the string. Component B (caller) has "Hello" in its
/// memory and calls process-string.
///
/// After fusion in multi-memory mode, the adapter must:
///   1. Allocate in the callee's memory via cabi_realloc
///   2. Copy "Hello" from caller's memory to callee's memory
///   3. Call the callee
///   4. Return the sum (72+101+108+108+111 = 500)
#[test]
fn test_sr12_adapter_generation_for_string_param() {
    let callee = build_callee_string_component();
    let caller = build_caller_string_component();

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        output_format: meld_core::OutputFormat::CoreModule,
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&callee, Some("callee-string"))
        .expect("callee component should parse");
    fuser
        .add_component_named(&caller, Some("caller-string"))
        .expect("caller component should parse");

    let (fused, stats) = fuser.fuse_with_stats().expect("fusion should succeed");

    eprintln!(
        "SR-12: {} bytes, {} funcs, {} adapters, {} imports resolved",
        stats.output_size, stats.total_functions, stats.adapter_functions, stats.imports_resolved,
    );

    // The fusion should produce at least one adapter function for the string-passing call
    assert!(
        stats.adapter_functions > 0,
        "SR-12: expected adapter functions for string-passing cross-component call, got 0"
    );

    // Validate the fused output
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("SR-12: fused output should validate");

    // Run through wasmtime
    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("SR-12: fused module should export 'run'");
    let result = run.call(&mut store, ()).unwrap();

    // "Hello" = [72, 101, 108, 108, 111] -> sum = 500
    assert_eq!(
        result, 500,
        "SR-12: run() should return 500 (sum of ASCII bytes of 'Hello')"
    );
}

// ===========================================================================
// SR-13: Correct cabi_realloc targeting
// ===========================================================================

/// Build a callee component that verifies allocation happens in its own memory.
///
/// The callee writes a sentinel value (0xBE) at byte 0 of its memory during
/// cabi_realloc, then process-string checks that byte 0 == 0xBE. If cabi_realloc
/// is called in the wrong memory, byte 0 of the callee's memory won't have 0xBE.
fn build_callee_realloc_verify_component() -> Vec<u8> {
    let core_module = {
        let mut types = TypeSection::new();
        // type 0: (i32, i32, i32, i32) -> i32 -- cabi_realloc
        types.ty().function(
            [
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
            ],
            [wasm_encoder::ValType::I32],
        );
        // type 1: (i32, i32) -> i32 -- process-string (ptr, len) -> result
        types.ty().function(
            [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            [wasm_encoder::ValType::I32],
        );

        let mut functions = FunctionSection::new();
        functions.function(0); // func 0: cabi_realloc
        functions.function(1); // func 1: process-string

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        // global 0: bump allocator start at 256
        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: wasm_encoder::ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(256),
        );

        let mut exports = ExportSection::new();
        exports.export("cabi_realloc", ExportKind::Func, 0);
        exports.export("test:api/api#check-alloc", ExportKind::Func, 1);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();

        // func 0: cabi_realloc with sentinel
        // Writes 0xBE at byte offset 0 of THIS memory, then bump-allocates.
        {
            let mut f = Function::new([]);
            // Write sentinel: memory[0] = 0xBE
            f.instruction(&Instruction::I32Const(0));
            f.instruction(&Instruction::I32Const(0xBE));
            f.instruction(&Instruction::I32Store8(wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: 0,
            }));
            // Standard bump allocator
            f.instruction(&Instruction::GlobalGet(0));
            f.instruction(&Instruction::GlobalGet(0));
            f.instruction(&Instruction::LocalGet(3)); // new_size
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::GlobalSet(0));
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        // func 1: check-alloc(ptr, len) -> i32
        // Returns memory[0] (should be 0xBE if cabi_realloc was called in this memory)
        {
            let mut f = Function::new([]);
            f.instruction(&Instruction::I32Const(0));
            f.instruction(&Instruction::I32Load8U(wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: 0,
            }));
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        let mut module = Module::new();
        module
            .section(&types)
            .section(&functions)
            .section(&memory)
            .section(&globals)
            .section(&exports)
            .section(&code);
        module
    };

    let mut component = Component::new();
    component.section(&ModuleSection(&core_module));

    // Component type: (func (param "s" string) (result u32))
    {
        let mut types = ComponentTypeSection::new();
        types
            .function()
            .params([(
                "s",
                wasm_encoder::ComponentValType::Primitive(wasm_encoder::PrimitiveValType::String),
            )])
            .result(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            ));
        component.section(&types);
    }

    // Instantiate core module
    {
        let mut inst = InstanceSection::new();
        let no_args: Vec<(&str, ModuleArg)> = vec![];
        inst.instantiate(0, no_args);
        component.section(&inst);
    }

    // Alias core exports
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Func,
            name: "cabi_realloc",
        });
        component.section(&aliases);
    }
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Func,
            name: "test:api/api#check-alloc",
        });
        component.section(&aliases);
    }
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Memory,
            name: "memory",
        });
        component.section(&aliases);
    }

    // Canon lift
    {
        let mut canon = CanonicalFunctionSection::new();
        canon.lift(
            1,
            0,
            [
                CanonicalOption::UTF8,
                CanonicalOption::Memory(0),
                CanonicalOption::Realloc(0),
            ],
        );
        component.section(&canon);
    }

    // Export
    {
        let mut exp = ComponentExportSection::new();
        exp.export("test:api/api", ComponentExportKind::Func, 0, None);
        component.section(&exp);
    }

    component.finish()
}

/// Build a caller component for the realloc-targeting test.
///
/// Has data "Hi" at offset 0 and calls check-alloc(0, 2). If the adapter
/// allocates in the callee's memory (correct), callee sees sentinel 0xBE.
fn build_caller_realloc_verify_component() -> Vec<u8> {
    let core_module = {
        let mut types = TypeSection::new();
        // type 0: (i32, i32) -> i32  -- imported check-alloc
        types.ty().function(
            [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            [wasm_encoder::ValType::I32],
        );
        // type 1: () -> i32  -- run
        types.ty().function([], [wasm_encoder::ValType::I32]);
        // type 2: cabi_realloc
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
        imports.import(
            "test:api/api",
            "check-alloc",
            wasm_encoder::EntityType::Function(0),
        );

        let mut functions = FunctionSection::new();
        functions.function(1); // func 1: run
        functions.function(2); // func 2: cabi_realloc

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: wasm_encoder::ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(1024),
        );

        let mut exports = ExportSection::new();
        exports.export("run", ExportKind::Func, 1);
        exports.export("cabi_realloc", ExportKind::Func, 2);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();

        // func 1: run() -> i32
        {
            let mut f = Function::new([]);
            f.instruction(&Instruction::I32Const(0)); // ptr
            f.instruction(&Instruction::I32Const(2)); // len
            f.instruction(&Instruction::Call(0)); // check-alloc (import)
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        // func 2: cabi_realloc
        {
            let mut f = Function::new([]);
            emit_cabi_realloc(&mut f, 0);
            code.function(&f);
        }

        // Data: "Hi" at offset 0
        let mut data = DataSection::new();
        data.segment(DataSegment {
            mode: DataSegmentMode::Active {
                memory_index: 0,
                offset: &ConstExpr::i32_const(0),
            },
            data: b"Hi".to_vec(),
        });

        let mut module = Module::new();
        module
            .section(&types)
            .section(&imports)
            .section(&functions)
            .section(&memory)
            .section(&globals)
            .section(&exports)
            .section(&code)
            .section(&data);
        module
    };

    let mut component = Component::new();

    // Component type 0: (func (param "s" string) (result u32))
    {
        let mut types = ComponentTypeSection::new();
        types
            .function()
            .params([(
                "s",
                wasm_encoder::ComponentValType::Primitive(wasm_encoder::PrimitiveValType::String),
            )])
            .result(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            ));
        component.section(&types);
    }

    // Component import: "test:api/api" as Func(0)
    {
        let mut imports = ComponentImportSection::new();
        imports.import("test:api/api", ComponentTypeRef::Func(0));
        component.section(&imports);
    }

    component.section(&ModuleSection(&core_module));
    component.finish()
}

/// SR-13: Verify that cabi_realloc is called in the callee's memory, not the caller's.
///
/// The callee's cabi_realloc writes sentinel 0xBE at byte 0 of its own memory.
/// The callee's check-alloc function reads byte 0 and returns it.
/// If the adapter correctly calls the callee's cabi_realloc (in the callee's memory),
/// the result will be 0xBE (190). If it incorrectly calls in the caller's memory,
/// byte 0 of the callee's memory will be 0.
#[test]
fn test_sr13_cabi_realloc_targets_correct_memory() {
    let callee = build_callee_realloc_verify_component();
    let caller = build_caller_realloc_verify_component();

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        output_format: meld_core::OutputFormat::CoreModule,
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&callee, Some("callee-realloc"))
        .expect("callee component should parse");
    fuser
        .add_component_named(&caller, Some("caller-realloc"))
        .expect("caller component should parse");

    let (fused, stats) = fuser.fuse_with_stats().expect("fusion should succeed");

    eprintln!(
        "SR-13: {} bytes, {} funcs, {} adapters",
        stats.output_size, stats.total_functions, stats.adapter_functions,
    );

    assert!(
        stats.adapter_functions > 0,
        "SR-13: expected adapter functions for cross-component string call"
    );

    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("SR-13: fused output should validate");

    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("SR-13: fused module should export 'run'");
    let result = run.call(&mut store, ()).unwrap();

    assert_eq!(
        result, 0xBE,
        "SR-13: run() should return 0xBE (190), proving cabi_realloc ran in callee's memory"
    );
}

// ===========================================================================
// SR-15: Correct list copy length (list<u32>)
// ===========================================================================

/// Build a callee component that accepts `list<u32>` and returns the sum.
///
/// Core function signature: `(i32, i32) -> i32` representing `(ptr, len) -> sum`.
/// Element size for `u32` is 4 bytes, so byte_size = len * 4.
fn build_callee_list_u32_component() -> Vec<u8> {
    let core_module = {
        let mut types = TypeSection::new();
        // type 0: cabi_realloc
        types.ty().function(
            [
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
            ],
            [wasm_encoder::ValType::I32],
        );
        // type 1: (i32, i32) -> i32 -- sum-list (ptr, count) -> sum
        types.ty().function(
            [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            [wasm_encoder::ValType::I32],
        );

        let mut functions = FunctionSection::new();
        functions.function(0); // cabi_realloc
        functions.function(1); // sum-list

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: wasm_encoder::ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(1024),
        );

        let mut exports = ExportSection::new();
        exports.export("cabi_realloc", ExportKind::Func, 0);
        exports.export("test:api/api#sum-list", ExportKind::Func, 1);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();

        // func 0: cabi_realloc
        {
            let mut f = Function::new([]);
            emit_cabi_realloc(&mut f, 0);
            code.function(&f);
        }

        // func 1: sum-list(ptr: i32, count: i32) -> i32
        // Sums count i32 values starting at ptr in memory 0
        {
            // locals: param 0=ptr, param 1=count, local 2=sum, local 3=index
            let mut f = Function::new(vec![(2, wasm_encoder::ValType::I32)]);
            f.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
            f.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

            // if index >= count, break
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::LocalGet(1));
            f.instruction(&Instruction::I32GeU);
            f.instruction(&Instruction::BrIf(1));

            // sum += load_i32(memory 0, ptr + index * 4)
            f.instruction(&Instruction::LocalGet(0));
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::I32Const(4));
            f.instruction(&Instruction::I32Mul);
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: 0,
                align: 2,
                memory_index: 0,
            }));
            f.instruction(&Instruction::LocalGet(2));
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::LocalSet(2));

            // index += 1
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::I32Const(1));
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::LocalSet(3));

            f.instruction(&Instruction::Br(0));
            f.instruction(&Instruction::End); // loop
            f.instruction(&Instruction::End); // block

            f.instruction(&Instruction::LocalGet(2));
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        let mut module = Module::new();
        module
            .section(&types)
            .section(&functions)
            .section(&memory)
            .section(&globals)
            .section(&exports)
            .section(&code);
        module
    };

    let mut component = Component::new();
    component.section(&ModuleSection(&core_module));

    // Component type 0: list<u32>
    {
        let mut types = ComponentTypeSection::new();
        types
            .defined_type()
            .list(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            ));
        component.section(&types);
    }

    // Component type 1: (func (param "items" (type 0)) (result u32))
    {
        let mut types = ComponentTypeSection::new();
        types
            .function()
            .params([("items", wasm_encoder::ComponentValType::Type(0))])
            .result(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            ));
        component.section(&types);
    }

    // Instantiate core module
    {
        let mut inst = InstanceSection::new();
        let no_args: Vec<(&str, ModuleArg)> = vec![];
        inst.instantiate(0, no_args);
        component.section(&inst);
    }

    // Alias core exports
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Func,
            name: "cabi_realloc",
        });
        component.section(&aliases);
    }
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Func,
            name: "test:api/api#sum-list",
        });
        component.section(&aliases);
    }
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Memory,
            name: "memory",
        });
        component.section(&aliases);
    }

    // Canon lift: core func 1 as component type 1
    {
        let mut canon = CanonicalFunctionSection::new();
        canon.lift(
            1,
            1,
            [
                CanonicalOption::UTF8,
                CanonicalOption::Memory(0),
                CanonicalOption::Realloc(0),
            ],
        );
        component.section(&canon);
    }

    // Export
    {
        let mut exp = ComponentExportSection::new();
        exp.export("test:api/api", ComponentExportKind::Func, 0, None);
        component.section(&exp);
    }

    component.finish()
}

/// Build a caller component for the list<u32> test.
///
/// Memory contains 3 u32 values [10, 20, 30] at offset 0 (12 bytes total).
/// Calls sum-list(ptr=0, count=3).
fn build_caller_list_u32_component() -> Vec<u8> {
    let core_module = {
        let mut types = TypeSection::new();
        // type 0: (i32, i32) -> i32  -- imported sum-list
        types.ty().function(
            [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            [wasm_encoder::ValType::I32],
        );
        // type 1: () -> i32  -- run
        types.ty().function([], [wasm_encoder::ValType::I32]);
        // type 2: cabi_realloc
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
        imports.import(
            "test:api/api",
            "sum-list",
            wasm_encoder::EntityType::Function(0),
        );

        let mut functions = FunctionSection::new();
        functions.function(1); // func 1: run
        functions.function(2); // func 2: cabi_realloc

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: wasm_encoder::ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(1024),
        );

        let mut exports = ExportSection::new();
        exports.export("run", ExportKind::Func, 1);
        exports.export("cabi_realloc", ExportKind::Func, 2);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();

        // func 1: run() -> i32
        {
            let mut f = Function::new([]);
            f.instruction(&Instruction::I32Const(0)); // ptr
            f.instruction(&Instruction::I32Const(3)); // count (3 elements)
            f.instruction(&Instruction::Call(0)); // sum-list (import)
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        // func 2: cabi_realloc
        {
            let mut f = Function::new([]);
            emit_cabi_realloc(&mut f, 0);
            code.function(&f);
        }

        // Data segment: [10, 20, 30] as little-endian i32s at offset 0
        let mut data_bytes = Vec::new();
        data_bytes.extend_from_slice(&10u32.to_le_bytes());
        data_bytes.extend_from_slice(&20u32.to_le_bytes());
        data_bytes.extend_from_slice(&30u32.to_le_bytes());

        let mut data = DataSection::new();
        data.segment(DataSegment {
            mode: DataSegmentMode::Active {
                memory_index: 0,
                offset: &ConstExpr::i32_const(0),
            },
            data: data_bytes,
        });

        let mut module = Module::new();
        module
            .section(&types)
            .section(&imports)
            .section(&functions)
            .section(&memory)
            .section(&globals)
            .section(&exports)
            .section(&code)
            .section(&data);
        module
    };

    let mut component = Component::new();

    // Component type 0: list<u32>
    {
        let mut types = ComponentTypeSection::new();
        types
            .defined_type()
            .list(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            ));
        component.section(&types);
    }

    // Component type 1: (func (param "items" list<u32>) (result u32))
    {
        let mut types = ComponentTypeSection::new();
        types
            .function()
            .params([("items", wasm_encoder::ComponentValType::Type(0))])
            .result(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            ));
        component.section(&types);
    }

    // Component import: "test:api/api" as Func(1)
    {
        let mut imports = ComponentImportSection::new();
        imports.import("test:api/api", ComponentTypeRef::Func(1));
        component.section(&imports);
    }

    component.section(&ModuleSection(&core_module));
    component.finish()
}

/// SR-15: Verify correct list copy length for `list<u32>`.
///
/// The caller has [10, 20, 30] in its memory. The adapter must copy
/// `3 * 4 = 12` bytes to the callee's memory. The callee sums the elements
/// and returns 60.
#[test]
fn test_sr15_list_copy_length() {
    let callee = build_callee_list_u32_component();
    let caller = build_caller_list_u32_component();

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        output_format: meld_core::OutputFormat::CoreModule,
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&callee, Some("callee-list"))
        .expect("callee component should parse");
    fuser
        .add_component_named(&caller, Some("caller-list"))
        .expect("caller component should parse");

    let (fused, stats) = fuser.fuse_with_stats().expect("fusion should succeed");

    eprintln!(
        "SR-15: {} bytes, {} funcs, {} adapters",
        stats.output_size, stats.total_functions, stats.adapter_functions,
    );

    assert!(
        stats.adapter_functions > 0,
        "SR-15: expected adapter functions for cross-component list call"
    );

    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("SR-15: fused output should validate");

    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("SR-15: fused module should export 'run'");
    let result = run.call(&mut store, ()).unwrap();

    assert_eq!(
        result, 60,
        "SR-15: run() should return 60 (sum of [10, 20, 30])"
    );
}

// ===========================================================================
// SR-16: Inner pointer fixup for list<string>
// ===========================================================================

/// Build a callee component that accepts `list<string>` and returns the total
/// byte count of all strings.
///
/// The canonical ABI layout for `list<string>` is:
///   - Outer: (ptr, count) where ptr points to an array of `count` elements
///   - Each element: 8 bytes = (str_ptr: i32, str_len: i32)
///
/// The callee reads `count` elements from memory at `ptr`, and for each element
/// reads the (str_ptr, str_len) pair to sum all str_len values.
fn build_callee_list_string_component() -> Vec<u8> {
    let core_module = {
        let mut types = TypeSection::new();
        // type 0: cabi_realloc
        types.ty().function(
            [
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
            ],
            [wasm_encoder::ValType::I32],
        );
        // type 1: (i32, i32) -> i32 -- concat-lengths (ptr, count) -> total_len
        types.ty().function(
            [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            [wasm_encoder::ValType::I32],
        );

        let mut functions = FunctionSection::new();
        functions.function(0); // cabi_realloc
        functions.function(1); // concat-lengths

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: wasm_encoder::ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(4096),
        );

        let mut exports = ExportSection::new();
        exports.export("cabi_realloc", ExportKind::Func, 0);
        exports.export("test:api/api#concat-lengths", ExportKind::Func, 1);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();

        // func 0: cabi_realloc
        {
            let mut f = Function::new([]);
            emit_cabi_realloc(&mut f, 0);
            code.function(&f);
        }

        // func 1: concat-lengths(ptr: i32, count: i32) -> i32
        // For each element at ptr[i] = (str_ptr, str_len), sum all the byte values
        // of all strings to prove that inner pointers were correctly fixed up.
        //
        // locals: param 0=ptr, param 1=count, local 2=total_sum, local 3=index,
        //         local 4=str_ptr, local 5=str_len, local 6=byte_index
        {
            let mut f = Function::new(vec![(5, wasm_encoder::ValType::I32)]);
            f.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
            f.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

            // if index >= count, break
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::LocalGet(1));
            f.instruction(&Instruction::I32GeU);
            f.instruction(&Instruction::BrIf(1));

            // Load element: str_ptr = load_i32(ptr + index * 8)
            f.instruction(&Instruction::LocalGet(0));
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::I32Const(8));
            f.instruction(&Instruction::I32Mul);
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: 0,
                align: 2,
                memory_index: 0,
            }));
            f.instruction(&Instruction::LocalSet(4)); // str_ptr

            // str_len = load_i32(ptr + index * 8 + 4)
            f.instruction(&Instruction::LocalGet(0));
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::I32Const(8));
            f.instruction(&Instruction::I32Mul);
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: 4,
                align: 2,
                memory_index: 0,
            }));
            f.instruction(&Instruction::LocalSet(5)); // str_len

            // Sum all bytes of this string
            // Reset byte_index = 0
            f.instruction(&Instruction::I32Const(0));
            f.instruction(&Instruction::LocalSet(6));
            f.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
            f.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

            // if byte_index >= str_len, break inner loop
            f.instruction(&Instruction::LocalGet(6));
            f.instruction(&Instruction::LocalGet(5));
            f.instruction(&Instruction::I32GeU);
            f.instruction(&Instruction::BrIf(1));

            // total_sum += load_u8(str_ptr + byte_index)
            f.instruction(&Instruction::LocalGet(4));
            f.instruction(&Instruction::LocalGet(6));
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::I32Load8U(wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: 0,
            }));
            f.instruction(&Instruction::LocalGet(2));
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::LocalSet(2));

            // byte_index += 1
            f.instruction(&Instruction::LocalGet(6));
            f.instruction(&Instruction::I32Const(1));
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::LocalSet(6));

            f.instruction(&Instruction::Br(0));
            f.instruction(&Instruction::End); // inner loop
            f.instruction(&Instruction::End); // inner block

            // index += 1
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::I32Const(1));
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::LocalSet(3));

            f.instruction(&Instruction::Br(0));
            f.instruction(&Instruction::End); // outer loop
            f.instruction(&Instruction::End); // outer block

            f.instruction(&Instruction::LocalGet(2));
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        let mut module = Module::new();
        module
            .section(&types)
            .section(&functions)
            .section(&memory)
            .section(&globals)
            .section(&exports)
            .section(&code);
        module
    };

    let mut component = Component::new();
    component.section(&ModuleSection(&core_module));

    // Component type 0: list<string>
    {
        let mut types = ComponentTypeSection::new();
        types
            .defined_type()
            .list(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::String,
            ));
        component.section(&types);
    }

    // Component type 1: (func (param "items" list<string>) (result u32))
    {
        let mut types = ComponentTypeSection::new();
        types
            .function()
            .params([("items", wasm_encoder::ComponentValType::Type(0))])
            .result(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            ));
        component.section(&types);
    }

    // Instantiate core module
    {
        let mut inst = InstanceSection::new();
        let no_args: Vec<(&str, ModuleArg)> = vec![];
        inst.instantiate(0, no_args);
        component.section(&inst);
    }

    // Alias core exports
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Func,
            name: "cabi_realloc",
        });
        component.section(&aliases);
    }
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Func,
            name: "test:api/api#concat-lengths",
        });
        component.section(&aliases);
    }
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Memory,
            name: "memory",
        });
        component.section(&aliases);
    }

    // Canon lift: core func 1 as component type 1
    {
        let mut canon = CanonicalFunctionSection::new();
        canon.lift(
            1,
            1,
            [
                CanonicalOption::UTF8,
                CanonicalOption::Memory(0),
                CanonicalOption::Realloc(0),
            ],
        );
        component.section(&canon);
    }

    // Export
    {
        let mut exp = ComponentExportSection::new();
        exp.export("test:api/api", ComponentExportKind::Func, 0, None);
        component.section(&exp);
    }

    component.finish()
}

/// Build a caller component for the list<string> test.
///
/// Memory layout (all at memory 0):
///   Offset 0..8:   element 0: (str_ptr=16, str_len=2)  -> "Hi"
///   Offset 8..16:  element 1: (str_ptr=18, str_len=5)  -> "World"
///   Offset 16..18: "Hi"
///   Offset 18..23: "World"
///
/// Calls concat-lengths(ptr=0, count=2).
/// Expected sum of bytes: H(72)+i(105) + W(87)+o(111)+r(114)+l(108)+d(100)
///                       = 177 + 520 = 697
fn build_caller_list_string_component() -> Vec<u8> {
    let core_module = {
        let mut types = TypeSection::new();
        // type 0: (i32, i32) -> i32  -- imported concat-lengths
        types.ty().function(
            [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            [wasm_encoder::ValType::I32],
        );
        // type 1: () -> i32  -- run
        types.ty().function([], [wasm_encoder::ValType::I32]);
        // type 2: cabi_realloc
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
        imports.import(
            "test:api/api",
            "concat-lengths",
            wasm_encoder::EntityType::Function(0),
        );

        let mut functions = FunctionSection::new();
        functions.function(1); // func 1: run
        functions.function(2); // func 2: cabi_realloc

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: wasm_encoder::ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(4096),
        );

        let mut exports = ExportSection::new();
        exports.export("run", ExportKind::Func, 1);
        exports.export("cabi_realloc", ExportKind::Func, 2);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();

        // func 1: run() -> i32
        {
            let mut f = Function::new([]);
            f.instruction(&Instruction::I32Const(0)); // ptr to element array
            f.instruction(&Instruction::I32Const(2)); // count = 2 elements
            f.instruction(&Instruction::Call(0)); // concat-lengths (import)
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        // func 2: cabi_realloc
        {
            let mut f = Function::new([]);
            emit_cabi_realloc(&mut f, 0);
            code.function(&f);
        }

        // Data segment layout:
        //   [0..4]:   str_ptr for element 0 = 16
        //   [4..8]:   str_len for element 0 = 2
        //   [8..12]:  str_ptr for element 1 = 18
        //   [12..16]: str_len for element 1 = 5
        //   [16..18]: "Hi"
        //   [18..23]: "World"
        let mut data_bytes = Vec::new();
        // Element 0: ptr=16, len=2
        data_bytes.extend_from_slice(&16u32.to_le_bytes());
        data_bytes.extend_from_slice(&2u32.to_le_bytes());
        // Element 1: ptr=18, len=5
        data_bytes.extend_from_slice(&18u32.to_le_bytes());
        data_bytes.extend_from_slice(&5u32.to_le_bytes());
        // String data
        data_bytes.extend_from_slice(b"Hi");
        data_bytes.extend_from_slice(b"World");

        let mut data = DataSection::new();
        data.segment(DataSegment {
            mode: DataSegmentMode::Active {
                memory_index: 0,
                offset: &ConstExpr::i32_const(0),
            },
            data: data_bytes,
        });

        let mut module = Module::new();
        module
            .section(&types)
            .section(&imports)
            .section(&functions)
            .section(&memory)
            .section(&globals)
            .section(&exports)
            .section(&code)
            .section(&data);
        module
    };

    let mut component = Component::new();

    // Component type 0: list<string>
    {
        let mut types = ComponentTypeSection::new();
        types
            .defined_type()
            .list(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::String,
            ));
        component.section(&types);
    }

    // Component type 1: (func (param "items" list<string>) (result u32))
    {
        let mut types = ComponentTypeSection::new();
        types
            .function()
            .params([("items", wasm_encoder::ComponentValType::Type(0))])
            .result(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            ));
        component.section(&types);
    }

    // Component import: "test:api/api" as Func(1)
    {
        let mut imports = ComponentImportSection::new();
        imports.import("test:api/api", ComponentTypeRef::Func(1));
        component.section(&imports);
    }

    component.section(&ModuleSection(&core_module));
    component.finish()
}

/// SR-16: Verify inner pointer fixup for `list<string>`.
///
/// The caller has two strings ["Hi", "World"] encoded as a list<string> in its
/// memory. The adapter must:
///   1. Bulk-copy the element array (16 bytes) to the callee's memory
///   2. Fix up inner string pointers: for each element, allocate the string data
///      in the callee's memory and rewrite the (str_ptr, str_len) pair
///   3. Call the callee
///
/// The callee sums all bytes of all strings.
/// Expected: H(72)+i(105) + W(87)+o(111)+r(114)+l(108)+d(100) = 697
#[test]
fn test_sr16_inner_pointer_fixup_list_string() {
    let callee = build_callee_list_string_component();
    let caller = build_caller_list_string_component();

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        output_format: meld_core::OutputFormat::CoreModule,
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&callee, Some("callee-list-string"))
        .expect("callee component should parse");
    fuser
        .add_component_named(&caller, Some("caller-list-string"))
        .expect("caller component should parse");

    let (fused, stats) = fuser.fuse_with_stats().expect("fusion should succeed");

    eprintln!(
        "SR-16: {} bytes, {} funcs, {} adapters",
        stats.output_size, stats.total_functions, stats.adapter_functions,
    );

    assert!(
        stats.adapter_functions > 0,
        "SR-16: expected adapter functions for cross-component list<string> call"
    );

    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("SR-16: fused output should validate");

    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("SR-16: fused module should export 'run'");
    let result = run.call(&mut store, ()).unwrap();

    // "Hi" = [72, 105] = 177
    // "World" = [87, 111, 114, 108, 100] = 520
    // Total = 697
    assert_eq!(
        result, 697,
        "SR-16: run() should return 697 (sum of bytes of 'Hi' + 'World')"
    );
}
