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
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
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
    // Default caller passes ASCII "Hello"; the data-parameterized helper
    // lets transcoding tests vary the source string (e.g. non-BMP code
    // points that force UTF-16 surrogate pairs — SR-17).
    build_caller_string_component_data(b"Hello")
}

fn build_caller_string_component_data(string_bytes: &[u8]) -> Vec<u8> {
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
            f.instruction(&Instruction::I32Const(string_bytes.len() as i32)); // byte len
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
            data: string_bytes.to_vec(),
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
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
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
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
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
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
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
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
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
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
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
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
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
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
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
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
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
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
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
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
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
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
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

// ===========================================================================
// SR-17: String transcoding — UTF-8 caller to UTF-16 callee
// ===========================================================================

/// Build a callee P2 component that exports a string function with UTF-16 encoding.
///
/// The callee's core function reads UTF-16 code units from memory and sums them.
/// The component-level type is `(func (param "s" string) (result u32))`.
/// The canon lift uses **UTF-16** encoding, so the core function receives
/// (ptr, code_unit_count) and reads 16-bit values from memory[ptr].
///
/// Core function: sum_utf16(ptr: i32, len: i32) -> i32
///   Sums all UTF-16 code units as u16 values: total += load16u(ptr + i*2)
fn build_callee_utf16_string_component() -> Vec<u8> {
    build_callee_codeunit_summing_component(CanonicalOption::UTF16)
}

/// A code-unit-summing callee parameterized on the `canon lift` string
/// encoding. With `UTF16` it is the UTF-16 callee used by the SR-17 tests;
/// with `CompactUTF16` (which meld maps to `Latin1`) it produces a
/// Latin1-lifting callee. The latter, paired with a UTF-16-lowering caller,
/// drives the still-unsupported (Utf16, Latin1) down-conversion onto the
/// #253 fail-loud catch-all (fusion errors before any code runs, so the
/// core body's 16-bit reads are never executed for that case).
fn build_callee_codeunit_summing_component(lift_encoding: CanonicalOption) -> Vec<u8> {
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
        // type 1: (i32, i32) -> i32 -- process-string (ptr, code_unit_count) -> sum
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

        // func 1: process-string(ptr: i32, code_unit_count: i32) -> i32
        // Sums all UTF-16 code units (u16 values) from memory.
        // This reads 16-bit values: for each i in 0..code_unit_count,
        //   sum += mem16[ptr + i * 2]
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

            // sum += load_u16(memory 0, ptr + index * 2)
            f.instruction(&Instruction::LocalGet(0));
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::I32Const(1));
            f.instruction(&Instruction::I32Shl); // index * 2
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::I32Load16U(wasm_encoder::MemArg {
                offset: 0,
                align: 1, // 2-byte alignment
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

    // --- Build P2 component with UTF-16 canon lift ---
    let mut component = Component::new();

    // 1. Embed core module
    component.section(&ModuleSection(&core_module));

    // 2. Define component function type: (func (param "s" string) (result u32))
    {
        let mut types = ComponentTypeSection::new();
        types
            .function()
            .params([(
                "s",
                wasm_encoder::ComponentValType::Primitive(wasm_encoder::PrimitiveValType::String),
            )])
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
        component.section(&types);
    }

    // 3. Instantiate core module
    {
        let mut inst = InstanceSection::new();
        let no_args: Vec<(&str, ModuleArg)> = vec![];
        inst.instantiate(0, no_args);
        component.section(&inst);
    }

    // 4. Alias core exports
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

    // 5. Canon lift with the parameterized encoding.
    //    Core func 1 expects (ptr, code_unit_count) -> sum.
    {
        let mut canon = CanonicalFunctionSection::new();
        canon.lift(
            1, // core func index: process-string
            0, // component type index
            [
                lift_encoding, // <-- parameterized string encoding
                CanonicalOption::Memory(0),
                CanonicalOption::Realloc(0),
            ],
        );
        component.section(&canon);
    }

    // 6. Export the lifted function
    {
        let mut exp = ComponentExportSection::new();
        exp.export("test:api/api", ComponentExportKind::Func, 0, None);
        component.section(&exp);
    }

    component.finish()
}

/// SR-17: Verify UTF-8 to UTF-16 string transcoding in cross-component calls.
///
/// The caller has "Hello" as UTF-8 bytes [72, 101, 108, 108, 111] in memory.
/// The callee lifts with UTF-16 encoding, so it reads 16-bit code units.
/// The adapter must transcode: each ASCII byte becomes a UTF-16 code unit.
///
/// For "Hello" (all ASCII), each byte maps 1:1 to a UTF-16 code unit:
///   UTF-16 code units: [0x0048, 0x0065, 0x006C, 0x006C, 0x006F]
///   = [72, 101, 108, 108, 111]
///
/// Sum of code units = 72 + 101 + 108 + 108 + 111 = 500
///
/// This tests the core of SR-17: the adapter's UTF-8 to UTF-16 transcoding
/// loop correctly decodes each UTF-8 byte and encodes it as a UTF-16 code unit
/// in the callee's memory.
#[test]
fn test_sr17_utf8_to_utf16_string_transcoding() {
    let callee = build_callee_utf16_string_component();
    let caller = build_caller_string_component(); // reuse UTF-8 caller from SR-12

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&callee, Some("callee-utf16"))
        .expect("callee component should parse");
    fuser
        .add_component_named(&caller, Some("caller-utf8"))
        .expect("caller component should parse");

    let (fused, stats) = fuser.fuse_with_stats().expect("fusion should succeed");

    eprintln!(
        "SR-17 UTF-8->UTF-16: {} bytes, {} funcs, {} adapters, {} imports resolved",
        stats.output_size, stats.total_functions, stats.adapter_functions, stats.imports_resolved,
    );

    // The fusion should produce at least one adapter for the transcoding call
    assert!(
        stats.adapter_functions > 0,
        "SR-17: expected adapter functions for UTF-8 to UTF-16 transcoding, got 0"
    );

    // Validate the fused output
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("SR-17: fused output should validate");

    // Run through wasmtime
    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("SR-17: fused module should export 'run'");
    let result = run.call(&mut store, ()).unwrap();

    // "Hello" in UTF-8 = [72, 101, 108, 108, 111]
    // Transcoded to UTF-16 code units: [72, 101, 108, 108, 111] (ASCII maps 1:1)
    // Sum = 500
    assert_eq!(
        result, 500,
        "SR-17: run() should return 500 (sum of UTF-16 code units for 'Hello')"
    );
}

/// SR-17 (surrogate-pair clause): a supplementary-plane code point
/// (U+10000 and above) transcoded UTF-8 → UTF-16 must be encoded as a
/// surrogate PAIR — two code units — not a single truncated unit. The
/// pre-existing SR-17 transcoding test only exercised ASCII (1 UTF-8
/// byte → 1 BMP code unit), leaving the `code_point >= 0x10000` branch
/// of `emit_utf8_to_utf16_transcode` (fact.rs) unexecuted. The
/// v0.31.0 traceability audit flagged this as SR-17's one open
/// requirement-text verification gap; this fixture closes it.
///
/// Oracle: U+1F600 (😀) is UTF-8 `F0 9F 98 80` (4 bytes). The canonical
/// surrogate decomposition is:
///   cp - 0x10000 = 0xF600
///   high = 0xD800 + (0xF600 >> 10)   = 0xD800 + 0x3D  = 0xD83D
///   low  = 0xDC00 + (0xF600 & 0x3FF) = 0xDC00 + 0x200 = 0xDE00
/// The callee sums the received UTF-16 code units, so a correct
/// surrogate pair yields 0xD83D + 0xDE00 = 55357 + 56832 = 112189.
/// A buggy single-unit or truncated encoding cannot produce this sum.
#[test]
fn test_sr17_utf8_to_utf16_supplementary_plane_transcoding() {
    let callee = build_callee_utf16_string_component();
    // "A😀": one BMP code point then one supplementary, to also prove
    // the dst-cursor advances by 1 then 2 and the units interleave.
    //   'A'  = 0x0041 (1 UTF-8 byte, 1 code unit)
    //   '😀' = U+1F600 → D83D DE00 (4 UTF-8 bytes, 2 code units)
    // Sum = 0x0041 + 0xD83D + 0xDE00 = 65 + 55357 + 56832 = 112254.
    let caller = build_caller_string_component_data(&[0x41, 0xF0, 0x9F, 0x98, 0x80]);

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&callee, Some("callee-utf16"))
        .expect("callee component should parse");
    fuser
        .add_component_named(&caller, Some("caller-utf8"))
        .expect("caller component should parse");

    let (fused, stats) = fuser.fuse_with_stats().expect("fusion should succeed");
    assert!(
        stats.adapter_functions > 0,
        "SR-17: expected a transcoding adapter, got 0"
    );

    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("SR-17: fused output should validate");

    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);
    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("SR-17: fused module should export 'run'");
    let result = run.call(&mut store, ()).unwrap();

    assert_eq!(
        result, 112254,
        "SR-17: 'A😀' must transcode to UTF-16 code units \
         [0x0041, 0xD83D, 0xDE00] (surrogate pair for U+1F600); \
         sum 112254. A wrong sum means the supplementary-plane branch \
         mis-encodes the surrogate pair."
    );
}

/// A caller component whose import is lowered with **UTF-16** encoding, so
/// the resolver attributes `caller_encoding = UTF16`. Paired with the
/// UTF-8 byte-summing callee (`build_callee_string_component`), this drives
/// meld to emit the *reverse* transcoder (`emit_utf16_to_utf8_transcode`).
///
/// A string `canon lower` requires a core memory + realloc, which cycles
/// with the caller module importing the lowered function. We break the
/// cycle with a tiny memory/realloc helper module instantiated first; the
/// lower references the helper's memory purely so the component parses,
/// and meld reads the lower only as encoding metadata while fusing the
/// real caller module by its core imports.
///
/// `code_units` are stored little-endian at offset 0 of the caller's
/// memory, and `run` calls `process-string(0, code_units.len())` — the
/// length is a UTF-16 code-unit count, per the canonical ABI.
fn build_caller_utf16_lowering_component(code_units: &[u16]) -> Vec<u8> {
    build_caller_lowering_component(code_units, CanonicalOption::UTF16)
}

/// Like `build_caller_utf16_lowering_component` but parameterized on the
/// `canon lower` string encoding, so tests can drive other caller-side
/// encodings (e.g. CompactUTF16 → Latin1) through the resolver.
fn build_caller_lowering_component(code_units: &[u16], lower_encoding: CanonicalOption) -> Vec<u8> {
    let mut data_bytes = Vec::new();
    for cu in code_units {
        data_bytes.extend_from_slice(&cu.to_le_bytes());
    }
    let code_unit_count = code_units.len() as i32;

    let core_module = {
        let mut types = TypeSection::new();
        types.ty().function(
            [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            [wasm_encoder::ValType::I32],
        );
        types.ty().function([], [wasm_encoder::ValType::I32]);
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
        functions.function(1); // run
        functions.function(2); // cabi_realloc

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
        {
            let mut f = Function::new([]);
            f.instruction(&Instruction::I32Const(0)); // ptr
            f.instruction(&Instruction::I32Const(code_unit_count)); // UTF-16 code-unit count
            f.instruction(&Instruction::Call(0)); // process-string (import)
            f.instruction(&Instruction::End);
            code.function(&f);
        }
        {
            let mut f = Function::new([]);
            emit_cabi_realloc(&mut f, 0);
            code.function(&f);
        }

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

    // Helper module providing a memory + realloc for the string lower to
    // reference (distinct export names so it is not a third "cabi_realloc"
    // in the fused output's namespace).
    let mem_provider = {
        let mut types = TypeSection::new();
        types.ty().function(
            [
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
            ],
            [wasm_encoder::ValType::I32],
        );
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
        exports.export("mp_realloc", ExportKind::Func, 0);
        exports.export("mp_memory", ExportKind::Memory, 0);
        let mut code = CodeSection::new();
        {
            let mut f = Function::new([]);
            emit_cabi_realloc(&mut f, 0);
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

    {
        let mut types = ComponentTypeSection::new();
        types
            .function()
            .params([(
                "s",
                wasm_encoder::ComponentValType::Primitive(wasm_encoder::PrimitiveValType::String),
            )])
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
        component.section(&types);
    }
    {
        let mut imports = ComponentImportSection::new();
        imports.import("test:api/api", ComponentTypeRef::Func(0));
        component.section(&imports);
    }

    component.section(&ModuleSection(&mem_provider));
    {
        let mut inst = InstanceSection::new();
        let no_args: Vec<(&str, ModuleArg)> = vec![];
        inst.instantiate(0, no_args);
        component.section(&inst);
    }
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Func,
            name: "mp_realloc",
        });
        component.section(&aliases);
    }
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Memory,
            name: "mp_memory",
        });
        component.section(&aliases);
    }
    {
        let mut canon = CanonicalFunctionSection::new();
        canon.lower(
            0,
            [
                lower_encoding,
                CanonicalOption::Memory(0),
                CanonicalOption::Realloc(0),
            ],
        );
        component.section(&canon);
    }

    component.section(&ModuleSection(&core_module));
    component.finish()
}

/// A Latin-1 caller: like [`build_caller_lowering_component`] but stores the
/// raw input as **1 byte per character** (Latin-1's on-the-wire form) and
/// passes `process-string(0, bytes.len())` — for Latin-1 the byte count IS
/// the character count. The import is lowered with `CompactUTF16`, which meld
/// maps to the `Latin1` string encoding, so this drives the resolver to the
/// (Latin1, Utf16) transcoder when paired with a UTF-16 callee.
///
/// This is distinct from `build_caller_lowering_component`, which stores 2
/// bytes per `u16` (correct for UTF-16/CompactUTF16-as-2-byte fixtures but
/// WRONG for Latin-1, where each char is a single byte).
fn build_caller_latin1_lowering_component(bytes: &[u8]) -> Vec<u8> {
    let data_bytes: Vec<u8> = bytes.to_vec();
    let byte_count = bytes.len() as i32;

    let core_module = {
        let mut types = TypeSection::new();
        types.ty().function(
            [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            [wasm_encoder::ValType::I32],
        );
        types.ty().function([], [wasm_encoder::ValType::I32]);
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
        functions.function(1); // run
        functions.function(2); // cabi_realloc

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
        {
            let mut f = Function::new([]);
            f.instruction(&Instruction::I32Const(0)); // ptr
            f.instruction(&Instruction::I32Const(byte_count)); // Latin-1 byte count == char count
            f.instruction(&Instruction::Call(0)); // process-string (import)
            f.instruction(&Instruction::End);
            code.function(&f);
        }
        {
            let mut f = Function::new([]);
            emit_cabi_realloc(&mut f, 0);
            code.function(&f);
        }

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

    // Helper module providing a memory + realloc for the string lower to
    // reference (distinct export names, matching build_caller_lowering_component).
    let mem_provider = {
        let mut types = TypeSection::new();
        types.ty().function(
            [
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
                wasm_encoder::ValType::I32,
            ],
            [wasm_encoder::ValType::I32],
        );
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
        exports.export("mp_realloc", ExportKind::Func, 0);
        exports.export("mp_memory", ExportKind::Memory, 0);
        let mut code = CodeSection::new();
        {
            let mut f = Function::new([]);
            emit_cabi_realloc(&mut f, 0);
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

    {
        let mut types = ComponentTypeSection::new();
        types
            .function()
            .params([(
                "s",
                wasm_encoder::ComponentValType::Primitive(wasm_encoder::PrimitiveValType::String),
            )])
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
        component.section(&types);
    }
    {
        let mut imports = ComponentImportSection::new();
        imports.import("test:api/api", ComponentTypeRef::Func(0));
        component.section(&imports);
    }

    component.section(&ModuleSection(&mem_provider));
    {
        let mut inst = InstanceSection::new();
        let no_args: Vec<(&str, ModuleArg)> = vec![];
        inst.instantiate(0, no_args);
        component.section(&inst);
    }
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Func,
            name: "mp_realloc",
        });
        component.section(&aliases);
    }
    {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind: ExportKind::Memory,
            name: "mp_memory",
        });
        component.section(&aliases);
    }
    {
        let mut canon = CanonicalFunctionSection::new();
        canon.lower(
            0,
            [
                // meld maps CompactUTF16 → Latin1.
                CanonicalOption::CompactUTF16,
                CanonicalOption::Memory(0),
                CanonicalOption::Realloc(0),
            ],
        );
        component.section(&canon);
    }

    component.section(&ModuleSection(&core_module));
    component.finish()
}

/// SR-17 (reverse direction): a supplementary-plane code point carried
/// UTF-16 → UTF-8 must decode the surrogate PAIR back to a single 4-byte
/// UTF-8 sequence. The forward gap was closed in #244; this exercises
/// `emit_utf16_to_utf8_transcode`'s surrogate-decode branch at runtime —
/// previously only the resolver's *requirement* for this direction was
/// unit-tested and lone-surrogate handling was structural (LS-P-16); the
/// end-to-end non-BMP round-trip had no executing oracle.
///
/// This fixture also pins #245: its two-core-module caller is the exact
/// shape that previously collided `cabi_realloc$1` in the fused output.
///
/// Oracle: "A😀" as UTF-16 code units [0x0041, 0xD83D, 0xDE00] must
/// transcode to UTF-8 bytes [0x41, 0xF0, 0x9F, 0x98, 0x80] ('A' +
/// U+1F600). The callee sums received UTF-8 bytes, so a correct
/// surrogate-pair *decode* yields 65 + 240 + 159 + 152 + 128 = 744.
#[test]
fn test_sr17_utf16_to_utf8_supplementary_plane_transcoding() {
    let callee = build_callee_string_component(); // UTF-8 lift, sums bytes
    let caller = build_caller_utf16_lowering_component(&[0x0041, 0xD83D, 0xDE00]);

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&callee, Some("callee-utf8"))
        .expect("callee component should parse");
    fuser
        .add_component_named(&caller, Some("caller-utf16"))
        .expect("caller component should parse");

    let (fused, stats) = fuser.fuse_with_stats().expect("fusion should succeed");
    eprintln!(
        "SR-17 UTF-16->UTF-8: {} bytes, {} adapters, {} imports resolved",
        stats.output_size, stats.adapter_functions, stats.imports_resolved,
    );
    assert!(
        stats.adapter_functions > 0,
        "SR-17 reverse: expected a UTF-16->UTF-8 transcoding adapter, got 0 \
         (caller_encoding may not have been read as UTF-16)"
    );

    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("SR-17 reverse: fused output should validate (also pins #245)");

    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);
    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("SR-17 reverse: fused module should export 'run'");
    let result = run.call(&mut store, ()).unwrap();

    assert_eq!(
        result, 744,
        "SR-17 reverse: UTF-16 [0x0041, 0xD83D, 0xDE00] must decode the \
         surrogate pair to UTF-8 [0x41, F0 9F 98 80] (sum 744). A wrong \
         sum means the surrogate-decode branch of emit_utf16_to_utf8_transcode \
         mis-handles the supplementary-plane code point."
    );
}

/// LS-P-16 (runtime): a **lone high surrogate at end of input** must be
/// lossily replaced with U+FFFD during UTF-16 → UTF-8 transcoding, not
/// trapped (the pre-v0.11 behaviour) and not read past the buffer (the
/// 2-byte OOB this scenario originally guarded). Until now LS-P-16 was
/// covered only structurally; this is its first executing oracle, reusing
/// the UTF-16-lowering caller landed with #246.
///
/// Input UTF-16 code units [0x0041, 0xD800]: 'A' then a high surrogate
/// with no following low surrogate (it is the last unit). The transcoder
/// must emit 'A' (0x41) then U+FFFD (UTF-8 `EF BF BD`). The callee sums
/// received UTF-8 bytes: 0x41 + 0xEF + 0xBF + 0xBD = 65 + 239 + 191 + 189
/// = 684. A trap or OOB read would not return 684.
#[test]
fn test_sr17_utf16_to_utf8_lone_high_surrogate_replacement() {
    let callee = build_callee_string_component(); // UTF-8 lift, sums bytes
    let caller = build_caller_utf16_lowering_component(&[0x0041, 0xD800]);

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&callee, Some("callee-utf8"))
        .expect("callee component should parse");
    fuser
        .add_component_named(&caller, Some("caller-utf16"))
        .expect("caller component should parse");

    let (fused, _stats) = fuser.fuse_with_stats().expect("fusion should succeed");

    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("LS-P-16: fused output should validate");

    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);
    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("LS-P-16: fused module should export 'run'");
    let result = run.call(&mut store, ()).unwrap();

    assert_eq!(
        result, 684,
        "LS-P-16: a lone trailing high surrogate [.., 0xD800] must become \
         U+FFFD (UTF-8 EF BF BD), so 'A' + U+FFFD sums to 684. A trap, OOB \
         read, or a wrong replacement would not produce 684."
    );
}

/// LS-P-16 (mid-string, runtime): a high surrogate NOT at end-of-input,
/// followed by a unit that is **not** a low surrogate, is still a lone
/// surrogate and must be replaced with U+FFFD — the second unit then
/// reprocessed on its own. The v0.11 mitigation only handled the
/// end-of-input case; the unvalidated-second-unit causal factor recorded
/// in LS-P-16 stayed open until this fix. Before it, `[0xD800, 0x0041]`
/// computed a garbage code point from `0x0041 - 0xDC00` (u32 underflow)
/// and emitted wrong UTF-8 (observed run() == 500).
///
/// Input [0xD800, 0x0041]: lone high surrogate then 'A'. Correct output
/// is U+FFFD (UTF-8 EF BF BD) then 'A' (0x41). The callee sums received
/// UTF-8 bytes: 0xEF + 0xBF + 0xBD + 0x41 = 239 + 191 + 189 + 65 = 684.
#[test]
fn test_sr17_utf16_to_utf8_midstring_lone_surrogate_replacement() {
    let callee = build_callee_string_component(); // UTF-8 lift, sums bytes
    let caller = build_caller_utf16_lowering_component(&[0xD800, 0x0041]);

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&callee, Some("callee-utf8"))
        .expect("callee component should parse");
    fuser
        .add_component_named(&caller, Some("caller-utf16"))
        .expect("caller component should parse");

    let (fused, _stats) = fuser.fuse_with_stats().expect("fusion should succeed");

    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("LS-P-16 mid-string: fused output should validate");

    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);
    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("LS-P-16 mid-string: fused module should export 'run'");
    let result = run.call(&mut store, ()).unwrap();

    assert_eq!(
        result, 684,
        "LS-P-16 mid-string: [0xD800, 0x0041] must transcode to U+FFFD + 'A' \
         (UTF-8 EF BF BD 41, sum 684). Pre-fix this returned 500 (garbage \
         code point from the unvalidated second unit)."
    );
}

/// Comprehensive malformed-UTF-16 matrix for UTF-16 → UTF-8 transcoding
/// (#249): every unpaired surrogate, at every position, must become U+FFFD
/// (UTF-8 `EF BF BD`, byte sum 619), and valid pairs must still decode.
/// The callee sums received UTF-8 bytes; expected sums are hand-computed
/// from: U+FFFD=619, 'A'=0x41=65, 'B'=0x42=66, U+1F600 → `F0 9F 98 80`=679.
///
/// This closes the lone-LOW-surrogate gap (#249, surfaced by PR #248's
/// Mythos pass) alongside the lone-HIGH cases fixed in v0.11 / #248, and
/// pins the whole class so a regression in any single arm is caught.
#[test]
fn test_sr17_utf16_to_utf8_malformed_surrogate_matrix() {
    // (input UTF-16 code units, expected callee byte-sum, label)
    let cases: &[(&[u16], i32, &str)] = &[
        (&[0xDC00, 0x0041], 684, "leading lone low → FFFD + A"),
        (&[0x0041, 0xDC00], 684, "trailing lone low → A + FFFD"),
        (
            &[0x0041, 0xDC00, 0x0042],
            750,
            "mid lone low → A + FFFD + B",
        ),
        (
            &[0xDC00, 0xDC00],
            1238,
            "consecutive lone lows → FFFD + FFFD",
        ),
        (&[0xDFFF], 619, "last low surrogate value alone → FFFD"),
        (&[0xD83D, 0xDE00], 679, "valid pair U+1F600 still decodes"),
        (
            &[0xDC00, 0xD83D, 0xDE00],
            1298,
            "lone low then valid pair → FFFD + U+1F600",
        ),
        (
            &[0xD800, 0xD800, 0x0041],
            1303,
            "consecutive lone highs → FFFD + FFFD + A",
        ),
    ];

    for (units, expected, label) in cases {
        let callee = build_callee_string_component();
        let caller = build_caller_utf16_lowering_component(units);
        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            component_provenance: false,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: meld_core::CustomSectionHandling::Drop,
            dwarf_handling: meld_core::DwarfHandling::Strip,
            output_format: meld_core::OutputFormat::CoreModule,
            opaque_resources: Vec::new(),
        };
        let mut fuser = Fuser::new(config);
        fuser
            .add_component_named(&callee, Some("callee-utf8"))
            .expect("callee parse");
        fuser
            .add_component_named(&caller, Some("caller-utf16"))
            .expect("caller parse");
        let (fused, _) = fuser.fuse_with_stats().expect("fusion");

        let mut validator = wasmparser::Validator::new();
        validator
            .validate_all(&fused)
            .unwrap_or_else(|e| panic!("#249 [{label}]: output must validate: {e}"));

        let mut ec = Config::new();
        ec.wasm_multi_memory(true);
        let engine = Engine::new(&ec).unwrap();
        let module = RuntimeModule::new(&engine, &fused).unwrap();
        let mut store = Store::new(&engine, ());
        let instance = Instance::new(&mut store, &module, &[]).unwrap();
        let run = instance
            .get_typed_func::<(), i32>(&mut store, "run")
            .unwrap();
        let result = run.call(&mut store, ()).unwrap();
        assert_eq!(
            result, *expected,
            "#249 [{label}]: input {units:#06x?} expected byte-sum {expected}, got {result}"
        );
    }
}

/// Comprehensive malformed-UTF-8 matrix for UTF-8 → UTF-16 transcoding
/// (#251): the forward-direction analogue of the #249 reverse matrix above.
/// Every ill-formed UTF-8 sequence — invalid continuation, invalid lead
/// (lone continuation / overlong 2-byte lead / out-of-range lead), overlong
/// encoding, UTF-8-encoded surrogate, and out-of-range 4-byte code point —
/// must transcode to U+FFFD (one UTF-16 code unit, 0xFFFD = 65533) per the
/// Canonical ABI, never to a wrong scalar. Valid inputs must be unchanged.
///
/// The callee sums received UTF-16 code units. Constants: U+FFFD = 65533,
/// 'A' = 0x41 = 65. Expected sums are hand-derived under the codebase's
/// established LS-P-19 "emit U+FFFD, consume ONLY the lead byte" convention:
/// on malformed detection src_idx advances by 1, so any trailing
/// continuation byte (0x80–0xBF) is reprocessed and — being a lone
/// continuation acting as a lead — itself becomes another U+FFFD. This makes
/// several cases emit MORE than one U+FFFD; the per-case derivations spell
/// out the exact count.
#[test]
fn test_sr17_utf8_to_utf16_malformed_matrix() {
    // (input UTF-8 bytes, expected callee code-unit-sum, label)
    //
    // Hand-derivations for the malformed cases (FFFD = 65533):
    //   [0xC2,0x41]            2-byte lead, 0x41 not a continuation
    //                          → FFFD (consume lead 0xC2), then 0x41 = 'A' = 65
    //                          → 65533 + 65 = 65598
    //   [0x80,0x41]            0x80 is a lone continuation < 0xC2 → invalid lead
    //                          → FFFD (consume 1), then 0x41 = 65
    //                          → 65533 + 65 = 65598
    //   [0xC0,0x80]            0xC0 < 0xC2 → invalid (overlong) lead → FFFD
    //                          (consume 1); reprocess 0x80, a lone continuation
    //                          < 0xC2 → invalid lead → FFFD (consume 1)
    //                          → 65533 + 65533 = 131066
    //   [0xED,0xA0,0x80]       0xED is a 3-byte lead; conts 0xA0,0x80 are valid
    //                          continuation bytes, decoding to cp = 0xD800 (a
    //                          UTF-8-encoded surrogate) → rejected → FFFD,
    //                          consume ONLY the lead. src_idx now 1: reprocess
    //                          0xA0 (lone cont) → FFFD, consume 1. src_idx 2:
    //                          reprocess 0x80 (lone cont) → FFFD, consume 1.
    //                          THREE U+FFFD → 65533 * 3 = 196599
    //   [0xF5,0x80,0x80,0x80]  0xF5 >= 0xF5 → out-of-range lead → FFFD,
    //                          consume 1; the three trailing 0x80 are each lone
    //                          continuations → FFFD each. FOUR U+FFFD
    //                          → 65533 * 4 = 262132
    //   [0xF4,0x90,0x80,0x80]  0xF4 is an in-range 4-byte lead; conts valid,
    //                          cp = 0x110000 > U+10FFFF (out of range) →
    //                          rejected → FFFD, consume ONLY the lead. The
    //                          three trailing bytes 0x90,0x80,0x80 are then
    //                          each lone continuations → FFFD each. FOUR U+FFFD
    //                          → 65533 * 4 = 262132
    //
    // Valid controls (must be byte-for-byte unchanged from the fast paths):
    //   [0x41]                 'A' = 65
    //   [0xC3,0xA9]            é = U+00E9 = 233
    //   [0xE2,0x82,0xAC]       € = U+20AC = 8364
    //   [0xF0,0x9F,0x98,0x80]  😀 = U+1F600 → surrogate pair 0xD83D + 0xDE00
    //                          = 55357 + 56832 = 112189
    let cases: &[(&[u8], i32, &str)] = &[
        // Malformed.
        (&[0xC2, 0x41], 65598, "2-byte bad continuation → FFFD + A"),
        (&[0x80, 0x41], 65598, "lone continuation as lead → FFFD + A"),
        (
            &[0xC0, 0x80],
            131066,
            "overlong 2-byte lead 0xC0 + lone cont → FFFD + FFFD",
        ),
        (
            &[0xED, 0xA0, 0x80],
            196599,
            "UTF-8-encoded surrogate U+D800 → FFFD x3 (lead + 2 reprocessed conts)",
        ),
        (
            &[0xF5, 0x80, 0x80, 0x80],
            262132,
            "out-of-range lead 0xF5 → FFFD x4",
        ),
        (
            &[0xF4, 0x90, 0x80, 0x80],
            262132,
            "4-byte > U+10FFFF → FFFD x4 (lead + 3 reprocessed conts)",
        ),
        // Valid controls.
        (&[0x41], 65, "valid ASCII 'A'"),
        (&[0xC3, 0xA9], 233, "valid 2-byte é U+00E9"),
        (&[0xE2, 0x82, 0xAC], 8364, "valid 3-byte € U+20AC"),
        (
            &[0xF0, 0x9F, 0x98, 0x80],
            112189,
            "valid 4-byte 😀 U+1F600 → surrogate pair",
        ),
    ];

    for (bytes, expected, label) in cases {
        let callee = build_callee_utf16_string_component();
        let caller = build_caller_string_component_data(bytes);
        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            component_provenance: false,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: meld_core::CustomSectionHandling::Drop,
            dwarf_handling: meld_core::DwarfHandling::Strip,
            output_format: meld_core::OutputFormat::CoreModule,
            opaque_resources: Vec::new(),
        };
        let mut fuser = Fuser::new(config);
        fuser
            .add_component_named(&callee, Some("callee-utf16"))
            .expect("callee parse");
        fuser
            .add_component_named(&caller, Some("caller-utf8"))
            .expect("caller parse");
        let (fused, _) = fuser.fuse_with_stats().expect("fusion");

        let mut validator = wasmparser::Validator::new();
        validator
            .validate_all(&fused)
            .unwrap_or_else(|e| panic!("#251 [{label}]: output must validate: {e}"));

        let mut ec = Config::new();
        ec.wasm_multi_memory(true);
        let engine = Engine::new(&ec).unwrap();
        let module = RuntimeModule::new(&engine, &fused).unwrap();
        let mut store = Store::new(&engine, ());
        let instance = Instance::new(&mut store, &module, &[]).unwrap();
        let run = instance
            .get_typed_func::<(), i32>(&mut store, "run")
            .unwrap();
        let result = run.call(&mut store, ()).unwrap();
        assert_eq!(
            result, *expected,
            "#251 [{label}]: input {bytes:#04x?} expected code-unit-sum {expected}, got {result}"
        );
    }
}

/// SR-17 (#253 increment 2): Latin-1 → UTF-16 string transcoding at runtime.
///
/// This direction is total and unambiguous — each Latin-1 byte 0x00–0xFF
/// zero-extends to exactly one UTF-16 code unit U+0000–U+00FF (no surrogates,
/// no malformed forms). Increment 1 (#254) refused this pair on the fail-loud
/// arm; increment 2 implements `emit_latin1_to_utf16_transcode`, so the
/// (Latin1, Utf16) pair now SUCCEEDS.
///
/// Fixture: a CompactUTF16-lowering caller (meld maps CompactUTF16 → Latin1)
/// storing 1 byte/char, fused into the UTF-16 code-unit-summing callee. The
/// callee sums the received code units, so the oracle is the sum of the
/// zero-extended bytes.
///
/// Hand-computed cases:
///   [] (empty)                  → []                       → sum 0
///   [0x00] (NUL)                → [0x0000]                 → sum 0
///   [0x7F] (ASCII boundary)     → [0x007F]                 → sum 127
///   [0x41, 0xE9, 0xFF]          → [0x0041, 0x00E9, 0x00FF] → 65+233+255 = 553
///   [0xFF, 0xFF]                → [0x00FF, 0x00FF]         → 255+255   = 510
#[test]
fn test_sr17_latin1_to_utf16_transcoding() {
    let cases: &[(&[u8], i32, &str)] = &[
        (&[], 0, "empty"),
        (&[0x00], 0, "NUL → U+0000"),
        (&[0x7F], 127, "ASCII boundary U+007F"),
        (&[0x41, 0xE9, 0xFF], 553, "A é ÿ → U+0041 U+00E9 U+00FF"),
        (&[0xFF, 0xFF], 510, "two U+00FF"),
    ];

    for (bytes, expected, label) in cases {
        let callee = build_callee_utf16_string_component(); // lifts UTF-16, sums code units
        let caller = build_caller_latin1_lowering_component(bytes);

        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            component_provenance: false,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: meld_core::CustomSectionHandling::Drop,
            dwarf_handling: meld_core::DwarfHandling::Strip,
            output_format: meld_core::OutputFormat::CoreModule,
            opaque_resources: Vec::new(),
        };
        let mut fuser = Fuser::new(config);
        fuser
            .add_component_named(&callee, Some("callee-utf16"))
            .expect("callee parse");
        fuser
            .add_component_named(&caller, Some("caller-latin1"))
            .expect("caller parse");
        let (fused, _) = fuser
            .fuse_with_stats()
            .unwrap_or_else(|e| panic!("#253 [{label}]: Latin1→Utf16 fusion must succeed: {e:?}"));

        let mut validator = wasmparser::Validator::new();
        validator
            .validate_all(&fused)
            .unwrap_or_else(|e| panic!("#253 [{label}]: output must validate: {e}"));

        let mut ec = Config::new();
        ec.wasm_multi_memory(true);
        let engine = Engine::new(&ec).unwrap();
        let module = RuntimeModule::new(&engine, &fused).unwrap();
        let mut store = Store::new(&engine, ());
        let instance = Instance::new(&mut store, &module, &[]).unwrap();
        let run = instance
            .get_typed_func::<(), i32>(&mut store, "run")
            .unwrap();
        let result = run.call(&mut store, ()).unwrap();
        assert_eq!(
            result, *expected,
            "#253 [{label}]: input {bytes:#04x?} expected code-unit-sum {expected}, got {result}"
        );
    }
}

/// #253 fail-loud guard (still-unsupported direction): the down-conversion
/// directions remain genuinely ambiguous and stay on the unchanged catch-all
/// `Err` arm. Increment 2 only added (Latin1 → Utf16); (Utf16 → Latin1) is
/// NOT implemented (code points > 0xFF are unrepresentable in Latin-1), so it
/// must still FAIL fusion loudly rather than silently emit a wrong adapter.
///
/// Fixture: a UTF-16-lowering caller fused into a CompactUTF16-lifting callee
/// (meld maps CompactUTF16 → Latin1), producing the (Utf16, Latin1) pair.
/// Fusion must return Err. (The complementary (Utf8 → Latin1) pair shares the
/// same unchanged catch-all and is not separately fixtured here.)
#[test]
fn test_253_utf16_to_latin1_transcode_fails_loud() {
    let callee = build_callee_codeunit_summing_component(CanonicalOption::CompactUTF16); // → Latin1
    let caller = build_caller_utf16_lowering_component(&[0x0041]);

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&callee, Some("callee-latin1"))
        .expect("callee parse");
    fuser
        .add_component_named(&caller, Some("caller-utf16"))
        .expect("caller parse");

    let result = fuser.fuse_with_stats();
    assert!(
        result.is_err(),
        "#253: (Utf16 -> Latin1) is a lossy down-conversion with no transcoder; \
         fusion must fail loudly rather than emit a silently-wrong copy. Got Ok."
    );
    let msg = format!("{:?}", result.err().unwrap());
    assert!(
        msg.contains("transcoding") || msg.contains("#253"),
        "#253: error should name the unsupported transcoding; got: {msg}"
    );
}
