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
//!
//! Test 3 (`test_multi_memory_result_copy_adapter`):
//!   Verifies that the cross-memory adapter correctly copies returned
//!   `(ptr, len)` data from callee's memory back to caller's memory.
//!   Builds a hand-assembled wasm module containing two memories, a callee
//!   function that returns a pointer into its memory, and an adapter that
//!   copies the returned data to the caller's memory. A `run` function calls
//!   the adapter and reads the copied data from the caller's memory.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, ConstExpr, DataSection, DataSegment, DataSegmentMode, ExportKind,
    ExportSection, Function, FunctionSection, GlobalSection, GlobalType, ImportSection,
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

// ---------------------------------------------------------------------------
// Test 3: Result copy adapter (callee → caller memory)
// ---------------------------------------------------------------------------

/// Build a raw wasm module (not component) with two memories that exercises
/// the cross-memory result-copy adapter pattern:
///
/// - Memory 0 (caller): zero-initialized
/// - Memory 1 (callee): data segment with i32 value 66 at offset 0
/// - `callee()`:      returns (ptr=0, len=4) into memory 1
/// - `realloc(…)`:    bump allocator in memory 0 using global 0
/// - `adapter()`:     calls callee, copies result from mem 1 → mem 0
/// - `run()`:         calls adapter, loads i32 from mem 0 at returned ptr
///
/// Expected: `run()` returns 66 — proving data was copied across memories.
fn build_result_copy_module() -> Vec<u8> {
    let mut types = TypeSection::new();
    // type 0: () -> (i32, i32)  -- callee and adapter (multi-value)
    types
        .ty()
        .function([], [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32]);
    // type 1: (i32, i32, i32, i32) -> i32  -- realloc
    types.ty().function(
        [
            wasm_encoder::ValType::I32,
            wasm_encoder::ValType::I32,
            wasm_encoder::ValType::I32,
            wasm_encoder::ValType::I32,
        ],
        [wasm_encoder::ValType::I32],
    );
    // type 2: () -> i32  -- run
    types.ty().function([], [wasm_encoder::ValType::I32]);

    // func 0: callee, func 1: realloc, func 2: adapter, func 3: run
    let mut functions = FunctionSection::new();
    functions.function(0); // callee: type 0
    functions.function(1); // realloc: type 1
    functions.function(0); // adapter: type 0
    functions.function(2); // run: type 2

    let mut memories = MemorySection::new();
    // memory 0: caller
    memories.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    // memory 1: callee (will have data segment)
    memories.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    // global 0: mutable i32 bump pointer for memory 0 realloc
    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: wasm_encoder::ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(0),
    );

    let mut exports = ExportSection::new();
    exports.export("run", ExportKind::Func, 3);
    exports.export("memory_0", ExportKind::Memory, 0);
    exports.export("memory_1", ExportKind::Memory, 1);

    let mut code = CodeSection::new();

    // func 0: callee() -> (i32, i32)
    // Returns (ptr=0, len=4) pointing to pre-initialized data in memory 1
    {
        let mut f = Function::new([]);
        f.instruction(&Instruction::I32Const(0)); // ptr
        f.instruction(&Instruction::I32Const(4)); // len
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 1: realloc(original_ptr, original_size, alignment, new_size) -> ptr
    // Bump allocator: returns current global[0], then bumps by new_size
    {
        let mut f = Function::new([]);
        f.instruction(&Instruction::GlobalGet(0)); // return value
        f.instruction(&Instruction::GlobalGet(0)); // current bump
        f.instruction(&Instruction::LocalGet(3)); // new_size
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::GlobalSet(0)); // bump += new_size
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 2: adapter() -> (i32, i32)
    // Calls callee, copies returned data from memory 1 to memory 0
    {
        // 3 scratch locals: callee_ptr(0), callee_len(1), caller_new_ptr(2)
        let mut f = Function::new(vec![(3, wasm_encoder::ValType::I32)]);

        // Call callee -> stack: [ptr, len]
        f.instruction(&Instruction::Call(0));
        // Save (stack pops in reverse: len first, then ptr)
        f.instruction(&Instruction::LocalSet(1)); // callee_len
        f.instruction(&Instruction::LocalSet(0)); // callee_ptr

        // Allocate in memory 0: realloc(0, 0, 1, callee_len) -> caller_new_ptr
        f.instruction(&Instruction::I32Const(0)); // original_ptr
        f.instruction(&Instruction::I32Const(0)); // original_size
        f.instruction(&Instruction::I32Const(1)); // alignment
        f.instruction(&Instruction::LocalGet(1)); // new_size = callee_len
        f.instruction(&Instruction::Call(1)); // -> caller_new_ptr
        f.instruction(&Instruction::LocalSet(2));

        // memory.copy: dst=memory 0, src=memory 1
        // Operands: (dst_addr, src_addr, len)
        f.instruction(&Instruction::LocalGet(2)); // dst = caller_new_ptr
        f.instruction(&Instruction::LocalGet(0)); // src = callee_ptr
        f.instruction(&Instruction::LocalGet(1)); // len = callee_len
        f.instruction(&Instruction::MemoryCopy {
            src_mem: 1,
            dst_mem: 0,
        });

        // Return (caller_new_ptr, callee_len)
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::LocalGet(1));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 3: run() -> i32
    // Calls adapter, reads i32 from memory 0 at the returned pointer
    {
        // 1 scratch local for discarding the len
        let mut f = Function::new(vec![(1, wasm_encoder::ValType::I32)]);

        // Call adapter -> stack: [ptr, len]
        f.instruction(&Instruction::Call(2));
        f.instruction(&Instruction::LocalSet(0)); // save len (discard)
        // Stack: [ptr]

        // Load i32 from memory 0 at ptr
        f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 0,
            align: 2, // 4-byte alignment
            memory_index: 0,
        }));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // Data segment: memory 1, offset 0, value 66 (0x42) as little-endian i32
    let mut data = DataSection::new();
    data.segment(DataSegment {
        mode: DataSegmentMode::Active {
            memory_index: 1,
            offset: &ConstExpr::i32_const(0),
        },
        data: vec![0x42, 0x00, 0x00, 0x00],
    });

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memories)
        .section(&globals)
        .section(&exports)
        .section(&code)
        .section(&data);

    module.finish()
}

#[test]
fn test_multi_memory_result_copy_adapter() {
    let wasm_bytes = build_result_copy_module();

    // Multi-memory and bulk-memory required
    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &wasm_bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // Verify 2 memory exports
    let mem_count = count_memory_exports(&instance, &mut store);
    assert_eq!(
        mem_count, 2,
        "module should export 2 memories (caller + callee)"
    );

    // run() should return 66: the i32 value from memory 1 copied to memory 0
    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap();
    let result = run.call(&mut store, ()).unwrap();
    assert_eq!(
        result, 66,
        "run() should return 66 (data copied from callee memory 1 to caller memory 0)"
    );
}

// ---------------------------------------------------------------------------
// Test 4: Memory grow isolation (memory 0 growth does not affect memory 1)
// ---------------------------------------------------------------------------

/// Build a raw wasm module with two memories that verifies growing one memory
/// does not corrupt the other:
///
/// - Memory 0 (caller): 2 pages initial
/// - Memory 1 (callee): 1 page, data segment with i32 value 42 at offset 0
/// - `grow_a()`:   grows memory 0 by 1 page, writes 0xAA at offset 131072
/// - `check_b()`:  loads i32 from memory 1 offset 0
/// - `run()`:      calls grow_a(), then check_b(), returns result
///
/// Expected: `run()` returns 42 — memory 1 is unaffected by memory 0 growth.
fn build_grow_isolation_module() -> Vec<u8> {
    let mut types = TypeSection::new();
    // type 0: () -> ()  -- grow_a
    types.ty().function([], []);
    // type 1: () -> i32  -- check_b and run
    types.ty().function([], [wasm_encoder::ValType::I32]);

    // func 0: grow_a (type 0), func 1: check_b (type 1), func 2: run (type 1)
    let mut functions = FunctionSection::new();
    functions.function(0); // grow_a: type 0
    functions.function(1); // check_b: type 1
    functions.function(1); // run: type 1

    let mut memories = MemorySection::new();
    // memory 0: 2 pages initial
    memories.memory(MemoryType {
        minimum: 2,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    // memory 1: 1 page initial (data segment with value 42)
    memories.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut exports = ExportSection::new();
    exports.export("run", ExportKind::Func, 2);

    let mut code = CodeSection::new();

    // func 0: grow_a() -> ()
    // Grows memory 0 by 1 page, writes 0xAA at offset 131072 (2 * 65536)
    {
        let mut f = Function::new([]);
        // memory.grow memory 0 by 1 page
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::MemoryGrow(0));
        f.instruction(&Instruction::Drop); // discard previous page count
        // Write 0xAA at the start of the new page (offset 2 * 65536 = 131072)
        f.instruction(&Instruction::I32Const(131072));
        f.instruction(&Instruction::I32Const(0xAA));
        f.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 1: check_b() -> i32
    // Loads i32 from memory 1 at offset 0
    {
        let mut f = Function::new([]);
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 1,
        }));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 2: run() -> i32
    // Calls grow_a(), then check_b(), returns the result
    {
        let mut f = Function::new([]);
        f.instruction(&Instruction::Call(0)); // grow_a()
        f.instruction(&Instruction::Call(1)); // check_b() -> i32
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // Data segment: memory 1, offset 0, value 42 as little-endian i32
    let mut data = DataSection::new();
    data.segment(DataSegment {
        mode: DataSegmentMode::Active {
            memory_index: 1,
            offset: &ConstExpr::i32_const(0),
        },
        data: vec![0x2A, 0x00, 0x00, 0x00],
    });

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memories)
        .section(&exports)
        .section(&code)
        .section(&data);

    module.finish()
}

#[test]
fn test_multi_memory_grow_isolation() {
    let wasm_bytes = build_grow_isolation_module();

    // Multi-memory required
    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &wasm_bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // run() should return 42: memory 1 is unaffected by memory 0 growth
    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap();
    let result = run.call(&mut store, ()).unwrap();
    assert_eq!(
        result, 42,
        "run() should return 42 (memory 1 unaffected by memory 0 growth)"
    );
}

// ---------------------------------------------------------------------------
// Test 5: Cross-memory string copy via adapter pattern
// ---------------------------------------------------------------------------

/// Build a raw wasm module with two memories that exercises a complete
/// cross-memory string copy and processing pipeline:
///
/// - Memory 0: 1 page, data segment with "Hello" (5 bytes) at offset 100
/// - Memory 1: 1 page, zero-initialized (target for copy)
/// - Global 0: mutable i32, bump allocator pointer for memory 1
/// - `realloc(orig_ptr, orig_size, align, new_size) -> ptr`:
///   bump allocator in memory 1 using global 0
/// - `callee(ptr, len) -> i32`:
///   sums bytes from memory 1 starting at ptr for len bytes
/// - `adapter(ptr, len) -> i32`:
///   allocates in memory 1 via realloc, copies data from memory 0 to
///   memory 1 via memory.copy, calls callee with the new pointer
/// - `run() -> i32`:
///   calls adapter(100, 5)
///
/// Expected: `run()` returns 500 — sum of ASCII values of "Hello"
/// (72 + 101 + 108 + 108 + 111 = 500).
fn build_string_copy_module() -> Vec<u8> {
    let mut types = TypeSection::new();
    // type 0: (i32, i32, i32, i32) -> i32  -- realloc
    types.ty().function(
        [
            wasm_encoder::ValType::I32,
            wasm_encoder::ValType::I32,
            wasm_encoder::ValType::I32,
            wasm_encoder::ValType::I32,
        ],
        [wasm_encoder::ValType::I32],
    );
    // type 1: (i32, i32) -> i32  -- callee and adapter
    types.ty().function(
        [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
        [wasm_encoder::ValType::I32],
    );
    // type 2: () -> i32  -- run
    types.ty().function([], [wasm_encoder::ValType::I32]);

    // func 0: realloc (type 0), func 1: callee (type 1),
    // func 2: adapter (type 1), func 3: run (type 2)
    let mut functions = FunctionSection::new();
    functions.function(0); // realloc: type 0
    functions.function(1); // callee: type 1
    functions.function(1); // adapter: type 1
    functions.function(2); // run: type 2

    let mut memories = MemorySection::new();
    // memory 0: source (contains "Hello" at offset 100)
    memories.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    // memory 1: destination (bump-allocated target)
    memories.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    // global 0: mutable i32 bump pointer for memory 1 realloc
    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: wasm_encoder::ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(0),
    );

    let mut exports = ExportSection::new();
    exports.export("run", ExportKind::Func, 3);

    let mut code = CodeSection::new();

    // func 0: realloc(original_ptr, original_size, alignment, new_size) -> ptr
    // Bump allocator: returns current global[0], then bumps by new_size
    {
        let mut f = Function::new([]);
        f.instruction(&Instruction::GlobalGet(0)); // return value = current bump
        f.instruction(&Instruction::GlobalGet(0)); // current bump
        f.instruction(&Instruction::LocalGet(3)); // new_size
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::GlobalSet(0)); // bump += new_size
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 1: callee(ptr: i32, len: i32) -> i32
    // Sums bytes from memory 1 starting at ptr for len bytes
    // Locals: param 0 = ptr, param 1 = len, local 2 = sum, local 3 = index
    {
        let mut f = Function::new(vec![(2, wasm_encoder::ValType::I32)]);

        // sum = 0 (default), index = 0 (default)
        // block $break
        f.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        // loop $loop
        f.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        // if index >= len, break
        f.instruction(&Instruction::LocalGet(3)); // index
        f.instruction(&Instruction::LocalGet(1)); // len
        f.instruction(&Instruction::I32GeU);
        f.instruction(&Instruction::BrIf(1)); // br to block end

        // sum += load_u8(memory 1, ptr + index)
        f.instruction(&Instruction::LocalGet(0)); // ptr
        f.instruction(&Instruction::LocalGet(3)); // index
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Load8U(wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: 1,
        }));
        f.instruction(&Instruction::LocalGet(2)); // sum
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(2)); // sum = sum + byte

        // index += 1
        f.instruction(&Instruction::LocalGet(3)); // index
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(3)); // index = index + 1

        // br to loop start
        f.instruction(&Instruction::Br(0));

        f.instruction(&Instruction::End); // end loop
        f.instruction(&Instruction::End); // end block

        // return sum
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::End); // end function
        code.function(&f);
    }

    // func 2: adapter(ptr: i32, len: i32) -> i32
    // Allocates in memory 1, copies from memory 0, calls callee
    // Locals: param 0 = ptr, param 1 = len, local 2 = new_ptr
    {
        let mut f = Function::new(vec![(1, wasm_encoder::ValType::I32)]);

        // Allocate len bytes in memory 1: realloc(0, 0, 1, len)
        f.instruction(&Instruction::I32Const(0)); // original_ptr
        f.instruction(&Instruction::I32Const(0)); // original_size
        f.instruction(&Instruction::I32Const(1)); // alignment
        f.instruction(&Instruction::LocalGet(1)); // new_size = len
        f.instruction(&Instruction::Call(0)); // realloc -> new_ptr
        f.instruction(&Instruction::LocalSet(2)); // save new_ptr

        // memory.copy: dst_mem=1 (memory 1), src_mem=0 (memory 0)
        // Stack operands: (dst_addr, src_addr, len)
        f.instruction(&Instruction::LocalGet(2)); // dst = new_ptr (in memory 1)
        f.instruction(&Instruction::LocalGet(0)); // src = ptr (in memory 0)
        f.instruction(&Instruction::LocalGet(1)); // len
        f.instruction(&Instruction::MemoryCopy {
            src_mem: 0,
            dst_mem: 1,
        });

        // Call callee(new_ptr, len) -> i32
        f.instruction(&Instruction::LocalGet(2)); // new_ptr
        f.instruction(&Instruction::LocalGet(1)); // len
        f.instruction(&Instruction::Call(1)); // callee

        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 3: run() -> i32
    // Calls adapter(100, 5) and returns the result
    {
        let mut f = Function::new([]);
        f.instruction(&Instruction::I32Const(100)); // ptr (offset of "Hello" in memory 0)
        f.instruction(&Instruction::I32Const(5)); // len (5 bytes)
        f.instruction(&Instruction::Call(2)); // adapter(100, 5)
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // Data segment: memory 0, offset 100, "Hello" bytes
    let mut data = DataSection::new();
    data.segment(DataSegment {
        mode: DataSegmentMode::Active {
            memory_index: 0,
            offset: &ConstExpr::i32_const(100),
        },
        data: vec![0x48, 0x65, 0x6C, 0x6C, 0x6F], // "Hello"
    });

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memories)
        .section(&globals)
        .section(&exports)
        .section(&code)
        .section(&data);

    module.finish()
}

#[test]
fn test_multi_memory_string_copy() {
    let wasm_bytes = build_string_copy_module();

    // Multi-memory and bulk-memory required
    let mut engine_config = Config::new();
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &wasm_bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // run() should return 500: sum of ASCII values of "Hello"
    // H(72) + e(101) + l(108) + l(108) + o(111) = 500
    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .unwrap();
    let result = run.call(&mut store, ()).unwrap();
    assert_eq!(
        result, 500,
        "run() should return 500 (sum of ASCII values of 'Hello': 72+101+108+108+111)"
    );
}
