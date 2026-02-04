use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, DataCountSection, DataSection, DataSegment, DataSegmentMode,
    ExportKind, ExportSection, Function, FunctionSection, Instruction, MemorySection, MemoryType,
    Module, ModuleSection, TypeSection,
};
use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};

const WASM_PAGE_SIZE: usize = 65_536;

fn build_component(module: Module) -> Vec<u8> {
    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
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
        .section(&shared_memory_section())
        .section(&exports)
        .section(&code);

    module
}

fn build_module_b() -> Module {
    let mut types = TypeSection::new();
    types.ty().function([], []);

    let mut functions = FunctionSection::new();
    functions.function(0);
    functions.function(0);
    functions.function(0);

    let mut exports = ExportSection::new();
    exports.export("b_init", ExportKind::Func, 0);
    exports.export("b_copy", ExportKind::Func, 1);
    exports.export("b_fill", ExportKind::Func, 2);

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

    let mut copy = Function::new([]);
    copy.instruction(&Instruction::I32Const(4));
    copy.instruction(&Instruction::I32Const(0));
    copy.instruction(&Instruction::I32Const(4));
    copy.instruction(&Instruction::MemoryCopy {
        src_mem: 0,
        dst_mem: 0,
    });
    copy.instruction(&Instruction::End);
    code.function(&copy);

    let mut fill = Function::new([]);
    fill.instruction(&Instruction::I32Const(8));
    fill.instruction(&Instruction::I32Const(0xBB));
    fill.instruction(&Instruction::I32Const(4));
    fill.instruction(&Instruction::MemoryFill(0));
    fill.instruction(&Instruction::End);
    code.function(&fill);

    let mut data = DataSection::new();
    data.segment(DataSegment {
        mode: DataSegmentMode::Passive,
        data: [1u8, 2, 3, 4],
    });

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&shared_memory_section())
        .section(&exports)
        .section(&DataCountSection { count: 1 })
        .section(&code)
        .section(&data);

    module
}

fn read_shared(memory: &wasmtime::SharedMemory, offset: usize, len: usize) -> Vec<u8> {
    let data = memory.data();
    (0..len)
        // Safe for this test: we read after all writes, with no concurrent access.
        .map(|idx| unsafe { *data[offset + idx].get() })
        .collect()
}

#[test]
fn test_address_rebasing_end_to_end() {
    let component_a = build_component(build_module_a());
    let component_b = build_component(build_module_b());

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        ..Default::default()
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component_a, Some("component-a"))
        .unwrap();
    fuser
        .add_component_named(&component_b, Some("component-b"))
        .unwrap();

    let fused = fuser.fuse().unwrap();

    let mut engine_config = Config::new();
    engine_config.wasm_threads(true);
    engine_config.shared_memory(true);
    engine_config.wasm_bulk_memory(true);

    let engine = Engine::new(&engine_config).unwrap();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let a_fill = instance
        .get_typed_func::<(), ()>(&mut store, "a_fill")
        .unwrap();
    let b_init = instance
        .get_typed_func::<(), ()>(&mut store, "b_init")
        .unwrap();
    let b_copy = instance
        .get_typed_func::<(), ()>(&mut store, "b_copy")
        .unwrap();
    let b_fill = instance
        .get_typed_func::<(), ()>(&mut store, "b_fill")
        .unwrap();

    a_fill.call(&mut store, ()).unwrap();
    b_init.call(&mut store, ()).unwrap();
    b_copy.call(&mut store, ()).unwrap();
    b_fill.call(&mut store, ()).unwrap();

    let memory = instance
        .get_shared_memory(&mut store, "memory")
        .expect("shared memory export not found");

    assert!(memory.data_size() >= 2 * WASM_PAGE_SIZE);

    let a_region = read_shared(&memory, 0, 4);
    assert_eq!(a_region, vec![0x11, 0x11, 0x11, 0x11]);

    let base = WASM_PAGE_SIZE;
    let b_init_region = read_shared(&memory, base, 4);
    assert_eq!(b_init_region, vec![1, 2, 3, 4]);

    let b_copy_region = read_shared(&memory, base + 4, 4);
    assert_eq!(b_copy_region, vec![1, 2, 3, 4]);

    let b_fill_region = read_shared(&memory, base + 8, 4);
    assert_eq!(b_fill_region, vec![0xBB, 0xBB, 0xBB, 0xBB]);
}
