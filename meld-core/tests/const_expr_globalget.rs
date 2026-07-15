//! #338 — extended-const expressions that BEGIN with `global.get` must be
//! preserved in full, not truncated to the leading `global.get`.
//!
//! meld used to read only the leading `global.get $base` of an initializer or
//! data/element offset of the position-independent `__memory_base + N` shape
//! (`global.get $base; i32.const N; i32.add`) and silently DROP the trailing
//! arithmetic — corrupting the value to `base + 0`. The fused module still
//! validates, so it is a silent miscompile. These executed-vs-wasmtime oracles
//! reproduce the bug: they PASS with the fix and FAIL (wrong value) without it.
//!
//! The value of a `global.get`-first expression is runtime-dependent (the
//! global's value), so meld cannot fold it to a constant; it must re-emit the
//! complete extended-const operator sequence with global indices remapped.
//!
//! `$base` is an IMPORTED immutable global (exactly `__memory_base`'s shape) —
//! a constant expression may only `global.get` an imported global.

use meld_core::{Fuser, FuserConfig};
use wasm_encoder::{
    CodeSection, Component, ConstExpr, DataSection, DataSegment, DataSegmentMode, ExportKind,
    ExportSection, Function, FunctionSection, GlobalSection, GlobalType, ImportSection,
    Instruction, MemorySection, MemoryType, Module, ModuleSection, TypeSection, ValType,
};
use wasmtime::{Engine, ExternType, Global, Instance, Module as RuntimeModule, Store, Val};

fn build_component(module: Module) -> Vec<u8> {
    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

fn imported_base_global() -> GlobalType {
    GlobalType {
        val_type: ValType::I32,
        mutable: false,
        shared: false,
    }
}

fn regular_memory_section() -> MemorySection {
    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    memory
}

fn fuse_single(module: Module) -> Vec<u8> {
    let component = build_component(module);
    let mut fuser = Fuser::new(FuserConfig::default());
    fuser
        .add_component_named(&component, Some("component-a"))
        .unwrap();
    fuser.fuse().unwrap()
}

/// Instantiate the fused core module, supplying `base` for every imported
/// (i32) global — meld leaves `$base` as an unresolved import, so we bind it
/// generically regardless of the module/name meld emits.
fn instantiate(fused: &[u8], base: i32) -> (Store<()>, Instance) {
    let engine = Engine::default();
    let module = RuntimeModule::new(&engine, fused).expect("fused module must validate");
    let mut store = Store::new(&engine, ());
    let mut externs = Vec::new();
    for imp in module.imports() {
        match imp.ty() {
            ExternType::Global(gt) => {
                let g = Global::new(&mut store, gt, Val::I32(base)).unwrap();
                externs.push(g.into());
            }
            other => panic!(
                "unexpected import {}::{} of type {other:?}",
                imp.module(),
                imp.name()
            ),
        }
    }
    let instance = Instance::new(&mut store, &module, &externs).unwrap();
    (store, instance)
}

const BASE: i32 = 1000;

/// Test 1 — GLOBAL INITIALIZER (`meld-core/src/merger.rs::convert_init_expr`).
///
/// `g (mut i32) = global.get $base; i32.const 100; i32.add` with `$base = 1000`
/// must initialise to 1100. Pre-fix, `convert_init_expr`'s `GlobalGet` arm
/// returned immediately with only `global.get $base`, dropping `+100`, so `g`
/// initialised to 1000 — this test FAILS (1000 != 1100) without the fix.
///
/// Negatives (must stay unchanged):
///   * `h (mut i32) = i32.const 5; i32.const 10; i32.add`  → 15  (pure const fold)
///   * `k (mut i32) = i32.const 100; global.get $base; i32.add` → 1100 (const-first
///     with an EMBEDDED global.get — the operand-swapped `N + base` shape). In
///     SINGLE-module fusion this happens to read correctly only because
///     `__memory_base` stays at import index 0, so the (formerly un-remapped)
///     global index still points at it. The multi-module test below shifts that
///     index off 0 and is the real regression guard for the embedded case (#338).
#[test]
fn test_338_global_initializer_extended_const_preserved() {
    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I32]); // type 0: () -> i32

    let mut imports = ImportSection::new();
    imports.import("env", "__memory_base", imported_base_global()); // global 0 = $base

    let mut globals = GlobalSection::new();
    let mut_i32 = GlobalType {
        val_type: ValType::I32,
        mutable: true,
        shared: false,
    };
    // global 1: $g = global.get $base; i32.const 100; i32.add  (=1100)
    globals.global(
        mut_i32,
        &ConstExpr::global_get(0).with_i32_const(100).with_i32_add(),
    );
    // global 2: $h = i32.const 5; i32.const 10; i32.add  (=15, pure fold)
    globals.global(
        mut_i32,
        &ConstExpr::i32_const(5).with_i32_const(10).with_i32_add(),
    );
    // global 3: $k = i32.const 100; global.get $base; i32.add  (=1100, const-first)
    globals.global(
        mut_i32,
        &ConstExpr::i32_const(100).with_global_get(0).with_i32_add(),
    );

    let mut functions = FunctionSection::new();
    functions.function(0);
    functions.function(0);
    functions.function(0);

    let mut exports = ExportSection::new();
    exports.export("get_g", ExportKind::Func, 0);
    exports.export("get_h", ExportKind::Func, 1);
    exports.export("get_k", ExportKind::Func, 2);

    let mut code = CodeSection::new();
    for global_index in [1u32, 2, 3] {
        let mut f = Function::new([]);
        f.instruction(&Instruction::GlobalGet(global_index));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    let mut module = Module::new();
    module
        .section(&types)
        .section(&imports)
        .section(&functions)
        .section(&globals)
        .section(&exports)
        .section(&code);

    let fused = fuse_single(module);
    let (mut store, instance) = instantiate(&fused, BASE);

    let get_g = instance
        .get_typed_func::<(), i32>(&mut store, "get_g")
        .unwrap();
    let get_h = instance
        .get_typed_func::<(), i32>(&mut store, "get_h")
        .unwrap();
    let get_k = instance
        .get_typed_func::<(), i32>(&mut store, "get_k")
        .unwrap();

    // THE BUG: pre-fix this is 1000 (base + 0), the dropped `+100`.
    assert_eq!(
        get_g.call(&mut store, ()).unwrap(),
        1100,
        "global.get-first extended-const initializer must be base+100=1100, \
         not the truncated base+0=1000 (#338)"
    );
    // Negative: pure const-fold unchanged.
    assert_eq!(get_h.call(&mut store, ()).unwrap(), 15);
    // Negative: const-first with an embedded global.get unchanged.
    assert_eq!(get_k.call(&mut store, ()).unwrap(), 1100);
}

/// Test 2 — DATA-SEGMENT OFFSET (`meld-core/src/segments.rs`).
///
/// An active data segment at offset `global.get $base; i32.const 100; i32.add`
/// (`$base = 1000`) must place its bytes at 1100. Pre-fix the offset truncated
/// to `global.get $base` = 1000, so the bytes landed at 1000 and address 1100
/// read back zero — this test FAILS without the fix.
///
/// Negative: a BARE `global.get $base` offset (no trailing arithmetic) must be
/// unchanged — its bytes land at exactly 1000.
#[test]
fn test_338_data_segment_offset_extended_const_preserved() {
    const PAYLOAD: [u8; 4] = [0xDE, 0xAD, 0xBE, 0xEF];
    const BARE: [u8; 2] = [0x11, 0x22];

    let mut imports = ImportSection::new();
    imports.import("env", "__memory_base", imported_base_global()); // global 0 = $base

    let mut exports = ExportSection::new();
    exports.export("mem", ExportKind::Memory, 0);

    // Extended offset: global.get $base; i32.const 100; i32.add  → 1100.
    let ext_offset = ConstExpr::global_get(0).with_i32_const(100).with_i32_add();
    // Bare offset: global.get $base  → 1000 (unchanged control).
    let bare_offset = ConstExpr::global_get(0);

    let mut data = DataSection::new();
    data.segment(DataSegment {
        mode: DataSegmentMode::Active {
            memory_index: 0,
            offset: &ext_offset,
        },
        data: PAYLOAD,
    });
    data.segment(DataSegment {
        mode: DataSegmentMode::Active {
            memory_index: 0,
            offset: &bare_offset,
        },
        data: BARE,
    });

    // Section order: Type, Import, Memory, Global, Export, DataCount/Code, Data.
    let mut module = Module::new();
    module
        .section(&imports)
        .section(&regular_memory_section())
        .section(&exports)
        .section(&data);

    let fused = fuse_single(module);
    let (mut store, instance) = instantiate(&fused, BASE);

    let mem = instance.get_memory(&mut store, "mem").expect("mem export");
    let data = mem.data(&store);

    // THE BUG: pre-fix the payload lands at 1000, so 1100..1104 reads zero.
    assert_eq!(
        &data[1100..1104],
        &PAYLOAD,
        "data segment must land at base+100=1100, not the truncated base+0=1000 (#338)"
    );
    // Negative: bare global.get offset unchanged — bytes at exactly 1000.
    assert_eq!(
        &data[1000..1002],
        &BARE,
        "bare global.get offset must be unchanged"
    );
}

/// Instantiate a fused module binding each imported (i32) global by NAME:
/// `__memory_base` -> `base`, anything else (e.g. `__stack_pointer`) ->
/// `other`. Distinct values let the test detect a wrong global index — reading
/// the wrong import yields the wrong arithmetic result.
fn instantiate_by_name(fused: &[u8], base: i32, other: i32) -> (Store<()>, Instance) {
    let engine = Engine::default();
    let module = RuntimeModule::new(&engine, fused).expect("fused module must validate");
    let mut store = Store::new(&engine, ());
    let mut externs = Vec::new();
    for imp in module.imports() {
        match imp.ty() {
            ExternType::Global(gt) => {
                let v = if imp.name() == "__memory_base" {
                    base
                } else {
                    other
                };
                let g = Global::new(&mut store, gt, Val::I32(v)).unwrap();
                externs.push(g.into());
            }
            other_ty => panic!(
                "unexpected import {}::{} of type {other_ty:?}",
                imp.module(),
                imp.name()
            ),
        }
    }
    let instance = Instance::new(&mut store, &module, &externs).unwrap();
    (store, instance)
}

/// Component A: imports `env::__stack_pointer` and exports a getter for it.
/// Fused FIRST, so `__stack_pointer` claims merged import-global index 0 and
/// pushes B's `__memory_base` to a NON-zero merged index.
fn build_component_stack_pointer() -> Vec<u8> {
    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I32]);

    let mut imports = ImportSection::new();
    imports.import("env", "__stack_pointer", imported_base_global()); // global 0

    let mut functions = FunctionSection::new();
    functions.function(0);

    let mut exports = ExportSection::new();
    exports.export("get_sp", ExportKind::Func, 0);

    let mut code = CodeSection::new();
    let mut f = Function::new([]);
    f.instruction(&Instruction::GlobalGet(0));
    f.instruction(&Instruction::End);
    code.function(&f);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&imports)
        .section(&functions)
        .section(&exports)
        .section(&code);
    build_component(module)
}

/// Component B: imports `env::__memory_base` as its ONLY global (local index 0)
/// and defines `$b (mut i32) = i32.const 100; global.get $__memory_base;
/// i32.add` — the operand-swapped `N + base` extended-const shape.
fn build_component_membase_initializer() -> Vec<u8> {
    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I32]);

    let mut imports = ImportSection::new();
    imports.import("env", "__memory_base", imported_base_global()); // local global 0

    let mut globals = GlobalSection::new();
    let mut_i32 = GlobalType {
        val_type: ValType::I32,
        mutable: true,
        shared: false,
    };
    // local global 1: i32.const 100; global.get $__memory_base; i32.add  (=base+100)
    globals.global(
        mut_i32,
        &ConstExpr::i32_const(100).with_global_get(0).with_i32_add(),
    );

    let mut functions = FunctionSection::new();
    functions.function(0);

    let mut exports = ExportSection::new();
    exports.export("get_b", ExportKind::Func, 0);

    let mut code = CodeSection::new();
    let mut f = Function::new([]);
    f.instruction(&Instruction::GlobalGet(1));
    f.instruction(&Instruction::End);
    code.function(&f);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&imports)
        .section(&functions)
        .section(&globals)
        .section(&exports)
        .section(&code);
    build_component(module)
}

/// Test 3 — MULTI-MODULE base-shift for the CONST-FIRST embedded `global.get`
/// (`meld-core/src/merger.rs::convert_init_expr`, i32.const arm).
///
/// Two independent components are fused. Component A (fused first) imports
/// `__stack_pointer`, claiming merged import-global index 0. Component B's
/// `__memory_base` is therefore remapped to merged index 1, while B's stored
/// initializer bytes name its LOCAL index 0. B's global initializer is
/// `i32.const 100; global.get $__memory_base; i32.add`.
///
/// Pre-fix, `convert_init_expr` folded `i32.const 100`, hit the embedded
/// `global.get`, its i32 arm returned `Err`, and the merger fell back to the
/// module's ORIGINAL un-remapped bytes — emitting `global.get 0`, which in the
/// merged module is `__stack_pointer` (bound to 5000 here), so `$b` initialised
/// to 5100. Observed pre-fix failure: `assertion left == right` with
/// `left: 5100, right: 1100`. Post-fix the sequence is preserved and the global
/// index remapped 0 -> 1, so `$b` reads `__memory_base` (1000) -> 1100.
#[test]
fn test_338_multimodule_const_first_embedded_globalget_remaps() {
    const OTHER: i32 = 5000; // __stack_pointer sentinel, != BASE

    let component_a = build_component_stack_pointer();
    let component_b = build_component_membase_initializer();

    let mut fuser = Fuser::new(FuserConfig::default());
    fuser
        .add_component_named(&component_a, Some("comp-a"))
        .unwrap();
    fuser
        .add_component_named(&component_b, Some("comp-b"))
        .unwrap();
    let fused = fuser.fuse().unwrap();

    // Confirm the setup actually shifts __memory_base off import index 0 —
    // otherwise the regression could not manifest.
    let engine = Engine::default();
    let module = RuntimeModule::new(&engine, &fused).expect("fused validates");
    let membase_pos = module
        .imports()
        .position(|imp| imp.name() == "__memory_base")
        .expect("__memory_base is an import");
    assert_ne!(
        membase_pos, 0,
        "test precondition: __memory_base must NOT be at import index 0, \
         else the base-shift regression cannot trigger"
    );

    let (mut store, instance) = instantiate_by_name(&fused, BASE, OTHER);
    let get_b = instance
        .get_typed_func::<(), i32>(&mut store, "get_b")
        .unwrap();

    assert_eq!(
        get_b.call(&mut store, ()).unwrap(),
        BASE + 100,
        "const-first embedded global.get must remap $__memory_base to its \
         merged index (base+100=1100), not emit the un-remapped local index \
         that reads $__stack_pointer (5100) (#338)"
    );
}

/// Test 4 — DATA-SEGMENT offset with a CONST-FIRST embedded `global.get`
/// (`meld-core/src/segments.rs`).
///
/// An active data segment at offset `i32.const 100; global.get $base; i32.add`
/// (`$base = 1000`) must place its bytes at 1100. Pre-fix, the data path folded
/// `i32.const 100`, hit the embedded `global.get`, and `fold_extended_const_i32`
/// returned `Err`, which `parse_data_segments` propagated via `?` — making the
/// WHOLE fuse hard-fail (`fuser.fuse()` returned `Err`, rejecting valid input).
/// Post-fix the offset is preserved-and-remapped and the payload lands at 1100.
#[test]
fn test_338_data_segment_const_first_embedded_globalget() {
    const PAYLOAD: [u8; 4] = [0xCA, 0xFE, 0xBA, 0xBE];

    let mut imports = ImportSection::new();
    imports.import("env", "__memory_base", imported_base_global()); // global 0 = $base

    let mut exports = ExportSection::new();
    exports.export("mem", ExportKind::Memory, 0);

    // Const-first embedded offset: i32.const 100; global.get $base; i32.add → 1100.
    let ext_offset = ConstExpr::i32_const(100).with_global_get(0).with_i32_add();

    let mut data = DataSection::new();
    data.segment(DataSegment {
        mode: DataSegmentMode::Active {
            memory_index: 0,
            offset: &ext_offset,
        },
        data: PAYLOAD,
    });

    let mut module = Module::new();
    module
        .section(&imports)
        .section(&regular_memory_section())
        .section(&exports)
        .section(&data);

    // Pre-fix this returned Err (hard-fail on valid input); post-fix it fuses.
    let fused = fuse_single(module);
    let (mut store, instance) = instantiate(&fused, BASE);

    let mem = instance.get_memory(&mut store, "mem").expect("mem export");
    let data = mem.data(&store);
    assert_eq!(
        &data[1100..1104],
        &PAYLOAD,
        "const-first embedded global.get data offset must land at base+100=1100 (#338)"
    );
}
