//! Regression test for issue #97 (synthetic, no external fixture).
//!
//! The original symptom appeared in `file_ops_component.wasm`, whose core
//! module had two imports both named `now` but coming from different host
//! modules:
//!
//! ```wat
//! (import "wasi:clocks/wall-clock@0.2.0"      "now" (func (result i64 i32)))
//! (import "wasi:clocks/monotonic-clock@0.2.0" "now" (func (result i64)))
//! ```
//!
//! The merger's intra-component resolution lookup matched `ModuleResolution`
//! entries by `(component_idx, from_module, import_name)` only, so both `now`
//! callers were routed to whichever resolution sat first in the list. The
//! fused output then called a function returning `i64` where `(i64, i32)` was
//! expected (or vice versa), failing core-wasm validation.
//!
//! Rather than ship the 844K real-world fixture, we synthesise the minimal
//! pattern here: a single P2 component containing three core modules, where
//! the consumer module imports `now` from two different `import.module`s with
//! different signatures, wired through the `InstanceSection` to two separate
//! provider modules. This is exactly the topology that exposes the
//! disambiguation bug, but expressed in a few hundred bytes built with
//! `wasm-encoder` so CI can always exercise it.

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasm_encoder::{
    CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection, ImportSection,
    InstanceSection, Instruction, Module, ModuleArg, ModuleSection, TypeSection,
};

/// Host module name used for the wall-clock-style import; matches the shape
/// of the real fixture (`wasi:clocks/wall-clock@0.2.0`) but the exact text
/// doesn't matter — only that it differs from the monotonic-clock name AND
/// matches a key in the consumer's `InstanceSection` arg map.
const WALL_MODULE: &str = "wasi:clocks/wall-clock@0.2.0";
const MONO_MODULE: &str = "wasi:clocks/monotonic-clock@0.2.0";

/// Build a core module that exports `now` with signature `() -> (i64, i32)`,
/// emulating the wall-clock `datetime` return.
fn build_wall_clock_module() -> Module {
    let mut types = TypeSection::new();
    types
        .ty()
        .function([], [wasm_encoder::ValType::I64, wasm_encoder::ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0);

    let mut exports = ExportSection::new();
    exports.export("now", ExportKind::Func, 0);

    let mut code = CodeSection::new();
    {
        let mut f = Function::new([]);
        f.instruction(&Instruction::I64Const(0));
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&exports)
        .section(&code);
    module
}

/// Build a core module that exports `now` with signature `() -> i64`,
/// emulating the monotonic-clock nanoseconds return.
fn build_monotonic_clock_module() -> Module {
    let mut types = TypeSection::new();
    types.ty().function([], [wasm_encoder::ValType::I64]);

    let mut functions = FunctionSection::new();
    functions.function(0);

    let mut exports = ExportSection::new();
    exports.export("now", ExportKind::Func, 0);

    let mut code = CodeSection::new();
    {
        let mut f = Function::new([]);
        f.instruction(&Instruction::I64Const(0));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&exports)
        .section(&code);
    module
}

/// Build the consumer core module: imports `now` from two different host
/// modules with two different signatures, then exports a `run` function
/// that calls each import in turn. The call sites' expected stack types
/// MUST match the imports' actual signatures — if the merger mis-routes,
/// validation will reject the fused module.
fn build_consumer_module() -> Module {
    let mut types = TypeSection::new();
    // type 0: () -> (i64, i32)  (wall-clock now)
    types
        .ty()
        .function([], [wasm_encoder::ValType::I64, wasm_encoder::ValType::I32]);
    // type 1: () -> i64         (monotonic-clock now)
    types.ty().function([], [wasm_encoder::ValType::I64]);
    // type 2: () -> ()          (run)
    types.ty().function([], []);

    let mut imports = ImportSection::new();
    // Both imports share the field name `now`, differing only in `module`.
    imports.import(WALL_MODULE, "now", wasm_encoder::EntityType::Function(0));
    imports.import(MONO_MODULE, "now", wasm_encoder::EntityType::Function(1));

    let mut functions = FunctionSection::new();
    functions.function(2); // `run`

    let mut exports = ExportSection::new();
    exports.export("run", ExportKind::Func, 2); // 0,1 are imports

    let mut code = CodeSection::new();
    {
        let mut f = Function::new([]);
        // call wall-clock `now` (import 0): pushes (i64, i32), drop both.
        f.instruction(&Instruction::Call(0));
        f.instruction(&Instruction::Drop); // drop i32
        f.instruction(&Instruction::Drop); // drop i64
        // call monotonic-clock `now` (import 1): pushes i64, drop it.
        f.instruction(&Instruction::Call(1));
        f.instruction(&Instruction::Drop);
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

/// Build a P2 component containing the wall-clock provider, the monotonic-
/// clock provider, and the consumer, wired together via the core
/// `InstanceSection` so that `WALL_MODULE` and `MONO_MODULE` resolve to
/// distinct provider instances. This produces two `ModuleResolution`s with
/// the same `import_name = "now"` but different `from_import_module`s — the
/// exact case that triggered issue #97.
fn build_collision_component() -> Vec<u8> {
    let wall = build_wall_clock_module();
    let mono = build_monotonic_clock_module();
    let consumer = build_consumer_module();

    let mut component = Component::new();

    // Module index 0: wall provider.
    component.section(&ModuleSection(&wall));
    // Module index 1: monotonic provider.
    component.section(&ModuleSection(&mono));
    // Module index 2: consumer.
    component.section(&ModuleSection(&consumer));

    // Instance section:
    //   instance 0 = instantiate module 0 (wall)   with no args
    //   instance 1 = instantiate module 1 (mono)   with no args
    //   instance 2 = instantiate module 2 (consumer) with
    //                  WALL_MODULE = instance 0, MONO_MODULE = instance 1
    let mut inst = InstanceSection::new();
    let no_args: Vec<(&str, ModuleArg)> = vec![];
    inst.instantiate(0, no_args.clone());
    inst.instantiate(1, no_args);
    inst.instantiate(
        2,
        vec![
            (WALL_MODULE, ModuleArg::Instance(0)),
            (MONO_MODULE, ModuleArg::Instance(1)),
        ],
    );
    component.section(&inst);

    component.finish()
}

/// Issue #97 regression: fuse a single P2 component whose consumer core
/// module imports two functions sharing the field name `now` from two
/// different `import.module`s with different signatures, and assert the
/// fused output validates. Before the fix in commit
/// `fix: disambiguate intra-component import resolution by module+name`,
/// the merger routed both `now` callers to whichever `ModuleResolution`
/// happened to come first, producing a fused module that called e.g. a
/// `() -> i64` provider where `() -> (i64, i32)` was expected. Validation
/// catches that as a stack-type mismatch.
#[test]
fn file_ops_fuses_and_validates() {
    let component_bytes = build_collision_component();

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        output_format: OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component_bytes, Some("issue-97-collision"))
        .expect("add_component");
    let fused = fuser.fuse().expect("fuse");

    // Validate using the same feature set the meld CLI enables for
    // `--validate`. Multi-memory must be on for the multi-memory strategy.
    let mut features = wasmparser::WasmFeatures::default();
    features.set(wasmparser::WasmFeatures::MULTI_MEMORY, true);
    let mut validator = wasmparser::Validator::new_with_features(features);
    validator
        .validate_all(&fused)
        .expect("fused module must validate (issue #97 regression)");
}
