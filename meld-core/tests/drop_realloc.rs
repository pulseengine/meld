//! #298 (SR-50) — dropping the vestigial `cabi_realloc` allocator.
//!
//! After `meld fuse` fully internalises a component boundary (no cross-component
//! imports, no adapter sites) and every component lift is provably scalar, each
//! input's canonical-ABI `cabi_realloc` allocator is *vestigial*: it existed
//! only to marshal pointer-carrying values across the boundary fusion removed.
//! Because it is an **export**, downstream DCE cannot remove it, so the
//! allocator + its `memory.grow` survive — and that surviving `memory.grow`
//! hard-blocks the single-address-space MCU path (`--memory shared
//! --address-rebase`, which rejects `memory.grow`).
//!
//! When `Fuser::cabi_realloc_drop_provably_safe` holds AND we are on the
//! rebasing path, meld now:
//!   1. drops the `cabi_realloc*` exports (so loom can DCE the allocator), and
//!   2. defers the now-dead allocator's `memory.grow` to `unreachable` instead
//!      of hard-failing.
//!
//! The verdict is fail-safe: on a non-scalar lift, a non-core output, or any
//! adapter site it returns `false` and behaviour is byte-identical to before
//! (the export survives and the `memory.grow` still hard-errors under rebasing).
//! Over-dropping would silently corrupt marshalling, so every uncertainty keeps
//! the allocator.

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasm_encoder::{
    Alias, CanonicalFunctionSection, CanonicalOption, CodeSection, Component,
    ComponentAliasSection, ComponentExportKind, ComponentExportSection, ComponentImportSection,
    ComponentTypeRef, ComponentTypeSection, ConstExpr, ExportKind, ExportSection, Function,
    FunctionSection, GlobalSection, GlobalType, ImportSection, InstanceSection, Instruction,
    MemorySection, MemoryType, Module, ModuleArg, ModuleSection, TypeSection, ValType,
};

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// The kind of high-level lift the exported component function carries.
#[derive(Clone, Copy)]
enum Lift {
    /// `func() -> u32` — no pointers, so the allocator is provably vestigial.
    Scalar,
    /// `func(s: string) -> u32` — a pointer-carrying param, so the allocator is
    /// live (the canonical ABI needs it to lower the string) and the verdict
    /// must keep it.
    String,
}

/// A `cabi_realloc(orig, size, align, new_size) -> ptr` whose body contains a
/// `memory.grow` — the shape of a real wit-bindgen `dlmalloc → $sbrk →
/// memory.grow` allocator, and exactly what hard-blocks the rebasing path.
fn emit_growing_realloc(func: &mut Function) {
    func.instruction(&Instruction::I32Const(1));
    func.instruction(&Instruction::MemoryGrow(0));
    func.instruction(&Instruction::Drop);
    func.instruction(&Instruction::I32Const(0));
    func.instruction(&Instruction::End);
}

/// A single, self-contained component that exports `test:api/api` (a lift of
/// `compute`) and carries a growing `cabi_realloc`. Fusing it internalises
/// nothing and creates no adapter sites, so the allocator is vestigial exactly
/// when the lift is [`Lift::Scalar`].
fn build_component(lift: Lift) -> Vec<u8> {
    let core_module = {
        let mut types = TypeSection::new();
        // type 0: cabi_realloc (i32,i32,i32,i32) -> i32
        types.ty().function(
            [ValType::I32, ValType::I32, ValType::I32, ValType::I32],
            [ValType::I32],
        );
        // type 1: compute — core signature of the lift.
        match lift {
            // scalar `func() -> u32` flattens to core `() -> i32`
            Lift::Scalar => {
                types.ty().function([], [ValType::I32]);
            }
            // `func(s: string) -> u32` flattens to core `(ptr, len) -> i32`
            Lift::String => {
                types
                    .ty()
                    .function([ValType::I32, ValType::I32], [ValType::I32]);
            }
        }

        let mut functions = FunctionSection::new();
        functions.function(0); // func 0: cabi_realloc
        functions.function(1); // func 1: compute

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        let mut exports = ExportSection::new();
        exports.export("cabi_realloc", ExportKind::Func, 0);
        exports.export("compute", ExportKind::Func, 1);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();
        {
            let mut f = Function::new([]);
            emit_growing_realloc(&mut f);
            code.function(&f);
        }
        {
            // compute: ignore any args, return a constant. No direct memory
            // access, so the #326 path-F reloc gate never fires — the only
            // rebasing obstacle is the allocator's `memory.grow`.
            let mut f = Function::new([]);
            f.instruction(&Instruction::I32Const(7));
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        let mut module = Module::new();
        module
            .section(&types)
            .section(&functions)
            .section(&memory)
            .section(&exports)
            .section(&code);
        module
    };

    let mut component = Component::new();
    component.section(&ModuleSection(&core_module));

    {
        let mut types = ComponentTypeSection::new();
        match lift {
            Lift::Scalar => {
                let no_params: [(&str, wasm_encoder::ComponentValType); 0] = [];
                types.function().params(no_params).result(Some(
                    wasm_encoder::ComponentValType::Primitive(wasm_encoder::PrimitiveValType::U32),
                ));
            }
            Lift::String => {
                types
                    .function()
                    .params([(
                        "s",
                        wasm_encoder::ComponentValType::Primitive(
                            wasm_encoder::PrimitiveValType::String,
                        ),
                    )])
                    .result(Some(wasm_encoder::ComponentValType::Primitive(
                        wasm_encoder::PrimitiveValType::U32,
                    )));
            }
        }
        component.section(&types);
    }

    {
        let mut inst = InstanceSection::new();
        let no_args: Vec<(&str, ModuleArg)> = vec![];
        inst.instantiate(0, no_args);
        component.section(&inst);
    }

    for (kind, name) in [
        (ExportKind::Func, "cabi_realloc"),
        (ExportKind::Func, "compute"),
        (ExportKind::Memory, "memory"),
    ] {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind,
            name,
        });
        component.section(&aliases);
    }

    {
        let mut canon = CanonicalFunctionSection::new();
        // Aliased core func 1 == compute; lift it with the component type 0.
        canon.lift(
            1,
            0,
            [CanonicalOption::Memory(0), CanonicalOption::Realloc(0)],
        );
        component.section(&canon);
    }
    {
        let mut exp = ComponentExportSection::new();
        exp.export("test:api/api", ComponentExportKind::Func, 0, None);
        component.section(&exp);
    }

    component.finish()
}

/// A single scalar-lift component whose LIVE `compute` body itself contains a
/// `memory.grow` — modelling a scalar-interface component that allocates
/// internally (`Vec`/`String`/`Box` → `dlmalloc` → `memory.grow`) reachable
/// from a live export. The interface boundary is still scalar (so the #298
/// interface verdict holds), but the allocator is NOT dead: the grow is
/// reachable from `compute`, a live root. Under shared+rebase this must KEEP
/// `cabi_realloc` and hard-error on the grow — NOT fuse-`Ok`-then-trap.
fn build_scalar_component_with_live_grow() -> Vec<u8> {
    let core_module = {
        let mut types = TypeSection::new();
        // type 0: cabi_realloc (i32,i32,i32,i32) -> i32
        types.ty().function(
            [ValType::I32, ValType::I32, ValType::I32, ValType::I32],
            [ValType::I32],
        );
        // type 1: compute — scalar `func() -> u32` flattens to core `() -> i32`
        types.ty().function([], [ValType::I32]);

        let mut functions = FunctionSection::new();
        functions.function(0); // func 0: cabi_realloc
        functions.function(1); // func 1: compute

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        let mut exports = ExportSection::new();
        exports.export("cabi_realloc", ExportKind::Func, 0);
        exports.export("compute", ExportKind::Func, 1);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();
        {
            let mut f = Function::new([]);
            emit_growing_realloc(&mut f);
            code.function(&f);
        }
        {
            // compute: allocates internally — `i32.const 1; memory.grow 0;
            // drop; i32.const 7`. This grow is reachable from the LIVE
            // `compute` export, so the allocator is not dead.
            let mut f = Function::new([]);
            f.instruction(&Instruction::I32Const(1));
            f.instruction(&Instruction::MemoryGrow(0));
            f.instruction(&Instruction::Drop);
            f.instruction(&Instruction::I32Const(7));
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        let mut module = Module::new();
        module
            .section(&types)
            .section(&functions)
            .section(&memory)
            .section(&exports)
            .section(&code);
        module
    };

    let mut component = Component::new();
    component.section(&ModuleSection(&core_module));

    {
        let mut types = ComponentTypeSection::new();
        let no_params: [(&str, wasm_encoder::ComponentValType); 0] = [];
        types
            .function()
            .params(no_params)
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
        component.section(&types);
    }
    {
        let mut inst = InstanceSection::new();
        let no_args: Vec<(&str, ModuleArg)> = vec![];
        inst.instantiate(0, no_args);
        component.section(&inst);
    }
    for (kind, name) in [
        (ExportKind::Func, "cabi_realloc"),
        (ExportKind::Func, "compute"),
        (ExportKind::Memory, "memory"),
    ] {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind,
            name,
        });
        component.section(&aliases);
    }
    {
        let mut canon = CanonicalFunctionSection::new();
        canon.lift(
            1,
            0,
            [CanonicalOption::Memory(0), CanonicalOption::Realloc(0)],
        );
        component.section(&canon);
    }
    {
        let mut exp = ComponentExportSection::new();
        exp.export("test:api/api", ComponentExportKind::Func, 0, None);
        component.section(&exp);
    }

    component.finish()
}

/// A scalar-lift component identical in shape to [`build_component`]`(Scalar)`
/// but carrying an EXTRA core export `extra_name` (a legitimately-authored
/// export that merely looks realloc-adjacent). Used to prove the #298 drop's
/// name match is tight: only the merger's own `cabi_realloc` / `cabi_realloc$
/// <digits>` shapes are dropped; e.g. `cabi_realloc$notdigits` is preserved.
fn build_scalar_component_with_extra_export(extra_name: &str) -> Vec<u8> {
    let core_module = {
        let mut types = TypeSection::new();
        types.ty().function(
            [ValType::I32, ValType::I32, ValType::I32, ValType::I32],
            [ValType::I32],
        );
        types.ty().function([], [ValType::I32]);

        let mut functions = FunctionSection::new();
        functions.function(0); // func 0: cabi_realloc
        functions.function(1); // func 1: compute (also the extra export target)

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        let mut exports = ExportSection::new();
        exports.export("cabi_realloc", ExportKind::Func, 0);
        exports.export("compute", ExportKind::Func, 1);
        // The extra, legitimately-named export → func 1 (a grow-free body).
        exports.export(extra_name, ExportKind::Func, 1);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();
        {
            let mut f = Function::new([]);
            emit_growing_realloc(&mut f);
            code.function(&f);
        }
        {
            let mut f = Function::new([]);
            f.instruction(&Instruction::I32Const(7));
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        let mut module = Module::new();
        module
            .section(&types)
            .section(&functions)
            .section(&memory)
            .section(&exports)
            .section(&code);
        module
    };

    let mut component = Component::new();
    component.section(&ModuleSection(&core_module));

    {
        let mut types = ComponentTypeSection::new();
        let no_params: [(&str, wasm_encoder::ComponentValType); 0] = [];
        types
            .function()
            .params(no_params)
            .result(Some(wasm_encoder::ComponentValType::Primitive(
                wasm_encoder::PrimitiveValType::U32,
            )));
        component.section(&types);
    }
    {
        let mut inst = InstanceSection::new();
        let no_args: Vec<(&str, ModuleArg)> = vec![];
        inst.instantiate(0, no_args);
        component.section(&inst);
    }
    for (kind, name) in [
        (ExportKind::Func, "cabi_realloc"),
        (ExportKind::Func, "compute"),
        (ExportKind::Memory, "memory"),
    ] {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind,
            name,
        });
        component.section(&aliases);
    }
    {
        let mut canon = CanonicalFunctionSection::new();
        canon.lift(
            1,
            0,
            [CanonicalOption::Memory(0), CanonicalOption::Realloc(0)],
        );
        component.section(&canon);
    }
    {
        let mut exp = ComponentExportSection::new();
        exp.export("test:api/api", ComponentExportKind::Func, 0, None);
        component.section(&exp);
    }

    component.finish()
}

// --- Cross-component (adapter-site) fixtures --------------------------------
//
// A string-passing caller→callee pair (same shape as
// `tests/realloc_safety.rs`): fusing them internalises a string boundary and so
// forces meld to emit a real adapter — the resolver populates
// `graph.adapter_sites`, which flips the #298 verdict to `false`. Each carries
// a **growing** `cabi_realloc` so that, under rebasing, the kept (non-vestigial)
// allocator's `memory.grow` hard-errors — proving no grow-defer happened.

/// Callee P2 component: exports `process-string(s: string) -> u32`, with a
/// growing `cabi_realloc`.
fn build_callee_string_component() -> Vec<u8> {
    let core_module = {
        let mut types = TypeSection::new();
        types.ty().function(
            [ValType::I32, ValType::I32, ValType::I32, ValType::I32],
            [ValType::I32],
        );
        types
            .ty()
            .function([ValType::I32, ValType::I32], [ValType::I32]);

        let mut functions = FunctionSection::new();
        functions.function(0);
        functions.function(1);

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        let mut exports = ExportSection::new();
        exports.export("cabi_realloc", ExportKind::Func, 0);
        exports.export("test:api/api#process-string", ExportKind::Func, 1);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();
        {
            let mut f = Function::new([]);
            emit_growing_realloc(&mut f);
            code.function(&f);
        }
        {
            // process-string(ptr, len) -> 0. Body does no direct memory access,
            // so the only rebasing obstacle is the growing allocator above.
            let mut f = Function::new([]);
            f.instruction(&Instruction::I32Const(0));
            f.instruction(&Instruction::End);
            code.function(&f);
        }

        let mut module = Module::new();
        module
            .section(&types)
            .section(&functions)
            .section(&memory)
            .section(&exports)
            .section(&code);
        module
    };

    let mut component = Component::new();
    component.section(&ModuleSection(&core_module));

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
        let mut inst = InstanceSection::new();
        let no_args: Vec<(&str, ModuleArg)> = vec![];
        inst.instantiate(0, no_args);
        component.section(&inst);
    }

    for (kind, name) in [
        (ExportKind::Func, "cabi_realloc"),
        (ExportKind::Func, "test:api/api#process-string"),
        (ExportKind::Memory, "memory"),
    ] {
        let mut aliases = ComponentAliasSection::new();
        aliases.alias(Alias::CoreInstanceExport {
            instance: 0,
            kind,
            name,
        });
        component.section(&aliases);
    }

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
    {
        let mut exp = ComponentExportSection::new();
        exp.export("test:api/api", ComponentExportKind::Func, 0, None);
        component.section(&exp);
    }

    component.finish()
}

/// Caller P2 component: imports `process-string`, calls it with "Hello", with a
/// growing `cabi_realloc`.
fn build_caller_string_component() -> Vec<u8> {
    let core_module = {
        let mut types = TypeSection::new();
        types
            .ty()
            .function([ValType::I32, ValType::I32], [ValType::I32]);
        types.ty().function([], [ValType::I32]);
        types.ty().function(
            [ValType::I32, ValType::I32, ValType::I32, ValType::I32],
            [ValType::I32],
        );

        let mut imports = ImportSection::new();
        imports.import(
            "test:api/api",
            "process-string",
            wasm_encoder::EntityType::Function(0),
        );

        let mut functions = FunctionSection::new();
        functions.function(1);
        functions.function(2);

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
                val_type: ValType::I32,
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
            f.instruction(&Instruction::I32Const(0));
            f.instruction(&Instruction::I32Const(5));
            f.instruction(&Instruction::Call(0));
            f.instruction(&Instruction::End);
            code.function(&f);
        }
        {
            let mut f = Function::new([]);
            emit_growing_realloc(&mut f);
            code.function(&f);
        }

        let mut module = Module::new();
        module
            .section(&types)
            .section(&imports)
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
    component.section(&ModuleSection(&core_module));
    component.finish()
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Names of every exported **function** in a core-wasm module.
fn export_func_names(bytes: &[u8]) -> Vec<String> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let Ok(wasmparser::Payload::ExportSection(reader)) = payload {
            for exp in reader.into_iter().flatten() {
                if matches!(
                    exp.kind,
                    wasmparser::ExternalKind::Func | wasmparser::ExternalKind::FuncExact
                ) {
                    out.push(exp.name.to_string());
                }
            }
        }
    }
    out
}

fn has_realloc_export(bytes: &[u8]) -> bool {
    export_func_names(bytes)
        .iter()
        .any(|n| n == "cabi_realloc" || n.starts_with("cabi_realloc$"))
}

fn shared_rebase_config() -> FuserConfig {
    FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        attestation: false,
        reproducible: false,
        component_provenance: false,
        ..Default::default()
    }
}

// ---------------------------------------------------------------------------
// 1. Positive: scalar-only boundary → drop + defer
// ---------------------------------------------------------------------------

/// A single scalar-lift component with a growing `cabi_realloc`, fused under
/// `SharedMemory` + `address_rebasing`:
///   * the fuse returns `Ok` — the vestigial `memory.grow` was deferred to
///     `unreachable`, not a hard error; and
///   * the fused core exports NO `cabi_realloc*` — the allocator export was
///     dropped so loom can DCE it.
#[test]
fn scalar_boundary_drops_realloc_and_defers_grow() {
    let component = build_component(Lift::Scalar);

    let mut fuser = Fuser::new(shared_rebase_config());
    fuser
        .add_component_named(&component, Some("scalar-app"))
        .expect("component parses");

    let fused = fuser
        .fuse()
        .expect("scalar boundary must fuse under shared+rebase (grow deferred)");

    // Output must validate — a malformed module would mask the real behaviour.
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&fused)
        .expect("fused output must validate");

    assert!(
        !has_realloc_export(&fused),
        "vestigial cabi_realloc export must be dropped; exports = {:?}",
        export_func_names(&fused)
    );
}

// ---------------------------------------------------------------------------
// 2. Negative controls — the verdict's conservatism must hold
// ---------------------------------------------------------------------------

/// (a) A non-scalar (string) lift keeps the allocator live, so the verdict is
/// `false`: the `memory.grow` still hard-errors under rebasing (no defer).
#[test]
fn string_lift_keeps_realloc_and_hard_errors_on_grow() {
    let component = build_component(Lift::String);

    let mut fuser = Fuser::new(shared_rebase_config());
    fuser
        .add_component_named(&component, Some("string-app"))
        .expect("component parses");

    let err = fuser
        .fuse()
        .expect_err("a string lift must NOT allow the vestigial drop / grow-defer");
    assert!(
        err.to_string().contains("memory.grow"),
        "expected the memory.grow rebase rejection (verdict must stay false for a \
         non-scalar lift), got: {err}"
    );
}

/// (b) A P2-component output (`OutputFormat::Component`) aliases `cabi_realloc`
/// for `canon lower`, so the verdict is `false`: the grow still hard-errors.
#[test]
fn component_output_keeps_realloc_and_hard_errors_on_grow() {
    let component = build_component(Lift::Scalar);

    let mut config = shared_rebase_config();
    config.output_format = OutputFormat::Component;

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component, Some("scalar-app"))
        .expect("component parses");

    let err = fuser
        .fuse()
        .expect_err("a P2 wrap output must NOT allow the vestigial drop / grow-defer");
    assert!(
        err.to_string().contains("memory.grow"),
        "expected the memory.grow rebase rejection (verdict must stay false for a \
         non-core output), got: {err}"
    );
}

/// (c) A fuse WITH a cross-component adapter site keeps the allocator (an
/// adapter may marshal pointers), so the verdict is `false`: the grow still
/// hard-errors under rebasing.
#[test]
fn adapter_site_keeps_realloc_and_hard_errors_on_grow() {
    // First, confirm the fixture genuinely produces an adapter — otherwise the
    // shared+rebase assertion below would pass for the wrong reason. A
    // multi-memory fuse succeeds today; assert an adapter was emitted AND the
    // allocator export survives (verdict false ⟹ no drop).
    {
        let mut fuser = Fuser::new(FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            address_rebasing: false,
            attestation: false,
            reproducible: false,
            component_provenance: false,
            ..Default::default()
        });
        fuser
            .add_component_named(&build_callee_string_component(), Some("callee"))
            .expect("callee parses");
        fuser
            .add_component_named(&build_caller_string_component(), Some("caller"))
            .expect("caller parses");
        let (fused, stats) = fuser.fuse_with_stats().expect("multi-memory fuse succeeds");
        assert!(
            stats.adapter_functions >= 1,
            "fixture must emit at least one adapter (got {}) so the adapter-site \
             branch of the verdict is actually exercised",
            stats.adapter_functions
        );
        assert!(
            has_realloc_export(&fused),
            "with an adapter site present the allocator export must survive; \
             exports = {:?}",
            export_func_names(&fused)
        );
    }

    // Now the real control: under shared+rebase the kept allocator's
    // `memory.grow` must still hard-error (no defer engaged).
    let mut fuser = Fuser::new(shared_rebase_config());
    fuser
        .add_component_named(&build_callee_string_component(), Some("callee"))
        .expect("callee parses");
    fuser
        .add_component_named(&build_caller_string_component(), Some("caller"))
        .expect("caller parses");

    let err = fuser
        .fuse()
        .expect_err("an adapter-site fuse must NOT allow the vestigial drop / grow-defer");
    assert!(
        err.to_string().contains("memory.grow"),
        "expected the memory.grow rebase rejection (verdict must stay false when an \
         adapter site is present), got: {err}"
    );
}

/// (d) FINDING 1 — a scalar interface whose LIVE `compute` body allocates
/// internally (`memory.grow` reachable from a live export). The interface
/// verdict holds (scalar boundary), but the allocator is NOT dead, so the
/// drop/defer must NOT fire: under shared+rebase this must KEEP `cabi_realloc`
/// and hard-error on the grow — a clean compile error, never a fuse-`Ok` that
/// traps at runtime.
#[test]
fn live_internal_grow_keeps_realloc_and_hard_errors() {
    let component = build_scalar_component_with_live_grow();

    let mut fuser = Fuser::new(shared_rebase_config());
    fuser
        .add_component_named(&component, Some("scalar-live-grow"))
        .expect("component parses");

    let err = fuser.fuse().expect_err(
        "a scalar interface with a LIVE internal memory.grow must NOT drop/defer \
         (allocator is not dead) — it must hard-error, not fuse-Ok-then-trap",
    );
    assert!(
        err.to_string().contains("memory.grow"),
        "expected the memory.grow rebase rejection (allocator not dead ⟹ no defer), \
         got: {err}"
    );
}

// ---------------------------------------------------------------------------
// 3. Guard: a normal non-shared fuse is unchanged
// ---------------------------------------------------------------------------

/// A non-rebasing (multi-memory) fuse of the very same scalar component must be
/// byte-identical to today: the drop is gated on the rebasing path, so
/// `cabi_realloc` is preserved.
#[test]
fn non_shared_fuse_preserves_realloc() {
    let component = build_component(Lift::Scalar);

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        address_rebasing: false,
        attestation: false,
        reproducible: false,
        component_provenance: false,
        ..Default::default()
    };

    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component, Some("scalar-app"))
        .expect("component parses");

    let fused = fuser.fuse().expect("multi-memory fuse succeeds");
    assert!(
        has_realloc_export(&fused),
        "a non-shared fuse must preserve cabi_realloc; exports = {:?}",
        export_func_names(&fused)
    );
}

// ---------------------------------------------------------------------------
// 4. FINDING 2: the export-name match is tight
// ---------------------------------------------------------------------------

/// A legitimately-authored export `cabi_realloc$notdigits` (non-digit suffix)
/// is NOT one the merger mints, so the #298 drop must PRESERVE it even on the
/// drop path — while still dropping the real `cabi_realloc`. Fused under
/// shared+rebase (the drop path): `cabi_realloc` gone, `cabi_realloc$notdigits`
/// kept.
#[test]
fn tight_match_preserves_realloc_lookalike_export() {
    // The predicate itself: only the merger's own shapes are droppable.
    use meld_core::memory_probe::is_vestigial_realloc_export_name as droppable;
    assert!(droppable("cabi_realloc"));
    assert!(droppable("cabi_realloc$0"));
    assert!(droppable("cabi_realloc$12"));
    assert!(!droppable("cabi_realloc$notdigits"));
    assert!(!droppable("cabi_realloc$")); // empty suffix
    assert!(!droppable("cabi_realloc$1a")); // mixed suffix
    assert!(!droppable("cabi_realloc_extra"));

    let component = build_scalar_component_with_extra_export("cabi_realloc$notdigits");

    let mut fuser = Fuser::new(shared_rebase_config());
    fuser
        .add_component_named(&component, Some("lookalike-app"))
        .expect("component parses");

    let fused = fuser
        .fuse()
        .expect("scalar boundary must fuse under shared+rebase (grow deferred)");
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&fused)
        .expect("fused output must validate");

    let names = export_func_names(&fused);
    assert!(
        !names.iter().any(|n| n == "cabi_realloc"),
        "the real cabi_realloc must be dropped; exports = {names:?}"
    );
    assert!(
        names.iter().any(|n| n == "cabi_realloc$notdigits"),
        "the legitimately-named cabi_realloc$notdigits must be preserved; \
         exports = {names:?}"
    );
}
