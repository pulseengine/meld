//! Emitter-wide LS-A-7 safety test.
//!
//! Loss scenario LS-A-7 (safety/stpa/loss-scenarios.yaml) requires that every
//! `cabi_realloc` call emitted into a fused meld output is followed by a null
//! guard of the form:
//!
//! ```wat
//! call $cabi_realloc
//! i32.eqz
//! if
//!   unreachable
//! end
//! ```
//!
//! Without the guard, an allocator returning 0 (OOM) would cause the
//! transcode/copy loop to write into callee memory offset 0 (leg (b) of
//! LS-A-7).  Per-emitter PoC tests live in
//! `meld-core/src/adapter/fact.rs` (search for `ls_a_7_`); this integration
//! test is the cross-emitter safety gate: it fuses two components
//! programmatically, then parses every function body in the fused output and
//! fails if any `cabi_realloc` call lacks the null guard.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    Alias, CanonicalFunctionSection, CanonicalOption, CodeSection, Component,
    ComponentAliasSection, ComponentExportKind, ComponentExportSection, ComponentImportSection,
    ComponentTypeRef, ComponentTypeSection, ConstExpr, DataSection, DataSegment, DataSegmentMode,
    ExportKind, ExportSection, Function, FunctionSection, GlobalSection, GlobalType, ImportSection,
    InstanceSection, Instruction, MemorySection, MemoryType, Module, ModuleArg, ModuleSection,
    TypeSection,
};

// ---------------------------------------------------------------------------
// Component fixtures: string-passing caller and callee.
//
// Same shape as `tests/adapter_safety.rs::test_sr12_*`: fusion of these two
// components forces meld to emit at least one string-passing adapter, which
// in turn contains a `cabi_realloc` call in the callee's memory that must be
// guarded.  We re-declare (rather than import) the builders because each
// integration-test file is a separate crate.
// ---------------------------------------------------------------------------

/// Minimal bump-allocator `cabi_realloc(orig_ptr, orig_size, align, new_size)`.
fn emit_cabi_realloc(func: &mut Function, bump_global: u32) {
    func.instruction(&Instruction::GlobalGet(bump_global));
    func.instruction(&Instruction::GlobalGet(bump_global));
    func.instruction(&Instruction::LocalGet(3)); // new_size
    func.instruction(&Instruction::I32Add);
    func.instruction(&Instruction::GlobalSet(bump_global));
    func.instruction(&Instruction::End);
}

/// Callee P2 component: exports `process-string(s: string) -> u32`.
fn build_callee_string_component() -> Vec<u8> {
    let core_module = {
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
        types.ty().function(
            [wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            [wasm_encoder::ValType::I32],
        );

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
        {
            let mut f = Function::new([]);
            emit_cabi_realloc(&mut f, 0);
            code.function(&f);
        }
        {
            // process-string(ptr, len) -> sum of bytes.
            let mut f = Function::new(vec![(2, wasm_encoder::ValType::I32)]);
            f.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
            f.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::LocalGet(1));
            f.instruction(&Instruction::I32GeU);
            f.instruction(&Instruction::BrIf(1));
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
            f.instruction(&Instruction::LocalGet(3));
            f.instruction(&Instruction::I32Const(1));
            f.instruction(&Instruction::I32Add);
            f.instruction(&Instruction::LocalSet(3));
            f.instruction(&Instruction::Br(0));
            f.instruction(&Instruction::End);
            f.instruction(&Instruction::End);
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

/// Caller P2 component: imports `process-string` and calls it with "Hello".
fn build_caller_string_component() -> Vec<u8> {
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
            f.instruction(&Instruction::I32Const(0));
            f.instruction(&Instruction::I32Const(5));
            f.instruction(&Instruction::Call(0));
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
// Guard scanner
// ---------------------------------------------------------------------------

/// Window (in operators) following a `call $realloc` in which the null guard
/// must appear. The canonical helper emits 6 operators
/// (`LocalSet; LocalGet; I32Eqz; If; Unreachable; End`), so 8 is a safe upper
/// bound that also tolerates a stray `Drop` or benign reorder.
const GUARD_WINDOW: usize = 8;

/// Return the function indices in the fused module that correspond to
/// `cabi_realloc` (or `cabi_realloc$N`).  Covers both imported and exported
/// realloc funcs: the former is how a realloc appears if meld ever leaves a
/// realloc as an import; the latter is how meld's internal realloc_map
/// entries surface in the fused output (see `merger.rs` — realloc_map keys
/// are exported as `cabi_realloc` / `cabi_realloc$N`).
fn collect_realloc_indices(fused: &[u8]) -> std::collections::HashSet<u32> {
    use std::collections::HashSet;
    let mut out = HashSet::new();
    let mut import_func_count: u32 = 0;
    let parser = wasmparser::Parser::new(0);

    for payload in parser.parse_all(fused) {
        match payload {
            Ok(wasmparser::Payload::ImportSection(reader)) => {
                for imp in reader.into_imports().flatten() {
                    if matches!(
                        imp.ty,
                        wasmparser::TypeRef::Func(_) | wasmparser::TypeRef::FuncExact(_)
                    ) {
                        if imp.name.starts_with("cabi_realloc") {
                            out.insert(import_func_count);
                        }
                        import_func_count += 1;
                    }
                }
            }
            Ok(wasmparser::Payload::ExportSection(reader)) => {
                for exp in reader.into_iter().flatten() {
                    if matches!(
                        exp.kind,
                        wasmparser::ExternalKind::Func | wasmparser::ExternalKind::FuncExact
                    ) && exp.name.starts_with("cabi_realloc")
                    {
                        out.insert(exp.index);
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// An unguarded `cabi_realloc` call site.
#[derive(Debug)]
struct OffendingSite {
    /// Merged-space function index of the enclosing function.
    function_idx: u32,
    /// Byte offset (within the fused module) of the `call` instruction.
    byte_offset: usize,
    /// Target (realloc) function index.
    target: u32,
}

/// Walk every function body and return (unguarded sites, total realloc
/// call count).  An unguarded site is a `call` targeting a realloc-family
/// function that is not followed by an `i32.eqz; if; unreachable; end`
/// sequence within the next `GUARD_WINDOW` operators.
fn scan_fused(
    fused: &[u8],
    realloc_indices: &std::collections::HashSet<u32>,
) -> (Vec<OffendingSite>, usize) {
    let mut offenders = Vec::new();
    let mut total_realloc_calls = 0usize;
    let mut import_func_count: u32 = 0;
    let parser = wasmparser::Parser::new(0);

    // First pass: count function imports so we can emit absolute function
    // indices for the error report.
    for payload in parser.parse_all(fused) {
        if let Ok(wasmparser::Payload::ImportSection(reader)) = payload {
            for imp in reader.into_imports().flatten() {
                if matches!(
                    imp.ty,
                    wasmparser::TypeRef::Func(_) | wasmparser::TypeRef::FuncExact(_)
                ) {
                    import_func_count += 1;
                }
            }
        }
    }

    // Second pass: scan function bodies.
    let parser2 = wasmparser::Parser::new(0);
    let mut code_func_offset: u32 = 0;
    for payload in parser2.parse_all(fused) {
        if let Ok(wasmparser::Payload::CodeSectionEntry(body)) = payload {
            let function_idx = import_func_count + code_func_offset;
            code_func_offset += 1;

            let reader = match body.get_operators_reader() {
                Ok(r) => r,
                Err(_) => continue,
            };

            // Collect (operator, byte_offset) pairs so we can look N steps
            // ahead after spotting a realloc call.
            let mut ops: Vec<(wasmparser::Operator, usize)> = Vec::new();
            let mut reader = reader;
            loop {
                if reader.is_end_then_eof() {
                    break;
                }
                match reader.read_with_offset() {
                    Ok(pair) => ops.push(pair),
                    Err(_) => break,
                }
            }

            for (idx, (op, off)) in ops.iter().enumerate() {
                let target = match op {
                    wasmparser::Operator::Call { function_index } => *function_index,
                    _ => continue,
                };
                if !realloc_indices.contains(&target) {
                    continue;
                }
                total_realloc_calls += 1;
                if !has_null_guard(&ops, idx) {
                    offenders.push(OffendingSite {
                        function_idx,
                        byte_offset: *off,
                        target,
                    });
                }
            }
        }
    }
    (offenders, total_realloc_calls)
}

/// Return true iff within the next `GUARD_WINDOW` operators after position
/// `call_idx` (exclusive) the sequence `I32Eqz; If { .. }; Unreachable; End`
/// appears.  Other operators between the call and the I32Eqz (e.g. the
/// canonical `LocalSet; LocalGet` that plumbs the result into a local) are
/// allowed — only the contiguous 4-op trap pattern is required.
fn has_null_guard(ops: &[(wasmparser::Operator, usize)], call_idx: usize) -> bool {
    let start = call_idx + 1;
    let end = (start + GUARD_WINDOW).min(ops.len());
    if end < start + 4 {
        return false;
    }
    for i in start..=end.saturating_sub(4) {
        let is_eqz = matches!(ops[i].0, wasmparser::Operator::I32Eqz);
        let is_if = matches!(ops[i + 1].0, wasmparser::Operator::If { .. });
        let is_unreach = matches!(ops[i + 2].0, wasmparser::Operator::Unreachable);
        let is_end = matches!(ops[i + 3].0, wasmparser::Operator::End);
        if is_eqz && is_if && is_unreach && is_end {
            return true;
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Test
// ---------------------------------------------------------------------------

/// LS-A-7 (leg b) emitter-wide gate.
///
/// Fuse a string-passing pair of components (the same fixture used by
/// `tests/adapter_safety.rs::test_sr12_*`), then scan every function body
/// in the fused module. Every `call` targeting a `cabi_realloc`-family
/// function must be immediately followed by the
/// `i32.eqz; if; unreachable; end` null guard; otherwise the test fails and
/// reports every offending (function_idx, byte_offset) pair.
#[test]
fn ls_a_7_every_realloc_call_has_null_guard() {
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
        "LS-A-7 scan: {} bytes, {} funcs, {} adapters, {} imports resolved",
        stats.output_size, stats.total_functions, stats.adapter_functions, stats.imports_resolved,
    );

    // Fused output must validate — a malformed module would mask emitter
    // bugs behind parser errors.
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&fused)
        .expect("LS-A-7: fused output should validate");

    let realloc_indices = collect_realloc_indices(&fused);
    assert!(
        !realloc_indices.is_empty(),
        "LS-A-7: expected at least one cabi_realloc-family function in the \
         fused output; scan would be vacuous otherwise"
    );
    eprintln!(
        "LS-A-7: tracking {} cabi_realloc-family function indices: {:?}",
        realloc_indices.len(),
        {
            let mut v: Vec<_> = realloc_indices.iter().copied().collect();
            v.sort();
            v
        }
    );

    let (offenders, call_count) = scan_fused(&fused, &realloc_indices);
    eprintln!("LS-A-7: scanned {call_count} realloc call sites");
    assert!(
        call_count > 0,
        "LS-A-7: expected at least one cabi_realloc call site in the fused \
         output; an adapter that never calls realloc would make the guard \
         check vacuous"
    );

    if !offenders.is_empty() {
        let mut report = String::new();
        report.push_str(
            "LS-A-7: the following cabi_realloc calls are missing the \
             `i32.eqz; if; unreachable; end` null guard (leg (b)):\n",
        );
        for site in &offenders {
            report.push_str(&format!(
                "  - function_idx={} target_realloc={} byte_offset=0x{:x}\n",
                site.function_idx, site.target, site.byte_offset
            ));
        }
        panic!("{report}");
    }
}
