//! #334 (SR-49) — MCU-dissolve fixups on the `--memory shared` path.
//!
//! Exercises the two fused fixups that unblock the downstream
//! `synth --native-pointer-abi --shadow-stack-size` dissolve:
//!   1. coalescing the N per-provider `__stack_pointer` globals into one
//!      shared shadow stack, and
//!   2. dropping the vestigial lowered-import trampoline's keep-alive export.
//!
//! The fixtures are hand-built `MergedModule`s (mirroring how
//! `tests/rebasing_end_to_end.rs` constructs modules with `wasm-encoder`),
//! plus minimal `ParsedComponent`s carrying the `name`-section global-name
//! subsection the primary detector reads. Assertions re-parse the transformed
//! output; the runtime test additionally runs the coalesced module in
//! wasmtime to prove the two providers' shadow stacks no longer alias.

use std::collections::{BTreeMap, HashMap};

use meld_core::mcu_dissolve::dissolve_fixups;
use meld_core::merger::{
    ImportCounts, MergedExport, MergedFuncType, MergedFunction, MergedGlobal, MergedModule,
    SyntheticKind,
};
use meld_core::parser::{self, CoreModule, ParsedComponent};
use meld_core::segments::{ElementSegmentMode, ReindexedElementItems, ReindexedElementSegment};

use wasm_encoder::{
    ConstExpr, ExportKind, Function, GlobalType as EncGlobalType, MemArg, RefType, ValType,
};

// ---------------------------------------------------------------------------
// Small binary-encoding helpers
// ---------------------------------------------------------------------------

fn uleb128(mut v: u64) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(byte);
            break;
        }
        out.push(byte | 0x80);
    }
    out
}

fn sleb128(mut v: i64) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        let sign = byte & 0x40 != 0;
        if (v == 0 && !sign) || (v == -1 && sign) {
            out.push(byte);
            break;
        }
        out.push(byte | 0x80);
    }
    out
}

/// `i32.const V` init-expr bytes WITHOUT the trailing `end` — the form
/// `parser::GlobalType::init_expr_bytes` stores.
fn i32_const_init(v: i32) -> Vec<u8> {
    let mut b = vec![0x41u8];
    b.extend(sleb128(v as i64));
    b
}

/// A `name` section payload (subsection stream) with a global-name
/// subsection (id 7) naming the given absolute global indices.
fn global_name_section(names: &[(u32, &str)]) -> Vec<u8> {
    let mut sub = uleb128(names.len() as u64);
    for (idx, name) in names {
        sub.extend(uleb128(*idx as u64));
        sub.extend(uleb128(name.len() as u64));
        sub.extend(name.as_bytes());
    }
    let mut payload = vec![0x07u8];
    payload.extend(uleb128(sub.len() as u64));
    payload.extend(sub);
    payload
}

// ---------------------------------------------------------------------------
// Fixture builders
// ---------------------------------------------------------------------------

fn merged_base() -> MergedModule {
    MergedModule {
        types: Vec::new(),
        imports: Vec::new(),
        functions: Vec::new(),
        tables: Vec::new(),
        memories: Vec::new(),
        globals: Vec::new(),
        defined_global_i32_const: std::collections::HashMap::new(),
        exports: Vec::new(),
        start_function: None,
        elements: Vec::new(),
        data_segments: Vec::new(),
        custom_sections: Vec::new(),
        fused_function_names: BTreeMap::new(),
        function_index_map: HashMap::new(),
        memory_index_map: HashMap::new(),
        table_index_map: HashMap::new(),
        global_index_map: HashMap::new(),
        type_index_map: HashMap::new(),
        realloc_map: HashMap::new(),
        import_counts: ImportCounts {
            func: 0,
            table: 0,
            memory: 0,
            global: 0,
        },
        import_memory_indices: Vec::new(),
        import_realloc_indices: Vec::new(),
        import_lower_sites: Vec::new(),
        resource_rep_by_component: HashMap::new(),
        resource_new_by_component: HashMap::new(),
        handle_tables: HashMap::new(),
        task_return_shims: HashMap::new(),
        async_result_globals: HashMap::new(),
        rewrite_params: HashMap::new(),
        unmapped_import_stubs: HashMap::new(),
        pending_wired_imports: std::collections::HashSet::new(),
        shared_stack_top: None,
        stackless_providers: 0,
        placements: Vec::new(),
    }
}

fn mut_i32_global(init: i32) -> MergedGlobal {
    MergedGlobal {
        ty: EncGlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        init_expr: ConstExpr::i32_const(init),
        init_ref_func: None,
        init_ref_origin: None,
    }
}

fn merged_func(type_idx: u32, body: Function) -> MergedFunction {
    MergedFunction {
        type_idx,
        body,
        origin: (0, 0, 0),
        synthetic_kind: None,
    }
}

fn parser_global(init: i32) -> parser::GlobalType {
    parser::GlobalType {
        content_type: ValType::I32,
        mutable: true,
        init_expr_bytes: i32_const_init(init),
    }
}

/// A one-module component whose defined globals are `globals`, optionally with
/// a `name` section naming some of them.
fn component_with_globals(
    globals: Vec<parser::GlobalType>,
    names: &[(u32, &str)],
) -> ParsedComponent {
    let mut m = CoreModule {
        index: 0,
        bytes: Vec::new(),
        types: Vec::new(),
        imports: Vec::new(),
        exports: Vec::new(),
        functions: Vec::new(),
        memories: Vec::new(),
        tables: Vec::new(),
        globals,
        start: None,
        data_count: None,
        element_count: 0,
        custom_sections: Vec::new(),
        code_section_range: None,
        global_section_range: None,
        element_section_range: None,
        data_section_range: None,
    };
    if !names.is_empty() {
        m.custom_sections
            .push(("name".to_string(), global_name_section(names)));
    }
    let mut c = ParsedComponent::empty();
    c.core_modules.push(m);
    c
}

// ---------------------------------------------------------------------------
// Re-encode a MergedModule to a runnable core module (subset the tests need).
// ---------------------------------------------------------------------------

fn encode_core(m: &MergedModule) -> Vec<u8> {
    use wasm_encoder::{
        CodeSection, ElementSection, ExportSection, FunctionSection, GlobalSection, MemorySection,
        Module, TableSection, TypeSection,
    };
    let mut module = Module::new();

    let mut types = TypeSection::new();
    for t in &m.types {
        types
            .ty()
            .function(t.params.iter().copied(), t.results.iter().copied());
    }
    module.section(&types);

    let mut funcs = FunctionSection::new();
    for f in &m.functions {
        funcs.function(f.type_idx);
    }
    module.section(&funcs);

    if !m.tables.is_empty() {
        let mut tables = TableSection::new();
        for t in &m.tables {
            tables.table(*t);
        }
        module.section(&tables);
    }

    if !m.memories.is_empty() {
        let mut mems = MemorySection::new();
        for mem in &m.memories {
            mems.memory(*mem);
        }
        module.section(&mems);
    }

    let mut globals = GlobalSection::new();
    for g in &m.globals {
        globals.global(g.ty, &g.init_expr);
    }
    module.section(&globals);

    let mut exports = ExportSection::new();
    for e in &m.exports {
        exports.export(&e.name, e.kind, e.index);
    }
    module.section(&exports);

    if !m.elements.is_empty() {
        let mut elems = ElementSection::new();
        for seg in &m.elements {
            meld_core::segments::encode_element_segment(&mut elems, seg);
        }
        module.section(&elems);
    }

    let mut code = CodeSection::new();
    for f in &m.functions {
        code.function(&f.body);
    }
    module.section(&code);

    module.finish()
}

/// Read `(mutable, i32, init_value)` triples for a module's globals.
fn parse_globals(bytes: &[u8]) -> Vec<(bool, bool, Option<i32>)> {
    let mut out = Vec::new();
    let parser = wasmparser::Parser::new(0);
    for payload in parser.parse_all(bytes) {
        if let wasmparser::Payload::GlobalSection(reader) = payload.unwrap() {
            for g in reader {
                let g = g.unwrap();
                let is_i32 = matches!(g.ty.content_type, wasmparser::ValType::I32);
                let mut init = None;
                for op in g.init_expr.get_operators_reader() {
                    if let Ok(wasmparser::Operator::I32Const { value }) = op {
                        init = Some(value);
                    }
                }
                out.push((g.ty.mutable, is_i32, init));
            }
        }
    }
    out
}

/// Read the operator stream of function body `func_idx` (defined-function
/// order) from an encoded module.
fn parse_body_ops(bytes: &[u8], func_idx: usize) -> Vec<String> {
    let mut idx = 0usize;
    let mut ops = Vec::new();
    let parser = wasmparser::Parser::new(0);
    for payload in parser.parse_all(bytes) {
        if let wasmparser::Payload::CodeSectionEntry(body) = payload.unwrap() {
            if idx == func_idx {
                for op in body.get_operators_reader().unwrap() {
                    ops.push(format!("{:?}", op.unwrap()));
                }
            }
            idx += 1;
        }
    }
    ops
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// Part 1 structural: a fused 2-provider shared module ends with exactly one
/// SP-class global, coalesced duplicate refs point at the survivor, and a
/// surviving global above the dropped slot renumbers down.
#[test]
fn stack_pointer_globals_coalesced() {
    const SP_INIT: i32 = 1024;

    // Merged layout: [0]=SP(A), [1]=SP(B, dup), [2]=plain(42).
    let mut m = merged_base();
    m.globals = vec![
        mut_i32_global(SP_INIT),
        mut_i32_global(SP_INIT),
        mut_i32_global(42),
    ];

    // A single function touching global 1 (dup SP → survivor 0) and global 2
    // (plain → renumbers 2→1). Type () -> ().
    m.types = vec![MergedFuncType {
        params: vec![],
        results: vec![],
    }];
    let mut body = Function::new([]);
    body.instructions()
        .i32_const(5)
        .global_set(1) // set dup SP  -> expect global_set 0
        .global_get(2) // get plain   -> expect global_get 1
        .drop()
        .global_get(0) // get survivor SP -> stays 0
        .drop()
        .end();
    m.functions = vec![merged_func(0, body)];

    // global_index_map: comp0.g0 -> 0 (SP A), comp0.g1 -> 2 (plain),
    // comp1.g0 -> 1 (SP B).
    m.global_index_map.insert((0, 0, 0), 0);
    m.global_index_map.insert((0, 0, 1), 2);
    m.global_index_map.insert((1, 0, 0), 1);

    let comps = vec![
        component_with_globals(
            vec![parser_global(SP_INIT), parser_global(42)],
            &[(0, "__stack_pointer")],
        ),
        component_with_globals(vec![parser_global(SP_INIT)], &[(0, "__stack_pointer")]),
    ];

    let stats = dissolve_fixups(&mut m, &comps).unwrap();
    assert_eq!(
        stats.stack_pointers_coalesced, 1,
        "exactly one duplicate SP coalesced away"
    );

    // Re-encode and re-parse the output globals.
    let bytes = encode_core(&m);
    wasmparser::validate(&bytes).expect("coalesced module must validate");
    let globals = parse_globals(&bytes);
    assert_eq!(globals.len(), 2, "one SP duplicate dropped: 3 -> 2 globals");
    let sp_class = globals
        .iter()
        .filter(|(mutable, is_i32, init)| *mutable && *is_i32 && *init == Some(SP_INIT))
        .count();
    assert_eq!(sp_class, 1, "exactly one SP-class (init==sp_init) global");

    // Redirected + renumbered instructions.
    let ops = parse_body_ops(&bytes, 0);
    assert_eq!(
        ops,
        vec![
            "I32Const { value: 5 }",
            "GlobalSet { global_index: 0 }", // dup SP 1 -> survivor 0
            "GlobalGet { global_index: 1 }", // plain 2 -> renumbered 1
            "Drop",
            "GlobalGet { global_index: 0 }", // survivor unchanged
            "Drop",
            "End",
        ],
        "coalesced refs point at survivor and surviving global renumbers down",
    );
}

/// Part 1 behavioural: after coalescing, the two providers descend one shared
/// shadow stack, so a nested cross-provider call no longer clobbers the
/// caller's frame. The pre-transform module (two independent SPs) clobbers;
/// the coalesced module does not.
#[test]
fn shared_stack_pointer_runtime_non_clobber() {
    use wasmtime::{Engine, Instance, Module, Store};

    const SP_INIT: i32 = 1024;
    const MARK_A: i32 = 0xAA;
    const MARK_B: i32 = 0xBB;
    let memarg = MemArg {
        offset: 0,
        align: 2,
        memory_index: 0,
    };

    let mut m = merged_base();
    m.import_counts.memory = 0;
    m.memories = vec![wasm_encoder::MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    }];
    m.globals = vec![mut_i32_global(SP_INIT), mut_i32_global(SP_INIT)];
    m.types = vec![
        MergedFuncType {
            params: vec![],
            results: vec![ValType::I32],
        },
        MergedFuncType {
            params: vec![],
            results: vec![],
        },
    ];

    // Provider A (uses SP global 0): alloc a frame, stamp MARK_A, call B,
    // reload the stamp, free the frame, return the reloaded value.
    let mut a = Function::new([]);
    a.instructions()
        .global_get(0)
        .i32_const(16)
        .i32_sub()
        .global_set(0)
        .global_get(0)
        .i32_const(MARK_A)
        .i32_store(memarg)
        .call(1)
        .global_get(0)
        .i32_load(memarg)
        .global_get(0)
        .i32_const(16)
        .i32_add()
        .global_set(0)
        .end();

    // Provider B (uses SP global 1): alloc a frame, stamp MARK_B, free.
    let mut b = Function::new([]);
    b.instructions()
        .global_get(1)
        .i32_const(16)
        .i32_sub()
        .global_set(1)
        .global_get(1)
        .i32_const(MARK_B)
        .i32_store(memarg)
        .global_get(1)
        .i32_const(16)
        .i32_add()
        .global_set(1)
        .end();

    m.functions = vec![merged_func(0, a), merged_func(1, b)];
    m.exports.push(MergedExport {
        name: "run".to_string(),
        kind: ExportKind::Func,
        index: 0,
    });

    m.global_index_map.insert((0, 0, 0), 0);
    m.global_index_map.insert((1, 0, 0), 1);
    let comps = vec![
        component_with_globals(vec![parser_global(SP_INIT)], &[(0, "__stack_pointer")]),
        component_with_globals(vec![parser_global(SP_INIT)], &[(0, "__stack_pointer")]),
    ];

    // Pre-transform: two independent SPs both start at the top, so B clobbers
    // A's frame — A observes MARK_B (the hazard #334 fixes).
    let pre = encode_core(&m);
    wasmparser::validate(&pre).expect("pre module validates");
    let run = |bytes: &[u8]| -> i32 {
        let engine = Engine::default();
        let module = Module::new(&engine, bytes).unwrap();
        let mut store = Store::new(&engine, ());
        let inst = Instance::new(&mut store, &module, &[]).unwrap();
        let f = inst.get_typed_func::<(), i32>(&mut store, "run").unwrap();
        f.call(&mut store, ()).unwrap()
    };
    assert_eq!(
        run(&pre),
        MARK_B,
        "pre-fix: independent SPs alias, B clobbers A's frame"
    );

    // Coalesce and re-check: one shared SP, B allocates below A's frame, so
    // A's stamp survives.
    let stats = dissolve_fixups(&mut m, &comps).unwrap();
    assert_eq!(stats.stack_pointers_coalesced, 1);
    assert_eq!(m.globals.len(), 1, "single shared shadow-stack global");

    let post = encode_core(&m);
    wasmparser::validate(&post).expect("post module validates");
    assert_eq!(
        run(&post),
        MARK_A,
        "post-fix: shared SP, nested provider call no longer clobbers"
    );
}

/// Part 2: a dead lowered-import trampoline's numeric keep-alive export is
/// dropped, while real exports, vtable-backed trampolines, and non-trampoline
/// numeric exports are left alone.
///
/// NOTE (#462): this models the dead table as holding an IMPORTED function.
/// That is not the shape wit-component's fixup module produces after fusion;
/// see `dead_trampoline_over_trap_stub_table_is_dropped_with_its_table_export`
/// for the real one.
#[test]
fn dead_import_trampoline_export_dropped() {
    let mut m = merged_base();
    m.import_counts.func = 1; // one imported function at index 0

    // Types: t0 = () -> () (import + normal), t1 = (i32) -> () (mis-typed).
    m.types = vec![
        MergedFuncType {
            params: vec![],
            results: vec![],
        },
        MergedFuncType {
            params: vec![ValType::I32],
            results: vec![],
        },
    ];

    // Two funcref tables: table 0 = import table (holds imported func 0),
    // table 1 = ordinary vtable (holds defined func 2).
    m.tables = vec![
        wasm_encoder::TableType {
            element_type: RefType::FUNCREF,
            minimum: 1,
            maximum: Some(1),
            table64: false,
            shared: false,
        },
        wasm_encoder::TableType {
            element_type: RefType::FUNCREF,
            minimum: 1,
            maximum: Some(1),
            table64: false,
            shared: false,
        },
    ];
    m.elements = vec![
        ReindexedElementSegment {
            mode: ElementSegmentMode::Active {
                table_index: 0,
                offset: ConstExpr::i32_const(0),
            },
            element_type: RefType::FUNCREF,
            items: ReindexedElementItems::Functions(vec![0]), // imported func
        },
        ReindexedElementSegment {
            mode: ElementSegmentMode::Active {
                table_index: 1,
                offset: ConstExpr::i32_const(0),
            },
            element_type: RefType::FUNCREF,
            items: ReindexedElementItems::Functions(vec![2]), // defined func
        },
    ];

    // Defined function 1: the dead lowered-import trampoline over table 0.
    let mut tramp = Function::new([]);
    tramp
        .instructions()
        .i32_const(0)
        .call_indirect(0, 1) // table 0 (import table), type 1 (mis-typed)
        .end();
    // Defined function 2: a normal exported function.
    let mut normal = Function::new([]);
    normal.instructions().end();
    // Defined function 3: a trampoline, but over the vtable (table 1) — live.
    let mut vtramp = Function::new([]);
    vtramp
        .instructions()
        .i32_const(0)
        .call_indirect(1, 1) // table 1 (vtable), type 1
        .end();
    // Defined function 4: numeric-exported but NOT a bare trampoline.
    let mut not_tramp = Function::new([]);
    not_tramp
        .instructions()
        .i32_const(1)
        .i32_const(2)
        .i32_add()
        .drop()
        .end();

    m.functions = vec![
        merged_func(0, tramp),     // merged idx 1
        merged_func(0, normal),    // merged idx 2
        merged_func(1, vtramp),    // merged idx 3
        merged_func(0, not_tramp), // merged idx 4
    ];

    m.exports = vec![
        MergedExport {
            name: "0".to_string(), // dead trampoline keep-alive — DROP
            kind: ExportKind::Func,
            index: 1,
        },
        MergedExport {
            name: "greet".to_string(), // real export — keep
            kind: ExportKind::Func,
            index: 2,
        },
        MergedExport {
            name: "9".to_string(), // vtable trampoline — keep (live table)
            kind: ExportKind::Func,
            index: 3,
        },
        MergedExport {
            name: "7".to_string(), // numeric but not a trampoline — keep
            kind: ExportKind::Func,
            index: 4,
        },
    ];

    let stats = dissolve_fixups(&mut m, &[]).unwrap();
    assert_eq!(
        stats.trampoline_exports_dropped, 1,
        "only the dead one drops"
    );

    let names: Vec<&str> = m.exports.iter().map(|e| e.name.as_str()).collect();
    assert!(!names.contains(&"0"), "dead trampoline export dropped");
    assert!(names.contains(&"greet"), "real export preserved");
    assert!(names.contains(&"9"), "vtable-backed trampoline preserved");
    assert!(
        names.contains(&"7"),
        "non-trampoline numeric export preserved"
    );
}

/// #462: the REAL shape of the wit-component shim, which the test above does
/// not model. There the fixup module's slots held no imported function: the
/// fixup's `"" "N"` imports were unmapped, so the merger stands a trapping
/// stub in each slot. The table is therefore "all stubs", not "an imported
/// func", and before #462 the identity fallback made it look like a vtable
/// (the slot held an unrelated DEFINED function), so Part 2 kept the export.
///
/// Dropped here: the numeric trampoline Func exports over the stub table AND
/// the `"$imports"` Table export. Kept (each is a negative control, so a Part 2
/// that simply dropped everything numeric or everything named `$imports` fails):
/// a trampoline that is called, one over a table holding a real function, a
/// real export, and an `"$imports"` table that is not statically populated.
#[test]
fn dead_trampoline_over_trap_stub_table_is_dropped_with_its_table_export() {
    let mut m = merged_base();
    m.import_counts.func = 0; // the real shape: no imported functions at all

    // t0 = () -> (), t1 = (i32) -> ().
    m.types = vec![
        MergedFuncType {
            params: vec![],
            results: vec![],
        },
        MergedFuncType {
            params: vec![ValType::I32],
            results: vec![],
        },
    ];
    let funcref_table = || wasm_encoder::TableType {
        element_type: RefType::FUNCREF,
        minimum: 2,
        maximum: Some(2),
        table64: false,
        shared: false,
    };
    // table 0: stubs only (the dead `$imports`); table 1: a real function in
    // it (a vtable); table 2: no static segment (host-populated).
    m.tables = vec![funcref_table(), funcref_table(), funcref_table()];
    let seg = |table_index: u32, fs: Vec<u32>| ReindexedElementSegment {
        mode: ElementSegmentMode::Active {
            table_index,
            offset: ConstExpr::i32_const(0),
        },
        element_type: RefType::FUNCREF,
        items: ReindexedElementItems::Functions(fs),
    };
    m.elements = vec![seg(0, vec![0, 0]), seg(1, vec![0, 5])];

    let trampoline = |table: u32| {
        let mut f = Function::new([]);
        f.instructions().i32_const(0).call_indirect(table, 0).end();
        f
    };
    let stub = || {
        let mut f = Function::new([]);
        f.instructions().unreachable().end();
        MergedFunction {
            type_idx: 0,
            body: f,
            origin: (usize::MAX, usize::MAX, 0),
            synthetic_kind: Some(SyntheticKind::TrapStub),
        }
    };
    let mut caller = Function::new([]);
    caller.instructions().call(2).end(); // calls trampoline "3": it is LIVE
    let mut real = Function::new([]);
    real.instructions().end();

    m.functions = vec![
        stub(),                        // 0: trap stub
        merged_func(0, trampoline(0)), // 1: dead trampoline over the stub table
        merged_func(0, trampoline(0)), // 2: called trampoline over the stub table
        merged_func(0, caller),        // 3: the caller
        merged_func(0, trampoline(1)), // 4: trampoline over a vtable
        merged_func(0, real),          // 5: a real function (held by table 1)
    ];
    // trampoline "3" is function 2; it is referenced by `caller`.
    let export = |name: &str, kind: ExportKind, index: u32| MergedExport {
        name: name.to_string(),
        kind,
        index,
    };
    m.exports = vec![
        export("0", ExportKind::Func, 1),         // dead trampoline: DROP
        export("3", ExportKind::Func, 2),         // called: keep
        export("greet", ExportKind::Func, 3),     // real export: keep
        export("4", ExportKind::Func, 4),         // over a vtable: keep
        export("$imports", ExportKind::Table, 0), // stub-only table: DROP
    ];

    let stats = dissolve_fixups(&mut m, &[]).unwrap();
    let names: Vec<(&str, bool)> = m
        .exports
        .iter()
        .map(|e| (e.name.as_str(), matches!(e.kind, ExportKind::Table)))
        .collect();
    assert!(
        !names.contains(&("0", false)),
        "dead trampoline export dropped"
    );
    assert!(
        !names.contains(&("$imports", true)),
        "the stub-only `$imports` table export is dropped with it"
    );
    assert_eq!(stats.trampoline_exports_dropped, 2);
    for keep in ["3", "greet", "4"] {
        assert!(names.contains(&(keep, false)), "{keep} must be preserved");
    }
    // Only exports are removed, never the functions behind them.
    assert_eq!(m.functions.len(), 6, "no function is removed");

    // Negative controls for the table export: a vtable, and a table with no
    // static segment, both named `$imports`, are kept.
    for table in [1u32, 2u32] {
        let mut m2 = merged_base();
        m2.types = m.types.clone();
        m2.tables = vec![funcref_table(), funcref_table(), funcref_table()];
        m2.elements = vec![seg(0, vec![0, 0]), seg(1, vec![0, 5])];
        m2.functions = vec![
            stub(),
            merged_func(0, trampoline(0)),
            merged_func(0, Function::new([])),
        ];
        m2.functions[2] = merged_func(0, {
            let mut f = Function::new([]);
            f.instructions().end();
            f
        });
        // functions 3..5 so that table 1's real function index 5 exists.
        for _ in 3..6 {
            let mut f = Function::new([]);
            f.instructions().end();
            m2.functions.push(merged_func(0, f));
        }
        m2.exports = vec![export("$imports", ExportKind::Table, table)];
        let stats2 = dissolve_fixups(&mut m2, &[]).unwrap();
        assert_eq!(stats2.trampoline_exports_dropped, 0);
        assert_eq!(m2.exports.len(), 1, "table {table} export must be kept");
    }
}

/// Guard: a single-SP shared module (nothing to coalesce) and a two-SP module
/// with DIFFERING inits (conservative equal-init rule) are both left
/// completely unchanged.
#[test]
fn conservative_no_coalesce_when_unsure() {
    // (a) single SP + one plain global: nothing to coalesce.
    let mut m = merged_base();
    m.globals = vec![mut_i32_global(1024), mut_i32_global(42)];
    m.global_index_map.insert((0, 0, 0), 0);
    m.global_index_map.insert((0, 0, 1), 1);
    let comps = vec![component_with_globals(
        vec![parser_global(1024), parser_global(42)],
        &[(0, "__stack_pointer")],
    )];
    let stats = dissolve_fixups(&mut m, &comps).unwrap();
    assert_eq!(stats.stack_pointers_coalesced, 0);
    assert_eq!(m.globals.len(), 2, "single SP: globals untouched");
    assert_eq!(stats.trampoline_exports_dropped, 0);

    // (b) two named SPs but DIFFERENT inits: must not fuse across partitions.
    let mut m = merged_base();
    m.globals = vec![mut_i32_global(1024), mut_i32_global(2048)];
    m.global_index_map.insert((0, 0, 0), 0);
    m.global_index_map.insert((1, 0, 0), 1);
    let comps = vec![
        component_with_globals(vec![parser_global(1024)], &[(0, "__stack_pointer")]),
        component_with_globals(vec![parser_global(2048)], &[(0, "__stack_pointer")]),
    ];
    let stats = dissolve_fixups(&mut m, &comps).unwrap();
    assert_eq!(
        stats.stack_pointers_coalesced, 0,
        "differing SP inits are not coalesced"
    );
    assert_eq!(m.globals.len(), 2);

    // (c) two UNNAMED mutable-i32 globals sharing an init (no `name` section
    // marking either `__stack_pointer`): must NOT coalesce (Mythos #334 review —
    // an init-value guess would fuse two unrelated globals and clobber one
    // component's writes). Absent the authoritative name, we never guess.
    let mut m = merged_base();
    m.globals = vec![mut_i32_global(1024), mut_i32_global(1024)];
    m.global_index_map.insert((0, 0, 0), 0);
    m.global_index_map.insert((1, 0, 0), 1);
    let comps = vec![
        component_with_globals(vec![parser_global(1024)], &[]),
        component_with_globals(vec![parser_global(1024)], &[]),
    ];
    let stats = dissolve_fixups(&mut m, &comps).unwrap();
    assert_eq!(
        stats.stack_pointers_coalesced, 0,
        "unnamed same-init globals are not coalesced (no init-value guessing)"
    );
    assert_eq!(m.globals.len(), 2, "unnamed globals untouched");
}
