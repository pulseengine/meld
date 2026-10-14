//! #462: a function import that no resolution step mapped must never fall
//! back to the identity function index.
//!
//! The synthetic module is the smallest shape that reaches the merger with an
//! import nothing maps: the graph carries no `unresolved_imports`, no adapter
//! site, and no module resolution for it. (In the wild this is the
//! wit-component fixup module's `"" "0"` imports; see
//! `tests/unmapped_import_stubs_462.rs` for the real inputs.)

use super::*;
use wasm_encoder::{
    CodeSection, Component, ConstExpr, ElementSection, Elements, ExportKind as EK, ExportSection,
    Function, FunctionSection, ImportSection, Instruction, MemorySection, MemoryType as WMem,
    Module, RefType, TableSection, TableType, TypeSection,
};

/// What references the unmapped import `"" "1"` (function index 1) besides the
/// `elem` slot every variant has.
#[derive(Clone, Copy, PartialEq)]
enum Use {
    /// Nothing else: the dead, wit-component shape.
    Nothing,
    /// A `call 1` in a defined function.
    Call,
    /// A `ref.func 1` in a defined function.
    RefFunc,
    /// A function export of the import itself.
    Export,
    /// A global initialiser `ref.func 1`.
    GlobalInit,
}

/// A core module importing `"" "0"` and `"" "1"` (type `() -> ()`), defining
/// one function that calls import 1 when `live_call`, and filling table 0 slot 0
/// with import 1.
fn module_with_unmapped_import(use_: Use) -> Vec<u8> {
    let mut types = TypeSection::new();
    types.ty().function([], []);
    let mut imports = ImportSection::new();
    imports.import("", "0", wasm_encoder::EntityType::Function(0));
    imports.import("", "1", wasm_encoder::EntityType::Function(0));
    let mut funcs = FunctionSection::new();
    funcs.function(0);
    let mut tables = TableSection::new();
    tables.table(TableType {
        element_type: RefType::FUNCREF,
        minimum: 1,
        maximum: Some(1),
        table64: false,
        shared: false,
    });
    let mut mems = MemorySection::new();
    mems.memory(WMem {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    let mut exports = ExportSection::new();
    exports.export("run", EK::Func, 2);
    if use_ == Use::Export {
        exports.export("re-exported", EK::Func, 1);
    }
    let mut globals = wasm_encoder::GlobalSection::new();
    if use_ == Use::GlobalInit {
        globals.global(
            wasm_encoder::GlobalType {
                val_type: wasm_encoder::ValType::Ref(RefType::FUNCREF),
                mutable: false,
                shared: false,
            },
            &ConstExpr::ref_func(1),
        );
    }
    let mut elems = ElementSection::new();
    elems.active(
        Some(0),
        &ConstExpr::i32_const(0),
        Elements::Functions(std::borrow::Cow::Borrowed(&[1])),
    );
    let mut code = CodeSection::new();
    let mut f = Function::new([]);
    match use_ {
        Use::Call => {
            f.instruction(&Instruction::Call(1));
        }
        Use::RefFunc => {
            f.instruction(&Instruction::RefFunc(1));
            f.instruction(&Instruction::Drop);
        }
        _ => {}
    }
    f.instruction(&Instruction::End);
    code.function(&f);

    let mut m = Module::new();
    m.section(&types)
        .section(&imports)
        .section(&funcs)
        .section(&tables)
        .section(&mems)
        .section(&globals)
        .section(&exports)
        .section(&elems)
        .section(&code);
    m.finish()
}

fn merge_synthetic(use_: Use) -> Result<MergedModule> {
    let core = module_with_unmapped_import(use_);
    let mut comp = Component::new();
    comp.section(&wasm_encoder::RawSection {
        id: 1, // core module section
        data: &core,
    });
    let component = crate::ComponentParser::new()
        .parse(&comp.finish())
        .expect("synthetic component must parse");
    let graph = crate::resolver::DependencyGraph {
        instantiation_order: vec![0],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        unresolved_imports: Vec::new(),
    };
    Merger::new(MemoryStrategy::MultiMemory, false).merge(&[component], &graph)
}

/// Negative control and the positive case in one: the same module, differing
/// only in whether anything LIVE names the unmapped import. The dead `elem`
/// reference fuses and holds a trapping stub; the live `call` is an error.
#[test]
fn a_dead_elem_reference_is_stubbed() {
    let merged = merge_synthetic(Use::Nothing).expect("an elem-only reference must fuse");
    let stub = *merged
        .unmapped_import_stubs
        .get(&(0, 0, 1))
        .expect("the unmapped import named by the elem must get a stub");
    let f = merged
        .defined_func(stub)
        .expect("stub is a defined function");
    assert_eq!(f.synthetic_kind, Some(SyntheticKind::TrapStub));
    assert_eq!(merged.elements.len(), 1);
    match &merged.elements[0].items {
        crate::segments::ReindexedElementItems::Functions(fs) => {
            // The import is function 1 and the stub is function 0, so an identity
            // fallback (1) cannot pass for the stub.
            assert_ne!(stub, 1);
            assert_eq!(fs, &vec![stub], "the slot must hold the stub, not index 1");
        }
        other => panic!("unexpected items {other:?}"),
    }
}

/// Every LIVE way of naming an unmapped import is an error that names the
/// component, the import and the use. The dead-`elem` case above is the
/// negative control: the same module minus the one extra reference fuses.
#[test]
fn every_live_use_of_an_unmapped_import_is_an_error() {
    for (use_, expect_in_msg) in [
        (Use::Call, "call"),
        (Use::RefFunc, "ref.func"),
        (Use::Export, "function export"),
        (Use::GlobalInit, "global initialiser"),
    ] {
        let err = merge_synthetic(use_).expect_err("a live use must not fuse via identity");
        let msg = err.to_string();
        assert!(
            matches!(err, Error::UnmappedFunctionImport { .. }),
            "wrong error for {expect_in_msg}: {msg}"
        );
        assert!(
            msg.contains("component 0") && msg.contains("::1") && msg.contains(expect_in_msg),
            "the message must name the component, the import and the use \
             ({expect_in_msg}): {msg}"
        );
    }
}
