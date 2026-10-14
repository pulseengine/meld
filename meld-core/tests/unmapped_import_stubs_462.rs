//! #462: a fixup-module import that no resolution step maps must never fall
//! back to the identity function index.
//!
//! wit-component emits, for a component with lowered imports, a shim module
//! whose trampolines `"0"`, `"1"`, ... `call_indirect` through a table exported
//! as `"$imports"`, plus a fixup module that imports the `canon lower`ed
//! functions as `"" "0"`, `"" "1"`, ... and fills that table with them. When
//! the merger left such an import unmapped, the element slot silently held
//! whatever fused function had that index NUMBER: 126 slots across the corpus,
//! 21 of them with a matching signature, so a host calling the (exported)
//! trampoline would have run an unrelated import.
//!
//! These tests assert structure, not a golden output: no element slot may name
//! a function that is neither a trapping stub nor one the slot was meant to
//! hold, a stub has the type of the trampoline that reads its slot, and the
//! dead scaffolding exports are gone under `--memory shared`. The synthetic
//! hard-error cases (a LIVE use of an unmapped import) live beside the merger
//! in `src/merger/tests_unmapped_462.rs`; the Part 2 export-drop cases live in
//! `tests/mcu_dissolve.rs`.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use std::path::Path;
use wasmparser::{ElementItems, ElementKind, Operator, Parser, Payload, ValType};

fn read(rel: &str) -> Vec<u8> {
    let p = Path::new(env!("CARGO_MANIFEST_DIR")).join(rel);
    std::fs::read(&p).unwrap_or_else(|e| panic!("fixture {}: {e}", p.display()))
}

/// One populated slot of a funcref table.
#[derive(Debug, Clone, Copy)]
struct Slot {
    table: u32,
    index: u32,
    func: u32,
}

/// A bare lowered-import trampoline: `local.get* ; i32.const K ;
/// call_indirect (type T) (table N) ; end`.
#[derive(Debug, Clone, Copy)]
struct Trampoline {
    table: u32,
    k: u32,
    type_idx: u32,
}

type Sig = (Vec<ValType>, Vec<ValType>);

/// What the tests need to know about a fused core module.
#[derive(Default, Debug)]
struct Shape {
    exports: Vec<(String, &'static str, u32)>,
    types: Vec<Sig>,
    import_funcs: u32,
    /// Per defined function (by position).
    func_types: Vec<u32>,
    is_trap_body: Vec<bool>,
    trampolines: Vec<Option<Trampoline>>,
    slots: Vec<Slot>,
}

fn shape(wasm: &[u8]) -> Shape {
    let mut s = Shape::default();
    for payload in Parser::new(0).parse_all(wasm) {
        match payload.expect("fused module must parse") {
            Payload::TypeSection(r) => {
                for g in r.into_iter_err_on_gc_types() {
                    let f = g.expect("func type");
                    s.types.push((f.params().to_vec(), f.results().to_vec()));
                }
            }
            Payload::ImportSection(r) => {
                for imp in r.into_imports() {
                    let imp = imp.expect("import");
                    if matches!(
                        imp.ty,
                        wasmparser::TypeRef::Func(_) | wasmparser::TypeRef::FuncExact(_)
                    ) {
                        s.import_funcs += 1;
                    }
                }
            }
            Payload::FunctionSection(r) => {
                for t in r {
                    s.func_types.push(t.expect("func type"));
                }
            }
            Payload::ExportSection(r) => {
                for e in r {
                    let e = e.expect("export");
                    let kind = match e.kind {
                        wasmparser::ExternalKind::Func | wasmparser::ExternalKind::FuncExact => {
                            "func"
                        }
                        wasmparser::ExternalKind::Table => "table",
                        wasmparser::ExternalKind::Memory => "memory",
                        wasmparser::ExternalKind::Global => "global",
                        wasmparser::ExternalKind::Tag => "tag",
                    };
                    s.exports.push((e.name.to_string(), kind, e.index));
                }
            }
            Payload::ElementSection(r) => {
                for e in r {
                    let e = e.expect("elem");
                    let ElementKind::Active {
                        table_index,
                        offset_expr,
                    } = e.kind
                    else {
                        continue;
                    };
                    let table = table_index.unwrap_or(0);
                    let base = offset_expr
                        .get_operators_reader()
                        .into_iter()
                        .find_map(|o| match o {
                            Ok(Operator::I32Const { value }) => Some(value as u32),
                            _ => None,
                        })
                        .expect("elem offset must be an i32.const");
                    let mut funcs = Vec::new();
                    match e.items {
                        ElementItems::Functions(fs) => {
                            for f in fs {
                                funcs.push(f.expect("elem func"));
                            }
                        }
                        ElementItems::Expressions(_, ex) => {
                            for x in ex {
                                for op in x.expect("expr").get_operators_reader() {
                                    if let Ok(Operator::RefFunc { function_index }) = op {
                                        funcs.push(function_index);
                                    }
                                }
                            }
                        }
                    }
                    for (i, func) in funcs.into_iter().enumerate() {
                        s.slots.push(Slot {
                            table,
                            index: base + i as u32,
                            func,
                        });
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                let ops: Vec<Operator> = body
                    .get_operators_reader()
                    .expect("ops")
                    .into_iter()
                    .map(|o| o.expect("op"))
                    .collect();
                s.is_trap_body.push(matches!(
                    ops.as_slice(),
                    [Operator::Unreachable, Operator::End]
                ));
                s.trampolines.push(match_trampoline(&ops));
            }
            _ => {}
        }
    }
    s
}

fn match_trampoline(ops: &[Operator]) -> Option<Trampoline> {
    let mut k = None;
    let mut ci = None;
    for op in ops {
        match op {
            Operator::LocalGet { .. } if ci.is_none() && k.is_none() => {}
            Operator::I32Const { value } if k.is_none() && ci.is_none() => k = Some(*value as u32),
            Operator::CallIndirect {
                type_index,
                table_index,
                ..
            } if ci.is_none() => ci = Some((*table_index, *type_index)),
            Operator::End => {}
            _ => return None,
        }
    }
    let (table, type_idx) = ci?;
    Some(Trampoline {
        table,
        k: k?,
        type_idx,
    })
}

impl Shape {
    fn defined(&self, f: u32) -> Option<usize> {
        f.checked_sub(self.import_funcs).map(|i| i as usize)
    }
    /// Is `f` a defined function whose body is exactly `unreachable`?
    fn is_trap_stub(&self, f: u32) -> bool {
        self.defined(f)
            .and_then(|i| self.is_trap_body.get(i))
            .copied()
            .unwrap_or(false)
    }
    fn sig_of_defined(&self, f: u32) -> Option<&Sig> {
        let i = self.defined(f)?;
        self.types.get(*self.func_types.get(i)? as usize)
    }
    fn has_export(&self, name: &str) -> bool {
        self.exports.iter().any(|(n, _, _)| n == name)
    }
}

fn validates(wasm: &[u8]) {
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(wasm)
        .expect("fused module must validate");
}

const THREE: [&str; 3] = [
    "falcon_cascade_estimator_cm.wasm",
    "falcon_cascade_control_cm.wasm",
    "falcon_cascade_split_cm.wasm",
];

fn fuse_three_shared() -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        ..Default::default()
    });
    for name in THREE {
        let bytes = read(&format!("tests/fixtures/issue_461/{name}"));
        fuser
            .add_component_named(&bytes, Some(name))
            .unwrap_or_else(|e| panic!("add {name}: {e}"));
    }
    fuser.fuse().expect("fuse must succeed on these inputs")
}

fn fuse_multi(rel: &str) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        ..Default::default()
    });
    fuser
        .add_component_named(&read(rel), Some(rel))
        .unwrap_or_else(|e| panic!("add {rel}: {e}"));
    fuser.fuse().expect("fuse must succeed")
}

/// cpetig's components (#461/#462) under the reported configuration.
///
/// The fixup module of the last component imports `"" "0"` and `"" "1"`,
/// which nothing maps; before #462 its table slots held fused functions 0 and
/// 1, which are the FIRST component's real functions.
#[test]
fn real_shape_has_no_scaffolding_exports_and_no_identity_slots() {
    let fused = fuse_three_shared();
    validates(&fused);
    let s = shape(&fused);

    for scaffold in ["0", "1", "$imports"] {
        assert!(
            !s.has_export(scaffold),
            "wit-component scaffolding export {scaffold:?} survived fusion (#462); exports: {:?}",
            s.exports
        );
    }

    // Slots that were already resolved before #462 and must still hold the
    // function they held: the first two components' fixup tables, each
    // `[configure, step]`. Pinned from the pre-fix output so that a stub
    // replacing a REAL target is caught as well as an identity slot.
    let intended: [(u32, u32); 6] = [(0, 1), (0, 2), (1, 18), (1, 19), (3, 37), (3, 38)];
    let mut stubs = 0;
    for slot in &s.slots {
        if s.is_trap_stub(slot.func) {
            stubs += 1;
            continue;
        }
        assert!(
            intended.contains(&(slot.table, slot.func)),
            "table {} slot {} holds function {}, which is neither a trap stub nor an \
             intended target: an unmapped import fell back to the identity index (#462)",
            slot.table,
            slot.index,
            slot.func
        );
    }
    assert_eq!(
        stubs, 2,
        "the one fixup table with unmapped imports must hold a trap stub in each slot \
         (slots: {:?})",
        s.slots
    );
}

/// The stub takes the type of the trampoline that reads its slot, so an
/// indirect call through the trampoline traps at `unreachable` and not on a
/// signature mismatch. Under `--memory multi` the trampolines are still
/// exported, so this can be checked on the real thing.
///
/// `custom-derives` is the corpus input whose fixup table holds an unmapped
/// import (its slot 0 held function 0, an unrelated WASI import).
#[test]
fn multi_memory_stub_has_the_type_of_the_trampoline_that_reads_it() {
    let fused = fuse_multi("../tests/wit_bindgen/fixtures/custom-derives.wasm");
    validates(&fused);
    let s = shape(&fused);

    let mut stubs = 0;
    let mut checked = 0;
    for slot in s.slots.iter().filter(|sl| s.is_trap_stub(sl.func)) {
        stubs += 1;
        let stub_sig = s.sig_of_defined(slot.func).expect("stub is defined");
        for t in s.trampolines.iter().flatten() {
            if t.table == slot.table && t.k == slot.index {
                assert_eq!(
                    stub_sig, &s.types[t.type_idx as usize],
                    "the stub in table {} slot {} must have the type its trampoline \
                     call_indirects with",
                    slot.table, slot.index
                );
                checked += 1;
            }
        }
    }
    assert!(
        stubs > 0,
        "no trap stub: the input no longer exercises #462"
    );
    assert!(
        checked > 0,
        "no trampoline reads a stubbed slot: the type check above is vacuous"
    );
}
