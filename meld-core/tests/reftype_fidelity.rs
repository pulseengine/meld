//! Reference-type fidelity runtime matrix (issue #258).
//!
//! Regression coverage for the `convert_ref_type` collapse defect: the parser
//! used to flatten every concrete typed-ref `(ref null $t)` and GC abstract
//! heap type to `funcref`, and the merger never remapped concrete heap-type
//! indices in the type/table/global sections. The two-part fix:
//!
//!   Part 1 — `parser.rs::convert_ref_type` faithfully preserves nullability +
//!            abstract heap type + concrete module-level index.
//!   Part 2 — `merger.rs` remaps those concrete module-level indices to the
//!            merged-module type index when emitting tables, func-type
//!            signatures, and globals.
//!
//! Each case fuses a component (or two), asserts the fused output VALIDATES
//! under `WasmFeatures::all()`, and asserts the relevant reference type is
//! PRESERVED (not collapsed to funcref) by inspecting the output binary.

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasmparser::{
    CompositeInnerType, GlobalType, HeapType, Parser, Payload, RefType, TableType, ValType,
    WasmFeatures,
};

/// Fuse a single component to a core module and return the fused bytes.
fn fuse_one(wat_src: &str) -> Vec<u8> {
    let bytes = wat::parse_str(wat_src).expect("WAT should parse");
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        output_format: OutputFormat::CoreModule,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser.add_component(&bytes).expect("add_component");
    fuser.fuse().expect("fuse")
}

/// Fuse two components to a core module and return the fused bytes.
fn fuse_two(wat_a: &str, wat_b: &str) -> Vec<u8> {
    let a = wat::parse_str(wat_a).expect("WAT a should parse");
    let b = wat::parse_str(wat_b).expect("WAT b should parse");
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        output_format: OutputFormat::CoreModule,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&a, Some("comp-a"))
        .expect("add a");
    fuser
        .add_component_named(&b, Some("comp-b"))
        .expect("add b");
    fuser.fuse().expect("fuse")
}

/// Validate fused output under the full feature set (GC, function-references,
/// multi-memory, etc.). A collapsed-but-valid module would still pass here, so
/// validation alone is NOT the regression guard — the type-preservation asserts
/// below are.
fn validate_all(fused: &[u8]) {
    let mut validator = wasmparser::Validator::new_with_features(WasmFeatures::all());
    validator
        .validate_all(fused)
        .expect("fused module must validate under WasmFeatures::all()");
}

/// Collect the table types, the func types, and the global types from a fused
/// core module by re-parsing it.
struct FusedSections {
    tables: Vec<TableType>,
    func_params_results: Vec<(Vec<ValType>, Vec<ValType>)>,
    globals: Vec<GlobalType>,
}

fn parse_sections(fused: &[u8]) -> FusedSections {
    let mut tables = Vec::new();
    let mut func_params_results = Vec::new();
    let mut globals = Vec::new();

    for payload in Parser::new(0).parse_all(fused) {
        match payload.expect("parse payload") {
            Payload::TypeSection(reader) => {
                for rec_group in reader {
                    let rec_group = rec_group.expect("rec group");
                    for sub in rec_group.into_types() {
                        if let CompositeInnerType::Func(ft) = &sub.composite_type.inner {
                            func_params_results.push((ft.params().to_vec(), ft.results().to_vec()));
                        }
                    }
                }
            }
            Payload::TableSection(reader) => {
                for table in reader {
                    tables.push(table.expect("table").ty);
                }
            }
            Payload::GlobalSection(reader) => {
                for global in reader {
                    globals.push(global.expect("global").ty);
                }
            }
            _ => {}
        }
    }

    FusedSections {
        tables,
        func_params_results,
        globals,
    }
}

/// Is this ref type a *concrete* typed reference (not funcref/externref/etc.)?
fn is_concrete_ref(rt: &RefType) -> Option<u32> {
    match rt.heap_type() {
        HeapType::Concrete(idx) => idx.as_module_index(),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Case 1: typed-func-ref table — element type must stay a concrete ref, not
// collapse to funcref.
// ---------------------------------------------------------------------------
#[test]
fn case1_typed_ref_table_element_preserved() {
    let wat = r#"
(component
  (core module $m
    (type $ft (func (param i32) (result i32)))
    (table $t 1 (ref null $ft))
    (func $f (export "f") (param i32) (result i32) (local.get 0))
    (elem (i32.const 0) (ref $ft) (ref.func $f))
  )
  (core instance $i (instantiate $m))
)
"#;
    let fused = fuse_one(wat);
    validate_all(&fused);

    let sections = parse_sections(&fused);
    // At least one table must carry a CONCRETE typed-func-ref element type
    // pointing at a func type in the output. If the collapse bug were present
    // this would be funcref (no concrete index).
    let concrete_tables: Vec<u32> = sections
        .tables
        .iter()
        .filter_map(|t| is_concrete_ref(&t.element_type))
        .collect();
    assert!(
        !concrete_tables.is_empty(),
        "case1: expected a concrete typed-ref table element type, got tables: {:?}",
        sections
            .tables
            .iter()
            .map(|t| t.element_type)
            .collect::<Vec<_>>()
    );
    // The concrete index must point at a real func type in the output.
    let n_types = sections.func_params_results.len() as u32;
    for idx in concrete_tables {
        assert!(
            idx < n_types,
            "case1: table element concrete index {idx} out of range (n_types={n_types})"
        );
    }
}

// ---------------------------------------------------------------------------
// Case 2: typed-ref table actually USED via call_indirect (type $ft). A wrong
// or collapsed element type causes a validation failure here.
// ---------------------------------------------------------------------------
#[test]
fn case2_typed_ref_table_used_by_call_indirect() {
    let wat = r#"
(component
  (core module $m
    (type $ft (func (param i32) (result i32)))
    (table $t 2 (ref null $ft))
    (func $impl (param i32) (result i32)
      (i32.mul (local.get 0) (i32.const 3)))
    (func $run (export "run") (param i32) (result i32)
      ;; call through the typed-ref table slot 0
      (call_indirect $t (type $ft) (local.get 0) (i32.const 0)))
    (elem (i32.const 0) (ref $ft) (ref.func $impl))
  )
  (core instance $i (instantiate $m))
)
"#;
    let fused = fuse_one(wat);
    // The crux: call_indirect (type $ft) against a typed-ref table only
    // validates if the table element type is the correct concrete ref.
    validate_all(&fused);

    let sections = parse_sections(&fused);
    let concrete = sections
        .tables
        .iter()
        .filter_map(|t| is_concrete_ref(&t.element_type))
        .count();
    assert!(
        concrete >= 1,
        "case2: typed-ref table collapsed to funcref; tables = {:?}",
        sections
            .tables
            .iter()
            .map(|t| t.element_type)
            .collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// Case 3: two components, each with its OWN func type + typed-ref table. After
// the merge renumbers types, component B's table concrete index must be
// remapped to its merged type index (Part 2). A wrong remap points at the
// wrong type -> validation failure (the table elem type would not match the
// element segment's `(ref $ft)` items).
// ---------------------------------------------------------------------------
#[test]
fn case3_two_components_concrete_index_remapped() {
    // Component A: type $fa = (func (param i32) (result i32))
    let wat_a = r#"
(component
  (core module $ma
    (type $fa (func (param i32) (result i32)))
    (table $ta 1 (ref null $fa))
    (func $ga (param i32) (result i32) (local.get 0))
    (func $run_a (export "run_a") (result i32)
      (call_indirect $ta (type $fa) (i32.const 7) (i32.const 0)))
    (elem (i32.const 0) (ref $fa) (ref.func $ga))
  )
  (core instance $i (instantiate $ma))
)
"#;
    // Component B: DISTINCT type shape $fb = (func (param i64 i64) (result i64))
    // so a wrong remap (pointing at A's i32->i32 type) is detectable.
    let wat_b = r#"
(component
  (core module $mb
    (type $fb (func (param i64 i64) (result i64)))
    (table $tb 1 (ref null $fb))
    (func $gb (param i64 i64) (result i64) (i64.add (local.get 0) (local.get 1)))
    (func $run_b (export "run_b") (result i64)
      (call_indirect $tb (type $fb) (i64.const 4) (i64.const 5) (i32.const 0)))
    (elem (i32.const 0) (ref $fb) (ref.func $gb))
  )
  (core instance $i (instantiate $mb))
)
"#;
    let fused = fuse_two(wat_a, wat_b);
    // If B's table concrete index were NOT remapped (left at module-level 0),
    // it would point at A's (i32)->(i32) type after the merge offset, and the
    // `(ref $fb)` element items (which ARE remapped, by the const-expr path)
    // would no longer subtype the table element type -> validation failure.
    validate_all(&fused);

    let sections = parse_sections(&fused);
    // Two distinct concrete typed-ref tables must survive, and their concrete
    // indices must point at func types with the EXPECTED distinct signatures.
    let concrete_table_indices: Vec<u32> = sections
        .tables
        .iter()
        .filter_map(|t| is_concrete_ref(&t.element_type))
        .collect();
    assert_eq!(
        concrete_table_indices.len(),
        2,
        "case3: expected two concrete typed-ref tables, got {:?}",
        sections
            .tables
            .iter()
            .map(|t| t.element_type)
            .collect::<Vec<_>>()
    );

    // Resolve each table's concrete index to its func signature and confirm
    // one is (i32)->(i32) and the other is (i64,i64)->(i64). This proves the
    // remap landed on the CORRECT (not merely valid) type for each component.
    let sigs: Vec<&(Vec<ValType>, Vec<ValType>)> = concrete_table_indices
        .iter()
        .map(|&idx| {
            sections
                .func_params_results
                .get(idx as usize)
                .unwrap_or_else(|| panic!("case3: table concrete index {idx} out of range"))
        })
        .collect();

    let has_i32 = sigs
        .iter()
        .any(|(p, r)| p.as_slice() == [ValType::I32] && r.as_slice() == [ValType::I32]);
    let has_i64 = sigs.iter().any(|(p, r)| {
        p.as_slice() == [ValType::I64, ValType::I64] && r.as_slice() == [ValType::I64]
    });
    assert!(
        has_i32 && has_i64,
        "case3: typed-ref table indices did not resolve to the expected distinct \
         signatures (i32->i32 and (i64,i64)->i64); got {sigs:?}"
    );
}

// ---------------------------------------------------------------------------
// Case 4: GC abstract ref — a global `(ref null any)`. The abstract heap type
// must be preserved (not collapsed to funcref).
// ---------------------------------------------------------------------------
#[test]
fn case4_gc_abstract_global_preserved() {
    let wat = r#"
(component
  (core module $m
    (global $g (export "g") (ref null any) (ref.null any))
  )
  (core instance $i (instantiate $m))
)
"#;
    let fused = fuse_one(wat);
    validate_all(&fused);

    let sections = parse_sections(&fused);
    // The global's content type must be a ref to the `any` abstract heap type.
    let has_any_ref = sections.globals.iter().any(|g| match g.content_type {
        ValType::Ref(rt) => matches!(
            rt.heap_type(),
            HeapType::Abstract {
                ty: wasmparser::AbstractHeapType::Any,
                ..
            }
        ),
        _ => false,
    });
    assert!(
        has_any_ref,
        "case4: global (ref null any) collapsed; globals = {:?}",
        sections
            .globals
            .iter()
            .map(|g| g.content_type)
            .collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// Case 4b: concrete typed-ref in a function SIGNATURE (param) is preserved and
// its index remapped (exercises the MergedFuncType param/result remap).
// ---------------------------------------------------------------------------
#[test]
fn case4b_concrete_ref_in_func_signature_preserved() {
    let wat = r#"
(component
  (core module $m
    (type $ft (func (param i32) (result i32)))
    ;; $sig takes a (ref null $ft) param -> concrete ref in a signature
    (type $sig (func (param (ref null $ft)) (result i32)))
    (func $impl (param i32) (result i32) (local.get 0))
    (func $use (export "use") (param (ref null $ft)) (result i32)
      (i32.const 0))
  )
  (core instance $i (instantiate $m))
)
"#;
    let fused = fuse_one(wat);
    validate_all(&fused);

    let sections = parse_sections(&fused);
    // Some func type must have a concrete-ref param whose index points at the
    // (i32)->(i32) func type.
    let mut found = false;
    for (params, _results) in &sections.func_params_results {
        for p in params {
            if let ValType::Ref(rt) = p
                && let Some(idx) = is_concrete_ref(rt)
            {
                // index must be in range and resolve to the i32->i32 type
                let target = &sections.func_params_results[idx as usize];
                assert_eq!(
                    (target.0.as_slice(), target.1.as_slice()),
                    (&[ValType::I32][..], &[ValType::I32][..]),
                    "case4b: concrete-ref param index {idx} resolves to wrong type"
                );
                found = true;
            }
        }
    }
    assert!(
        found,
        "case4b: no concrete-ref param found in any func signature (collapse regression)"
    );
}

// ---------------------------------------------------------------------------
// Case 5: regression — plain funcref table + ordinary func signature still
// fuse and validate, and the funcref table stays funcref (not turned into a
// spurious concrete ref). The common case must be unchanged.
// ---------------------------------------------------------------------------
#[test]
fn case5_plain_funcref_regression_unchanged() {
    let wat = r#"
(component
  (core module $m
    (type $ft (func (param i32) (result i32)))
    (table $t 1 funcref)
    (func $f (export "f") (param i32) (result i32) (local.get 0))
    (elem (i32.const 0) func $f)
  )
  (core instance $i (instantiate $m))
)
"#;
    let fused = fuse_one(wat);
    validate_all(&fused);

    let sections = parse_sections(&fused);
    // Every table must be funcref (abstract Func heap type), none concrete.
    for t in &sections.tables {
        assert!(
            is_concrete_ref(&t.element_type).is_none(),
            "case5: plain funcref table became a concrete ref: {:?}",
            t.element_type
        );
        assert!(
            t.element_type.is_func_ref(),
            "case5: plain funcref table element type changed: {:?}",
            t.element_type
        );
    }
}
