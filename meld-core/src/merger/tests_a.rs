//! Merger unit tests (part A): name/version, index-map, decompose,
//! import-order, and dedup coverage. Split out of the original inline
//! `mod tests` purely to keep each file small; see also `tests_b`.

use super::*;

/// #328: the name-section remap accumulates function names under their
/// FUSED indices, and drops entries whose source index isn't in the
/// fused map (dead/internalized) — never emitting a wrong index.
#[test]
fn accumulate_remapped_function_names_remaps_and_drops_unmapped() {
    // A `name` section body with a function-name subsection (id 1)
    // naming source func 0 -> "foo" and source func 5 -> "bar".
    // Layout: [subsec_id=1][size=0x0b][count=2][idx=0,len=3,"foo"][idx=5,len=3,"bar"]
    let data: Vec<u8> = vec![
        0x01, 0x0b, 0x02, 0x00, 0x03, b'f', b'o', b'o', 0x05, 0x03, b'b', b'a', b'r',
    ];
    // Fused index map for (comp 0, module 0): 0 -> 10; source 5 is
    // intentionally unmapped (should be dropped).
    let mut map: HashMap<(usize, usize, u32), u32> = HashMap::new();
    map.insert((0, 0, 0), 10);

    let mut out: std::collections::BTreeMap<u32, String> = std::collections::BTreeMap::new();
    accumulate_remapped_function_names(&data, 0, 0, &map, &mut out);

    assert_eq!(
        out.get(&10).map(String::as_str),
        Some("foo"),
        "source 0 -> fused 10"
    );
    assert_eq!(
        out.len(),
        1,
        "unmapped source func 5 (\"bar\") must be dropped, not emitted at a wrong index"
    );
}

#[test]
fn test_convert_memory_type() {
    let mem = MemoryType {
        memory64: false,
        shared: false,
        initial: 1,
        maximum: Some(10),
    };
    let converted = convert_memory_type(&mem);
    assert_eq!(converted.minimum, 1);
    assert_eq!(converted.maximum, Some(10));
    assert!(!converted.memory64);
    assert!(!converted.shared);
}

#[test]
fn test_create_global_init() {
    let expr = create_global_init(&ValType::I32);
    // The expression should be valid (we can't easily inspect it)
    let _ = expr;

    let expr = create_global_init(&ValType::F64);
    let _ = expr;
}

#[test]
fn test_combine_memory_types_rebased() {
    let mem_a = MemoryType {
        memory64: false,
        shared: false,
        initial: 2,
        maximum: Some(5),
    };
    let mem_b = MemoryType {
        memory64: false,
        shared: false,
        initial: 3,
        maximum: Some(7),
    };

    let combined = combine_memory_types_rebased(&[mem_a, mem_b]).unwrap();
    assert_eq!(combined.initial, 5);
    assert_eq!(combined.maximum, Some(12));
}

#[test]
fn test_combine_memory_types_shared() {
    let mem_a = MemoryType {
        memory64: false,
        shared: false,
        initial: 2,
        maximum: Some(10),
    };
    let mem_b = MemoryType {
        memory64: false,
        shared: false,
        initial: 4,
        maximum: Some(8),
    };

    let combined = combine_memory_types_shared(&[mem_a, mem_b]).unwrap();
    assert_eq!(combined.initial, 4);
    assert_eq!(combined.maximum, Some(8));
}

fn make_test_module(memories: Vec<MemoryType>) -> CoreModule {
    CoreModule {
        index: 0,
        bytes: Vec::new(),
        types: Vec::new(),
        imports: Vec::new(),
        exports: Vec::new(),
        functions: Vec::new(),
        memories,
        tables: Vec::new(),
        globals: Vec::new(),
        start: None,
        data_count: None,
        element_count: 0,
        custom_sections: Vec::new(),
        code_section_range: None,
        global_section_range: None,
        element_section_range: None,
        data_section_range: None,
    }
}

#[test]
fn test_multi_memory_index_maps() {
    // Simulate two modules each with one defined memory in multi-memory mode
    let module_a = make_test_module(vec![MemoryType {
        memory64: false,
        shared: false,
        initial: 1,
        maximum: None,
    }]);
    let module_b = make_test_module(vec![MemoryType {
        memory64: false,
        shared: false,
        initial: 2,
        maximum: None,
    }]);

    let mut merged = MergedModule {
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
        fused_function_names: std::collections::BTreeMap::new(),
        function_index_map: HashMap::new(),
        memory_index_map: HashMap::new(),
        table_index_map: HashMap::new(),
        global_index_map: HashMap::new(),
        type_index_map: HashMap::new(),
        realloc_map: HashMap::new(),
        import_counts: ImportCounts::default(),
        import_memory_indices: Vec::new(),
        import_realloc_indices: Vec::new(),
        resource_rep_by_component: HashMap::new(),
        resource_new_by_component: HashMap::new(),
        handle_tables: HashMap::new(),
        task_return_shims: HashMap::new(),
        async_result_globals: HashMap::new(),
        segment_bases: HashMap::new(),
        shared_stack_top: None,
        placements: Vec::new(),
    };

    // Simulate multi-memory merging for module A (comp 0, mod 0)
    let mem_offset_a = merged.memories.len() as u32; // 0
    merged.memory_index_map.insert((0, 0, 0), mem_offset_a);
    merged
        .memories
        .push(convert_memory_type(&module_a.memories[0]));

    // Simulate multi-memory merging for module B (comp 1, mod 0)
    let mem_offset_b = merged.memories.len() as u32; // 1
    merged.memory_index_map.insert((1, 0, 0), mem_offset_b);
    merged
        .memories
        .push(convert_memory_type(&module_b.memories[0]));

    // Verify: 2 separate memories
    assert_eq!(merged.memories.len(), 2);
    assert_eq!(merged.memories[0].minimum, 1);
    assert_eq!(merged.memories[1].minimum, 2);

    // Verify: index maps point to different memories
    assert_eq!(merged.memory_index_map[&(0, 0, 0)], 0);
    assert_eq!(merged.memory_index_map[&(1, 0, 0)], 1);

    // Verify: IndexMaps for rewriter map correctly
    let maps_a = build_index_maps_for_module(
        0,
        0,
        &module_a,
        &merged,
        MemoryStrategy::MultiMemory,
        false,
        0,
        false,
        None,
        0,
        0,
        None,
    );
    assert_eq!(maps_a.remap_memory(0), 0);

    let maps_b = build_index_maps_for_module(
        1,
        0,
        &module_b,
        &merged,
        MemoryStrategy::MultiMemory,
        false,
        0,
        false,
        None,
        0,
        0,
        None,
    );
    assert_eq!(maps_b.remap_memory(0), 1);
}

/// Mythos finding B (PR #220): an unresolved `MemoryStrategy::Auto`
/// reaching `Merger::new` directly must normalize to MultiMemory.
/// Without normalization the merger is split-brained — `== SharedMemory`
/// sites treat Auto as multi while `== MultiMemory` sites treat it as
/// shared, silently dropping the second component's memory export.
#[test]
fn test_merger_new_normalizes_auto_to_multi_memory() {
    let merger = Merger::new(MemoryStrategy::Auto, false);
    assert_eq!(
        merger.memory_strategy,
        MemoryStrategy::MultiMemory,
        "Merger::new(Auto, _) must normalize to MultiMemory"
    );
}

/// Regression test for Bug #7: Merger::default() must use MultiMemory strategy.
/// The default memory strategy should be MultiMemory (not SharedMemory) because
/// SharedMemory is broken when any component uses memory.grow.
#[test]
fn test_merger_default_uses_multi_memory() {
    let merger = Merger::default();
    assert_eq!(
        merger.memory_strategy,
        MemoryStrategy::MultiMemory,
        "Merger::default() must use MultiMemory strategy"
    );
    assert!(
        !merger.address_rebasing,
        "Merger::default() must not enable address rebasing"
    );
}

/// Test decompose_component_core_func_index for single-module components
#[test]
fn test_decompose_core_func_index_single_module() {
    use crate::parser::ParsedComponent;

    // Single module with 2 imported functions + 3 defined functions = 5 total
    let module = CoreModule {
        index: 0,
        bytes: Vec::new(),
        types: Vec::new(),
        imports: vec![
            crate::parser::ModuleImport {
                module: "env".to_string(),
                name: "f0".to_string(),
                kind: ImportKind::Function(0),
            },
            crate::parser::ModuleImport {
                module: "env".to_string(),
                name: "f1".to_string(),
                kind: ImportKind::Function(0),
            },
        ],
        exports: Vec::new(),
        functions: vec![0, 0, 0], // 3 defined functions
        memories: Vec::new(),
        tables: Vec::new(),
        globals: Vec::new(),
        start: None,
        data_count: None,
        element_count: 0,
        custom_sections: Vec::new(),
        code_section_range: None,
        global_section_range: None,
        element_section_range: None,
        data_section_range: None,
    };

    let component = ParsedComponent {
        name: None,
        core_modules: vec![module],
        imports: Vec::new(),
        exports: Vec::new(),
        types: Vec::new(),
        instances: Vec::new(),
        canonical_functions: Vec::new(),
        sub_components: Vec::new(),
        component_aliases: Vec::new(),
        component_instances: Vec::new(),
        core_entity_order: Vec::new(),
        component_func_defs: Vec::new(),
        component_instance_defs: Vec::new(),
        component_type_defs: Vec::new(),
        original_size: 0,
        original_hash: String::new(),
        depth_0_sections: Vec::new(),
        p3_async_features: Vec::new(),
    };

    // Function indices 0-4 should all map to (module 0, local idx)
    assert_eq!(
        decompose_component_core_func_index(&component, 0),
        Some((0, 0))
    );
    assert_eq!(
        decompose_component_core_func_index(&component, 2),
        Some((0, 2))
    );
    assert_eq!(
        decompose_component_core_func_index(&component, 4),
        Some((0, 4))
    );
    // Index 5 is out of bounds
    assert_eq!(decompose_component_core_func_index(&component, 5), None);
}

/// Test decompose_component_core_func_index for multi-module components
#[test]
fn test_decompose_core_func_index_multi_module() {
    use crate::parser::ParsedComponent;

    // Module A: 1 import + 2 defined = 3 total (indices 0, 1, 2)
    let module_a = CoreModule {
        index: 0,
        bytes: Vec::new(),
        types: Vec::new(),
        imports: vec![crate::parser::ModuleImport {
            module: "env".to_string(),
            name: "f0".to_string(),
            kind: ImportKind::Function(0),
        }],
        exports: Vec::new(),
        functions: vec![0, 0],
        memories: Vec::new(),
        tables: Vec::new(),
        globals: Vec::new(),
        start: None,
        data_count: None,
        element_count: 0,
        custom_sections: Vec::new(),
        code_section_range: None,
        global_section_range: None,
        element_section_range: None,
        data_section_range: None,
    };

    // Module B: 0 imports + 4 defined = 4 total (indices 3, 4, 5, 6)
    let module_b = CoreModule {
        index: 1,
        bytes: Vec::new(),
        types: Vec::new(),
        imports: Vec::new(),
        exports: Vec::new(),
        functions: vec![0, 0, 0, 0],
        memories: Vec::new(),
        tables: Vec::new(),
        globals: Vec::new(),
        start: None,
        data_count: None,
        element_count: 0,
        custom_sections: Vec::new(),
        code_section_range: None,
        global_section_range: None,
        element_section_range: None,
        data_section_range: None,
    };

    let component = ParsedComponent {
        name: None,
        core_modules: vec![module_a, module_b],
        imports: Vec::new(),
        exports: Vec::new(),
        types: Vec::new(),
        instances: Vec::new(),
        canonical_functions: Vec::new(),
        sub_components: Vec::new(),
        component_aliases: Vec::new(),
        component_instances: Vec::new(),
        core_entity_order: Vec::new(),
        component_func_defs: Vec::new(),
        component_instance_defs: Vec::new(),
        component_type_defs: Vec::new(),
        original_size: 0,
        original_hash: String::new(),
        depth_0_sections: Vec::new(),
        p3_async_features: Vec::new(),
    };

    // Indices 0-2 belong to module A
    assert_eq!(
        decompose_component_core_func_index(&component, 0),
        Some((0, 0))
    );
    assert_eq!(
        decompose_component_core_func_index(&component, 2),
        Some((0, 2))
    );

    // Indices 3-6 belong to module B (local indices 0-3)
    assert_eq!(
        decompose_component_core_func_index(&component, 3),
        Some((1, 0))
    );
    assert_eq!(
        decompose_component_core_func_index(&component, 6),
        Some((1, 3))
    );

    // Index 7 is out of bounds
    assert_eq!(decompose_component_core_func_index(&component, 7), None);
}

/// Verify that `compute_unresolved_import_assignments` and
/// `add_unresolved_imports` agree on import counts for a graph with
/// mixed unresolved import kinds.
///
/// This test constructs a `DependencyGraph` with several unresolved
/// imports (function, global, table, memory) and runs the full merge
/// pipeline, which triggers the debug assertions inside
/// `add_unresolved_imports`.  If the two functions ever diverge in
/// iteration order, the assertions will fire and this test will fail.
#[test]
fn test_import_order_invariant_holds() {
    use crate::parser::{FuncType, ModuleImport, ParsedComponent};
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    // Build a single component with one module that has several
    // unresolved imports of different kinds.
    let module = CoreModule {
        index: 0,
        bytes: Vec::new(),
        types: vec![FuncType {
            params: vec![],
            results: vec![],
        }],
        imports: vec![
            ModuleImport {
                module: "env".to_string(),
                name: "imported_func".to_string(),
                kind: ImportKind::Function(0),
            },
            ModuleImport {
                module: "env".to_string(),
                name: "imported_global".to_string(),
                kind: ImportKind::Global(GlobalType {
                    content_type: ValType::I32,
                    mutable: false,
                    init_expr_bytes: Vec::new(),
                }),
            },
            ModuleImport {
                module: "env".to_string(),
                name: "imported_table".to_string(),
                kind: ImportKind::Table(TableType {
                    element_type: ValType::Ref(RefType::FUNCREF),
                    initial: 1,
                    maximum: None,
                }),
            },
        ],
        exports: Vec::new(),
        functions: Vec::new(),
        memories: vec![MemoryType {
            memory64: false,
            shared: false,
            initial: 1,
            maximum: None,
        }],
        tables: Vec::new(),
        globals: Vec::new(),
        start: None,
        data_count: None,
        element_count: 0,
        custom_sections: Vec::new(),
        code_section_range: None,
        global_section_range: None,
        element_section_range: None,
        data_section_range: None,
    };

    let component = ParsedComponent {
        name: None,
        core_modules: vec![module],
        imports: Vec::new(),
        exports: Vec::new(),
        types: Vec::new(),
        instances: Vec::new(),
        canonical_functions: Vec::new(),
        sub_components: Vec::new(),
        component_aliases: Vec::new(),
        component_instances: Vec::new(),
        core_entity_order: Vec::new(),
        component_func_defs: Vec::new(),
        component_instance_defs: Vec::new(),
        component_type_defs: Vec::new(),
        original_size: 0,
        original_hash: String::new(),
        depth_0_sections: Vec::new(),
        p3_async_features: Vec::new(),
    };

    let graph = DependencyGraph {
        instantiation_order: vec![0],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        unresolved_imports: vec![
            UnresolvedImport {
                component_idx: 0,
                module_idx: 0,
                module_name: "env".to_string(),
                field_name: "imported_func".to_string(),
                kind: ImportKind::Function(0),
                display_module: None,
                display_field: None,
            },
            UnresolvedImport {
                component_idx: 0,
                module_idx: 0,
                module_name: "env".to_string(),
                field_name: "imported_global".to_string(),
                kind: ImportKind::Global(GlobalType {
                    content_type: ValType::I32,
                    mutable: false,
                    init_expr_bytes: Vec::new(),
                }),
                display_module: None,
                display_field: None,
            },
            UnresolvedImport {
                component_idx: 0,
                module_idx: 0,
                module_name: "env".to_string(),
                field_name: "imported_table".to_string(),
                kind: ImportKind::Table(TableType {
                    element_type: ValType::Ref(RefType::FUNCREF),
                    initial: 1,
                    maximum: None,
                }),
                display_module: None,
                display_field: None,
            },
        ],
    };

    let merger = Merger::new(MemoryStrategy::MultiMemory, false);
    // This will trigger debug_assert! inside add_unresolved_imports
    // if the import order invariant is broken.
    let result = merger.merge(&[component], &graph);
    assert!(result.is_ok(), "merge should succeed: {:?}", result.err());

    let merged = result.unwrap();
    // Verify the counts match what we expect
    assert_eq!(merged.import_counts.func, 1, "one unresolved func import");
    assert_eq!(
        merged.import_counts.global, 1,
        "one unresolved global import"
    );
    assert_eq!(merged.import_counts.table, 1, "one unresolved table import");
    assert_eq!(
        merged.import_counts.memory, 0,
        "no unresolved memory import"
    );

    // Verify the actual imports match
    assert_eq!(merged.imports.len(), 3);
    assert_eq!(merged.imports[0].name, "imported_func");
    assert_eq!(merged.imports[1].name, "imported_global");
    assert_eq!(merged.imports[2].name, "imported_table");
}

/// SR-8 — Correct function base offset calculation.
///
/// Requirement: the merger computes each component's function base offset
/// as the cumulative sum of all preceding components' total function counts
/// (imports + defined functions). In a flat wasm index space ALL imports
/// are hoisted ahead of ALL defined functions (the module format requires
/// it), so the equivalent, mechanically-checkable invariant is:
///
///   fused_index(defined func at array position `p` of module M)
///       = import_counts.func            // the whole hoisted import block
///       + Σ(defined counts of every module merged before M)
///       + p
///
/// (SR-8's parenthetical "(imports + defined functions)" describes a
/// per-component `[imports][defined]` block layout that the flat wasm index
/// space cannot have; this test pins the equivalent correct invariant that
/// the implementation must satisfy — see merger.rs:1957-1966.)
///
/// Three single-module components with KNOWN counts:
///   comp 0: 1 func import + 2 defined
///   comp 1: 0 imports    + 3 defined
///   comp 2: 1 func import + 1 defined
/// Total hoisted func imports = 2; defined counts = [2, 3, 1].
/// Expected fused indices: comp0 defined -> [2, 3]; comp1 -> [4, 5, 6];
/// comp2 -> [7].
///
/// Teeth: dropping the `import_counts.func` term (merger.rs:1961) makes
/// comp0 land at [0,1] not [2,3] -> red. Zeroing/ resetting `func_offset`
/// per module (losing the cumulative sum) makes comp1 land at [2,3,4] not
/// [4,5,6] -> red. An off-by-one in either term shifts the literals -> red.
/// A LATER component's import (comp2's) that fails to hoist into the front
/// block would leave comp0/comp1 defined indices unshifted -> red.
#[test]
fn sr8_function_base_offset_is_cumulative() {
    use crate::parser::{FuncType, ModuleImport, ParsedComponent};
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    // Build a single-module component: `import_count` unresolved func
    // imports (module "env") followed by `defined_count` defined functions,
    // all of the trivial `() -> ()` type 0. No code section is required —
    // `extract_function_body` stubs an `unreachable` body when
    // `code_section_range` is None, but `function_index_map` is populated
    // in the merger's FIRST pass purely from `module.functions`, so the
    // index arithmetic under test is exercised regardless.
    fn make_component(import_count: u32, defined_count: u32) -> ParsedComponent {
        let imports: Vec<ModuleImport> = (0..import_count)
            .map(|i| ModuleImport {
                module: "env".to_string(),
                name: format!("host_fn_{i}"),
                kind: ImportKind::Function(0),
            })
            .collect();

        let module = CoreModule {
            index: 0,
            bytes: Vec::new(),
            types: vec![FuncType {
                params: vec![],
                results: vec![],
            }],
            imports,
            exports: Vec::new(),
            // `defined_count` defined functions, each of type 0.
            functions: vec![0u32; defined_count as usize],
            memories: vec![MemoryType {
                memory64: false,
                shared: false,
                initial: 1,
                maximum: None,
            }],
            tables: Vec::new(),
            globals: Vec::new(),
            start: None,
            data_count: None,
            element_count: 0,
            custom_sections: Vec::new(),
            code_section_range: None,
            global_section_range: None,
            element_section_range: None,
            data_section_range: None,
        };

        ParsedComponent {
            name: None,
            core_modules: vec![module],
            imports: Vec::new(),
            exports: Vec::new(),
            types: Vec::new(),
            instances: Vec::new(),
            canonical_functions: Vec::new(),
            sub_components: Vec::new(),
            component_aliases: Vec::new(),
            component_instances: Vec::new(),
            core_entity_order: Vec::new(),
            component_func_defs: Vec::new(),
            component_instance_defs: Vec::new(),
            component_type_defs: Vec::new(),
            original_size: 0,
            original_hash: String::new(),
            depth_0_sections: Vec::new(),
            p3_async_features: Vec::new(),
        }
    }

    // comp 0: 1 import + 2 defined; comp 1: 0 + 3; comp 2: 1 + 1.
    let components = vec![
        make_component(1, 2),
        make_component(0, 3),
        make_component(1, 1),
    ];

    // One UnresolvedImport per module func import, so the merger hoists
    // them into the shared front import block.
    let unresolved_imports = vec![
        UnresolvedImport {
            component_idx: 0,
            module_idx: 0,
            module_name: "env".to_string(),
            field_name: "host_fn_0".to_string(),
            kind: ImportKind::Function(0),
            display_module: None,
            display_field: None,
        },
        UnresolvedImport {
            component_idx: 2,
            module_idx: 0,
            module_name: "env".to_string(),
            field_name: "host_fn_0".to_string(),
            kind: ImportKind::Function(0),
            display_module: None,
            display_field: None,
        },
    ];

    let graph = DependencyGraph {
        instantiation_order: vec![0, 1, 2],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        unresolved_imports,
    };

    let merger = Merger::new(MemoryStrategy::MultiMemory, false);
    let merged = merger
        .merge(&components, &graph)
        .expect("merge of three single-module components must succeed");

    // Both host func imports are hoisted into the single front block.
    assert_eq!(
        merged.import_counts.func, 2,
        "two unresolved func imports hoist into the front block"
    );
    // No synthetic functions were inserted between modules; the defined
    // block is exactly 2 + 3 + 1. (Guards the hard-coded literals below
    // against a future shim being minted mid-merge.)
    assert_eq!(
        merged.functions.len(),
        6,
        "defined function count is the plain sum 2 + 3 + 1"
    );

    // import_counts.func = 2 (whole hoisted import block).
    //
    // comp 0's 2 defined funcs have module-local indices 1,2 (after its 1
    // local import). Cumulative preceding defined = 0. Fused = 2 + {0,1}.
    assert_eq!(merged.function_index_map.get(&(0, 0, 1)), Some(&2));
    assert_eq!(merged.function_index_map.get(&(0, 0, 2)), Some(&3));

    // comp 1's 3 defined funcs (no local imports) have module-local indices
    // 0,1,2. Cumulative preceding defined = 2. Fused = 2 + 2 + {0,1,2}.
    assert_eq!(merged.function_index_map.get(&(1, 0, 0)), Some(&4));
    assert_eq!(merged.function_index_map.get(&(1, 0, 1)), Some(&5));
    assert_eq!(merged.function_index_map.get(&(1, 0, 2)), Some(&6));

    // comp 2's 1 defined func has module-local index 1 (after its 1 local
    // import). Cumulative preceding defined = 2 + 3 = 5. Fused = 2 + 5 + 0.
    assert_eq!(merged.function_index_map.get(&(2, 0, 1)), Some(&7));
}

// -----------------------------------------------------------------------
// Import deduplication utility tests
// -----------------------------------------------------------------------

#[test]
fn test_normalize_wasi_module_name() {
    // WASI names with version suffix
    assert_eq!(
        normalize_wasi_module_name("wasi:io/error@0.2.0"),
        "wasi:io/error"
    );
    assert_eq!(
        normalize_wasi_module_name("wasi:cli/stderr@0.2.6"),
        "wasi:cli/stderr"
    );
    assert_eq!(
        normalize_wasi_module_name("wasi:io/streams@0.2.6"),
        "wasi:io/streams"
    );
    // Non-WASI names should be unchanged
    assert_eq!(normalize_wasi_module_name("env"), "env");
    assert_eq!(normalize_wasi_module_name(""), "");
    // Email-like strings (@ without colon) should NOT strip
    assert_eq!(normalize_wasi_module_name("user@host"), "user@host");
}

#[test]
fn test_compare_version() {
    use std::cmp::Ordering;
    // Pure numeric triples (existing coverage).
    assert_eq!(compare_version("0.2.6", "0.2.0"), Ordering::Greater);
    assert_eq!(compare_version("0.2.0", "0.2.6"), Ordering::Less);
    assert_eq!(compare_version("0.2.6", "0.2.6"), Ordering::Equal);
    assert_eq!(compare_version("1.0.0", "0.9.9"), Ordering::Greater);
    assert_eq!(compare_version("0.3.0", "0.2.9"), Ordering::Greater);
}

#[test]
fn test_compare_version_prerelease_regression_issue_98() {
    use std::cmp::Ordering;
    // Issue #98: previously returned Less because filter_map(parse::<u32>)
    // dropped the "99-rc1" segment, leaving [0, 2] vs [0, 2, 0]. After the
    // fix the pre-release suffix is split off and 99 > 0 wins.
    assert_eq!(compare_version("0.2.99-rc1", "0.2.0"), Ordering::Greater);
}

#[test]
fn test_compare_version_prerelease_below_release() {
    use std::cmp::Ordering;
    // Per semver §11: a pre-release version sorts BELOW the same version
    // without a pre-release suffix.
    assert_eq!(compare_version("0.2.0-rc1", "0.2.0"), Ordering::Less);
    assert_eq!(compare_version("0.2.0", "0.2.0-rc1"), Ordering::Greater);
    assert_eq!(compare_version("1.0.0-alpha", "1.0.0"), Ordering::Less);
}

#[test]
fn test_compare_version_prerelease_ordering() {
    use std::cmp::Ordering;
    // Both have pre-release: compare identifier-wise.
    assert_eq!(compare_version("1.0.0-alpha", "1.0.0-beta"), Ordering::Less);
    assert_eq!(compare_version("1.0.0-rc1", "1.0.0-rc2"), Ordering::Less);
    // Numeric identifiers sort below alphanumeric ones (semver §11.4.3).
    assert_eq!(compare_version("1.0.0-1", "1.0.0-alpha"), Ordering::Less);
    // Longer pre-release wins when shared segments match.
    assert_eq!(
        compare_version("1.0.0-alpha", "1.0.0-alpha.1"),
        Ordering::Less
    );
    assert_eq!(
        compare_version("1.0.0-alpha.1", "1.0.0-alpha.1"),
        Ordering::Equal
    );
}

#[test]
fn test_compare_version_build_metadata_ignored() {
    use std::cmp::Ordering;
    // Build metadata (+...) does not affect precedence.
    assert_eq!(
        compare_version("1.0.0+meta", "1.0.0+other"),
        Ordering::Equal
    );
    assert_eq!(compare_version("1.0.0+meta", "1.0.0"), Ordering::Equal);
    assert_eq!(compare_version("0.2.6+sha.abc", "0.2.0"), Ordering::Greater);
    // Build metadata after pre-release is also ignored.
    assert_eq!(
        compare_version("1.0.0-rc1+build.5", "1.0.0-rc1"),
        Ordering::Equal
    );
}

#[test]
fn test_compare_version_missing_segments() {
    use std::cmp::Ordering;
    // Missing trailing segments default to 0.
    assert_eq!(compare_version("0.2", "0.2.0"), Ordering::Equal);
    assert_eq!(compare_version("1", "1.0.0"), Ordering::Equal);
    assert_eq!(compare_version("0.3", "0.2.99"), Ordering::Greater);
    assert_eq!(compare_version("0.2", "0.2.1"), Ordering::Less);
}

#[test]
fn test_compare_version_mixed_alphanumeric() {
    use std::cmp::Ordering;
    // Non-numeric main segments fall back to lexical comparison of that
    // segment so we never silently drop them like the old impl did.
    assert_eq!(compare_version("0.2.x", "0.2.x"), Ordering::Equal);
    // Different non-numeric segments compare lexically.
    assert_ne!(compare_version("0.2.a", "0.2.b"), Ordering::Equal);
    // A numeric segment vs a non-numeric one is decidable (not silently
    // dropped) — exact ordering depends on lexical fallback, but it
    // must not be Equal.
    assert_ne!(compare_version("0.2.0", "0.2.x"), Ordering::Equal);
}

#[test]
fn test_compare_version_large_numbers() {
    use std::cmp::Ordering;
    // u64-range segments must compare numerically, not lexically.
    // Lexical "10" < "9" but numeric 10 > 9.
    assert_eq!(compare_version("0.0.10", "0.0.9"), Ordering::Greater);
    assert_eq!(
        compare_version("0.0.4294967296", "0.0.4294967295"),
        Ordering::Greater
    );
}

#[test]
fn test_extract_version() {
    assert_eq!(extract_version("wasi:io/error@0.2.6"), Some("0.2.6"));
    assert_eq!(extract_version("wasi:io/error@0.2.0"), Some("0.2.0"));
    assert_eq!(extract_version("env"), None);
    assert_eq!(extract_version("user@host"), None);
}

#[test]
fn test_import_dedup_exact_match() {
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    // Two imports with identical effective (module, field) should dedup
    let graph = DependencyGraph {
        instantiation_order: vec![0],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        unresolved_imports: vec![
            UnresolvedImport {
                component_idx: 0,
                module_idx: 0,
                module_name: "".to_string(),
                field_name: "0".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                display_field: Some("get-stderr".to_string()),
            },
            UnresolvedImport {
                component_idx: 0,
                module_idx: 1,
                module_name: "".to_string(),
                field_name: "5".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                display_field: Some("get-stderr".to_string()),
            },
        ],
    };

    let (counts, assignments, _dedup_info) =
        compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

    // Should be 1 unique func import, not 2
    assert_eq!(counts.func, 1, "duplicate imports should be deduplicated");

    // Both assignments should point to the same position (0)
    assert_eq!(
        assignments.func[&(0, 0, "".to_string(), "0".to_string())],
        0
    );
    assert_eq!(
        assignments.func[&(0, 1, "".to_string(), "5".to_string())],
        0
    );
}

#[test]
fn test_import_dedup_version_mismatch() {
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    // Two imports for the same WASI function but different versions
    let graph = DependencyGraph {
        instantiation_order: vec![0],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        unresolved_imports: vec![
            UnresolvedImport {
                component_idx: 0,
                module_idx: 0,
                module_name: "".to_string(),
                field_name: "0".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:io/error@0.2.0".to_string()),
                display_field: Some("drop".to_string()),
            },
            UnresolvedImport {
                component_idx: 0,
                module_idx: 1,
                module_name: "".to_string(),
                field_name: "3".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:io/error@0.2.6".to_string()),
                display_field: Some("drop".to_string()),
            },
        ],
    };

    let (counts, assignments, dedup_info) =
        compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

    // Should be 1 unique func import (version-normalized key matches)
    assert_eq!(
        counts.func, 1,
        "version-mismatched imports should be deduplicated"
    );

    // Both assignments point to position 0
    assert_eq!(
        assignments.func[&(0, 0, "".to_string(), "0".to_string())],
        0
    );
    assert_eq!(
        assignments.func[&(0, 1, "".to_string(), "3".to_string())],
        0
    );

    // Best version should be the higher one (@0.2.6)
    // In SharedMemory mode, dedup key has None as the component dimension
    let key = ("wasi:io/error".to_string(), "drop".to_string(), None);
    assert_eq!(dedup_info.best_module_version[&key], "wasi:io/error@0.2.6");
}

#[test]
fn test_import_dedup_different_fields_not_deduped() {
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    // Same module, different field — should NOT dedup
    let graph = DependencyGraph {
        instantiation_order: vec![0],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        unresolved_imports: vec![
            UnresolvedImport {
                component_idx: 0,
                module_idx: 0,
                module_name: "".to_string(),
                field_name: "0".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                display_field: Some("get-stderr".to_string()),
            },
            UnresolvedImport {
                component_idx: 0,
                module_idx: 0,
                module_name: "".to_string(),
                field_name: "1".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                display_field: Some("write".to_string()),
            },
        ],
    };

    let (counts, _assignments, _dedup_info) =
        compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

    assert_eq!(
        counts.func, 2,
        "different fields should remain separate imports"
    );
}

// -----------------------------------------------------------------------
// Multi-memory WASI import lowering tests
// -----------------------------------------------------------------------

/// In MultiMemory mode, the same (module, field) from two different
/// components must get separate import slots (different DedupKey because
/// the component dimension differs). Each slot gets its own canon lower
/// with the correct Memory(N) and Realloc(N).
#[test]
fn test_multi_memory_dedup_separates_components() {
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    let graph = DependencyGraph {
        instantiation_order: vec![0, 1],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        unresolved_imports: vec![
            UnresolvedImport {
                component_idx: 0,
                module_idx: 0,
                module_name: "".to_string(),
                field_name: "0".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                display_field: Some("get-stderr".to_string()),
            },
            UnresolvedImport {
                component_idx: 1,
                module_idx: 0,
                module_name: "".to_string(),
                field_name: "0".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                display_field: Some("get-stderr".to_string()),
            },
        ],
    };

    let (counts, assignments, _dedup_info) =
        compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::MultiMemory);

    // MultiMemory: same (module, field) from different components -> 2 slots
    assert_eq!(
        counts.func, 2,
        "multi-memory mode must allocate separate import slots per component"
    );

    // Each component's import should map to a distinct position
    let pos_comp0 = assignments.func[&(0, 0, "".to_string(), "0".to_string())];
    let pos_comp1 = assignments.func[&(1, 0, "".to_string(), "0".to_string())];
    assert_ne!(
        pos_comp0, pos_comp1,
        "component 0 and component 1 must have different import positions"
    );
}

/// In SharedMemory mode, the same (module, field) from two different
/// components should still deduplicate to a single import slot (the
/// component dimension is None).
#[test]
fn test_shared_memory_dedup_merges_components() {
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    let graph = DependencyGraph {
        instantiation_order: vec![0, 1],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        unresolved_imports: vec![
            UnresolvedImport {
                component_idx: 0,
                module_idx: 0,
                module_name: "".to_string(),
                field_name: "0".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                display_field: Some("get-stderr".to_string()),
            },
            UnresolvedImport {
                component_idx: 1,
                module_idx: 0,
                module_name: "".to_string(),
                field_name: "0".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:cli/stderr@0.2.6".to_string()),
                display_field: Some("get-stderr".to_string()),
            },
        ],
    };

    let (counts, assignments, _dedup_info) =
        compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

    // SharedMemory: same effective key -> 1 slot (deduped)
    assert_eq!(
        counts.func, 1,
        "shared-memory mode must deduplicate same (module, field) across components"
    );

    // Both assignments point to the same position
    let pos_comp0 = assignments.func[&(0, 0, "".to_string(), "0".to_string())];
    let pos_comp1 = assignments.func[&(1, 0, "".to_string(), "0".to_string())];
    assert_eq!(
        pos_comp0, pos_comp1,
        "deduplicated imports must share the same position"
    );
}

/// Two components import the same-named global `env.g` at DIFFERENT types
/// (comp0: i32 immutable, comp1: i64 mutable). The structural type check
/// must refuse to dedup them: TWO distinct global import slots, and the
/// two components' assignments (which feed `global_index_map`) must point
/// at DIFFERENT positions. Pre-fix this collapsed to a single slot.
#[test]
fn ls_m_10_test_global_import_type_mismatch_not_deduped() {
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    let graph = DependencyGraph {
        instantiation_order: vec![0, 1],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        unresolved_imports: vec![
            UnresolvedImport {
                component_idx: 0,
                module_idx: 0,
                module_name: "env".to_string(),
                field_name: "g".to_string(),
                kind: ImportKind::Global(GlobalType {
                    content_type: ValType::I32,
                    mutable: false,
                    init_expr_bytes: Vec::new(),
                }),
                display_module: None,
                display_field: None,
            },
            UnresolvedImport {
                component_idx: 1,
                module_idx: 0,
                module_name: "env".to_string(),
                field_name: "g".to_string(),
                kind: ImportKind::Global(GlobalType {
                    content_type: ValType::I64,
                    mutable: true,
                    init_expr_bytes: Vec::new(),
                }),
                display_module: None,
                display_field: None,
            },
        ],
    };

    let (counts, assignments, dedup_info) =
        compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

    assert_eq!(
        counts.global, 2,
        "globals with mismatched (type, mutability) must NOT dedup"
    );
    let pos0 = assignments.global[&(0, 0, "env".to_string(), "g".to_string())];
    let pos1 = assignments.global[&(1, 0, "env".to_string(), "g".to_string())];
    assert_ne!(
        pos0, pos1,
        "mismatched-type globals must map to different import slots"
    );
    // The second occurrence must be recorded as a type mismatch so the
    // emit side knows to emit a separate import.
    assert!(
        dedup_info
            .type_mismatch_entries
            .contains(&(1, 0, "env".to_string(), "g".to_string())),
        "mismatched global must be recorded in type_mismatch_entries"
    );
}

/// Two components import the same-named table `env.t` at DIFFERENT types
/// (comp0: funcref[1..], comp1: externref[5..]). Must emit TWO distinct
/// table import slots with distinct assignment positions.
#[test]
fn test_table_import_type_mismatch_not_deduped() {
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    let graph = DependencyGraph {
        instantiation_order: vec![0, 1],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        unresolved_imports: vec![
            UnresolvedImport {
                component_idx: 0,
                module_idx: 0,
                module_name: "env".to_string(),
                field_name: "t".to_string(),
                kind: ImportKind::Table(TableType {
                    element_type: ValType::Ref(RefType::FUNCREF),
                    initial: 1,
                    maximum: None,
                }),
                display_module: None,
                display_field: None,
            },
            UnresolvedImport {
                component_idx: 1,
                module_idx: 0,
                module_name: "env".to_string(),
                field_name: "t".to_string(),
                kind: ImportKind::Table(TableType {
                    element_type: ValType::Ref(RefType::EXTERNREF),
                    initial: 5,
                    maximum: None,
                }),
                display_module: None,
                display_field: None,
            },
        ],
    };

    let (counts, assignments, dedup_info) =
        compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

    assert_eq!(
        counts.table, 2,
        "tables with mismatched (element_type, limits) must NOT dedup"
    );
    let pos0 = assignments.table[&(0, 0, "env".to_string(), "t".to_string())];
    let pos1 = assignments.table[&(1, 0, "env".to_string(), "t".to_string())];
    assert_ne!(
        pos0, pos1,
        "mismatched-type tables must map to different import slots"
    );
    assert!(
        dedup_info
            .type_mismatch_entries
            .contains(&(1, 0, "env".to_string(), "t".to_string())),
        "mismatched table must be recorded in type_mismatch_entries"
    );
}

/// Regression: two components importing the SAME-typed `env.g`
/// (i32 immutable) must still deduplicate to ONE slot (current behaviour).
#[test]
fn test_global_import_same_type_still_deduped() {
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    let mk = |comp: usize| UnresolvedImport {
        component_idx: comp,
        module_idx: 0,
        module_name: "env".to_string(),
        field_name: "g".to_string(),
        kind: ImportKind::Global(GlobalType {
            content_type: ValType::I32,
            mutable: false,
            init_expr_bytes: Vec::new(),
        }),
        display_module: None,
        display_field: None,
    };

    let graph = DependencyGraph {
        instantiation_order: vec![0, 1],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        unresolved_imports: vec![mk(0), mk(1)],
    };

    let (counts, assignments, dedup_info) =
        compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

    assert_eq!(
        counts.global, 1,
        "same-typed globals must dedup to one slot"
    );
    let pos0 = assignments.global[&(0, 0, "env".to_string(), "g".to_string())];
    let pos1 = assignments.global[&(1, 0, "env".to_string(), "g".to_string())];
    assert_eq!(pos0, pos1, "same-typed globals must share the slot");
    assert!(
        dedup_info.type_mismatch_entries.is_empty(),
        "no mismatch must be recorded for identical types"
    );
}

/// Regression: two components importing the SAME-typed `env.t`
/// (funcref[1..]) must still deduplicate to ONE slot.
#[test]
fn test_table_import_same_type_still_deduped() {
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    let mk = |comp: usize| UnresolvedImport {
        component_idx: comp,
        module_idx: 0,
        module_name: "env".to_string(),
        field_name: "t".to_string(),
        kind: ImportKind::Table(TableType {
            element_type: ValType::Ref(RefType::FUNCREF),
            initial: 1,
            maximum: Some(10),
        }),
        display_module: None,
        display_field: None,
    };

    let graph = DependencyGraph {
        instantiation_order: vec![0, 1],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        unresolved_imports: vec![mk(0), mk(1)],
    };

    let (counts, assignments, dedup_info) =
        compute_unresolved_import_assignments(&graph, None, &[], MemoryStrategy::SharedMemory);

    assert_eq!(counts.table, 1, "same-typed tables must dedup to one slot");
    let pos0 = assignments.table[&(0, 0, "env".to_string(), "t".to_string())];
    let pos1 = assignments.table[&(1, 0, "env".to_string(), "t".to_string())];
    assert_eq!(pos0, pos1, "same-typed tables must share the slot");
    assert!(
        dedup_info.type_mismatch_entries.is_empty(),
        "no mismatch must be recorded for identical types"
    );
}
