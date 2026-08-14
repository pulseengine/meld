//! Merger unit tests (part B): realloc/memory-index population, cabi
//! realloc exports, #298 grow-guard, multiply-instantiated guards, and
//! LS-A resource/init-expr coverage. Split out of the original inline
//! `mod tests`; see also `tests_a`.

use super::*;

/// Verify that `add_unresolved_imports` populates `import_memory_indices`
/// and `import_realloc_indices` with per-component values. Component 0's
/// import should reference memory 0, component 1's import should reference
/// memory 1.
#[test]
fn test_import_memory_and_realloc_indices_populated() {
    use crate::parser::{FuncType, ModuleExport, ModuleImport, ParsedComponent};
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    // Build two components, each with one module. Each module has:
    // - 1 unresolved func import (WASI-like)
    // - 1 memory
    // - 1 cabi_realloc export
    let make_module = |idx: usize| -> CoreModule {
        CoreModule {
            index: 0,
            bytes: Vec::new(),
            types: vec![
                // type 0: () -> ()  (for the unresolved import)
                FuncType {
                    params: vec![],
                    results: vec![],
                },
                // type 1: (i32, i32, i32, i32) -> i32  (cabi_realloc)
                FuncType {
                    params: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
                    results: vec![ValType::I32],
                },
            ],
            imports: vec![ModuleImport {
                module: "".to_string(),
                name: format!("{}", idx),
                kind: ImportKind::Function(0),
            }],
            exports: vec![ModuleExport {
                name: "cabi_realloc".to_string(),
                kind: ExportKind::Function,
                index: 1, // defined func 0 = func idx 1 (after 1 import)
            }],
            functions: vec![1], // one defined function with type 1 (cabi_realloc sig)
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
        }
    };

    let make_component = |idx: usize| -> ParsedComponent {
        ParsedComponent {
            name: None,
            core_modules: vec![make_module(idx)],
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
    };

    let components = vec![make_component(0), make_component(1)];

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

    let merger = Merger::new(MemoryStrategy::MultiMemory, false);
    let merged = merger
        .merge(&components, &graph)
        .expect("merge should succeed");

    // Should have 2 function imports (one per component)
    assert_eq!(
        merged.import_counts.func, 2,
        "multi-memory: two func imports"
    );

    // import_memory_indices should have one entry per func import
    assert_eq!(
        merged.import_memory_indices.len(),
        2,
        "should have memory index for each func import"
    );

    // Component 0's memory index and component 1's should differ
    // (each component's memory is separate in multi-memory mode)
    let mem_idx_0 = merged.import_memory_indices[0];
    let mem_idx_1 = merged.import_memory_indices[1];
    assert_ne!(
        mem_idx_0, mem_idx_1,
        "components must reference different memories: comp0={}, comp1={}",
        mem_idx_0, mem_idx_1,
    );

    // import_realloc_indices should also have one entry per func import
    assert_eq!(
        merged.import_realloc_indices.len(),
        2,
        "should have realloc index for each func import"
    );

    // Both components define cabi_realloc, so both should be Some
    assert!(
        merged.import_realloc_indices[0].is_some(),
        "component 0 should have a realloc index"
    );
    assert!(
        merged.import_realloc_indices[1].is_some(),
        "component 1 should have a realloc index"
    );

    // The realloc indices should be different (different merged functions)
    assert_ne!(
        merged.import_realloc_indices[0], merged.import_realloc_indices[1],
        "each component's realloc should map to a different merged function"
    );
}

/// Verify that in multi-memory mode, merging generates `cabi_realloc$N`
/// exports for component indices > 0.
#[test]
fn test_cabi_realloc_suffixed_exports_generated() {
    use crate::parser::{FuncType, ModuleExport, ModuleImport, ParsedComponent};
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    let make_module = |idx: usize| -> CoreModule {
        CoreModule {
            index: 0,
            bytes: Vec::new(),
            types: vec![
                FuncType {
                    params: vec![],
                    results: vec![],
                },
                FuncType {
                    params: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
                    results: vec![ValType::I32],
                },
            ],
            imports: vec![ModuleImport {
                module: "".to_string(),
                name: format!("{}", idx),
                kind: ImportKind::Function(0),
            }],
            exports: vec![ModuleExport {
                name: "cabi_realloc".to_string(),
                kind: ExportKind::Function,
                index: 1, // defined func 0 = wasm idx 1 (after 1 import)
            }],
            functions: vec![1], // cabi_realloc signature
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
        }
    };

    let make_component = |idx: usize| -> ParsedComponent {
        ParsedComponent {
            name: None,
            core_modules: vec![make_module(idx)],
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
    };

    let components = vec![make_component(0), make_component(1), make_component(2)];

    let graph = DependencyGraph {
        instantiation_order: vec![0, 1, 2],
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
                display_module: Some("wasi:io/error@0.2.6".to_string()),
                display_field: Some("drop".to_string()),
            },
            UnresolvedImport {
                component_idx: 1,
                module_idx: 0,
                module_name: "".to_string(),
                field_name: "0".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:io/error@0.2.6".to_string()),
                display_field: Some("drop".to_string()),
            },
            UnresolvedImport {
                component_idx: 2,
                module_idx: 0,
                module_name: "".to_string(),
                field_name: "0".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:io/error@0.2.6".to_string()),
                display_field: Some("drop".to_string()),
            },
        ],
    };

    let merger = Merger::new(MemoryStrategy::MultiMemory, false);
    let merged = merger
        .merge(&components, &graph)
        .expect("merge should succeed");

    // Component 0's cabi_realloc should be exported as "cabi_realloc" (plain)
    let has_plain = merged.exports.iter().any(|e| e.name == "cabi_realloc");
    assert!(has_plain, "component 0 should export plain cabi_realloc");

    // Component 1 should get cabi_realloc$1
    let has_suffixed_1 = merged.exports.iter().any(|e| e.name == "cabi_realloc$1");
    assert!(has_suffixed_1, "component 1 should export cabi_realloc$1");

    // Component 2 should get cabi_realloc$2
    let has_suffixed_2 = merged.exports.iter().any(|e| e.name == "cabi_realloc$2");
    assert!(has_suffixed_2, "component 2 should export cabi_realloc$2");

    // The suffixed exports should point to different function indices
    let realloc_1_idx = merged
        .exports
        .iter()
        .find(|e| e.name == "cabi_realloc$1")
        .unwrap()
        .index;
    let realloc_2_idx = merged
        .exports
        .iter()
        .find(|e| e.name == "cabi_realloc$2")
        .unwrap()
        .index;
    assert_ne!(
        realloc_1_idx, realloc_2_idx,
        "cabi_realloc$1 and cabi_realloc$2 must point to different functions"
    );
}

/// Verify that in SharedMemory mode, no `cabi_realloc$N` suffixed
/// exports are generated (only the plain `cabi_realloc` is present).
#[test]
fn test_shared_memory_no_suffixed_realloc_exports() {
    use crate::parser::{FuncType, ModuleExport, ModuleImport, ParsedComponent};
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    let make_module = |idx: usize| -> CoreModule {
        CoreModule {
            index: 0,
            bytes: Vec::new(),
            types: vec![
                FuncType {
                    params: vec![],
                    results: vec![],
                },
                FuncType {
                    params: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
                    results: vec![ValType::I32],
                },
            ],
            imports: vec![ModuleImport {
                module: "".to_string(),
                name: format!("{}", idx),
                kind: ImportKind::Function(0),
            }],
            exports: vec![ModuleExport {
                name: "cabi_realloc".to_string(),
                kind: ExportKind::Function,
                index: 1,
            }],
            functions: vec![1],
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
        }
    };

    let make_component = |idx: usize| -> ParsedComponent {
        ParsedComponent {
            name: None,
            core_modules: vec![make_module(idx)],
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
    };

    let components = vec![make_component(0), make_component(1)];

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
                display_module: Some("wasi:io/error@0.2.6".to_string()),
                display_field: Some("drop".to_string()),
            },
            UnresolvedImport {
                component_idx: 1,
                module_idx: 0,
                module_name: "".to_string(),
                field_name: "0".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:io/error@0.2.6".to_string()),
                display_field: Some("drop".to_string()),
            },
        ],
    };

    let merger = Merger::new(MemoryStrategy::SharedMemory, false);
    let merged = merger
        .merge(&components, &graph)
        .expect("merge should succeed");

    // SharedMemory should NOT produce cabi_realloc$1
    let has_suffixed = merged
        .exports
        .iter()
        .any(|e| e.name.starts_with("cabi_realloc$"));
    assert!(
        !has_suffixed,
        "shared-memory mode must not generate cabi_realloc$N exports, \
         but found: {:?}",
        merged
            .exports
            .iter()
            .filter(|e| e.name.starts_with("cabi_realloc$"))
            .map(|e| &e.name)
            .collect::<Vec<_>>()
    );
}

/// #298 kill-criterion oracle (in-repo reproduction).
///
/// Until now this failure was only reproducible *externally* — via gale's
/// `crates/gale-app-demo/dissolve.sh` on a real wit-bindgen component pair.
/// This pins it inside meld: fusing an all-scalar-boundary component pair in
/// the real MCU config (`SharedMemory` ⟹ `address_rebasing = true`, exactly
/// what `lib.rs` forces for shared memory) currently **hard-fails** because
/// the vestigial canonical-ABI allocator's `memory.grow` (here standing in
/// for `cabi_realloc → … → $sbrk → memory.grow`) reaches the address-rebase
/// rewriter, which rejects `memory.grow` (`rewriter.rs` `MemoryGrow` arm).
///
/// The boundary between the two components is fully internalized and scalar,
/// so the allocator is provably dead — but the rewrite chokes on it *during
/// merge*, before any DCE/reachability pass could run. That ordering is the
/// crux of #298 (and why #298 ⟺ #299 are coupled).
///
/// This asserts **today's** behavior (the hard-fail). When the #298
/// dead-allocator handling lands, this test goes red — at which point its
/// assertion must flip to the success criterion: merge succeeds, the fused
/// core exports **0** `cabi_realloc`, and contains **0** `memory.grow`.
#[test]
fn test_298_vestigial_grow_blocks_shared_rebase_fusion() {
    use crate::parser::{FuncType, ModuleExport, ModuleImport, ParsedComponent};
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    // A real core module whose exported `cabi_realloc` body contains a
    // `memory.grow` — the canonical-ABI allocator meld must learn to drop.
    let src = r#"(module
        (type (func))
        (type (func (param i32 i32 i32 i32) (result i32)))
        (import "" "0" (func (type 0)))
        (memory 1)
        (func (type 1)
            i32.const 1
            memory.grow
            drop
            i32.const 0)
        (export "cabi_realloc" (func 1)))"#;
    let module_bytes = wat::parse_str(src).expect("wat compiles");

    // Locate the code section payload range (the parser fills this in real
    // runs; we mirror it so `extract_function_body` reads real bytes).
    let mut code_range = None;
    for payload in wasmparser::Parser::new(0).parse_all(&module_bytes) {
        if let wasmparser::Payload::CodeSectionStart { range, .. } = payload.expect("payload") {
            code_range = Some((range.start, range.end));
        }
    }
    let code_range = code_range.expect("module has a code section");

    let make_module = move || -> CoreModule {
        CoreModule {
            index: 0,
            bytes: module_bytes.clone(),
            types: vec![
                FuncType {
                    params: vec![],
                    results: vec![],
                },
                FuncType {
                    params: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
                    results: vec![ValType::I32],
                },
            ],
            imports: vec![ModuleImport {
                module: "".to_string(),
                name: "0".to_string(),
                kind: ImportKind::Function(0),
            }],
            exports: vec![ModuleExport {
                name: "cabi_realloc".to_string(),
                kind: ExportKind::Function,
                index: 1, // imported func 0, defined func = wasm idx 1
            }],
            functions: vec![1], // one defined func, type 1
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
            code_section_range: Some(code_range),
            global_section_range: None,
            element_section_range: None,
            data_section_range: None,
        }
    };

    let make_component = |module: CoreModule| -> ParsedComponent {
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
    };

    let components = vec![make_component(make_module()), make_component(make_module())];

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
                display_module: Some("wasi:io/error@0.2.6".to_string()),
                display_field: Some("drop".to_string()),
            },
            UnresolvedImport {
                component_idx: 1,
                module_idx: 0,
                module_name: "".to_string(),
                field_name: "0".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("wasi:io/error@0.2.6".to_string()),
                display_field: Some("drop".to_string()),
            },
        ],
    };

    // Real MCU config: shared memory forces address rebasing.
    let merger = Merger::new(MemoryStrategy::SharedMemory, true);
    let result = merger.merge(&components, &graph);

    // TODO(#298): when the dead-allocator handling lands, flip this to:
    //   let merged = result.expect("fusion of a scalar boundary succeeds");
    //   assert!(!merged.exports.iter().any(|e| e.name.starts_with("cabi_realloc")));
    //   // and assert 0 memory.grow in the encoded core.
    let err = result.expect_err(
        "today: shared+rebase fusion must reject the vestigial allocator's memory.grow",
    );
    let msg = err.to_string();
    assert!(
        msg.contains("memory.grow"),
        "expected the memory.grow rebase rejection (the #298 coupling), got: {msg}"
    );
}

/// #298 positive control — validates the fork-side no-grow approach
/// (pulseengine/wit-bindgen `integration/embedded-rt-no-grow`, which backs
/// `cabi_realloc` with an embedder arena instead of `dlmalloc → $sbrk →
/// memory.grow`).
///
/// The hypothesis the fork branch rests on: a component whose `cabi_realloc`
/// carries **no** `memory.grow` already fuses under `--memory shared`
/// (⟹ `address_rebasing`) **today**, with no #298 fix — because the
/// rewriter only rejects `memory.grow`, nothing else about the allocator.
///
/// This faithfully mirrors the **real** fork output shape (verified against
/// `pulseengine/wit-bindgen@4753871d`, the `cabi-realloc-extern` feature):
/// `cabi_realloc` stays **exported** (so the same build still links on a
/// composing host like wasmtime) but its body **forwards to an imported**
/// `__cabi_arena_realloc(old_ptr, old_len, align, new_len) -> ptr` — the
/// embedder-provided bounded arena that traps on exhaustion instead of
/// calling `memory.grow`. The arena import is left **unresolved** (gale, the
/// embedder, links it post-fuse over one policy for the whole image).
///
/// This must SUCCEED and the fused core must (a) still export `cabi_realloc`
/// and (b) retain the `__cabi_arena_realloc` import (the embedder seam).
///
/// So the two fixes are complementary: the fork's no-grow `cabi_realloc`
/// unblocks the MCU path directly (belt), and #298's meld-side drop handles
/// the mixed/un-elided case (suspenders).
#[test]
fn test_298_fork_arena_realloc_fuses_under_shared_rebase_today() {
    use crate::parser::{FuncType, ModuleExport, ModuleImport, ParsedComponent};
    use crate::resolver::{DependencyGraph, UnresolvedImport};

    // The real fork shape: cabi_realloc forwards to the imported arena
    // function; NO memory.grow anywhere.
    let src = r#"(module
        (type (func (param i32 i32 i32 i32) (result i32)))
        (import "pulseengine:embedder/arena" "__cabi_arena_realloc" (func (type 0)))
        (memory 1)
        (func (type 0)
            local.get 0
            local.get 1
            local.get 2
            local.get 3
            call 0)
        (export "cabi_realloc" (func 1)))"#;
    let module_bytes = wat::parse_str(src).expect("wat compiles");

    let mut code_range = None;
    for payload in wasmparser::Parser::new(0).parse_all(&module_bytes) {
        if let wasmparser::Payload::CodeSectionStart { range, .. } = payload.expect("payload") {
            code_range = Some((range.start, range.end));
        }
    }
    let code_range = code_range.expect("module has a code section");

    let make_module = move || -> CoreModule {
        CoreModule {
            index: 0,
            bytes: module_bytes.clone(),
            types: vec![FuncType {
                params: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
                results: vec![ValType::I32],
            }],
            imports: vec![ModuleImport {
                module: "pulseengine:embedder/arena".to_string(),
                name: "__cabi_arena_realloc".to_string(),
                kind: ImportKind::Function(0),
            }],
            exports: vec![ModuleExport {
                name: "cabi_realloc".to_string(),
                kind: ExportKind::Function,
                index: 1, // imported arena func 0, defined cabi_realloc = wasm idx 1
            }],
            functions: vec![0],
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
            code_section_range: Some(code_range),
            global_section_range: None,
            element_section_range: None,
            data_section_range: None,
        }
    };

    let make_component = |module: CoreModule| -> ParsedComponent {
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
    };

    let components = vec![make_component(make_module()), make_component(make_module())];

    let graph = DependencyGraph {
        instantiation_order: vec![0, 1],
        resolved_imports: HashMap::new(),
        adapter_sites: Vec::new(),
        module_resolutions: Vec::new(),
        resource_graph: None,
        stream_pair_graph: None,
        reexporter_components: Vec::new(),
        reexporter_resources: Vec::new(),
        // The arena function is the embedder seam: gale provides it
        // post-fuse, so it stays unresolved through fusion.
        unresolved_imports: vec![
            UnresolvedImport {
                component_idx: 0,
                module_idx: 0,
                module_name: "pulseengine:embedder/arena".to_string(),
                field_name: "__cabi_arena_realloc".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("pulseengine:embedder/arena".to_string()),
                display_field: Some("__cabi_arena_realloc".to_string()),
            },
            UnresolvedImport {
                component_idx: 1,
                module_idx: 0,
                module_name: "pulseengine:embedder/arena".to_string(),
                field_name: "__cabi_arena_realloc".to_string(),
                kind: ImportKind::Function(0),
                display_module: Some("pulseengine:embedder/arena".to_string()),
                display_field: Some("__cabi_arena_realloc".to_string()),
            },
        ],
    };

    let merger = Merger::new(MemoryStrategy::SharedMemory, true);
    let merged = merger.merge(&components, &graph).expect(
        "a fork arena-backed (grow-free) realloc must fuse under shared+rebase TODAY \
         (no #298 needed)",
    );

    // Success under address-rebasing IS the grow-free proof: the rewriter
    // rejects any reachable `memory.grow` (see the kill-criterion oracle),
    // so a completed merge means no body grew memory. Both cabi_realloc
    // bodies survive (the suspenders #298 will later drop are belt here).
    assert_eq!(
        merged.functions.len(),
        2,
        "both arena-backed cabi_realloc bodies survive the rebase fuse"
    );

    // The fused core must still export cabi_realloc (kept present for a
    // composing host) ...
    assert!(
        merged.exports.iter().any(|e| e.name == "cabi_realloc"),
        "fused core keeps cabi_realloc exported (wasmtime-composability), \
         got exports: {:?}",
        merged.exports.iter().map(|e| &e.name).collect::<Vec<_>>()
    );

    // ... and must retain the __cabi_arena_realloc import — the embedder
    // seam gale links post-fuse. Without it the fused core could not
    // allocate, so meld must not drop or mis-wire it.
    assert!(
        merged
            .imports
            .iter()
            .any(|i| i.name == "__cabi_arena_realloc"),
        "fused core must retain the embedder arena import, got imports: {:?}",
        merged
            .imports
            .iter()
            .map(|i| format!("{}/{}", i.module, i.name))
            .collect::<Vec<_>>()
    );

    // #301: the retained import's module is in the recognized
    // `pulseengine:embedder` namespace, so meld preserves it as INTENTIONAL
    // embedder passthrough — not merely incidental survival of an unresolved
    // import. This ties the real fork fixture's module name to the explicit
    // recognition predicate the strict-resolution carve-out relies on.
    assert!(
        merged
            .imports
            .iter()
            .any(|i| i.name == "__cabi_arena_realloc"
                && crate::resolver::is_embedder_passthrough(&i.module)),
        "retained arena import must be recognized as embedder passthrough by namespace, \
         got imports: {:?}",
        merged
            .imports
            .iter()
            .map(|i| format!("{}/{}", i.module, i.name))
            .collect::<Vec<_>>()
    );
}

// -- SR-31: Multiply-instantiated module detection -------------------------

/// Helper to build a minimal ParsedComponent with given instances.
fn make_component_with_instances(
    instances: Vec<crate::parser::ComponentInstance>,
) -> ParsedComponent {
    ParsedComponent {
        name: None,
        core_modules: vec![],
        imports: vec![],
        exports: vec![],
        types: vec![],
        instances,
        canonical_functions: vec![],
        sub_components: vec![],
        component_aliases: vec![],
        component_instances: vec![],
        core_entity_order: vec![],
        component_func_defs: vec![],
        component_instance_defs: vec![],
        component_type_defs: vec![],
        original_size: 0,
        original_hash: String::new(),
        depth_0_sections: vec![],
        p3_async_features: vec![],
    }
}

/// LS-M-5 gate-convention regression: a component that
/// instantiates the same core module twice must be rejected at
/// merge time with `DuplicateModuleInstantiation`, never silently
/// mis-merged. This pins the detection-and-reject mitigation that
/// closes the LS-M-5 silent-corruption hazard. (Named to satisfy
/// the LS-N verification gate's `ls_<letter>_<num>_*` convention;
/// `test_duplicate_module_instantiation_rejected` below predates
/// the convention and is kept as-is.)
#[test]
fn ls_m_5_multiply_instantiated_module_rejected() {
    let comp = make_component_with_instances(vec![
        crate::parser::ComponentInstance {
            index: 0,
            kind: crate::parser::InstanceKind::Instantiate {
                module_idx: 2,
                args: vec![],
            },
        },
        crate::parser::ComponentInstance {
            index: 1,
            kind: crate::parser::InstanceKind::Instantiate {
                module_idx: 2, // same module instantiated again
                args: vec![],
            },
        },
    ]);
    let err = Merger::check_no_duplicate_instantiations(&[comp])
        .expect_err("multiply-instantiated module must be rejected");
    match err {
        Error::DuplicateModuleInstantiation {
            component_idx,
            module_idx,
        } => {
            assert_eq!(component_idx, 0);
            assert_eq!(module_idx, 2);
        }
        other => panic!("expected DuplicateModuleInstantiation, got {other:?}"),
    }
}

#[test]
fn test_duplicate_module_instantiation_rejected() {
    let comp = make_component_with_instances(vec![
        crate::parser::ComponentInstance {
            index: 0,
            kind: crate::parser::InstanceKind::Instantiate {
                module_idx: 0,
                args: vec![],
            },
        },
        crate::parser::ComponentInstance {
            index: 1,
            kind: crate::parser::InstanceKind::Instantiate {
                module_idx: 0, // duplicate!
                args: vec![],
            },
        },
    ]);
    let result = Merger::check_no_duplicate_instantiations(&[comp]);
    assert!(result.is_err());
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("instantiates core module 0 more than once"),
        "Error should mention duplicate module: {}",
        err_msg
    );
}

#[test]
fn test_single_instantiation_accepted() {
    let comp = make_component_with_instances(vec![
        crate::parser::ComponentInstance {
            index: 0,
            kind: crate::parser::InstanceKind::Instantiate {
                module_idx: 0,
                args: vec![],
            },
        },
        crate::parser::ComponentInstance {
            index: 1,
            kind: crate::parser::InstanceKind::Instantiate {
                module_idx: 1, // different module — OK
                args: vec![],
            },
        },
    ]);
    let result = Merger::check_no_duplicate_instantiations(&[comp]);
    assert!(result.is_ok());
}

#[test]
fn test_no_instances_accepted() {
    let comp = make_component_with_instances(vec![]);
    let result = Merger::check_no_duplicate_instantiations(&[comp]);
    assert!(result.is_ok());
}

// ---------------------------------------------------------------
// LS-A-11 — extended-const truncation in global initializers
// LS-A-15 — HashMap iteration non-determinism
//
// Shared empty-merged fixture used by both regression suites.
// ---------------------------------------------------------------

fn empty_merged_fixture() -> MergedModule {
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
        fused_function_names: std::collections::BTreeMap::new(),
        function_index_map: std::collections::HashMap::new(),
        memory_index_map: std::collections::HashMap::new(),
        table_index_map: std::collections::HashMap::new(),
        global_index_map: std::collections::HashMap::new(),
        type_index_map: std::collections::HashMap::new(),
        realloc_map: std::collections::HashMap::new(),
        import_counts: Default::default(),
        import_memory_indices: Vec::new(),
        import_realloc_indices: Vec::new(),
        resource_rep_by_component: std::collections::HashMap::new(),
        resource_new_by_component: std::collections::HashMap::new(),
        handle_tables: std::collections::HashMap::new(),
        task_return_shims: std::collections::HashMap::new(),
        async_result_globals: std::collections::HashMap::new(),
        segment_bases: std::collections::HashMap::new(),
    }
}

// LS-A-11: convert_init_expr must fold multi-op extended-const
// expressions (was previously truncating to the first operator).
#[test]
fn ls_a_11_convert_init_expr_folds_extended_const_i32_add() {
    // Init expr bytes WITHOUT trailing `end` (the function appends
    // it). Use small operands that fit in single-byte sleb (no sign
    // bit at position 6): i32.const 5, i32.const 10, i32.add → 15.
    let bytes: Vec<u8> = vec![0x41, 5, 0x41, 10, 0x6A];
    let merged = empty_merged_fixture();

    let expr = convert_init_expr(&bytes, 0, 0, &merged, &ValType::I32);

    let mut encoded = Vec::new();
    wasm_encoder::Encode::encode(&expr, &mut encoded);
    let mut expected = Vec::new();
    wasm_encoder::Encode::encode(&ConstExpr::i32_const(15), &mut expected);

    assert_eq!(
        encoded, expected,
        "convert_init_expr must fold (i32.const 5)(i32.const 10) i32.add \
         to i32.const 15; got bytes {encoded:?}",
    );
}

#[test]
fn ls_a_11_convert_init_expr_preserves_single_const() {
    // Regression: the fold path must not change behavior for a
    // simple single-const initializer.
    let bytes: Vec<u8> = vec![0x41, 5];
    let merged = empty_merged_fixture();

    let expr = convert_init_expr(&bytes, 0, 0, &merged, &ValType::I32);
    let mut encoded = Vec::new();
    wasm_encoder::Encode::encode(&expr, &mut encoded);
    let mut expected = Vec::new();
    wasm_encoder::Encode::encode(&ConstExpr::i32_const(5), &mut expected);
    assert_eq!(encoded, expected);
}

// LS-A-15: component_realloc_index fallback must be deterministic
// when multiple modules carry cabi_realloc (was hash-seed dependent).
#[test]
fn ls_a_15_component_realloc_index_picks_lowest_module_deterministically() {
    // Component 0 has reallocs at modules 1 (idx 10), 2 (idx 11),
    // and 3 (idx 12), but no module 0. The function must
    // deterministically pick the realloc bound to the LOWEST module
    // index (module 1 → idx 10), not whatever HashMap happens to
    // iterate first.
    //
    // Rebuilding the HashMap from scratch each iteration gives
    // each instance a fresh hash seed, so iteration order varies
    // across iterations — if the impl picked an arbitrary entry,
    // we'd see more than one observed value.
    let mut observed = std::collections::HashSet::new();
    for _ in 0..64 {
        let mut merged = empty_merged_fixture();
        merged.realloc_map.insert((0, 1), 10);
        merged.realloc_map.insert((0, 2), 11);
        merged.realloc_map.insert((0, 3), 12);
        let got = component_realloc_index(&merged, 0).unwrap();
        observed.insert(got);
    }
    assert_eq!(
        observed.len(),
        1,
        "component_realloc_index must return a deterministic value \
         across runs; saw {observed:?}",
    );
    assert!(
        observed.contains(&10),
        "lowest module index (1 → realloc 10) must be selected; \
         observed {observed:?}",
    );
}

#[test]
fn ls_a_15_component_realloc_index_prefers_module_0() {
    // Regression: when module 0 has a realloc, the function must
    // return it regardless of other modules in the map.
    let mut merged = empty_merged_fixture();
    merged.realloc_map.insert((0, 0), 100);
    merged.realloc_map.insert((0, 1), 200);
    assert_eq!(component_realloc_index(&merged, 0), Some(100));
}

// LS-A-19: find_exact_resource_import_idx must match the full
// `[resource-{rep,new}]<name>` import string exactly. The prior
// `imp.name.ends_with(rn)` form let `float` match both
// `[resource-rep]float` and `[resource-rep]bigfloat`, so the
// dedup-skip path would register the wrong import for the
// wrong-suffix component (silent cross-resource confusion at
// runtime, no host trap).
fn merged_import(name: &str) -> MergedImport {
    MergedImport {
        module: "test".to_string(),
        name: name.to_string(),
        entity_type: EntityType::Function(0),
        component_idx: None,
    }
}

#[test]
fn ls_a_19_exact_match_picks_float_not_bigfloat() {
    // imports[0] = [resource-rep]bigfloat
    // imports[1] = [resource-rep]float
    // Tracking has both indices. Asking for "[resource-rep]float"
    // must return 1, not 0 — even though the buggy ends_with
    // would have matched bigfloat first under some iteration
    // orders.
    let mut merged = empty_merged_fixture();
    merged.imports.push(merged_import("[resource-rep]bigfloat"));
    merged.imports.push(merged_import("[resource-rep]float"));
    merged
        .resource_rep_by_component
        .insert((0, "bigfloat".to_string()), 0);
    merged
        .resource_rep_by_component
        .insert((1, "float".to_string()), 1);

    let idx = find_exact_resource_import_idx(
        &merged.resource_rep_by_component,
        &merged.imports,
        "[resource-rep]float",
    );
    assert_eq!(
        idx,
        Some(1),
        "exact match must pick float (idx 1), not bigfloat"
    );
}

#[test]
fn ls_a_19_no_match_returns_none_even_with_suffix_collision() {
    // Only bigfloat in tracking, but caller asks for plain float.
    // The buggy ends_with("float") would have returned bigfloat's
    // index. Exact match must return None.
    let mut merged = empty_merged_fixture();
    merged.imports.push(merged_import("[resource-rep]bigfloat"));
    merged
        .resource_rep_by_component
        .insert((0, "bigfloat".to_string()), 0);

    let idx = find_exact_resource_import_idx(
        &merged.resource_rep_by_component,
        &merged.imports,
        "[resource-rep]float",
    );
    assert_eq!(
        idx, None,
        "no exact match for 'float' must return None even though \
         'bigfloat' shares the suffix",
    );
}

#[test]
fn ls_a_19_resource_new_lookup_is_also_exact() {
    // Same suffix-collision case for [resource-new] table.
    let mut merged = empty_merged_fixture();
    merged.imports.push(merged_import("[resource-new]bigfloat"));
    merged.imports.push(merged_import("[resource-new]float"));
    merged
        .resource_new_by_component
        .insert((0, "bigfloat".to_string()), 0);
    merged
        .resource_new_by_component
        .insert((1, "float".to_string()), 1);

    let idx = find_exact_resource_import_idx(
        &merged.resource_new_by_component,
        &merged.imports,
        "[resource-new]float",
    );
    assert_eq!(idx, Some(1));
}
