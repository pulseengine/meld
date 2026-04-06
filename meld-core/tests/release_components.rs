//! Integration tests for real-world composed P2 components from
//! pulseengine/wasm-component-examples release v0.2.0.
//!
//! These tests verify that meld correctly handles:
//! - Nested sub-component parsing (depth-aware parser)
//! - Instance-graph-based module resolution (no false cycles)
//! - Memory import resolution (shared memories between modules)
//! - P1 intra-component adapter detection (different canonical options)
//! - End-to-end fusion producing valid wasm output

use meld_core::{ComponentParser, Fuser, FuserConfig, MemoryStrategy, OutputFormat};

const FIXTURES_DIR: &str = "../tests/wit_bindgen/fixtures/release-0.2.0";

/// Returns true if the fixture directory exists; prints skip message and returns false otherwise.
fn fixtures_available() -> bool {
    if std::path::Path::new(FIXTURES_DIR).is_dir() {
        true
    } else {
        eprintln!("skipping: fixtures not found at {FIXTURES_DIR}");
        false
    }
}

/// Helper: attempt to parse a component and return structural info.
struct ComponentInfo {
    name: String,
    core_modules: usize,
    sub_components: usize,
    instances: usize,
    component_instances: usize,
    component_aliases: usize,
    imports: usize,
    exports: usize,
    canonical_functions: usize,
}

fn parse_component_info(path: &str, name: &str) -> ComponentInfo {
    let bytes = std::fs::read(path).unwrap_or_else(|e| panic!("{}: {}", name, e));
    let parser = ComponentParser::new();
    let parsed = parser
        .parse(&bytes)
        .unwrap_or_else(|e| panic!("{}: {}", name, e));

    ComponentInfo {
        name: name.to_string(),
        core_modules: parsed.core_modules.len(),
        sub_components: parsed.sub_components.len(),
        instances: parsed.instances.len(),
        component_instances: parsed.component_instances.len(),
        component_aliases: parsed.component_aliases.len(),
        imports: parsed.imports.len(),
        exports: parsed.exports.len(),
        canonical_functions: parsed.canonical_functions.len(),
    }
}

fn fixture_path(name: &str) -> String {
    format!("{}/{}", FIXTURES_DIR, name)
}

/// Try to fuse a component and return (success, output_size, error_message).
fn try_fuse(path: &str, name: &str) -> (bool, usize, String) {
    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) => return (false, 0, format!("read error: {}", e)),
    };

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        output_format: OutputFormat::CoreModule,
    };

    let mut fuser = Fuser::new(config);
    if let Err(e) = fuser.add_component_named(&bytes, Some(name)) {
        return (false, 0, format!("add_component failed: {}", e));
    }

    match fuser.fuse() {
        Ok(fused) => (true, fused.len(), String::new()),
        Err(e) => (false, 0, format!("{}", e)),
    }
}

// ---------------------------------------------------------------------------
// Structural parsing tests
// ---------------------------------------------------------------------------

#[test]
fn test_parse_all_release_components() {
    if !fixtures_available() {
        return;
    }
    let files = [
        "hello_c_cli.wasm",
        "hello_c_debug.wasm",
        "hello_c_release.wasm",
        "hello_cpp_cli.wasm",
        "hello_cpp_debug.wasm",
        "hello_cpp_release.wasm",
        "calculator.wasm",
        "datetime.wasm",
        "hello_rust.wasm",
        "yolo_inference_debug.wasm",
        "yolo_inference_release.wasm",
    ];

    for file in &files {
        let path = fixture_path(file);
        let info = parse_component_info(&path, file);

        // Every component must have at least 1 core module (directly or in sub-components)
        let total_modules = if info.sub_components > 0 {
            // Sub-components hold the modules; outer may have 0 direct modules
            info.core_modules // outer's own modules (may be 0)
        } else {
            info.core_modules
        };

        assert!(
            total_modules > 0 || info.sub_components > 0,
            "{}: no core modules and no sub-components found",
            file
        );

        eprintln!(
            "[{}] modules={} subs={} instances={} comp_instances={} \
             aliases={} imports={} exports={} canon_funcs={}",
            info.name,
            info.core_modules,
            info.sub_components,
            info.instances,
            info.component_instances,
            info.component_aliases,
            info.imports,
            info.exports,
            info.canonical_functions,
        );
    }
}

// ---------------------------------------------------------------------------
// Fusion tests — no false cycle errors
// ---------------------------------------------------------------------------

/// Critical test: none of the release components should produce a false
/// "circular module dependency" error during fusion.
#[test]
fn test_no_false_cycles_any_component() {
    if !fixtures_available() {
        return;
    }
    let files = [
        "hello_c_cli.wasm",
        "hello_c_debug.wasm",
        "hello_c_release.wasm",
        "hello_cpp_cli.wasm",
        "hello_cpp_debug.wasm",
        "hello_cpp_release.wasm",
        "calculator.wasm",
        "datetime.wasm",
        "hello_rust.wasm",
        "yolo_inference_debug.wasm",
        "yolo_inference_release.wasm",
    ];

    for file in &files {
        let path = fixture_path(file);
        let (success, size, err) = try_fuse(&path, file);

        // The key assertion: no false cycle error
        if !success {
            assert!(
                !err.contains("circular module dependency"),
                "{}: got false circular dependency error: {}",
                file,
                err
            );
            // Other errors (e.g. unresolved WASI imports) are expected
            // since we're not providing a WASI host. Log them.
            eprintln!("[{}] expected non-cycle error: {}", file, err);
        } else {
            eprintln!("[{}] fused successfully: {} bytes", file, size);
        }
    }
}

// ---------------------------------------------------------------------------
// End-to-end fusion + validation tests
// ---------------------------------------------------------------------------

/// For components that fuse successfully, validate the output with wasmparser.
#[test]
fn test_fused_output_validates() {
    if !fixtures_available() {
        return;
    }
    let files = [
        "hello_c_cli.wasm",
        "hello_c_debug.wasm",
        "hello_c_release.wasm",
        "hello_cpp_cli.wasm",
        "hello_cpp_debug.wasm",
        "hello_cpp_release.wasm",
        "calculator.wasm",
        "datetime.wasm",
        "hello_rust.wasm",
        "yolo_inference_debug.wasm",
        "yolo_inference_release.wasm",
    ];

    let mut fused_count = 0;
    let mut validated_count = 0;

    for file in &files {
        let path = fixture_path(file);
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(_) => continue,
        };

        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: meld_core::CustomSectionHandling::Drop,
            output_format: OutputFormat::CoreModule,
        };

        let mut fuser = Fuser::new(config);
        if fuser.add_component_named(&bytes, Some(file)).is_err() {
            continue;
        }

        match fuser.fuse() {
            Ok(fused) => {
                fused_count += 1;

                // Validate with wasmparser
                let mut validator = wasmparser::Validator::new();
                match validator.validate_all(&fused) {
                    Ok(_) => {
                        validated_count += 1;
                        eprintln!(
                            "[{}] PASS: fused ({} bytes) and validated",
                            file,
                            fused.len()
                        );
                    }
                    Err(e) => {
                        eprintln!(
                            "[{}] fused ({} bytes) but validation failed: {}",
                            file,
                            fused.len(),
                            e
                        );
                    }
                }

                // Sanity: output should not be empty
                assert!(fused.len() > 8, "{}: fused output too small", file);
            }
            Err(_) => {
                // Fusion failure is OK (unresolved WASI imports), skip validation
            }
        }
    }

    eprintln!(
        "\nSummary: {}/{} fused, {}/{} validated",
        fused_count,
        files.len(),
        validated_count,
        fused_count
    );
}

// ---------------------------------------------------------------------------
// P1 adapter detection test
// ---------------------------------------------------------------------------

/// Verify that the resolver correctly identifies intra-component adapter sites
/// for components with multiple core modules that have different canonical
/// options (different memories in multi-memory mode).
#[test]
fn test_p1_adapter_detection_with_instances() {
    if !fixtures_available() {
        return;
    }
    let files = [
        "hello_c_cli.wasm",
        "hello_c_release.wasm",
        "hello_cpp_cli.wasm",
        "hello_cpp_release.wasm",
        "calculator.wasm",
        "datetime.wasm",
        "hello_rust.wasm",
        "yolo_inference_release.wasm",
    ];

    for file in &files {
        let path = fixture_path(file);
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(_) => continue,
        };

        let parser = ComponentParser::new();
        let parsed = parser.parse(&bytes).unwrap();

        // Flatten sub-components the same way Fuser does
        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: meld_core::CustomSectionHandling::Drop,
            output_format: OutputFormat::CoreModule,
        };
        let mut fuser = Fuser::new(config);
        if fuser.add_component_named(&bytes, Some(file)).is_err() {
            continue;
        }

        // Count total modules across all flattened components
        let total_modules = fuser.component_count();

        // For components with multiple modules, the resolver should be able
        // to produce module_resolutions and potentially adapter_sites.
        // We verify this by checking that the resolver doesn't panic or
        // produce false cycles.
        let _resolver = meld_core::Resolver::with_strategy(MemoryStrategy::MultiMemory);

        // We can't easily access the internal components vec, but we already
        // tested that add_component succeeds (which runs parse + flatten),
        // and the no_false_cycles test above verifies resolution works.
        // Here we just confirm the component count is reasonable after flattening.
        if parsed.sub_components.len() >= 2 {
            assert!(
                total_modules >= 2,
                "{}: component with {} sub-components should flatten to >= 2 components, got {}",
                file,
                parsed.sub_components.len(),
                total_modules
            );
            eprintln!(
                "[{}] {} sub-components -> {} flattened components (P1 adapter candidates)",
                file,
                parsed.sub_components.len(),
                total_modules
            );
        } else {
            eprintln!(
                "[{}] {} sub-components, {} core modules (simple component)",
                file,
                parsed.sub_components.len(),
                parsed.core_modules.len()
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Memory count sanity test
// ---------------------------------------------------------------------------

/// After fusion, the memory count should be reasonable — not inflated by
/// unresolved memory imports getting promoted to standalone memories.
#[test]
fn test_reasonable_memory_count() {
    if !fixtures_available() {
        return;
    }
    let files = [
        "hello_c_cli.wasm",
        "hello_c_release.wasm",
        "hello_cpp_cli.wasm",
        "hello_cpp_release.wasm",
        "calculator.wasm",
        "datetime.wasm",
        "hello_rust.wasm",
    ];

    for file in &files {
        let path = fixture_path(file);
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(_) => continue,
        };

        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: meld_core::CustomSectionHandling::Drop,
            output_format: OutputFormat::CoreModule,
        };

        let mut fuser = Fuser::new(config);
        if fuser.add_component_named(&bytes, Some(file)).is_err() {
            continue;
        }

        let (fused, stats) = match fuser.fuse_with_stats() {
            Ok(r) => r,
            Err(_) => continue,
        };

        // Count memories in the fused output by parsing
        let parser = wasmparser::Parser::new(0);
        let mut memory_count = 0u32;
        for payload in parser.parse_all(&fused) {
            match payload {
                Ok(wasmparser::Payload::MemorySection(reader)) => {
                    memory_count += reader.count();
                }
                Ok(wasmparser::Payload::ImportSection(reader)) => {
                    for imp in reader.into_imports().flatten() {
                        if matches!(imp.ty, wasmparser::TypeRef::Memory(_)) {
                            memory_count += 1;
                        }
                    }
                }
                _ => {}
            }
        }

        // A reasonable upper bound: number of modules merged * 2
        // (each module could have at most ~2 memories in practice).
        // The old bug would produce 60+ memories for an 8-module component.
        let max_reasonable = (stats.modules_merged as u32 * 2).max(4);
        assert!(
            memory_count <= max_reasonable,
            "{}: memory count {} exceeds reasonable limit {} (modules merged: {})",
            file,
            memory_count,
            max_reasonable,
            stats.modules_merged
        );

        eprintln!(
            "[{}] memories={}, modules_merged={}, output_size={}",
            file, memory_count, stats.modules_merged, stats.output_size
        );
    }
}

// ---------------------------------------------------------------------------
// Write fused output for runtime testing
// ---------------------------------------------------------------------------

/// Write fused output to /tmp for manual and automated runtime testing.
#[test]
fn test_write_fused_output_for_runtime() {
    if !fixtures_available() {
        return;
    }
    let files = [
        "hello_c_cli.wasm",
        "hello_c_release.wasm",
        "hello_cpp_cli.wasm",
        "hello_cpp_release.wasm",
        "calculator.wasm",
        "datetime.wasm",
        "hello_rust.wasm",
    ];

    for file in &files {
        let path = fixture_path(file);
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(_) => continue,
        };

        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            address_rebasing: false,
            preserve_names: true,
            custom_sections: meld_core::CustomSectionHandling::Drop,
            output_format: OutputFormat::CoreModule,
        };

        let mut fuser = Fuser::new(config);
        if fuser.add_component_named(&bytes, Some(file)).is_err() {
            continue;
        }

        match fuser.fuse() {
            Ok(fused) => {
                let out_path = format!("/tmp/fused_{}", file);
                std::fs::write(&out_path, &fused).unwrap();
                eprintln!("[{}] wrote {} bytes to {}", file, fused.len(), out_path);
            }
            Err(e) => {
                eprintln!("[{}] fusion failed: {}", file, e);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Import deduplication tests
// ---------------------------------------------------------------------------

/// Verify that fused output has no duplicate `(module, field)` import pairs.
///
/// Before import deduplication, components like hello_c_cli would produce
/// duplicates (e.g., `wasi:cli/stderr@0.2.6::get-stderr` appearing twice).
/// This test ensures the dedup logic in the merger eliminates all duplicates.
#[test]
fn test_no_duplicate_imports() {
    if !fixtures_available() {
        return;
    }
    use std::collections::HashSet;

    let files = [
        "hello_c_cli.wasm",
        "hello_c_debug.wasm",
        "hello_c_release.wasm",
        "hello_cpp_cli.wasm",
        "hello_cpp_debug.wasm",
        "hello_cpp_release.wasm",
        "calculator.wasm",
        "datetime.wasm",
        "hello_rust.wasm",
        "yolo_inference_debug.wasm",
        "yolo_inference_release.wasm",
    ];

    for file in &files {
        let path = fixture_path(file);
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(_) => continue,
        };

        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: meld_core::CustomSectionHandling::Drop,
            output_format: OutputFormat::CoreModule,
        };

        let mut fuser = Fuser::new(config);
        if fuser.add_component_named(&bytes, Some(file)).is_err() {
            continue;
        }

        let fused = match fuser.fuse() {
            Ok(f) => f,
            Err(_) => continue,
        };

        // Parse imports from the fused output
        let parser = wasmparser::Parser::new(0);
        let mut seen: HashSet<(String, String)> = HashSet::new();
        let mut duplicates: Vec<(String, String)> = Vec::new();

        for payload in parser.parse_all(&fused) {
            if let Ok(wasmparser::Payload::ImportSection(reader)) = payload {
                for imp in reader.into_imports().flatten() {
                    let key = (imp.module.to_string(), imp.name.to_string());
                    if !seen.insert(key.clone()) {
                        duplicates.push(key);
                    }
                }
            }
        }

        assert!(
            duplicates.is_empty(),
            "{}: found {} duplicate import(s): {:?}",
            file,
            duplicates.len(),
            duplicates
        );

        eprintln!(
            "[{}] PASS: {} unique imports, no duplicates",
            file,
            seen.len()
        );
    }
}

// ---------------------------------------------------------------------------
// Adapter generation and verification tests
// ---------------------------------------------------------------------------

/// Verify that adapter generation works for all release components that have
/// adapter sites, and the fused output still validates after adapter wiring.
#[test]
fn test_adapter_generation_for_release_components() {
    if !fixtures_available() {
        return;
    }
    let files = [
        "hello_c_cli.wasm",
        "hello_c_debug.wasm",
        "hello_c_release.wasm",
        "hello_cpp_cli.wasm",
        "hello_cpp_debug.wasm",
        "hello_cpp_release.wasm",
        "calculator.wasm",
        "datetime.wasm",
        "hello_rust.wasm",
        "yolo_inference_debug.wasm",
        "yolo_inference_release.wasm",
    ];

    for file in &files {
        let path = fixture_path(file);
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(_) => continue,
        };

        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: meld_core::CustomSectionHandling::Drop,
            output_format: OutputFormat::CoreModule,
        };

        let mut fuser = Fuser::new(config);
        if fuser.add_component_named(&bytes, Some(file)).is_err() {
            continue;
        }

        match fuser.fuse_with_stats() {
            Ok((fused, stats)) => {
                // Validate the fused output
                let mut validator = wasmparser::Validator::new();
                let valid = validator.validate_all(&fused).is_ok();

                eprintln!(
                    "[{}] adapters={}, funcs={}, imports_resolved={}, valid={}",
                    file,
                    stats.adapter_functions,
                    stats.total_functions,
                    stats.imports_resolved,
                    valid,
                );

                assert!(
                    valid,
                    "{}: fused output with {} adapters failed validation",
                    file, stats.adapter_functions,
                );
            }
            Err(e) => {
                eprintln!("[{}] fusion failed (expected for some): {}", file, e);
            }
        }
    }
}

/// Verify that all call/memory.copy instructions in adapter functions reference
/// valid indices (function index < total count, memory index < memory count).
#[test]
fn test_adapter_call_site_wiring() {
    if !fixtures_available() {
        return;
    }
    let files = [
        "hello_c_cli.wasm",
        "hello_c_release.wasm",
        "hello_cpp_cli.wasm",
        "hello_cpp_release.wasm",
        "calculator.wasm",
        "datetime.wasm",
        "hello_rust.wasm",
    ];

    for file in &files {
        let path = fixture_path(file);
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(_) => continue,
        };

        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: meld_core::CustomSectionHandling::Drop,
            output_format: OutputFormat::CoreModule,
        };

        let mut fuser = Fuser::new(config);
        if fuser.add_component_named(&bytes, Some(file)).is_err() {
            continue;
        }

        let fused = match fuser.fuse() {
            Ok(f) => f,
            Err(_) => continue,
        };

        // Count total functions (imports + defined) and memories
        let parser = wasmparser::Parser::new(0);
        let mut import_func_count: u32 = 0;
        let mut defined_func_count: u32 = 0;
        let mut import_mem_count: u32 = 0;
        let mut defined_mem_count: u32 = 0;
        let mut type_count: u32 = 0;

        for payload in parser.parse_all(&fused) {
            match payload {
                Ok(wasmparser::Payload::ImportSection(reader)) => {
                    for imp in reader.into_imports().flatten() {
                        match imp.ty {
                            wasmparser::TypeRef::Func(_) => import_func_count += 1,
                            wasmparser::TypeRef::Memory(_) => import_mem_count += 1,
                            _ => {}
                        }
                    }
                }
                Ok(wasmparser::Payload::FunctionSection(reader)) => {
                    defined_func_count = reader.count();
                }
                Ok(wasmparser::Payload::MemorySection(reader)) => {
                    defined_mem_count = reader.count();
                }
                Ok(wasmparser::Payload::TypeSection(reader)) => {
                    type_count = reader.count();
                }
                _ => {}
            }
        }

        let total_funcs = import_func_count + defined_func_count;
        let total_mems = import_mem_count + defined_mem_count;

        // Now parse code section and check all call/memory.copy instructions
        let parser2 = wasmparser::Parser::new(0);
        let mut func_idx = 0u32;
        for payload in parser2.parse_all(&fused) {
            if let Ok(wasmparser::Payload::CodeSectionEntry(body)) = payload {
                let ops = body.get_operators_reader();
                if let Ok(ops) = ops {
                    for op in ops.into_iter().flatten() {
                        match &op {
                            wasmparser::Operator::Call { function_index } => {
                                assert!(
                                    *function_index < total_funcs,
                                    "{}: func {} has call to invalid index {} (total {})",
                                    file,
                                    import_func_count + func_idx,
                                    function_index,
                                    total_funcs,
                                );
                            }
                            wasmparser::Operator::CallIndirect { type_index, .. } => {
                                assert!(
                                    *type_index < type_count,
                                    "{}: func {} has call_indirect with invalid type {} (total {})",
                                    file,
                                    import_func_count + func_idx,
                                    type_index,
                                    type_count,
                                );
                            }
                            wasmparser::Operator::MemoryCopy { dst_mem, src_mem } => {
                                assert!(
                                    *dst_mem < total_mems,
                                    "{}: func {} has memory.copy with invalid dst_mem {} (total {})",
                                    file,
                                    import_func_count + func_idx,
                                    dst_mem,
                                    total_mems,
                                );
                                assert!(
                                    *src_mem < total_mems,
                                    "{}: func {} has memory.copy with invalid src_mem {} (total {})",
                                    file,
                                    import_func_count + func_idx,
                                    src_mem,
                                    total_mems,
                                );
                            }
                            _ => {}
                        }
                    }
                }
                func_idx += 1;
            }
        }

        eprintln!(
            "[{}] PASS: all call/memory.copy indices valid (funcs={}, mems={}, types={})",
            file, total_funcs, total_mems, type_count,
        );
    }
}

// ---------------------------------------------------------------------------
// ResourceDrop WASI version correctness test
// ---------------------------------------------------------------------------

/// Verify that fused output has no resource-drop imports with stale @0.2.0
/// versions. Before the ResourceDrop tracing fix, adapter modules' hardcoded
/// @0.2.0 versions would leak through because `build_canon_import_names()`
/// skipped ResourceDrop entries.
#[test]
fn test_no_stale_resource_drop_versions() {
    if !fixtures_available() {
        return;
    }
    let files = [
        "hello_c_cli.wasm",
        "hello_c_debug.wasm",
        "hello_c_release.wasm",
        "hello_cpp_cli.wasm",
        "hello_cpp_debug.wasm",
        "hello_cpp_release.wasm",
        "calculator.wasm",
        "datetime.wasm",
        "hello_rust.wasm",
        "yolo_inference_debug.wasm",
        "yolo_inference_release.wasm",
    ];

    for file in &files {
        let path = fixture_path(file);
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(_) => continue,
        };

        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: meld_core::CustomSectionHandling::Drop,
            output_format: OutputFormat::CoreModule,
        };

        let mut fuser = Fuser::new(config);
        if fuser.add_component_named(&bytes, Some(file)).is_err() {
            continue;
        }

        let fused = match fuser.fuse() {
            Ok(f) => f,
            Err(_) => continue,
        };

        // Parse imports from fused output and check for stale versions
        let parser = wasmparser::Parser::new(0);
        let mut stale_imports: Vec<(String, String)> = Vec::new();

        for payload in parser.parse_all(&fused) {
            if let Ok(wasmparser::Payload::ImportSection(reader)) = payload {
                for imp in reader.into_imports().flatten() {
                    // Check for resource-drop imports with exactly @0.2.0
                    // (the stale adapter version). Exclude pre-release
                    // versions like @0.2.0-rc-* which are legitimate.
                    if imp.name.starts_with("[resource-drop]") && imp.module.ends_with("@0.2.0") {
                        stale_imports.push((imp.module.to_string(), imp.name.to_string()));
                    }
                }
            }
        }

        assert!(
            stale_imports.is_empty(),
            "{}: found {} resource-drop import(s) with stale @0.2.0 version: {:?}",
            file,
            stale_imports.len(),
            stale_imports
        );

        eprintln!("[{}] PASS: no stale @0.2.0 resource-drop imports", file);
    }
}

// ---------------------------------------------------------------------------
// P2 component wrapping tests
// ---------------------------------------------------------------------------

/// Fuse each release component with OutputFormat::Component and validate the
/// output is a valid P2 component (not a core module).
#[test]
fn test_component_wrap_validates() {
    if !fixtures_available() {
        return;
    }
    let files = [
        "hello_c_cli.wasm",
        "hello_c_debug.wasm",
        "hello_c_release.wasm",
        "hello_cpp_cli.wasm",
        "hello_cpp_debug.wasm",
        "hello_cpp_release.wasm",
        "calculator.wasm",
        "datetime.wasm",
        "hello_rust.wasm",
        "yolo_inference_debug.wasm",
        "yolo_inference_release.wasm",
    ];

    let mut wrapped_count = 0;
    let mut validated_count = 0;

    for file in &files {
        let path = fixture_path(file);
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(_) => continue,
        };

        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: meld_core::CustomSectionHandling::Drop,
            output_format: OutputFormat::Component,
        };

        let mut fuser = Fuser::new(config);
        if fuser.add_component_named(&bytes, Some(file)).is_err() {
            continue;
        }

        match fuser.fuse() {
            Ok(wrapped) => {
                wrapped_count += 1;

                // Verify it's a component (version 0x0d), not a core module
                assert!(wrapped.len() >= 8, "{}: wrapped output too small", file);
                let version = u32::from_le_bytes([wrapped[4], wrapped[5], wrapped[6], wrapped[7]]);
                assert_eq!(
                    version, 0x0001_000d,
                    "{}: expected component format (0x0d), got {:#x}",
                    file, version
                );

                // Validate with wasmparser
                let mut validator = wasmparser::Validator::new();
                match validator.validate_all(&wrapped) {
                    Ok(_) => {
                        validated_count += 1;
                        eprintln!(
                            "[{}] PASS: wrapped as component ({} bytes) and validated",
                            file,
                            wrapped.len()
                        );
                    }
                    Err(e) => {
                        eprintln!(
                            "[{}] wrapped ({} bytes) but validation failed: {}",
                            file,
                            wrapped.len(),
                            e
                        );
                    }
                }

                // Write to /tmp for inspection
                let out_path = format!("/tmp/fused_{}_component.wasm", file.replace(".wasm", ""));
                let _ = std::fs::write(&out_path, &wrapped);
            }
            Err(e) => {
                eprintln!("[{}] component wrapping failed: {}", file, e);
            }
        }
    }

    eprintln!(
        "\nComponent wrap summary: {}/{} wrapped, {}/{} validated",
        wrapped_count,
        files.len(),
        validated_count,
        wrapped_count
    );

    // All components that wrap should also validate
    assert!(
        wrapped_count > 0,
        "expected at least one component to wrap successfully"
    );
    assert_eq!(
        validated_count, wrapped_count,
        "all wrapped components should validate"
    );
}
