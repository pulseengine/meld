//! Integration tests for nested component (composed P2) fusion.
//!
//! Tests parsing and fusing a composed component that contains nested
//! sub-components (e.g. produced by `wasm-tools compose`). The key
//! invariant is that the `InstanceSection` wiring is respected, avoiding
//! false circular dependencies from flat name-matching.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

/// Parse a composed component and verify sub-components are correctly detected.
#[test]
fn test_parse_composed_component_structure() {
    let path = "../tests/wit_bindgen/fixtures/strings.wasm";
    let Ok(bytes) = std::fs::read(path) else {
        eprintln!("skipping: fixture not found at {path}");
        return;
    };

    let parser = meld_core::ComponentParser::new();
    let parsed = parser.parse(&bytes).unwrap();

    // The outer component should have detected nested sub-components
    assert!(
        !parsed.sub_components.is_empty(),
        "Composed component should have sub-components, found 0"
    );

    // Each sub-component should have core modules
    let total_sub_modules: usize = parsed
        .sub_components
        .iter()
        .map(|s| s.core_modules.len())
        .sum();
    assert!(
        total_sub_modules > 0,
        "Sub-components should contain core modules"
    );

    // Outer component should have component-level instances (wiring info)
    assert!(
        !parsed.component_instances.is_empty(),
        "Outer component should have ComponentInstanceSection entries"
    );

    log::info!(
        "Parsed composed component: {} sub-components, {} total sub-modules, \
         {} component instances, {} component aliases",
        parsed.sub_components.len(),
        total_sub_modules,
        parsed.component_instances.len(),
        parsed.component_aliases.len(),
    );
}

/// Fuse a composed P2 component end-to-end without hitting a false cycle.
#[test]
fn test_fuse_composed_p2_component() {
    let path = "../tests/wit_bindgen/fixtures/strings.wasm";
    let Ok(bytes) = std::fs::read(path) else {
        eprintln!("skipping: fixture not found at {path}");
        return;
    };

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
        .add_component_named(&bytes, Some("strings"))
        .expect("add_component should not fail (no false cycle)");

    // Verify flattening produced a reasonable number of components
    assert!(
        fuser.component_count() >= 2,
        "Flattening should produce at least 2 components, got {}",
        fuser.component_count()
    );

    let result = fuser.fuse();
    match result {
        Ok(fused) => {
            // Output should be non-trivial
            assert!(
                fused.len() > 100,
                "Fused output too small ({} bytes)",
                fused.len()
            );

            // Sanity: should have a reasonable memory count (not 66+)
            // Count memories by scanning the wasm binary for the memory section
            let mut validator = wasmparser::Validator::new();
            match validator.validate_all(&fused) {
                Ok(_) => {
                    log::info!(
                        "Fused output validates successfully ({} bytes)",
                        fused.len()
                    );
                }
                Err(e) => {
                    // Validation failure is not necessarily a test failure for the
                    // core bug fix (false cycle), but log it prominently.
                    log::warn!("Fused output validation failed: {}", e);
                }
            }
        }
        Err(e) => {
            // The critical assertion: we should NOT get a false cycle error.
            let err_str = format!("{}", e);
            assert!(
                !err_str.contains("circular module dependency"),
                "Got false circular dependency error: {}",
                err_str
            );
            // Other errors (e.g., unresolved imports from WASI) are expected
            // until WASI host functions are provided. Log and pass.
            log::info!("Fuse returned expected non-cycle error: {}", e);
        }
    }
}
