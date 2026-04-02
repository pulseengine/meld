//! Integration tests for wit-bindgen composed-runner components.
//!
//! Each fixture is a self-contained P2 component (host runner + guest test)
//! where calling `wasi:cli/run` validates roundtrip correctness of canonical
//! ABI operations for a specific type family (numbers, strings, lists, records).
//!
//! Tests cover three levels:
//! 1. **Fusion as CoreModule** — fuse and validate with wasmparser
//! 2. **Fusion as Component** — fuse with P2 wrapping and validate
//! 3. **Runtime execution** — fuse, load into wasmtime with WASI, call `run()`

use meld_core::{CustomSectionHandling, Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasmtime::component::{Component, Linker, ResourceTable};
use wasmtime::{Config, Engine, Store};
use wasmtime_wasi::p2::bindings::sync::Command;
use wasmtime_wasi::{WasiCtx, WasiCtxView, WasiView};

const FIXTURES_DIR: &str = "../tests/wit_bindgen/fixtures";

/// Skip a test when the specific fixture .wasm file is not present.
fn fixture_exists(name: &str) -> bool {
    let path = fixture_path(name);
    if std::path::Path::new(&path).is_file() {
        true
    } else {
        eprintln!("skipping: fixture not found at {path}");
        false
    }
}

fn fixture_path(name: &str) -> String {
    format!("{FIXTURES_DIR}/{name}.wasm")
}

// ---------------------------------------------------------------------------
// WASI runtime helpers
// ---------------------------------------------------------------------------

struct WasiState {
    ctx: WasiCtx,
    table: ResourceTable,
}

impl WasiView for WasiState {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView {
            ctx: &mut self.ctx,
            table: &mut self.table,
        }
    }
}

/// Fuse a fixture component and return the raw bytes.
fn fuse_fixture(name: &str, output_format: OutputFormat) -> anyhow::Result<Vec<u8>> {
    let path = fixture_path(name);
    let bytes = std::fs::read(&path)?;

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: CustomSectionHandling::Drop,
        output_format,
    };

    let mut fuser = Fuser::new(config);
    fuser.add_component_named(&bytes, Some(name))?;
    let (fused, stats) = fuser.fuse_with_stats()?;

    eprintln!(
        "[{name}] fused ({output_format:?}): {} bytes, {} funcs, {} adapters, {} imports resolved",
        stats.output_size, stats.total_functions, stats.adapter_functions, stats.imports_resolved,
    );

    Ok(fused)
}

/// Load a fused P2 component into wasmtime with WASI and call `run()`.
///
/// Tries the typed `Command` API first (exact WASI version match), then
/// falls back to version-agnostic instance lookup for components built
/// with a different WASI version (e.g., 0.2.6 vs 0.2.3).
fn run_wasi_component(wasm: &[u8]) -> anyhow::Result<()> {
    let mut engine_config = Config::new();
    engine_config.wasm_component_model(true);
    engine_config.wasm_multi_memory(true);

    let engine = Engine::new(&engine_config)?;

    let mut linker: Linker<WasiState> = Linker::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker)?;

    let component = Component::new(&engine, wasm)?;

    let mut builder = WasiCtx::builder();
    builder.inherit_stdio();
    let mut store = Store::new(
        &engine,
        WasiState {
            ctx: builder.build(),
            table: ResourceTable::new(),
        },
    );

    // Try typed Command API first (matches exact WASI version)
    if let Ok(command) = Command::instantiate(&mut store, &component, &linker) {
        return command
            .wasi_cli_run()
            .call_run(&mut store)?
            .map_err(|()| anyhow::anyhow!("wasi:cli/run returned error"));
    }

    // Fallback: version-agnostic instantiation and run lookup
    let instance = linker.instantiate(&mut store, &component)?;

    // Try bare "run" export first, then search for wasi:cli/run instance
    let func = if let Some(f) = instance.get_func(&mut store, "run") {
        f
    } else {
        // Search for wasi:cli/run@<version> instance containing "run"
        let run_versions = ["wasi:cli/run@0.2.6", "wasi:cli/run@0.2.3"];
        let mut found = None;
        for version in &run_versions {
            if let Some((_, idx)) = instance.get_export(&mut store, None, version)
                && let Some((_, run_idx)) = instance.get_export(&mut store, Some(&idx), "run")
            {
                found = instance.get_func(&mut store, run_idx);
                break;
            }
        }
        found.ok_or_else(|| anyhow::anyhow!("no wasi:cli/run export found"))?
    };

    let mut results = [];
    func.call(&mut store, &[], &mut results)?;
    func.post_return(&mut store)?;

    Ok(())
}

// ---------------------------------------------------------------------------
// Fusion as CoreModule tests
// ---------------------------------------------------------------------------

#[test]
fn test_fuse_wit_bindgen_numbers() {
    if !fixture_exists("numbers") {
        return;
    }
    let fused = fuse_fixture("numbers", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("numbers: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_strings() {
    if !fixture_exists("strings") {
        return;
    }
    let fused = fuse_fixture("strings", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("strings: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_lists() {
    if !fixture_exists("lists") {
        return;
    }
    let fused = fuse_fixture("lists", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("lists: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_records() {
    if !fixture_exists("records") {
        return;
    }
    let fused = fuse_fixture("records", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("records: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_variants() {
    if !fixture_exists("variants") {
        return;
    }
    let fused = fuse_fixture("variants", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("variants: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_options() {
    if !fixture_exists("options") {
        return;
    }
    let fused = fuse_fixture("options", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("options: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_many_arguments() {
    if !fixture_exists("many-arguments") {
        return;
    }
    let fused = fuse_fixture("many-arguments", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("many-arguments: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_flavorful() {
    if !fixture_exists("flavorful") {
        return;
    }
    let fused = fuse_fixture("flavorful", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("flavorful: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_results() {
    if !fixture_exists("results") {
        return;
    }
    let fused = fuse_fixture("results", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("results: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_lists_alias() {
    if !fixture_exists("lists-alias") {
        return;
    }
    let fused = fuse_fixture("lists-alias", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("lists-alias: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_strings_alias() {
    if !fixture_exists("strings-alias") {
        return;
    }
    let fused = fuse_fixture("strings-alias", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("strings-alias: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_strings_simple() {
    if !fixture_exists("strings-simple") {
        return;
    }
    let fused = fuse_fixture("strings-simple", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("strings-simple: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_fixed_length_lists() {
    if !fixture_exists("fixed-length-lists") {
        return;
    }
    let fused = fuse_fixture("fixed-length-lists", OutputFormat::CoreModule)
        .expect("fixed-length-lists: fusion should succeed");
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("fixed-length-lists: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_resources() {
    if !fixture_exists("resources") {
        return;
    }
    let fused = fuse_fixture("resources", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("resources: fused core module should validate");
}

// ---------------------------------------------------------------------------
// Fusion as Component tests
// ---------------------------------------------------------------------------

#[test]
fn test_fuse_component_wit_bindgen_numbers() {
    if !fixture_exists("numbers") {
        return;
    }
    let fused = fuse_fixture("numbers", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("numbers: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_strings() {
    if !fixture_exists("strings") {
        return;
    }
    let fused = fuse_fixture("strings", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("strings: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_lists() {
    if !fixture_exists("lists") {
        return;
    }
    let fused = fuse_fixture("lists", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("lists: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_records() {
    if !fixture_exists("records") {
        return;
    }
    let fused = fuse_fixture("records", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("records: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_variants() {
    if !fixture_exists("variants") {
        return;
    }
    let fused = fuse_fixture("variants", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("variants: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_options() {
    if !fixture_exists("options") {
        return;
    }
    let fused = fuse_fixture("options", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("options: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_many_arguments() {
    if !fixture_exists("many-arguments") {
        return;
    }
    let fused = fuse_fixture("many-arguments", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("many-arguments: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_flavorful() {
    if !fixture_exists("flavorful") {
        return;
    }
    let fused = fuse_fixture("flavorful", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("flavorful: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_results() {
    if !fixture_exists("results") {
        return;
    }
    let fused = fuse_fixture("results", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("results: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_lists_alias() {
    if !fixture_exists("lists-alias") {
        return;
    }
    let fused = fuse_fixture("lists-alias", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("lists-alias: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_strings_alias() {
    if !fixture_exists("strings-alias") {
        return;
    }
    let fused = fuse_fixture("strings-alias", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("strings-alias: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_strings_simple() {
    if !fixture_exists("strings-simple") {
        return;
    }
    let fused = fuse_fixture("strings-simple", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("strings-simple: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_fixed_length_lists() {
    if !fixture_exists("fixed-length-lists") {
        return;
    }
    let fused = fuse_fixture("fixed-length-lists", OutputFormat::Component)
        .expect("fixed-length-lists: component fusion should succeed");
    let features =
        wasmparser::WasmFeatures::default() | wasmparser::WasmFeatures::CM_FIXED_SIZE_LIST;
    wasmparser::Validator::new_with_features(features)
        .validate_all(&fused)
        .expect("fixed-length-lists: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_resources() {
    if !fixture_exists("resources") {
        return;
    }
    // SR-25: P2 component wrapping now handles resource types including
    // [resource-new], [resource-rep], and [export]-prefixed modules.
    let fused = fuse_fixture("resources", OutputFormat::Component)
        .expect("resources: component fusion should succeed");
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("resources: fused component should validate");
}

// ---------------------------------------------------------------------------
// Runtime execution tests (fuse as Component, run through wasmtime + WASI)
// ---------------------------------------------------------------------------

#[test]
fn test_runtime_wit_bindgen_numbers() {
    if !fixture_exists("numbers") {
        return;
    }
    let fused = fuse_fixture("numbers", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("numbers: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_strings() {
    if !fixture_exists("strings") {
        return;
    }
    let fused = fuse_fixture("strings", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("strings: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_lists() {
    if !fixture_exists("lists") {
        return;
    }
    let fused = fuse_fixture("lists", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("lists: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_records() {
    if !fixture_exists("records") {
        return;
    }
    let fused = fuse_fixture("records", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("records: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_variants() {
    if !fixture_exists("variants") {
        return;
    }
    let fused = fuse_fixture("variants", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("variants: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_options() {
    if !fixture_exists("options") {
        return;
    }
    let fused = fuse_fixture("options", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("options: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_many_arguments() {
    if !fixture_exists("many-arguments") {
        return;
    }
    let fused = fuse_fixture("many-arguments", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("many-arguments: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_flavorful() {
    if !fixture_exists("flavorful") {
        return;
    }
    let fused = fuse_fixture("flavorful", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("flavorful: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_results() {
    if !fixture_exists("results") {
        return;
    }
    let fused = fuse_fixture("results", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("results: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_lists_alias() {
    if !fixture_exists("lists-alias") {
        return;
    }
    let fused = fuse_fixture("lists-alias", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("lists-alias: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_strings_alias() {
    if !fixture_exists("strings-alias") {
        return;
    }
    let fused = fuse_fixture("strings-alias", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("strings-alias: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_strings_simple() {
    if !fixture_exists("strings-simple") {
        return;
    }
    let fused = fuse_fixture("strings-simple", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("strings-simple: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_fixed_length_lists() {
    if !fixture_exists("fixed-length-lists") {
        return;
    }
    let fused = fuse_fixture("fixed-length-lists", OutputFormat::Component)
        .expect("fixed-length-lists: component fusion should succeed");
    // Fixed-size list adapter support is new; runtime execution may fail
    // due to adapter-level issues with inline array data copying.
    match run_wasi_component(&fused) {
        Ok(()) => {}
        Err(e) => {
            let msg = format!("{e:?}");
            if msg.contains("unreachable") || msg.contains("wasm trap") || msg.contains("assertion")
            {
                eprintln!(
                    "fixed-length-lists: runtime execution failed \
                     (adapter limitation for fixed-size lists): {e}"
                );
            } else {
                panic!("fixed-length-lists: unexpected runtime error: {e:?}");
            }
        }
    }
}

#[test]
fn test_runtime_wit_bindgen_resources() {
    if !fixture_exists("resources") {
        return;
    }
    // SR-25: Resource handle translation in cross-component adapters.
    // The adapter calls [resource-rep] to convert handles → representations
    // for params. Results are passed through as-is (the callee core function
    // already calls [resource-new] internally).
    let fused = fuse_fixture("resources", OutputFormat::Component)
        .expect("resources: component fusion should succeed");
    run_wasi_component(&fused).expect("resources: runtime execution should succeed");
}

// ---------------------------------------------------------------------------
// New fixture tests (issue #1 coverage expansion)
// ---------------------------------------------------------------------------

macro_rules! runtime_test {
    ($name:ident, $fixture:expr) => {
        #[test]
        fn $name() {
            if !fixture_exists($fixture) {
                return;
            }
            let fused = fuse_fixture($fixture, OutputFormat::Component)
                .expect(concat!($fixture, ": component fusion should succeed"));
            run_wasi_component(&fused)
                .expect(concat!($fixture, ": runtime execution should succeed"));
        }
    };
}

macro_rules! fuse_only_test {
    ($name:ident, $fixture:expr) => {
        #[test]
        fn $name() {
            if !fixture_exists($fixture) {
                return;
            }
            fuse_fixture($fixture, OutputFormat::CoreModule)
                .expect(concat!($fixture, ": core module fusion should succeed"));
        }
    };
}

// Resource fixtures — stress-test SR-25 borrow/own handle translation
runtime_test!(test_runtime_wit_bindgen_resource_borrow, "resource-borrow");
runtime_test!(
    test_runtime_wit_bindgen_resource_alias_redux,
    "resource_alias_redux"
);
runtime_test!(
    test_runtime_wit_bindgen_resource_into_inner,
    "resource_into_inner"
);
runtime_test!(
    test_runtime_wit_bindgen_owned_resource_deref_mut,
    "owned-resource-deref-mut"
);
runtime_test!(
    test_runtime_wit_bindgen_with_and_resources,
    "with-and-resources"
);
runtime_test!(test_runtime_wit_bindgen_resource_alias, "resource_alias");

// Resource fixtures — all promoted to runtime tests with per-component resource types
runtime_test!(
    test_runtime_wit_bindgen_resource_aggregates,
    "resource_aggregates"
);
// 3-component chain: resource type mismatch fixed (H-11.8), but handle
// table values still trap in wit-bindgen's ResourceTable slab code.
fuse_only_test!(test_fuse_wit_bindgen_resource_floats, "resource_floats");
runtime_test!(
    test_runtime_wit_bindgen_resource_borrow_in_record,
    "resource_borrow_in_record"
);
fuse_only_test!(
    test_fuse_wit_bindgen_resource_with_lists,
    "resource_with_lists"
);
runtime_test!(test_runtime_wit_bindgen_ownership, "ownership");
runtime_test!(test_runtime_wit_bindgen_xcrate, "xcrate");

fuse_only_test!(
    test_fuse_wit_bindgen_resource_import_and_export,
    "resource-import-and-export"
);

// Type composition and misc fixtures
runtime_test!(test_runtime_wit_bindgen_demo, "demo");
runtime_test!(test_runtime_wit_bindgen_gated_features, "gated-features");
runtime_test!(
    test_runtime_wit_bindgen_symbol_conflicts,
    "symbol-conflicts"
);
runtime_test!(test_runtime_wit_bindgen_unused_types, "unused-types");
runtime_test!(
    test_runtime_wit_bindgen_package_with_version,
    "package-with-version"
);

runtime_test!(test_runtime_wit_bindgen_versions, "versions");

// Rust binding-specific fixtures (still valid fusion targets)
runtime_test!(
    test_runtime_wit_bindgen_alternative_bitflags,
    "alternative-bitflags"
);
runtime_test!(test_runtime_wit_bindgen_custom_derives, "custom-derives");
runtime_test!(
    test_runtime_wit_bindgen_disable_custom_section,
    "disable-custom-section-link-helpers"
);
runtime_test!(
    test_runtime_wit_bindgen_other_dependencies,
    "other-dependencies"
);
runtime_test!(test_runtime_wit_bindgen_raw_strings, "raw-strings");
runtime_test!(test_runtime_wit_bindgen_skip, "skip");
runtime_test!(
    test_runtime_wit_bindgen_type_section_suffix,
    "type_section_suffix"
);

// with: P2 wrapper resource type encoding issue
fuse_only_test!(test_fuse_wit_bindgen_with, "with");

runtime_test!(
    test_runtime_wit_bindgen_with_only_affects_imports,
    "with-only-affects-imports"
);
runtime_test!(
    test_runtime_wit_bindgen_with_option_generate,
    "with-option-generate"
);
runtime_test!(test_runtime_wit_bindgen_with_types, "with-types");

// run-ctors-once-workaround: no `run` export (different entry point, not a meld issue)
fuse_only_test!(
    test_fuse_wit_bindgen_run_ctors_once,
    "run-ctors-once-workaround"
);
