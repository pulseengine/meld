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
/// Supports both `wasi:cli/run` command components and components that
/// export a bare `run` function (wit-bindgen test fixtures).
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

    let instance = linker.instantiate(&mut store, &component)?;

    let func = instance
        .get_func(&mut store, "run")
        .ok_or_else(|| anyhow::anyhow!("no `run` export found"))?;

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
fn test_fuse_component_wit_bindgen_resources() {
    if !fixture_exists("resources") {
        return;
    }
    let fused = fuse_fixture("resources", OutputFormat::Component).unwrap();
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
fn test_runtime_wit_bindgen_resources() {
    if !fixture_exists("resources") {
        return;
    }
    let fused = fuse_fixture("resources", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("resources: run() should succeed without trap");
}
