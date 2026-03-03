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

/// Skip tests when fixture files are not present.
fn fixtures_available() -> bool {
    if std::path::Path::new(FIXTURES_DIR).is_dir() {
        true
    } else {
        eprintln!("skipping: wit-bindgen fixtures not found at {FIXTURES_DIR}");
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

    let command = Command::instantiate(&mut store, &component, &linker)?;
    let result = command.wasi_cli_run().call_run(&mut store)?;

    match result {
        Ok(()) => Ok(()),
        Err(()) => anyhow::bail!("wasi:cli/run returned error"),
    }
}

// ---------------------------------------------------------------------------
// Fusion as CoreModule tests
// ---------------------------------------------------------------------------

#[test]
fn test_fuse_wit_bindgen_numbers() {
    if !fixtures_available() {
        return;
    }
    let fused = fuse_fixture("numbers", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("numbers: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_strings() {
    if !fixtures_available() {
        return;
    }
    let fused = fuse_fixture("strings", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("strings: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_lists() {
    if !fixtures_available() {
        return;
    }
    let fused = fuse_fixture("lists", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("lists: fused core module should validate");
}

#[test]
fn test_fuse_wit_bindgen_records() {
    if !fixtures_available() {
        return;
    }
    let fused = fuse_fixture("records", OutputFormat::CoreModule).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("records: fused core module should validate");
}

// ---------------------------------------------------------------------------
// Fusion as Component tests
// ---------------------------------------------------------------------------

#[test]
fn test_fuse_component_wit_bindgen_numbers() {
    if !fixtures_available() {
        return;
    }
    let fused = fuse_fixture("numbers", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("numbers: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_strings() {
    if !fixtures_available() {
        return;
    }
    let fused = fuse_fixture("strings", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("strings: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_lists() {
    if !fixtures_available() {
        return;
    }
    let fused = fuse_fixture("lists", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("lists: fused component should validate");
}

#[test]
fn test_fuse_component_wit_bindgen_records() {
    if !fixtures_available() {
        return;
    }
    let fused = fuse_fixture("records", OutputFormat::Component).unwrap();
    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("records: fused component should validate");
}

// ---------------------------------------------------------------------------
// Runtime execution tests (fuse as Component, run through wasmtime + WASI)
// ---------------------------------------------------------------------------

#[test]
fn test_runtime_wit_bindgen_numbers() {
    if !fixtures_available() {
        return;
    }
    let fused = fuse_fixture("numbers", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("numbers: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_strings() {
    if !fixtures_available() {
        return;
    }
    let fused = fuse_fixture("strings", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("strings: run() should succeed without trap");
}

// Lists require element-size-aware allocation (len * sizeof(element)) and
// recursive pointer copying for nested types (list<string>, list<list<T>>).
#[test]
#[ignore = "needs element-size-aware list adapter and recursive pointer copy"]
fn test_runtime_wit_bindgen_lists() {
    if !fixtures_available() {
        return;
    }
    let fused = fuse_fixture("lists", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("lists: run() should succeed without trap");
}

#[test]
fn test_runtime_wit_bindgen_records() {
    if !fixtures_available() {
        return;
    }
    let fused = fuse_fixture("records", OutputFormat::Component).unwrap();
    run_wasi_component(&fused).expect("records: run() should succeed without trap");
}
