//! Rust 1.100 wasip2 components import `wasi:cli/exit@0.2.12`
//! `exit-with-code`, hello-world included: std links it. wasmtime 45 and
//! older refuse such a component at instantiation (ordeal#309). The wasmtime
//! 41 CLI reports "instance export `exit-with-code` has the wrong type".
//!
//! This test checks that fusion keeps that import resolvable. It fuses a
//! Rust 1.100 fixture and requires three things of the output:
//! - it still imports `exit-with-code` from `wasi:cli/exit@0.2.12`;
//! - it instantiates under this crate's wasmtime (50.0.3, above the 46.0.0
//!   floor);
//! - it behaves like the unfused original: the same stdout, and exit code 7
//!   delivered through `exit-with-code`.
//!
//! Fixture: `tests/fixtures/rust_1100_exit/hello_exit_1100.wasm`, built from
//! `hello_exit_1100.rs` next to it with
//!   rustc +1.100.0 --edition 2021 --target wasm32-wasip2 \
//!     -C opt-level=s -C strip=symbols -o hello_exit_1100.wasm hello_exit_1100.rs
//! Two builds gave the same SHA-256 (ce405625…5330876).

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasmtime::component::types::ComponentItem;
use wasmtime::component::{Component, Linker, ResourceTable};
use wasmtime::{Config, Engine, Store};
use wasmtime_wasi::p2::bindings::sync::Command;
use wasmtime_wasi::p2::pipe::MemoryOutputPipe;
use wasmtime_wasi::{I32Exit, WasiCtx, WasiCtxView, WasiView};

const FIXTURE: &str = "tests/fixtures/rust_1100_exit/hello_exit_1100.wasm";
const OLDER_FIXTURE: &str = "../tests/wit_bindgen/fixtures/release-0.2.0/hello_rust.wasm";
const EXIT_IFACE: &str = "wasi:cli/exit@0.2.12";
const EXPECTED_STDOUT: &[u8] = b"hello from rust 1.100\n";
const EXPECTED_CODE: i32 = 7;

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

fn engine() -> Engine {
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    cfg.wasm_multi_memory(true);
    Engine::new(&cfg).expect("engine")
}

fn fixture() -> Vec<u8> {
    std::fs::read(FIXTURE).unwrap_or_else(|e| {
        panic!("fixture {FIXTURE} is tracked in the repository and must exist: {e}")
    })
}

/// Whether the component imports `exit-with-code` from `wasi:cli/exit@0.2.12`,
/// read from the component's own type, not from printed text.
fn imports_exit_with_code(engine: &Engine, component: &Component) -> bool {
    component
        .component_type()
        .imports(engine)
        .any(|(name, item)| match item.ty {
            ComponentItem::ComponentInstance(inst) if name == EXIT_IFACE => inst
                .exports(engine)
                .any(|(export, _)| export == "exit-with-code"),
            _ => false,
        })
}

/// Run `wasi:cli/run` and return (stdout, exit code). A run that returns
/// without calling exit reports `None`.
fn run(engine: &Engine, component: &Component) -> (Vec<u8>, Option<i32>) {
    let mut linker: Linker<WasiState> = Linker::new(engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker).expect("wasi linker");
    let stdout = MemoryOutputPipe::new(1 << 16);
    let mut builder = WasiCtx::builder();
    builder.stdout(stdout.clone());
    let mut store = Store::new(
        engine,
        WasiState {
            ctx: builder.build(),
            table: ResourceTable::new(),
        },
    );
    let command = Command::instantiate(&mut store, component, &linker)
        .expect("instantiate: every import, exit-with-code included, must resolve");
    let code = match command.wasi_cli_run().call_run(&mut store) {
        Ok(_) => None,
        Err(e) => Some(
            e.downcast_ref::<I32Exit>()
                .unwrap_or_else(|| panic!("run trapped instead of exiting: {e:?}"))
                .0,
        ),
    };
    (stdout.contents().to_vec(), code)
}

#[test]
fn rust_1100_wasip2_exit_with_code_survives_fusion() {
    let engine = engine();
    let original_bytes = fixture();
    let original = Component::new(&engine, &original_bytes).expect("compile original");

    // Precondition: the fixture has the shape this test is about.
    assert!(
        imports_exit_with_code(&engine, &original),
        "fixture no longer imports {EXIT_IFACE} exit-with-code; rebuild it with Rust 1.100.0"
    );
    // Control for the import check: an older Rust component imports
    // wasi:cli/exit@0.2.6 without exit-with-code, so the check must say no.
    let older = Component::new(
        &engine,
        std::fs::read(OLDER_FIXTURE).expect("older fixture"),
    )
    .expect("compile older fixture");
    assert!(
        !imports_exit_with_code(&engine, &older),
        "the import check reports exit-with-code on a component that lacks it"
    );

    let golden = run(&engine, &original);
    assert_eq!(
        golden,
        (EXPECTED_STDOUT.to_vec(), Some(EXPECTED_CODE)),
        "unfused original"
    );

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        output_format: OutputFormat::Component,
        attestation: false,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&original_bytes, Some("hello_exit_1100"))
        .expect("add fixture");
    let fused_bytes = fuser.fuse().expect("fuse");
    let fused = Component::new(&engine, &fused_bytes).expect("compile fused");

    assert!(
        imports_exit_with_code(&engine, &fused),
        "fusion dropped the {EXIT_IFACE} exit-with-code import"
    );
    assert_eq!(run(&engine, &fused), golden, "fused vs unfused");
}
