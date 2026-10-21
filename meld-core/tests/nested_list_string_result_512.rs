//! #512 — a `list<string>` behind an option/result/variant discriminant must be
//! deep-copied across memories, element by element.
//!
//! Reported by o-murphy against meld 0.64.0: a C wit-bindgen provider/guest
//! pair, composed with `wasm-tools compose` and fused with
//! `meld fuse --component`, returned
//!
//! ```text
//! get=apple,3,[,]          (fused)
//! get=apple,3,[red,big]    (composed, run directly)
//! ```
//!
//! for `get: func(id: u32) -> option<item>` with
//! `record item { name: string, qty: u32, tags: list<string> }`. The fused
//! component validated and ran at exit 0.
//!
//! The adapter's conditional copy paths copied the OUTER buffer of a
//! conditional pointer pair (here the `tags` array of `(ptr, len)` string
//! descriptors) but never the strings it points at, so every descriptor in the
//! caller's copy still held a callee-memory address. The unconditional paths
//! have always recursed. Both fixtures are committed with their sources; see
//! `tests/wit_bindgen/fixtures/issue_512/README.md`.
//!
//! Every assertion here compares the fused component against the SAME
//! composition run directly by wasmtime. Fusion is a semantics-preserving
//! transform, so the composition is the oracle; the literal expectations only
//! pin that the oracle itself is the value the C sources compute.

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasmtime::component::{Component, Linker, ResourceTable};
use wasmtime::{Config, Engine, Store};
use wasmtime_wasi::{WasiCtx, WasiCtxView, WasiView};

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

fn fixture(rel: &str) -> Vec<u8> {
    let path = format!(
        "{}/../tests/wit_bindgen/fixtures/issue_512/{rel}",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read(&path).unwrap_or_else(|e| {
        panic!(
            "{path}: {e} — every fixture a test reads is tracked in the repository (SR-85); \
             a missing one is a repository error, not a reason to report success"
        )
    })
}

fn fuse(bytes: &[u8]) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        output_format: OutputFormat::Component,
        attestation: false,
        reproducible: true,
        ..Default::default()
    });
    fuser
        .add_component_named(bytes, Some("composed.wasm"))
        .expect("fixture parses");
    let fused = fuser.fuse().expect("fusion succeeds");
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&fused)
        .expect("fused component validates");
    fused
}

/// Instantiate `wasm` under WASI (the C components import it; `run-all` does
/// not call it) and return `<iface>#run-all()`.
fn run_all(wasm: &[u8], iface: &str) -> String {
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).expect("engine");
    let mut linker: Linker<WasiState> = Linker::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker).expect("wasi linker");
    let component = Component::new(&engine, wasm).expect("component loads");
    let mut store = Store::new(
        &engine,
        WasiState {
            ctx: WasiCtx::builder().build(),
            table: ResourceTable::new(),
        },
    );
    let instance = linker
        .instantiate(&mut store, &component)
        .expect("instantiate");
    let (_, iface_idx) = instance
        .get_export(&mut store, None, iface)
        .unwrap_or_else(|| panic!("no {iface} export"));
    let (_, f_idx) = instance
        .get_export(&mut store, Some(&iface_idx), "run-all")
        .expect("no run-all in the app interface");
    let f = instance
        .get_func(&mut store, f_idx)
        .expect("run-all is a function")
        .typed::<(), (String,)>(&store)
        .expect("run-all: func() -> string");
    f.call(&mut store, ()).expect("run-all must not trap").0
}

/// The reporter's component, verbatim.
const CX_EXPECTED: &str = "put=ok:0;put0=err:qty must be > 0;get=apple,3,[red,big];get9=none;\
                           area=48,42,0;level=0,1,2;perms=3;sum=4000000006;\
                           counter=15,counter=15,peek=100";

// rivet: verifies SR-16
#[test]
fn issue_512_reporter_component_fused_matches_composed() {
    let composed = fixture("cx/composed.wasm");
    let want = run_all(&composed, "demo:cx/app@0.1.0");
    assert_eq!(want, CX_EXPECTED, "the oracle itself drifted");

    let got = run_all(&fuse(&composed), "demo:cx/app@0.1.0");
    assert_eq!(
        got, want,
        "#512: the fused component must return what the composition returns \
         (before the fix: `get=apple,3,[,]` — the tags' strings were never copied)"
    );
}

/// One entry per shape; see `shapes/wit/sh.wit`. Each is `<label>=<value>`.
///
/// | label | shape                                        | adapter path                 |
/// |-------|----------------------------------------------|------------------------------|
/// | a     | `-> list<string>`                            | retptr, unconditional (ok)   |
/// | b     | `-> record { tags: list<string> }`           | retptr, unconditional (ok)   |
/// | c     | `-> option<list<string>>`                    | retptr Phase 5b (#512)       |
/// | d     | `-> option<record { name, qty, tags }>`      | retptr Phase 5b (#512)       |
/// | e     | `-> option<string>`                          | retptr Phase 5b, Bulk (ok)   |
/// | f     | `-> result<list<string>, string>`            | retptr Phase 5b (#512)       |
/// | g     | `-> option<record { tags }>`                 | retptr Phase 5b (#512)       |
/// | h     | `-> list<option<string>>`                    | retptr, guarded inner (ok)   |
/// | p     | `(option<list<string>>) -> string`           | retptr Phase 1b (#512)       |
/// | q     | `(string, option<string>) -> u32`            | memory-copy, mixed pairs     |
/// | r     | `(option<list<string>>) -> u32`              | memory-copy conditional      |
const SHAPES_EXPECTED: &[(&str, &str)] = &[
    ("a", "2[red,big]"),
    ("b", "2[rec,ord]"),
    ("c", "2[opt,lst]"),
    ("d", "apple,3,2[itm,tag]"),
    ("e", "solo"),
    ("f", "2[res,ok]"),
    ("g", "2[owr,apx]"),
    ("h", "2[los,two]"),
    ("p", "arg|in|"),
    ("q", "933777361"),
    ("r", "40033474"),
];

fn split_shapes(s: &str) -> Vec<(String, String)> {
    s.split(';')
        .map(|kv| {
            let (k, v) = kv.split_once('=').expect("label=value");
            (k.to_string(), v.to_string())
        })
        .collect()
}

/// Shape-by-shape, so a failure names the shape rather than one long string.
// rivet: verifies SR-16
#[test]
fn issue_512_every_shape_fused_matches_composed() {
    let composed = fixture("shapes/composed.wasm");
    let want = split_shapes(&run_all(&composed, "demo:sh/app@0.1.0"));
    let expected: Vec<(String, String)> = SHAPES_EXPECTED
        .iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect();
    assert_eq!(want, expected, "the oracle itself drifted");

    let got = split_shapes(&run_all(&fuse(&composed), "demo:sh/app@0.1.0"));
    assert_eq!(got.len(), want.len());
    let diverged: Vec<String> = want
        .iter()
        .zip(&got)
        .filter(|(w, g)| w != g)
        .map(|((k, w), (_, g))| format!("{k}: composed={w:?} fused={g:?}"))
        .collect();
    assert!(
        diverged.is_empty(),
        "#512: fused output diverged from the composition for shape(s):\n  {}",
        diverged.join("\n  ")
    );
}
