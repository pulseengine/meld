//! #545: cross-encoding calls that return a string or list now fuse, and
//! the fused module returns the right answer.
//!
//! The upstream `test/values/transcode.wast` components each export `run`.
//! `run` returns a fixed value only when every transcoded byte matches, on
//! both sides: the callee checks the argument and the caller checks the
//! result. Otherwise it hits `unreachable`. Before #545's retptr transcoding
//! adapter, four of them fused to invalid modules, refused by SR-114.
//! Validation alone cannot show the fix is right: a valid module that skips
//! a transcode traps here.
//!
//! Component 3 (latin1+utf16 on both sides) is not in the table. It fuses
//! and validates, but returns a wrong answer (the deflate case), tracked on
//! #582.

use std::path::Path;

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasmtime::{Config, Engine, Instance, Module, Store};
use wast::parser::{self, ParseBuffer};
use wast::{QuoteWat, Wast, WastDirective, Wat};

/// Every top-level component in the WAST, in order (the ratchet's
/// `component_index`).
fn components(rel: &str) -> Vec<Vec<u8>> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../tests/spec/component-model/test")
        .join(rel);
    let text = std::fs::read_to_string(&path).expect("vendored WAST present");
    let buf = ParseBuffer::new(&text).expect("lex");
    let wast: Wast<'_> = parser::parse(&buf).expect("parse");
    let mut out = Vec::new();
    for d in wast.directives {
        if let WastDirective::Module(mut q) = d
            && matches!(q, QuoteWat::Wat(Wat::Component(_)))
        {
            out.push(q.encode().expect("encode"));
        }
    }
    out
}

fn fuse_and_run(input: &[u8]) -> Result<u32, String> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component(input).map_err(|e| e.to_string())?;
    let fused = fuser.fuse().map_err(|e| format!("fuse: {e}"))?;

    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).map_err(|e| e.to_string())?;
    let module = Module::new(&engine, &fused).map_err(|e| format!("load: {e}"))?;
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).map_err(|e| format!("inst: {e}"))?;
    let run = instance
        .get_typed_func::<(), u32>(&mut store, "run")
        .map_err(|e| format!("run export: {e}"))?;
    run.call(&mut store, ()).map_err(|e| format!("trap: {e:?}"))
}

// rivet: verifies SR-115
#[test]
fn transcoded_string_and_list_results_execute_correctly() {
    let comps = components("values/transcode.wast");
    // (component index, encoding pair, the WAST's expected `run` value)
    let cases = [
        (0, "utf16 -> utf8, string result", 42),
        (1, "utf8 -> utf16, string result", 43),
        (2, "latin1+utf16 -> utf8, string result", 44),
        (4, "utf16 -> utf8, list<string> param and result", 46),
    ];
    let mut failures = Vec::new();
    for (idx, what, want) in cases {
        match fuse_and_run(&comps[idx]) {
            Ok(got) if got == want => {}
            Ok(got) => failures.push(format!(
                "component {idx} ({what}): run = {got}, want {want}"
            )),
            Err(e) => failures.push(format!("component {idx} ({what}): {e}")),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
