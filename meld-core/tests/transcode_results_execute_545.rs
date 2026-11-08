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
//! Component 3 (latin1+utf16 on both sides) validated before #582 but
//! trapped: meld copied the string unchanged where the Canonical ABI deflates
//! a utf16-tagged string that fits latin1.

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

fn run_unfused(bytes: &[u8]) -> u32 {
    let mut config = Config::new();
    config.wasm_component_model(true);
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let c = wasmtime::component::Component::new(&engine, bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let linker = wasmtime::component::Linker::<()>::new(&engine);
    let inst = linker.instantiate(&mut store, &c).unwrap();
    let f = inst
        .get_typed_func::<(), (u32,)>(&mut store, "run")
        .unwrap();
    f.call(&mut store, ()).unwrap().0
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
        // #582: same encoding, but a utf16-tagged "AB" must arrive deflated.
        (3, "latin1+utf16 both sides, deflate", 45),
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

/// A `list<u8>` is binary, not text: under a cross-encoding call it must be
/// copied byte for byte, never transcoded. The copy emitters decide
/// "string" from a 1-byte element layout, which a `list<u8>` shares. So this
/// pins the case: utf16 caller, utf8 callee, `(param list<u8>) (result
/// string)`. The callee checks the exact bytes `FF 00 41` and length 3, and
/// the caller checks the transcoded result "ok". `run` returns 7 only if both
/// hold.
// rivet: verifies SR-115
#[test]
fn list_u8_param_is_copied_not_transcoded() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/transcode_545/list_u8_param_string_result.wat");
    let input = wat::parse_file(&path).expect("fixture parses");
    // The fixture is right only if the Canonical ABI as wasmtime implements
    // it, independently of meld, gives 7 unfused.
    assert_eq!(run_unfused(&input), 7, "fixture: unfused component");
    match fuse_and_run(&input) {
        Ok(7) => {}
        other => panic!("list<u8> param across a utf16 -> utf8 call: {other:?}"),
    }
}

/// #582 result side: component 3 never returns a utf16-tagged string that
/// fits latin1, so this fixture does. The expectation (9) is checked unfused
/// on wasmtime's component runtime first: deflating on the way back is the
/// Canonical ABI's behaviour, not meld's reading of it.
// rivet: verifies SR-117
#[test]
fn compact_utf16_result_is_deflated() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/transcode_545/compact_result_deflate.wat");
    let input = wat::parse_file(&path).expect("fixture parses");
    assert_eq!(run_unfused(&input), 9, "fixture: unfused component");
    match fuse_and_run(&input) {
        Ok(9) => {}
        other => panic!("latin1+utf16 result deflation: {other:?}"),
    }
}
