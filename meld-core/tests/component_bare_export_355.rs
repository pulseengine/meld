//! #355 — `fuse --component` must lift bare *world* exports with their real
//! signatures, not an empty `(func)`.
//!
//! avrabe's fixtures (`tests/reloc351/{a,b}.wasm`) expose bare world exports:
//! `get-b: func(i:s32)->u32`, `set-b: func(i:s32,v:u32)` (void),
//! `ptr-b: func()->u32`. Before the fix every export was lifted with an empty
//! component type, producing an INVALID component (`wasm-tools validate`:
//! "lowered parameter types [] do not match [I32] of core function 0").
//!
//! The fix touched three latent defects, so the oracle checks two things:
//!  1. the output is a **valid** component (catches the empty-type bug and the
//!     missing no-result func encoding), and
//!  2. each export lifts with its **correct arity** (catches the export-alias
//!     index-skip that shifted every export onto the previous one's type).

use meld_core::parser::{CanonicalEntry, ComponentFuncDef, ComponentParser, ComponentTypeKind};
use meld_core::{Fuser, FuserConfig, OutputFormat};

fn fuse_as_component(paths: &[&str]) -> Vec<u8> {
    let config = FuserConfig {
        output_format: OutputFormat::Component,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    for p in paths {
        let bytes = std::fs::read(p).unwrap_or_else(|e| panic!("read {p}: {e}"));
        fuser
            .add_component_named(&bytes, Some(p))
            .unwrap_or_else(|e| panic!("add {p}: {e:?}"));
    }
    fuser.fuse().expect("fuse --component")
}

/// (params, results) arity of each Func export, resolved through the component's
/// func-index space → lift → type. This is exactly the path the wrapper mis-used.
fn export_arities(bytes: &[u8]) -> std::collections::HashMap<String, (usize, usize)> {
    let pc = ComponentParser::new().parse(bytes).expect("parse output");
    let mut out = std::collections::HashMap::new();
    for e in &pc.exports {
        if e.kind != wasmparser::ComponentExternalKind::Func {
            continue;
        }
        if let Some(ComponentFuncDef::Lift(ci)) = pc.component_func_defs.get(e.index as usize)
            && let Some(CanonicalEntry::Lift { type_index, .. }) = pc.canonical_functions.get(*ci)
            && let Some(td) = pc.get_type_definition(*type_index)
            && let ComponentTypeKind::Function { params, results } = &td.kind
        {
            out.insert(e.name.clone(), (params.len(), results.len()));
        }
    }
    out
}

fn assert_valid_component(bytes: &[u8]) {
    let mut v = wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all());
    v.validate_all(bytes)
        .expect("#355: fused --component output must be a valid component");
}

#[test]
fn test_355_bare_world_exports_single_component() {
    let out = fuse_as_component(&["../tests/reloc351/b.wasm"]);
    assert_valid_component(&out);
    let sig = export_arities(&out);
    assert_eq!(sig.get("get-b"), Some(&(1, 1)), "get-b: func(i:s32)->u32");
    assert_eq!(
        sig.get("set-b"),
        Some(&(2, 0)),
        "set-b: func(i:s32,v:u32)->()"
    );
    assert_eq!(sig.get("ptr-b"), Some(&(0, 1)), "ptr-b: func()->u32");
}

#[test]
fn test_355_bare_world_exports_two_components() {
    // avrabe's exact repro: `meld fuse --component a.wasm b.wasm`.
    let out = fuse_as_component(&["../tests/reloc351/a.wasm", "../tests/reloc351/b.wasm"]);
    assert_valid_component(&out);
    let sig = export_arities(&out);
    // Whichever component's world is exported, the bare-export arities must be
    // correct (the bug shifted them regardless of component count).
    for (name, arity) in &sig {
        let expected = match name.as_str() {
            n if n.starts_with("get-") => (1, 1),
            n if n.starts_with("set-") => (2, 0),
            n if n.starts_with("ptr-") => (0, 1),
            _ => continue,
        };
        assert_eq!(
            arity, &expected,
            "export {name} must lift with its real signature"
        );
    }
    assert!(
        !sig.is_empty(),
        "at least one bare world export must be lifted"
    );
}
