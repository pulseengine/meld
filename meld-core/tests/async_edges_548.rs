//! #548 / #557 / #558 -- P3 async calls between fused components.
//!
//! Until the ADR-10 adapters land, meld refuses what it cannot fuse instead of
//! exiting 0 with an import no host can serve (maintainer decision 2026-11-04,
//! recorded in ADR-10 "Resolved"):
//!
//! * #548: a caller that lowers with the async option (`[async-lower]f`)
//!   whose callee is another fused component is refused, naming the edge.
//! * #557: an `[async-lower]` import that IS left to the host keeps the
//!   producer's prefix, so the host binds it with the async convention.
//! * #558: `stream.read`/`write` and `future.read`/`write` reached through
//!   wit-component's indirect-call shim (`"actual" "<n>"`) are refused instead
//!   of leaking the shim's internal name.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn fuse(components: &[&str]) -> Result<Vec<u8>, String> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    for wat in components {
        let bytes = wat::parse_str(wat).expect("fixture parses");
        fuser.add_component(&bytes).map_err(|e| e.to_string())?;
    }
    fuser.fuse().map_err(|e| e.to_string())
}

fn imports(core: &[u8]) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(core) {
        if let Ok(wasmparser::Payload::ImportSection(r)) = payload {
            for imp in r.into_imports() {
                let imp = imp.expect("import parses");
                out.push((imp.module.to_string(), imp.name.to_string()));
            }
        }
    }
    out
}

/// Callee: exports `local:t/i` with `f: async func()`, lifted with the
/// stackless callback ABI.
const CALLEE: &str = r#"
(component
  (core module $m
    (func (export "[async-lift]local:t/i#f") (result i32) i32.const 0)
    (func (export "[callback][async-lift]local:t/i#f")
      (param i32 i32 i32) (result i32) i32.const 0))
  (core instance $ci (instantiate $m))
  (type $ft (func async))
  (func $f (type $ft)
    (canon lift (core func $ci "[async-lift]local:t/i#f") async
      (callback (core func $ci "[callback][async-lift]local:t/i#f"))))
  (instance $inst (export "f" (func $f)))
  (export "local:t/i" (instance $inst)))
"#;

/// Caller: imports `local:t/i` and lowers `f` with the async option, so its
/// core import is `[async-lower]f` with signature `() -> i32` (status).
const ASYNC_CALLER: &str = r#"
(component
  (import "local:t/i" (instance $i (export "f" (func async))))
  (alias export $i "f" (func $f))
  (core func $lf (canon lower (func $f) async))
  (core module $m
    (import "local:t/i" "[async-lower]f" (func (result i32)))
    (func (export "run")))
  (core instance $imp (export "[async-lower]f" (func $lf)))
  (core instance $ci (instantiate $m (with "local:t/i" (instance $imp)))))
"#;

/// A callee exporting a DIFFERENT interface: the caller's import stays with
/// the host, so the #548 refusal must not fire.
const OTHER_CALLEE: &str = r#"
(component
  (core module $m
    (func (export "[async-lift]local:t/other#g") (result i32) i32.const 0)
    (func (export "[callback][async-lift]local:t/other#g")
      (param i32 i32 i32) (result i32) i32.const 0))
  (core instance $ci (instantiate $m))
  (type $ft (func async))
  (func $g (type $ft)
    (canon lift (core func $ci "[async-lift]local:t/other#g") async
      (callback (core func $ci "[callback][async-lift]local:t/other#g"))))
  (instance $inst (export "g" (func $g)))
  (export "local:t/other" (instance $inst)))
"#;

// rivet: verifies SWV-123
#[test]
fn async_lower_edge_between_fused_components_is_refused() {
    let err = fuse(&[ASYNC_CALLER, CALLEE]).expect_err("an async-lower edge must be refused");
    assert!(err.contains("#548"), "error cites #548: {err}");
    assert!(err.contains("ADR-10"), "error cites ADR-10: {err}");
    assert!(
        err.contains("local:t/i#f"),
        "error names the callee export: {err}"
    );
    assert!(
        err.contains("[async-lower]f"),
        "error names the caller import: {err}"
    );
}

// rivet: verifies SWV-123
#[test]
fn async_lower_import_to_an_unrelated_component_is_not_refused() {
    // Negative control for the refusal: same caller, but no fused component
    // implements `local:t/i`, so the import is left to the host.
    let core = fuse(&[ASYNC_CALLER, OTHER_CALLEE]).expect("no edge, so no refusal");
    assert!(
        imports(&core)
            .iter()
            .any(|(m, f)| m == "local:t/i" && f == "[async-lower]f"),
        "the host-bound import is present: {:?}",
        imports(&core)
    );
}

// rivet: verifies SWV-124
#[test]
fn host_bound_async_lower_import_keeps_the_producer_prefix() {
    let core = fuse(&[ASYNC_CALLER]).expect("a lone caller fuses");
    let imps = imports(&core);
    assert!(
        imps.iter()
            .any(|(m, f)| m == "local:t/i" && f == "[async-lower]f"),
        "async lowering keeps `[async-lower]`: {imps:?}"
    );
    assert!(
        !imps.iter().any(|(m, f)| m == "local:t/i" && f == "f"),
        "the bare sync name must not appear (#557): {imps:?}"
    );
}

/// wit-component's shim pattern in miniature: `stream.read` takes a memory
/// option, so it is exported from a `FromExports` instance as "0" and a fixup
/// module imports it as `"actual" "0"`.
const SHIM_STREAM_READ: &str = r#"
(component
  (core module $mm
    (memory (export "memory") 1)
    (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 0))
  (core instance $mi (instantiate $mm))
  (alias core export $mi "memory" (core memory $mem))
  (alias core export $mi "cabi_realloc" (core func $rea))
  (type $st (stream u8))
  (canon stream.read $st async (memory $mem) (realloc $rea) (core func $sr))
  (core instance $actual (export "0" (func $sr)))
  (core module $fixup
    (import "actual" "0" (func (param i32 i32 i32) (result i32))))
  (core instance $fx (instantiate $fixup (with "actual" (instance $actual)))))
"#;

// rivet: verifies SWV-125
#[test]
fn stream_read_through_the_shim_is_refused_not_leaked() {
    let err = fuse(&[SHIM_STREAM_READ]).expect_err("must be refused");
    assert!(err.contains("stream.read"), "names the built-in: {err}");
    assert!(err.contains("#558"), "cites #558: {err}");
}

/// No shim: the payload needs no realloc and the module imports its memory,
/// so wit-component hands `stream.read` to the module under its producer
/// name. That import is host-servable and must pass through, not be refused.
const DIRECT_STREAM_READ: &str = r#"
(component
  (core module $mm (memory (export "memory") 1))
  (core instance $mi (instantiate $mm))
  (alias core export $mi "memory" (core memory $mem))
  (type $st (stream u8))
  (canon stream.read $st async (memory $mem) (core func $sr))
  (core instance $rootinst (export "[async-lower][stream-read-0]f" (func $sr)))
  (core module $main
    (import "env" "memory" (memory 1))
    (import "$root" "[async-lower][stream-read-0]f" (func (param i32 i32 i32) (result i32)))
    (func (export "run")))
  (core instance $envinst (export "memory" (memory $mem)))
  (core instance $ci (instantiate $main
    (with "env" (instance $envinst)) (with "$root" (instance $rootinst)))))
"#;

// rivet: verifies SWV-125
#[test]
fn producer_named_stream_read_is_not_refused() {
    // Negative control for the #558 refusal (found by the local Mythos pass
    // on PR #559): the refusal must be limited to the shim's internal name.
    let core = fuse(&[DIRECT_STREAM_READ]).expect("producer-named stream.read must pass through");
    let imps = imports(&core);
    assert!(
        imps.iter()
            .any(|(m, f)| m == "$root" && f == "[async-lower][stream-read-0]f"),
        "the producer-named import is kept: {imps:?}"
    );
}

/// #560: a world-level func import lowered with the async option. meld used
/// to emit it as `(import "f" "")` with the async core type, which a host
/// binds as a sync call.
const WORLD_ASYNC_CALLER: &str = r#"
(component
  (import "f" (func $f async))
  (core func $lf (canon lower (func $f) async))
  (core module $m
    (import "$root" "[async-lower]f" (func (result i32)))
    (func (export "run")))
  (core instance $imp (export "[async-lower]f" (func $lf)))
  (core instance $ci (instantiate $m (with "$root" (instance $imp)))))
"#;

/// Control for #560: the same world-level import lowered synchronously keeps
/// fusing under `(import "f" "")`.
const WORLD_SYNC_CALLER: &str = r#"
(component
  (import "f" (func $f))
  (core func $lf (canon lower (func $f)))
  (core module $m
    (import "$root" "f" (func))
    (func (export "run")))
  (core instance $imp (export "f" (func $lf)))
  (core instance $ci (instantiate $m (with "$root" (instance $imp)))))
"#;

// rivet: verifies SWV-126
#[test]
fn async_lowered_world_func_import_is_refused() {
    let err =
        fuse(&[WORLD_ASYNC_CALLER]).expect_err("must be refused, not emitted as a sync import");
    assert!(err.contains("#560"), "cites #560: {err}");
    assert!(err.contains("[async-lower]f"), "names the import: {err}");
}

// rivet: verifies SWV-126
#[test]
fn sync_lowered_world_func_import_still_fuses() {
    let core = fuse(&[WORLD_SYNC_CALLER]).expect("a sync world-level import is unaffected");
    let imps = imports(&core);
    assert!(
        imps.iter().any(|(m, f)| m == "f" && f.is_empty()),
        "keeps (import \"f\" \"\"): {imps:?}"
    );
}

/// Callee exporting a WORLD-level `f: async func()`, lifted with the
/// stackless callback ABI.
const WORLD_CALLEE: &str = r#"
(component
  (core module $m
    (func (export "[async-lift]f") (result i32) i32.const 0)
    (func (export "[callback][async-lift]f") (param i32 i32 i32) (result i32) i32.const 0))
  (core instance $ci (instantiate $m))
  (type $ft (func async))
  (func $f (type $ft)
    (canon lift (core func $ci "[async-lift]f") async
      (callback (core func $ci "[callback][async-lift]f"))))
  (export "f" (func $f)))
"#;

// rivet: verifies SWV-126
#[test]
fn async_lowered_world_import_served_by_a_fused_component_is_the_548_edge() {
    // The world-level async caller is wired to a fused callee: this is the
    // #548 edge, not a host-bound #560 import, and must say so.
    let err =
        fuse(&[WORLD_ASYNC_CALLER, WORLD_CALLEE]).expect_err("an async-lower edge must be refused");
    assert!(err.contains("#548"), "cites #548: {err}");
    assert!(!err.contains("#560"), "not misattributed to #560: {err}");
}

/// The wasmtime / component-model test-suite naming: an instance-export
/// lowering with the async option whose core import carries NO
/// `[async-lower]` prefix. A name-based check misses it.
const ASYNC_CALLER_UNPREFIXED: &str = r#"
(component
  (import "local:t/i" (instance $i (export "f" (func async))))
  (alias export $i "f" (func $f))
  (core func $lf (canon lower (func $f) async))
  (core module $m
    (import "local:t/i" "f" (func (result i32)))
    (func (export "run")))
  (core instance $imp (export "f" (func $lf)))
  (core instance $ci (instantiate $m (with "local:t/i" (instance $imp)))))
"#;

// rivet: verifies SWV-126
#[test]
fn async_lower_edge_is_refused_whatever_the_core_import_is_named() {
    let err = fuse(&[ASYNC_CALLER_UNPREFIXED, CALLEE])
        .expect_err("the async option decides, not the field name");
    assert!(err.contains("#548"), "cites #548: {err}");
}
