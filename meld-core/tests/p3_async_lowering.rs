//! Integration tests for the P3 async foundation (issue #94).
//!
//! These tests exercise the *foundation* layer of P3 async support:
//!
//! 1. Detection — meld correctly identifies P3 `stream<T>` / `future<T>` types
//!    and async canonical built-ins in a component.
//! 2. Host-intrinsic ABI — the documented `pulseengine:async` ABI surface
//!    is stable and complete for the canonical built-ins meld already parses.
//! 3. End-to-end fusion — a synthetic component using `stream<u8>` parses
//!    and is summarised correctly via `Fuser::p3_async_summary`.
//!
//! The actual lowering pass that rewrites `(canon stream.new)` to
//! `(import "pulseengine:async" "stream_new" ...)` calls in the fused
//! output is **deferred** to a follow-up PR (see ADR-1). This file is
//! deliberately scoped to the foundation layer so that lowering can be
//! added incrementally without changing the ABI contract or detection API.

use meld_core::p3_async::{HOST_INTRINSIC_MODULE, HostIntrinsic, P3AsyncFeatures};
use meld_core::{Fuser, FuserConfig};

/// Helper: collect all imports under module `pulseengine:async` from a
/// fused core-module byte blob.
fn collect_pulseengine_async_imports(fused: &[u8]) -> Vec<String> {
    let parser = wasmparser::Parser::new(0);
    let mut out = Vec::new();
    for payload in parser.parse_all(fused) {
        if let Ok(wasmparser::Payload::ImportSection(reader)) = payload {
            for imp in reader.into_imports() {
                if let Ok(imp) = imp
                    && imp.module == HOST_INTRINSIC_MODULE
                {
                    out.push(imp.name.to_string());
                }
            }
        }
    }
    out.sort();
    out
}

// ---------------------------------------------------------------------------
// ABI-level invariants
// ---------------------------------------------------------------------------

/// The host-intrinsic module name is stable. Downstream runtimes (kiln,
/// wasmtime, …) depend on this constant. Changing it is a breaking change.
#[test]
fn host_intrinsic_module_name_is_stable() {
    assert_eq!(
        meld_core::p3_async::HOST_INTRINSIC_MODULE,
        "pulseengine:async"
    );
}

/// All 14 canonical-built-in → intrinsic mappings produce imports under the
/// `pulseengine:async` module with non-empty, distinct names.
#[test]
fn all_intrinsics_emit_pulseengine_async_imports() {
    let all = [
        HostIntrinsic::StreamNew,
        HostIntrinsic::StreamRead,
        HostIntrinsic::StreamWrite,
        HostIntrinsic::StreamCancelRead,
        HostIntrinsic::StreamCancelWrite,
        HostIntrinsic::StreamDropReadable,
        HostIntrinsic::StreamDropWritable,
        HostIntrinsic::FutureNew,
        HostIntrinsic::FutureRead,
        HostIntrinsic::FutureWrite,
        HostIntrinsic::FutureCancelRead,
        HostIntrinsic::FutureCancelWrite,
        HostIntrinsic::FutureDropReadable,
        HostIntrinsic::FutureDropWritable,
    ];

    let mut seen = std::collections::HashSet::new();
    for intr in all {
        let (module, name) = intr.import();
        assert_eq!(module, "pulseengine:async");
        assert!(!name.is_empty(), "intrinsic {intr:?} has empty name");
        assert!(seen.insert(name), "duplicate intrinsic name: {name}");
    }
    assert_eq!(seen.len(), 14);
}

// ---------------------------------------------------------------------------
// End-to-end parse + detect: stream<u8>
// ---------------------------------------------------------------------------

/// Build a minimal P3 component that exposes a `stream<u8>` type and the
/// canonical built-ins to allocate, read, write, and drop it.
///
/// The component shape:
/// ```wit
/// type byte-stream = stream<u8>;
/// // canonical built-ins materialised via (canon stream.* ...) at the
/// // component level.
/// ```
///
/// Note: this test does NOT assert that fusion-lowering rewrites these
/// canonicals to `pulseengine:async/*` imports — that's deferred.
/// It DOES assert that:
///   * The parser identifies the `stream<u8>` type.
///   * `detect_features` returns the expected `HostIntrinsic` set.
///   * `Fuser::p3_async_summary` exposes the same view to consumers.
fn build_stream_u8_component_wat() -> &'static str {
    // Tiny core module that just defines memory + a no-op realloc, so the
    // canon stream.read/write options can reference it. The component's
    // job here is purely to exercise the type/canon detection paths.
    //
    // Using $idx based core funcs declared via canon stream.* — these are
    // recognised by wasmparser as P3 async canonical built-ins.
    r#"
(component
  (core module $m
    (memory (export "memory") 1)
    (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
      i32.const 0)
  )
  (core instance $i (instantiate $m))
  (alias core export $i "memory" (core memory $mem))
  (alias core export $i "cabi_realloc" (core func $rea))

  (type $st (stream u8))

  (canon stream.new $st (core func $sn))
  (canon stream.read $st async (memory $mem) (realloc $rea) (core func $sr))
  (canon stream.write $st async (memory $mem) (realloc $rea) (core func $sw))
  (canon stream.drop-readable $st (core func $sdr))
  (canon stream.drop-writable $st (core func $sdw))
)
"#
}

/// Parse the stream<u8> component WAT and verify detection. This is the
/// "stream<u8> e2e" milestone for the foundation PR — everything from
/// parsing through detection works correctly.
#[test]
fn stream_u8_component_detected_end_to_end() {
    let wat_src = build_stream_u8_component_wat();
    let bytes = match wat::parse_str(wat_src) {
        Ok(b) => b,
        Err(e) => {
            // If the wat crate version doesn't yet support P3 stream syntax,
            // skip rather than fail — the unit tests in `p3_async::tests`
            // still cover the detection logic against synthetic input.
            eprintln!("skipping: wat crate cannot parse P3 stream syntax: {e}");
            return;
        }
    };

    let mut fuser = Fuser::new(FuserConfig::default());
    fuser
        .add_component_named(&bytes, Some("stream-u8-fixture"))
        .expect("parser should accept P3 component (no longer rejected)");

    let summary = fuser.p3_async_summary();
    assert_eq!(summary.len(), 1, "exactly one component added");

    let (name, feats) = &summary[0];
    assert_eq!(name.as_deref(), Some("stream-u8-fixture"));

    assert!(
        !feats.is_empty(),
        "stream<u8> component should not be P3-clean"
    );
    assert!(feats.uses_data_plane(), "stream is a data-plane construct");
    assert!(
        !feats.stream_types.is_empty(),
        "expected at least one stream<T> type, got {feats:?}"
    );

    // Canonicals should map to the expected intrinsic set.
    assert!(
        feats
            .required_intrinsics
            .contains(&HostIntrinsic::StreamNew),
        "missing StreamNew in {:?}",
        feats.required_intrinsics
    );
    assert!(
        feats
            .required_intrinsics
            .contains(&HostIntrinsic::StreamRead),
        "missing StreamRead in {:?}",
        feats.required_intrinsics
    );
    assert!(
        feats
            .required_intrinsics
            .contains(&HostIntrinsic::StreamWrite),
        "missing StreamWrite in {:?}",
        feats.required_intrinsics
    );
    assert!(
        feats
            .required_intrinsics
            .contains(&HostIntrinsic::StreamDropReadable),
        "missing StreamDropReadable in {:?}",
        feats.required_intrinsics
    );
    assert!(
        feats
            .required_intrinsics
            .contains(&HostIntrinsic::StreamDropWritable),
        "missing StreamDropWritable in {:?}",
        feats.required_intrinsics
    );
}

// ---------------------------------------------------------------------------
// Lowering pass: stream<u8> emits pulseengine:async imports (issue #120)
// ---------------------------------------------------------------------------

/// After `Fuser::fuse()`, the `stream<u8>` fixture's import section must
/// contain entries under module `pulseengine:async` whose names exactly
/// match the [`HostIntrinsic`] set returned by `p3_async_summary()`.
///
/// This is the acceptance test for issue #120 (lowering pass) — the
/// foundation PR (#94) only ships detection; this PR rewrites the
/// component-level `(canon stream.*)` built-ins into core-module
/// imports.
#[test]
fn stream_u8_lowering_emits_pulseengine_async_imports() {
    let wat_src = build_stream_u8_component_wat();
    let bytes = match wat::parse_str(wat_src) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("skipping: wat crate cannot parse P3 stream syntax: {e}");
            return;
        }
    };

    let mut fuser = Fuser::new(FuserConfig::default());
    fuser
        .add_component_named(&bytes, Some("stream-u8-fixture"))
        .expect("parser should accept the P3 component");

    // Snapshot the required intrinsics BEFORE fusing so we can compare
    // against the import section AFTER.
    let summary = fuser.p3_async_summary();
    let (_, feats) = &summary[0];
    let mut expected_names: Vec<String> = feats
        .required_intrinsics
        .iter()
        .map(|i| i.name().to_string())
        .collect();
    expected_names.sort();
    assert!(
        !expected_names.is_empty(),
        "fixture should declare at least one P3 async intrinsic"
    );

    // Fuse and inspect the import section.
    let fused = fuser.fuse().expect("fuse should succeed");
    let imports_under_pulseengine_async = collect_pulseengine_async_imports(&fused);

    assert_eq!(
        imports_under_pulseengine_async, expected_names,
        "lowering pass must emit one import per detected intrinsic; \
         got {imports_under_pulseengine_async:?}, expected {expected_names:?}"
    );
}

// ---------------------------------------------------------------------------
// Lowering pass: future<T> symmetric coverage
// ---------------------------------------------------------------------------

/// A minimal P3 component that exercises the `future<T>` family of
/// canonical built-ins. Symmetric to `stream<u8>` — uses the same
/// shape/idioms, just with `future` instead of `stream` and an `s32`
/// payload instead of `u8`.
fn build_future_s32_component_wat() -> &'static str {
    r#"
(component
  (core module $m
    (memory (export "memory") 1)
    (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
      i32.const 0)
  )
  (core instance $i (instantiate $m))
  (alias core export $i "memory" (core memory $mem))
  (alias core export $i "cabi_realloc" (core func $rea))

  (type $ft (future s32))

  (canon future.new $ft (core func $fn))
  (canon future.read $ft async (memory $mem) (realloc $rea) (core func $fr))
  (canon future.write $ft async (memory $mem) (realloc $rea) (core func $fw))
  (canon future.drop-readable $ft (core func $fdr))
  (canon future.drop-writable $ft (core func $fdw))
)
"#
}

/// Fuse-only acceptance test for `future<T>`: same shape as the
/// stream<u8> assertion, but exercises the symmetric `future_*` half of
/// the host-intrinsic ABI.
#[test]
fn future_s32_lowering_emits_pulseengine_async_imports() {
    let wat_src = build_future_s32_component_wat();
    let bytes = match wat::parse_str(wat_src) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("skipping: wat crate cannot parse P3 future syntax: {e}");
            return;
        }
    };

    let mut fuser = Fuser::new(FuserConfig::default());
    fuser
        .add_component_named(&bytes, Some("future-s32-fixture"))
        .expect("parser should accept the P3 component");

    let summary = fuser.p3_async_summary();
    let (_, feats) = &summary[0];

    // The fixture should at minimum declare future-data-plane intrinsics.
    assert!(feats.uses_data_plane(), "future is a data-plane construct");
    assert!(
        feats
            .required_intrinsics
            .contains(&HostIntrinsic::FutureNew),
        "missing FutureNew in {:?}",
        feats.required_intrinsics
    );
    assert!(
        feats
            .required_intrinsics
            .contains(&HostIntrinsic::FutureRead),
        "missing FutureRead in {:?}",
        feats.required_intrinsics
    );

    let mut expected_names: Vec<String> = feats
        .required_intrinsics
        .iter()
        .map(|i| i.name().to_string())
        .collect();
    expected_names.sort();

    let fused = fuser.fuse().expect("fuse should succeed");
    let imports_under_pulseengine_async = collect_pulseengine_async_imports(&fused);

    assert_eq!(
        imports_under_pulseengine_async, expected_names,
        "lowering pass must emit one import per detected future intrinsic"
    );

    // Spot-check: every emitted name must actually be a future_* intrinsic.
    for name in &imports_under_pulseengine_async {
        assert!(
            name.starts_with("future_"),
            "future fixture must only emit future_* intrinsics, got '{name}'"
        );
    }
}

// ---------------------------------------------------------------------------
// Regression: P2 components stay P3-async-clean
// ---------------------------------------------------------------------------

/// A purely-P2 component (no stream/future, no async lift/lower) must
/// produce an *empty* `P3AsyncFeatures` summary. This guards against
/// false positives in detection.
#[test]
fn pure_p2_component_has_no_p3_features() {
    let wat_src = r#"
(component
  (core module $m
    (memory (export "memory") 1)
    (func (export "f") (param i32) (result i32) local.get 0)
  )
  (core instance $i (instantiate $m))
  (alias core export $i "memory" (core memory $mem))
  (alias core export $i "f" (core func $f))
  (type $ft (func (param "x" u32) (result u32)))
  (canon lift (core func $f) (memory $mem) (func (type $ft)))
)
"#;
    let bytes = wat::parse_str(wat_src).expect("WAT should parse");
    let mut fuser = Fuser::new(FuserConfig::default());
    fuser
        .add_component_named(&bytes, Some("pure-p2"))
        .expect("P2 component should parse");

    let summary = fuser.p3_async_summary();
    assert_eq!(summary.len(), 1);
    let (_, feats) = &summary[0];
    assert!(
        feats.is_empty(),
        "pure P2 component should have empty features, got {feats:?}"
    );

    // And — critically for issue #120 — the lowering pass must be a
    // no-op on P2 components: no pulseengine:async imports appear in
    // the fused output.
    let fused = fuser.fuse().expect("P2 fusion should succeed");
    let imports_under_pulseengine_async = collect_pulseengine_async_imports(&fused);
    assert!(
        imports_under_pulseengine_async.is_empty(),
        "P2 component should produce zero pulseengine:async imports, got {imports_under_pulseengine_async:?}"
    );
}

// ---------------------------------------------------------------------------
// Regression: `P3AsyncFeatures::is_empty()` round-trip
// ---------------------------------------------------------------------------

/// A default-constructed `P3AsyncFeatures` is empty. (Sanity check on the
/// foundation API contract.)
#[test]
fn default_features_is_empty() {
    let f = P3AsyncFeatures::default();
    assert!(f.is_empty());
    assert!(!f.uses_data_plane());
    assert!(!f.uses_control_plane());
}
