//! #662: since 0.68 (#558) meld refused a `stream.write` that wit-component
//! routes through its indirect-call shim. The fixup module imports it as
//! `"" "0"` (or `"actual" "0"`), a name no host can serve, and meld had no
//! producer name for it.
//!
//! The producer name is recoverable from the component itself: the fixup is
//! instantiated with the shim module's `$imports` table, and the real module
//! imports the shim's export `"0"` as `[async-lower][stream-write-0]get`.
//! meld now emits the built-in under that name, after checking that it names
//! the same built-in family as the canonical function wired to it, and the
//! import map describes it: kind, element size and alignment, async, and the
//! memory and encoding from the built-in's own canonical options.
//!
//! `stream_write_via_shim.wat` is the reporter's 510-byte component
//! (`x.wit` + `a.core.wat`, printed). `stream_write_misnamed_read.wat` is the
//! same component with the producer name changed to `stream-read`: the name
//! no longer matches the wired `stream.write`, so meld still refuses.

use std::path::Path;

use meld_core::import_map::{BuiltinInfo, LowerOption};
use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn fixture(name: &str) -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/issue_662")
        .join(name);
    wat::parse_file(&path).unwrap_or_else(|e| panic!("tracked fixture {name}: {e}"))
}

fn fuse(bytes: &[u8]) -> meld_core::Result<(Vec<u8>, meld_core::FusionStats)> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component(bytes)?;
    fuser.fuse_with_stats()
}

#[test]
fn shim_routed_stream_write_gets_its_producer_name() {
    let (fused, stats) = fuse(&fixture("stream_write_via_shim.wat")).expect("fuses");
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&fused)
        .expect("fused module validates");

    let write = stats
        .import_map
        .iter()
        .find(|e| e.name == "[async-lower][stream-write-0]get")
        .unwrap_or_else(|| {
            panic!(
                "producer-named stream.write import: {:#?}",
                stats.import_map
            )
        });
    assert_eq!(write.module, "[export]test:x/api");
    assert_eq!(write.component, Some(0));
    assert_eq!(
        write.builtin,
        Some(BuiltinInfo {
            kind: "stream-write".into(),
            element: Some((4, 4)),
            async_: true,
        })
    );
    match &write.memory {
        LowerOption::Present(m) => assert_eq!(m.index, 0),
        other => panic!("stream.write names its memory: {other:?}"),
    }
    assert_eq!(write.realloc, LowerOption::Absent);

    assert!(
        !stats
            .import_map
            .iter()
            .any(|e| e.name.parse::<u32>().is_ok()),
        "no shim-index import may be left: {:#?}",
        stats.import_map
    );
    let new = stats
        .import_map
        .iter()
        .find(|e| e.name == "[stream-new-0]get")
        .expect("stream.new import");
    assert_eq!(
        new.builtin.as_ref().map(|b| b.kind.as_str()),
        Some("stream-new")
    );
    assert_eq!(new.memory, LowerOption::Absent, "stream.new has no options");
}

#[test]
fn producer_name_of_another_builtin_is_still_refused() {
    let err = fuse(&fixture("stream_write_misnamed_read.wat"))
        .expect_err("a stream-read name on a stream.write: meld must not emit it");
    assert!(err.to_string().contains("#558"), "unexpected error: {err}");
}
