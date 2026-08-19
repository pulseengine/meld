//! SR-56 / LS-M-12 (#370) oracle: `--memory shared` fusion without rebasing
//! places every component's data at its source offset in one shared linear
//! memory. When two components share an offset (the wasm-ld base 1048576 is
//! the common case), their active data segments overlap — the later segment
//! silently overwrites the earlier one at instantiation (later-wins), so the
//! fuse succeeds with a clean exit while corrupting a component's data.
//!
//! SR-56 makes that loud: the emitted-module overlap check hard-fails. These
//! tests are the oracle — the negative case must be rejected, and the two
//! positive cases pin the false-positive boundary (disjoint and merely
//! adjacent segments must still fuse).

use meld_core::{
    CustomSectionHandling, DwarfHandling, Error, Fuser, FuserConfig, MemoryStrategy, OutputFormat,
};

/// A component whose single core module writes 4 bytes at `offset` in a
/// 17-page memory (17 * 65536 = 1114112 B, enough to hold the base 1048576
/// plus the 4-byte word) and lifts a `read` returning that word.
fn comp(offset: u32, kebab: &str) -> Vec<u8> {
    let wat = format!(
        r#"(component
          (core module $m (memory (export "mem") 17)
            (data (i32.const {off}) "\aa\bb\cc\dd")
            (func (export "read") (result i32) (i32.load (i32.const {off}))))
          (core instance $i (instantiate $m))
          (alias core export $i "read" (core func $f))
          (func $l (result u32) (canon lift (core func $f)))
          (export "{k}" (func $l)))"#,
        off = offset,
        k = kebab,
    );
    wat::parse_str(&wat).unwrap()
}

/// Fuse two single-data-segment components under `--memory shared` with no
/// address rebasing (the #370 configuration).
fn fuse_shared(a_off: u32, b_off: u32) -> meld_core::Result<Vec<u8>> {
    let a = comp(a_off, "read-a");
    let b = comp(b_off, "read-b");
    let cfg = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        attestation: false,
        reproducible: false,
        component_provenance: false,
        address_rebasing: false,
        pack_rebase: false,
        share_stack: false,
        profile: meld_core::Profile::Ecosystem,
        preserve_names: false,
        custom_sections: CustomSectionHandling::Drop,
        dwarf_handling: DwarfHandling::Strip,
        output_format: OutputFormat::CoreModule,
        opaque_resources: vec![],
    };
    let mut f = Fuser::new(cfg);
    f.add_component_named(&a, Some("a")).unwrap();
    f.add_component_named(&b, Some("b")).unwrap();
    f.fuse_with_stats().map(|(bytes, _)| bytes)
}

/// NEGATIVE: both components put data at the wasm-ld base 1048576. Without
/// rebasing the segments overlap → SR-56 must hard-fail rather than emit a
/// silently-corrupting module.
#[test]
fn shared_overlap_at_same_base_is_rejected() {
    let err = fuse_shared(1048576, 1048576).expect_err("overlapping segments must be rejected");
    eprintln!("SR-56 rejected overlap with: {err}");
    match err {
        Error::OverlappingDataSegments {
            pair_count,
            memory_index,
            second_start,
            ..
        } => {
            assert_eq!(pair_count, 1, "exactly one overlapping pair expected");
            assert_eq!(memory_index, 0, "overlap is in the shared memory 0");
            assert_eq!(second_start, 1048576, "overlap starts at the wasm-ld base");
        }
        other => panic!("expected OverlappingDataSegments, got: {other:?}"),
    }
}

/// POSITIVE (disjoint): well-separated source offsets stay disjoint in the
/// shared memory, so the check must NOT false-positive.
#[test]
fn shared_disjoint_segments_fuse_clean() {
    let fused = fuse_shared(100, 200).expect("disjoint segments must fuse clean");
    assert!(!fused.is_empty(), "fused module produced");
}

/// POSITIVE (adjacent boundary): `[0, 4)` and `[4, 8)` touch but do not
/// overlap. The detector uses `start < max_end` (strict), so this must pass —
/// it pins the off-by-one that a `<=` comparison would introduce.
#[test]
fn shared_adjacent_segments_are_not_overlap() {
    let fused = fuse_shared(0, 4).expect("adjacent (non-overlapping) segments must fuse");
    assert!(!fused.is_empty(), "fused module produced");
}
