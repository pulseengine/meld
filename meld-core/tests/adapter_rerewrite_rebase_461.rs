//! #461: the adapter re-rewrite must not discard shared-memory rebasing.
//!
//! Under `--memory shared --address-rebase`, a module whose import is
//! redirected to an adapter had every function body regenerated FROM THE
//! ORIGINAL MODULE BYTES with `memory_base_offset = 0`, replacing the bodies
//! the merge pass had already rebased. Its data segments were not regenerated,
//! so they kept their rebased addresses: data moved, code reverted, and the
//! module read a neighbour's statics at exit 0 with validation passing.
//!
//! Reported by @cpetig with the three components in
//! `tests/fixtures/issue_461` (see the README there for provenance and why a
//! synthetic fixture would not trigger it).
//!
//! The assertion is structural rather than a golden file: every absolute
//! address in the third component's code must land inside the window it was
//! placed in. A golden output would also have caught this, but it would break
//! on any unrelated encoding change and say nothing about why.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use std::path::Path;

fn fixture(name: &str) -> Vec<u8> {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/issue_461")
        .join(name);
    std::fs::read(&p).unwrap_or_else(|e| panic!("fixture {}: {e}", p.display()))
}

/// Every explicit `offset=` immediate on a memory instruction in the fused
/// module, read back from the encoded bytes.
fn memory_offsets(wasm: &[u8]) -> Vec<u64> {
    use wasmparser::{Parser, Payload};
    let mut out = Vec::new();
    for payload in Parser::new(0).parse_all(wasm) {
        let Ok(Payload::CodeSectionEntry(body)) = payload else {
            continue;
        };
        let Ok(reader) = body.get_operators_reader() else {
            continue;
        };
        for op in reader {
            let Ok(op) = op else { continue };
            // every load/store carries a MemArg; match on the shared shape
            let memarg = match op {
                wasmparser::Operator::I32Load { memarg }
                | wasmparser::Operator::I64Load { memarg }
                | wasmparser::Operator::F32Load { memarg }
                | wasmparser::Operator::F64Load { memarg }
                | wasmparser::Operator::I32Load8S { memarg }
                | wasmparser::Operator::I32Load8U { memarg }
                | wasmparser::Operator::I32Load16S { memarg }
                | wasmparser::Operator::I32Load16U { memarg }
                | wasmparser::Operator::I64Load8S { memarg }
                | wasmparser::Operator::I64Load8U { memarg }
                | wasmparser::Operator::I64Load16S { memarg }
                | wasmparser::Operator::I64Load16U { memarg }
                | wasmparser::Operator::I64Load32S { memarg }
                | wasmparser::Operator::I64Load32U { memarg }
                | wasmparser::Operator::I32Store { memarg }
                | wasmparser::Operator::I64Store { memarg }
                | wasmparser::Operator::F32Store { memarg }
                | wasmparser::Operator::F64Store { memarg }
                | wasmparser::Operator::I32Store8 { memarg }
                | wasmparser::Operator::I32Store16 { memarg }
                | wasmparser::Operator::I64Store8 { memarg }
                | wasmparser::Operator::I64Store16 { memarg }
                | wasmparser::Operator::I64Store32 { memarg } => memarg,
                _ => continue,
            };
            out.push(memarg.offset);
        }
    }
    out
}

fn fuse_the_three() -> Vec<u8> {
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    for name in [
        "falcon_cascade_estimator_cm.wasm",
        "falcon_cascade_control_cm.wasm",
        "falcon_cascade_split_cm.wasm",
    ] {
        let bytes = fixture(name);
        fuser
            .add_component_named(&bytes, Some(name))
            .unwrap_or_else(|e| panic!("add {name}: {e}"));
    }
    fuser.fuse().expect("fuse must succeed on these inputs")
}

/// The component placed at the highest base must have its code rebased into
/// that window.
///
/// Before the fix the fused module held **zero** memory offsets at or above
/// 128K while `split` was placed at 131072 — every one of its 95 absolute
/// offsets had reverted to its pre-fusion value, landing inside the first
/// component's region.
#[test]
fn the_last_placed_component_has_its_code_rebased() {
    let fused = fuse_the_three();
    let offsets = memory_offsets(&fused);
    assert!(
        !offsets.is_empty(),
        "no memory offsets found at all — the reader found nothing, so this \
         test would pass regardless of the bug"
    );

    // split is the third component and is placed at 131072 (2 pages in).
    const SPLIT_BASE: u64 = 131_072;
    let in_split_window = offsets.iter().filter(|&&o| o >= SPLIT_BASE).count();
    assert!(
        in_split_window > 0,
        "no load/store offset lands at or above {SPLIT_BASE}, so the component \
         placed there has un-rebased code while its data segments were moved — \
         it reads another component's memory (#461). Found {} offsets, highest {:?}",
        offsets.len(),
        offsets.iter().max()
    );
}

/// The specific addresses from the report, shifted by exactly the base.
///
/// Pinned because the generic assertion above would also pass if only SOME of
/// split's offsets were rebased, and a partial rebase is just as wrong.
#[test]
fn the_reported_offsets_are_shifted_by_exactly_the_base() {
    let fused = fuse_the_three();
    let offsets = memory_offsets(&fused);
    const SPLIT_BASE: u64 = 131_072;

    // (original offset, how many times it occurs in split's input)
    for (original, count) in [(8224u64, 6usize), (8420, 10), (16624, 6)] {
        let rebased = original + SPLIT_BASE;
        let found = offsets.iter().filter(|&&o| o == rebased).count();
        assert_eq!(
            found,
            count,
            "offset {original} should appear {count}x as {rebased} after rebasing; \
             found {found}. Un-rebased copies still present: {}",
            offsets.iter().filter(|&&o| o == original).count()
        );
    }
}
