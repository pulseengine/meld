//! SR-83 (#426) — a count declared in a section header is bounded by the
//! section's bytes.
//!
//! These helpers deliberately read the count *without* parsing the entries, so
//! the number is whatever the input claims. The per-module segment index map
//! was sized from it directly: local indices `0..count` each get an entry.
//!
//! A 60-byte fuzz input whose **9-byte** element section declares
//! **134,069,110** segments therefore cost 95 seconds and gigabytes — and then
//! returned the parse error it could have returned immediately. libFuzzer
//! reports that as an out-of-memory under its 2 GB limit, which is how it
//! surfaced.
//!
//! The input lives in `fuzz/corpus/fuzz_merger_idempotent/` so the fuzzer
//! replays it, and is driven here so the property is checked without a fuzz
//! run.

use meld_core::merger::Merger;
use meld_core::{ComponentParser, MemoryStrategy, Resolver};

/// The fuzz finding, byte for byte.
fn oom_input() -> Option<Vec<u8>> {
    std::fs::read(format!(
        "{}/../fuzz/corpus/fuzz_merger_idempotent/oom_426_element_count.bin",
        env!("CARGO_MANIFEST_DIR")
    ))
    .ok()
}

/// What the input claims, versus what its bytes can hold.
// rivet: verifies SR-83
#[test]
fn a_declared_count_cannot_exceed_its_section() {
    let Some(data) = oom_input() else {
        panic!(
            "corpus input absent — every fixture a test reads is tracked in the repository \
             (SR-85); a missing one is a repository error, not a reason to report success"
        );
    };
    let parsed = ComponentParser::without_validation()
        .parse(&data)
        .expect("the input parses; the defect is downstream of parsing");
    let module = parsed
        .core_modules
        .first()
        .expect("guard: the input carries a core module");

    let (start, end) = module
        .element_section_range
        .expect("guard: the input carries an element section — the declared count lives there");
    let section_len = (end - start) as u32;
    assert_eq!(section_len, 9, "guard: the section is 9 bytes");

    let counted = meld_core::segments::count_element_segments(module);
    assert!(
        counted <= section_len,
        "SR-83: a {section_len}-byte section cannot hold {counted} segments — every segment \
         costs at least a byte, and the index map gets an entry per counted index"
    );
}

/// The property that actually matters: work is bounded by the input. Merging
/// this 60-byte input took 94.8 s before the clamp and 187 µs after, so the
/// budget is generous by three orders of magnitude and still fails loudly if
/// the count is trusted again.
// rivet: verifies SR-83
#[test]
fn merging_a_hostile_count_stays_bounded() {
    let Some(data) = oom_input() else {
        panic!(
            "corpus input absent — every fixture a test reads is tracked in the repository \
             (SR-85); a missing one is a repository error, not a reason to report success"
        );
    };
    let parsed = ComponentParser::without_validation()
        .parse(&data)
        .expect("parses");
    let components = vec![parsed];
    let graph = Resolver::with_strategy(MemoryStrategy::MultiMemory)
        .resolve(&components)
        .expect("resolves");

    let started = std::time::Instant::now();
    let outcome = Merger::new(MemoryStrategy::MultiMemory, false).merge(&components, &graph);
    let elapsed = started.elapsed();

    // It still fails — the module is malformed — but it fails at once rather
    // than after materialising 134 million map entries.
    assert!(
        outcome.is_err(),
        "guard: this input is malformed and must still be rejected, not merged"
    );
    assert!(
        elapsed < std::time::Duration::from_secs(5),
        "SR-83: merging 60 bytes took {elapsed:?}; a declared count is being trusted beyond \
         the bytes that back it"
    );
}
