//! Parser robustness fuzz target.
//!
//! Property: `ComponentParser::parse(bytes)` must NEVER panic, abort, or
//! consume unbounded memory on arbitrary byte input. It is allowed (and
//! expected) to return an `Err` for malformed binaries.
//!
//! This target is the single biggest dynamic-V&V gap for meld: the parser
//! consumes untrusted component binaries and feeds the rest of the pipeline.
//! A panic here is a crash bug; an OOM is a denial-of-service vector.
#![no_main]

use libfuzzer_sys::fuzz_target;
use meld_core::ComponentParser;

fuzz_target!(|data: &[u8]| {
    // Disable validation to drive the parser harder. Validation is itself a
    // wasmparser invariant we trust; the parser-state-machine is what we are
    // fuzzing. Every reachable code path inside parse() must produce
    // Ok | Err — never panic.
    let parser = ComponentParser::without_validation();
    let _ = parser.parse(data);

    // Run the validating parser too, so we also exercise the
    // wasmparser::Validator interaction path. Both arms must return
    // gracefully.
    let validating = ComponentParser::new();
    let _ = validating.parse(data);
});
