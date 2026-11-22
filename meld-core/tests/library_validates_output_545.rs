//! #545: the library refuses its own invalid output.
//!
//! `Fuser::fuse` used to return bytes that fail validation as `Ok`. Only
//! the CLI checked them. The reproducer from the issue was the first
//! component of the upstream `test/async/empty-wait.wast`.
//!
//! That component now fuses to a valid module: its start wrapper called the
//! imports the P3 shift prepends, and is now rebuilt after the shift
//! (SR-136). No known input still produces invalid output, so the refusal
//! itself is tested in `meld-core/src/lib.rs`
//! (`sr114_library_refuses_invalid_output_by_default`), with a component
//! built to be invalid that only the library can feed past input validation.
//! This file keeps the former reproducer as a regression test, and checks
//! that validation leaves valid output alone.

use std::path::Path;

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wast::parser::{self, ParseBuffer};
use wast::{QuoteWat, Wast, WastDirective, Wat};

fn first_component(rel: &str) -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../tests/spec/component-model/test")
        .join(rel);
    let text = std::fs::read_to_string(&path).expect("vendored WAST present");
    let buf = ParseBuffer::new(&text).expect("lex");
    let wast: Wast<'_> = parser::parse(&buf).expect("parse");
    for d in wast.directives {
        if let WastDirective::Module(mut q) = d
            && matches!(q, QuoteWat::Wat(Wat::Component(_)))
        {
            return q.encode().expect("encode");
        }
    }
    panic!("no component in {rel}");
}

fn fuse(bytes: &[u8], validate_output: bool) -> meld_core::Result<Vec<u8>> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        validate_output,
        ..Default::default()
    });
    fuser.add_component(bytes)?;
    fuser.fuse()
}

#[test]
fn former_545_reproducer_now_fuses_to_valid_output() {
    // async/empty-wait.wast's first component: two start functions, so a
    // start wrapper, plus stream built-ins, so the P3 import shift. The
    // wrapper used to call two of the prepended imports and leave a value on
    // the stack.
    let input = first_component("async/empty-wait.wast");
    let out = fuse(&input, true).expect("fuses with validation on");
    meld_core::validate_output(&out, false).expect("and the output validates");
}

// rivet: verifies SR-114
// rivet: verifies SWV-128
#[test]
fn library_validation_does_not_refuse_valid_output() {
    // A component the baseline records as `fused`: validation on by default
    // must leave it alone. Without this, "refuse everything" would pass the
    // test above.
    let input = first_component("async/cancel-stream.wast");
    let out = fuse(&input, true).expect("valid output is returned");
    meld_core::validate_output(&out, false).expect("and it validates");
}
