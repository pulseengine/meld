//! #545: the library refuses its own invalid output.
//!
//! `Fuser::fuse` used to return bytes that fail validation as `Ok`. Only
//! the CLI checked them. The reproducer from the issue is the first
//! component of the upstream `test/async/empty-wait.wast`. Fused under
//! `--memory multi` it produces an adapter that leaves values on the stack.
//!
//! Both halves are asserted. With `validate_output` on (the default) the
//! library returns `Error::InvalidOutput`. With it off, the same input comes
//! back as bytes that fail validation. The second half shows the refusal comes
//! from the validation and not from somewhere else, and that `--no-validate`
//! still means what it says.

use std::path::Path;

use meld_core::{Error, Fuser, FuserConfig, MemoryStrategy};
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

// rivet: verifies SR-114
#[test]
fn library_refuses_invalid_output_by_default() {
    let input = first_component("async/empty-wait.wast");

    match fuse(&input, true) {
        Err(Error::InvalidOutput(msg)) => assert!(
            msg.contains("type mismatch"),
            "expected the adapter stack defect, got: {msg}"
        ),
        Err(e) => panic!("expected InvalidOutput, got a different refusal: {e}"),
        Ok(_) => panic!("#545 regressed: invalid output returned as Ok"),
    }

    // The opt-out returns the very bytes the default refused, and they are
    // invalid: the refusal above is the validation, not an earlier failure.
    let unchecked = fuse(&input, false).expect("opt-out returns the bytes");
    assert!(
        meld_core::validate_output(&unchecked, false).is_err(),
        "with validation off the output should be the invalid module"
    );
}

// rivet: verifies SR-114
#[test]
fn library_validation_does_not_refuse_valid_output() {
    // A component the baseline records as `fused`: validation on by default
    // must leave it alone. Without this, "refuse everything" would pass the
    // test above.
    let input = first_component("async/cancel-stream.wast");
    let out = fuse(&input, true).expect("valid output is returned");
    meld_core::validate_output(&out, false).expect("and it validates");
}
