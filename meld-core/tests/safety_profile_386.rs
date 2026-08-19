//! ADR-7 sealed-safety profile (#386) — `--profile safety` refuses to INFER a
//! safety-relevant property that the build should have DECLARED.
//!
//! ADR-7 gave meld a dual identity: the generic RFC-46 reference fuser AND a
//! sealed-safety product. The difference is not the fusion algorithm, it is how
//! much the build may infer. ADR-4 ("explicit, not auto") says a functional-safety
//! build must state its memory strategy — the inter-component isolation model
//! decides whether a fault in one component can reach another's state. Until now
//! that was only a `log::warn!`, and it could not be promoted to an error because
//! `attestation` defaults ON and `--memory` defaults to `auto`, so "attested +
//! Auto" is the DEFAULT invocation, not a safety corner. The profile is the
//! signal that separates them.
//!
//! Contract pinned here:
//!   1. safety profile + `Auto`      → hard error naming the remedy
//!   2. safety profile + explicit    → fuses normally
//!   3. ecosystem profile + `Auto`   → unchanged (no error) — the default path
//!   4. a safety build's output is byte-identical to the same explicit
//!      invocation under ecosystem (the profile gates, it does not transform)

use meld_core::{Fuser, FuserConfig, MemoryStrategy, Profile};
use wasm_encoder::{
    CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection, Instruction,
    Module, ModuleSection, TypeSection, ValType,
};

/// A minimal, memory-free component — the profile check is a build-configuration
/// gate, so it must not depend on input shape.
fn build_component(tag: &str) -> Vec<u8> {
    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0);

    let mut exports = ExportSection::new();
    exports.export(&format!("f_{tag}"), ExportKind::Func, 0);

    let mut code = CodeSection::new();
    let mut f = Function::new([]);
    f.instruction(&Instruction::I32Const(7));
    f.instruction(&Instruction::End);
    code.function(&f);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&exports)
        .section(&code);

    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

fn fuse(profile: Profile, memory_strategy: MemoryStrategy) -> Result<Vec<u8>, String> {
    let config = FuserConfig {
        profile,
        memory_strategy,
        // Reproducible so the byte-identity assertion below compares fusion
        // output rather than a random attestation id / timestamp.
        reproducible: true,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&build_component("a"), Some("comp-a"))
        .unwrap();
    fuser
        .add_component_named(&build_component("b"), Some("comp-b"))
        .unwrap();
    fuser.fuse().map_err(|e| e.to_string())
}

#[test]
fn safety_profile_refuses_to_infer_the_memory_strategy() {
    let err = fuse(Profile::Safety, MemoryStrategy::Auto)
        .expect_err("safety profile must refuse an inferred memory strategy");
    assert!(
        err.contains("safety profile"),
        "error must identify the profile violation, got: {err}"
    );
    assert!(
        err.contains("--memory"),
        "error must name the remedy (state --memory explicitly), got: {err}"
    );
}

#[test]
fn safety_profile_accepts_an_explicit_memory_strategy() {
    fuse(Profile::Safety, MemoryStrategy::MultiMemory)
        .expect("safety profile accepts an explicitly stated memory strategy");
}

#[test]
fn ecosystem_profile_still_infers() {
    // The default path must be untouched — this is what makes the profile
    // non-breaking (`attestation` defaults ON and `--memory` defaults to auto,
    // so this combination is the ordinary invocation).
    fuse(Profile::Ecosystem, MemoryStrategy::Auto)
        .expect("ecosystem profile keeps inferring the memory strategy");
}

#[test]
fn profile_gates_but_does_not_transform() {
    // A build that passes under `safety` must emit exactly what the same
    // explicit invocation emits under `ecosystem`. The profile decides what may
    // be inferred; it must never change the artifact.
    let safety = fuse(Profile::Safety, MemoryStrategy::MultiMemory).expect("safety fuse");
    let ecosystem = fuse(Profile::Ecosystem, MemoryStrategy::MultiMemory).expect("ecosystem fuse");
    assert_eq!(
        safety, ecosystem,
        "the profile must gate the build, not alter its output"
    );
}
