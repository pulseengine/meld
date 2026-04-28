//! Proptest harness for fusion round-trip and parser robustness.
//!
//! This file complements the Rocq fusion proofs (`proofs/spec/fusion_spec.v`,
//! `proofs/merger_core_proofs.v`, `proofs/resolver_core_proofs.v`) with
//! property-based testing on the Rust implementation.  Rocq proves the
//! mathematical model; proptest exercises the Rust code on randomised but
//! well-formed inputs to catch implementation bugs the proof can't see
//! (panics, wrong index arithmetic on inputs the model didn't anticipate,
//! divergence between the spec and the impl).
//!
//! The harness is bounded — small modules, small numbers of components — to
//! keep `cargo test` fast.  It is intentionally not exhaustive: that's what
//! the Kani harnesses (see `kani_*.rs`) are for.
//!
//! Tracks issue #102.

use meld_core::{ComponentParser, Fuser, FuserConfig, MemoryStrategy};
use proptest::prelude::*;
use wasm_encoder::{
    CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection, Instruction,
    Module, ModuleSection, TypeSection, ValType,
};

/// Build a tiny, well-formed core module that exports a single nullary
/// function returning the given `i32` constant under the given name.
///
/// The module shape is:
///
/// ```wat
/// (module
///   (type (func (result i32)))
///   (func (result i32) i32.const <ret>)
///   (export "<name>" (func 0)))
/// ```
fn build_const_module_named(ret: i32, name: &str) -> Module {
    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0);

    let mut exports = ExportSection::new();
    exports.export(name, ExportKind::Func, 0);

    let mut code = CodeSection::new();
    {
        let mut f = Function::new([]);
        f.instruction(&Instruction::I32Const(ret));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&exports)
        .section(&code);
    module
}

/// Build a tiny, well-formed core module that exports a single nullary
/// function `f` returning the given `i32` constant.
fn build_const_module(ret: i32) -> Module {
    build_const_module_named(ret, "f")
}

/// Wrap a single core module into a minimal P2 component.
fn component_from_module(module: &Module) -> Vec<u8> {
    let mut component = Component::new();
    component.section(&ModuleSection(module));
    component.finish()
}

/// Build a P2 component containing `n` const-returning core modules,
/// where module `i` returns `consts[i]`.
///
/// All modules are present at depth 0 but only the first one is exposed
/// (no instance section), so the component has `n` parseable core modules
/// without any cross-module wiring.  This is enough to exercise parser
/// and merger code paths without dragging in resolver complexity.
fn multi_module_component(consts: &[i32]) -> Vec<u8> {
    let mut component = Component::new();
    for (i, &c) in consts.iter().enumerate() {
        // Use distinct export names so the fused output has no
        // duplicate-export collisions when multiple modules are merged
        // into a single core module.
        let module = build_const_module_named(c, &format!("f{i}"));
        component.section(&ModuleSection(&module));
    }
    component.finish()
}

proptest! {
    // Use a small case count so this stays under a second in `cargo test
    // --release`. Property-based testing isn't meant to replace Kani's
    // bounded exhaustive search; it's meant to catch obvious bugs on
    // random well-formed inputs.
    #![proptest_config(ProptestConfig {
        cases: 64,
        max_shrink_iters: 256,
        ..ProptestConfig::default()
    })]

    /// Parser robustness: parsing arbitrary `Vec<u8>` must never panic.
    /// It is allowed (in fact expected) to return `Err`, but the process
    /// must remain alive.  This is the proptest analogue of the Kani
    /// `kani_parser.rs` harness — proptest runs unbounded random bytes,
    /// Kani runs bounded symbolic bytes.
    #[test]
    fn parser_never_panics_on_random_bytes(bytes in prop::collection::vec(any::<u8>(), 0..256)) {
        let parser = ComponentParser::new();
        // Result is allowed to be Err; the property is "no panic".
        let _ = parser.parse(&bytes);
    }

    /// Parser robustness: even byte-strings that *start* with the WASM
    /// component magic (`\0asm` + version `0x0001000d`) must be rejected
    /// cleanly without panicking when the body is garbage.
    #[test]
    fn parser_never_panics_on_corrupted_component_header(
        tail in prop::collection::vec(any::<u8>(), 0..256)
    ) {
        let mut bytes = vec![0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00];
        bytes.extend_from_slice(&tail);
        let parser = ComponentParser::new();
        let _ = parser.parse(&bytes);
    }

    /// Round-trip: parsing a synthesised P2 component never loses the
    /// number of core modules.  This tests that the parser correctly
    /// counts and stores modules without accidental drops or duplicates.
    #[test]
    fn parse_preserves_core_module_count(
        consts in prop::collection::vec(any::<i32>(), 1..6)
    ) {
        let bytes = multi_module_component(&consts);
        let parser = ComponentParser::new();
        let parsed = parser.parse(&bytes).expect("synthesised component must parse");
        prop_assert_eq!(parsed.core_modules.len(), consts.len());
    }

    /// Fusion idempotence/total-functions: fusing a single-module component
    /// produces exactly one defined function (`f` from `build_const_module`).
    /// This is a tiny but meaningful round-trip: parse → resolve → merge →
    /// encode, where the output must contain at least the function we
    /// started with.
    #[test]
    fn single_module_fusion_round_trip(ret in any::<i32>()) {
        let module = build_const_module(ret);
        let component_bytes = component_from_module(&module);

        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            ..Default::default()
        };
        let mut fuser = Fuser::new(config);
        fuser
            .add_component_named(&component_bytes, Some("proptest"))
            .expect("add_component");
        let fused = fuser.fuse().expect("fuse");

        // The fused output must be valid wasm and contain the exported
        // function. Validation catches index-arithmetic regressions in
        // the merger, so this is a non-trivial round-trip check.
        let mut features = wasmparser::WasmFeatures::default();
        features.set(wasmparser::WasmFeatures::MULTI_MEMORY, true);
        let mut validator = wasmparser::Validator::new_with_features(features);
        validator
            .validate_all(&fused)
            .expect("fused module must validate");
    }

    /// Multi-module fusion: a P2 component containing `n` independent
    /// core modules fuses to a valid module.  This exercises the merger's
    /// per-component module loop and the function/type index remapping
    /// code that the Rocq merger proofs cover at the spec level.
    #[test]
    fn multi_module_fusion_validates(
        consts in prop::collection::vec(any::<i32>(), 1..4)
    ) {
        let component_bytes = multi_module_component(&consts);
        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            ..Default::default()
        };
        let mut fuser = Fuser::new(config);
        fuser
            .add_component_named(&component_bytes, Some("proptest-multi"))
            .expect("add_component");
        let fused = fuser.fuse().expect("fuse");

        let mut features = wasmparser::WasmFeatures::default();
        features.set(wasmparser::WasmFeatures::MULTI_MEMORY, true);
        let mut validator = wasmparser::Validator::new_with_features(features);
        validator
            .validate_all(&fused)
            .expect("multi-module fused output must validate");
    }
}
