//! #353 inc4 — the static-PIC base-fold covers the BARE `global.get $base`
//! data offset but NOT the extended-const `base + N` shape.
//!
//! `wasm-tools component link` emits base-relative data at the position-
//! independent offset `(data (i32.add (global.get $__memory_base) (i32.const N)))`
//! for every N > 0 (only the N == 0 segment is a bare `global.get`). After
//! fusion the dylib's imported `__memory_base` becomes a DEFINED global, so a
//! `global.get` of it in a segment offset is INVALID for wasmtime ("constant
//! expression required: global.get of locally defined global").
//!
//! The #353 fold in `ParsedConstExpr::reindex` folds only the bare
//! `GlobalGet` arm; the `ExtendedGlobalGet` arm remaps the index but leaves the
//! `global.get` in place. So the extended-const case emits
//! `global.get <defined_idx>; i32.const N; i32.add` — accepted by wasm-tools
//! (lenient) but REJECTED by wasmtime.
//!
//! This is the concrete differential: wasm-tools validates the fused output,
//! wasmtime does not.

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

fn base_config() -> FuserConfig {
    FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        reproducible: false,
        component_provenance: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: meld_core::CustomSectionHandling::Drop,
        dwarf_handling: meld_core::DwarfHandling::Strip,
        output_format: meld_core::OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    }
}

/// `$main` defines+exports `__memory_base` = 0x10000 and owns the memory;
/// `$lib` imports both and holds a base-relative data segment at the
/// extended-const offset `__memory_base + 8`.
fn pic_ext_component() -> Vec<u8> {
    let wat = r#"
    (component
      (core module $main
        (global (export "__memory_base") i32 (i32.const 65536))
        (memory (export "memory") 2))
      (core module $lib
        (import "env" "memory" (memory 1))
        (import "env" "__memory_base" (global $base i32))
        (data (i32.add (global.get $base) (i32.const 8)) "\aa\bb\cc\dd"))
      (core instance $mi (instantiate $main))
      (core instance $li (instantiate $lib (with "env" (instance $mi)))))
    "#;
    wat::parse_str(wat).expect("PIC ext-const component WAT must assemble")
}

#[test]
fn pic_extended_const_data_offset_valid_for_wasmtime_353() {
    let component = pic_ext_component();
    let mut fuser = Fuser::new(base_config());
    fuser
        .add_component_named(&component, Some("pic-ext"))
        .unwrap();
    let (fused, _) = fuser
        .fuse_with_stats()
        .expect("PIC ext-const component must fuse");

    // wasm-tools (lenient) accepts the output either way.
    assert!(
        wasmparser::Validator::new().validate_all(&fused).is_ok(),
        "fused output must validate under wasm-tools"
    );

    // The real invariant: the fused core must be VALID for wasmtime. A
    // `global.get` of a locally-defined global in a data-segment offset is
    // rejected — this is the #353 gap for the extended-const shape.
    use wasmtime::{Config, Engine, Module as RuntimeModule};
    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).unwrap();
    RuntimeModule::new(&engine, &fused).expect(
        "fused PIC output must be valid for wasmtime: the extended-const \
         `__memory_base + N` data offset must be folded, not left as a \
         `global.get` of a now-defined global (#353)",
    );
}
