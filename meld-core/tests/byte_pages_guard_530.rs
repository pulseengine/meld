//! SR-107 (#530): a cross-domain copy on byte-sized memories, end to end.
//!
//! Two inputs, one memory each, the call between them kept as a Canonical ABI
//! copy (`list<list<string>>`, deep-copied by the adapter). The page-sized and
//! byte-sized fusions must deliver the same answer and hold the same bytes over
//! the byte-sized extent.
//!
//! NOTE what this does NOT reach: the adapter emits `memory.size << 16` bounds
//! checks only in its transcoding paths (adapter/fact.rs), and a transcoding
//! boundary through a call_indirect shim did not run in this fixture even on
//! page-sized memories (`indirect call type mismatch`, an issue separate from
//! this one), so the output guard's refusal is covered by the unit tests in
//! `meld-core/src/byte_pages.rs`, not here.

use meld_core::{Fuser, FuserConfig, MemoryPageSize, MemoryStrategy};

const STRING_PROVIDER: &str = r#"(component $A
    (core module $am
      (memory (export "mem") 1)
      (data (i32.const 16) "\20\00\00\00\01\00\00\00")
      (data (i32.const 32) "\30\00\00\00\01\00\00\00")
      (data (i32.const 48) "\40\00\00\00\05\00\00\00")
      (data (i32.const 64) "hello")
      (func (export "get") (result i32) i32.const 16))
    (core instance $ai (instantiate $am))
    (func (export "get") (result (list (list string)))
      (canon lift (core func $ai "get") (memory (core memory $ai "mem")))))"#;

const STRING_CONSUMER: &str = r#"(component $B
    (import "get" (func $get (result (list (list string)))))
    (core module $shim
      (type $t (func (param i32)))
      (table (export "$imports") 1 funcref)
      (func (export "0") (param i32) local.get 0 i32.const 0 call_indirect (type $t)))
    (core module $main
      (import "shim" "0" (func $get (param i32)))
      (memory (export "mem") 1)
      (global $bump (mut i32) (i32.const 1024))
      (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
        (local $r i32)
        global.get $bump local.set $r
        global.get $bump local.get 3 i32.add global.set $bump
        local.get $r)
      (func (export "run") (result i32)
        (call $get (i32.const 128))
        (i32.load8_u (i32.load (i32.load (i32.load (i32.const 128)))))))
    (core module $fixup
      (import "shim" "$imports" (table 1 funcref))
      (import "env" "get" (func (param i32)))
      (elem (i32.const 0) func 0))
    (core instance $si (instantiate $shim))
    (core instance $mi (instantiate $main (with "shim" (instance $si))))
    (core func $gx (canon lower (func $get)
      (memory (core memory $mi "mem"))
      (realloc (core func $mi "cabi_realloc"))))
    (core instance $env (export "get" (func $gx)))
    (core instance $fi (instantiate $fixup (with "shim" (instance $si)) (with "env" (instance $env))))
    (func (export "run") (result u32) (canon lift (core func $mi "run"))))"#;

fn fuse_strings(page: MemoryPageSize) -> Result<Vec<u8>, String> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        pack_rebase: true,
        // Two domains: the string copy is kept, as the privilege boundary.
        domains: vec![vec![0], vec![1]],
        memory_page_size: page,
        attestation: false,
        ..Default::default()
    });
    for (name, wat_text) in [("provider", STRING_PROVIDER), ("consumer", STRING_CONSUMER)] {
        fuser
            .add_component_named(&wat::parse_str(wat_text).expect("wat"), Some(name))
            .map_err(|e| e.to_string())?;
    }
    fuser.fuse().map_err(|e| e.to_string())
}

/// Run `run` and return its result plus the image of every exported memory.
fn run(bytes: &[u8], custom_page_sizes: bool) -> (i32, Vec<(String, Vec<u8>)>) {
    use wasmtime::{Config, Engine, Instance, Module, Store};
    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    cfg.wasm_custom_page_sizes(custom_page_sizes);
    let engine = Engine::new(&cfg).unwrap();
    let module = Module::new(&engine, bytes).expect("validates");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiates");
    let result = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .expect("run")
        .call(&mut store, ())
        .expect("run completes");
    let names: Vec<String> = module
        .exports()
        .filter(|e| e.ty().memory().is_some())
        .map(|e| e.name().to_string())
        .collect();
    let images = names
        .into_iter()
        .map(|n| {
            let data = instance
                .get_memory(&mut store, &n)
                .expect("memory")
                .data(&store)
                .to_vec();
            (n, data)
        })
        .collect();
    (result, images)
}

/// A string copied across a domain boundary runs identically on byte-sized
/// memories: the consumer reads the provider's first byte through a real
/// `list<list<string>>` deep copy, and every memory image over the declared
/// extent matches the page-sized run's.
// rivet: verifies SWV-119
#[test]
fn a_cross_domain_deep_copy_runs_identically_on_byte_paged_memories() {
    let paged = fuse_strings(MemoryPageSize::Page).expect("page-sized fusion succeeds");
    let bytes = fuse_strings(MemoryPageSize::Byte).expect("byte-paged fusion succeeds");

    let (expected, paged_images) = run(&paged, false);
    assert_eq!(expected, i32::from(b'h'), "control: the copy delivers 'h'");
    let (actual, byte_images) = run(&bytes, true);
    assert_eq!(actual, expected, "byte-paged result must match");

    assert!(!byte_images.is_empty());
    for (name, image) in &byte_images {
        let (_, other) = paged_images
            .iter()
            .find(|(n, _)| n == name)
            .expect("same memory exported");
        assert!(other.len() >= image.len());
        assert!(
            other[..image.len()] == image[..],
            "memory `{name}` must hold the same bytes over its declared extent"
        );
    }
    assert!(
        byte_images.iter().any(|(_, i)| i.iter().any(|&b| b != 0)),
        "guard: the images must not be all zeros"
    );
}
