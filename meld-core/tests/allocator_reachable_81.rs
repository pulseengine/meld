//! SR-81 (#400) — an export that needs the guest's allocator must be able to
//! reach one.
//!
//! Two ways a fused module used to leave such an export uninvocable:
//!
//! 1. **Pruned.** #298 drops the vestigial `cabi_realloc*` exports so loom can
//!    DCE `memory.grow`, gated on a predicate that treated "no parameter type
//!    *contains* a pointer" as "no allocator needed". Above `MAX_FLAT_PARAMS`
//!    the Canonical ABI stages the argument tuple in memory the **callee's**
//!    allocator provides, so a record of 17 floats needs one while containing
//!    no pointer at all. `meld fuse provider.wasm --memory shared
//!    --address-rebase` exported the lifted function and nothing else.
//!
//! 2. **Never exported.** In shared memory every component names its allocator
//!    `cabi_realloc`, so only one can hold that name. The others were simply
//!    absent, which is what kiln hit on the falcon cascade: three of five
//!    exports needed an allocator that the fused module did not expose.
//!
//! Both are checked here on in-repo fixtures, and the second is checked by
//! actually calling through it.

use meld_core::signature_manifest::{self, SignatureManifest};
use meld_core::{Fuser, FuserConfig, MemoryStrategy};

/// `cabi_realloc(old_ptr, old_size, align, new_size) -> ptr`
fn is_realloc(sig: &signature_manifest::CoreSignature) -> bool {
    sig.params == ["i32", "i32", "i32", "i32"] && sig.results == ["i32"]
}

fn fixture(name: &str) -> Option<Vec<u8>> {
    std::fs::read(format!(
        "{}/../tests/wit_bindgen/fixtures/compose_record_use_wide/{name}",
        env!("CARGO_MANIFEST_DIR")
    ))
    .ok()
}

fn read_manifest(fused: &[u8]) -> Option<SignatureManifest> {
    for payload in wasmparser::Parser::new(0).parse_all(fused) {
        if let Ok(wasmparser::Payload::CustomSection(reader)) = payload
            && reader.name() == signature_manifest::SECTION_NAME
        {
            return Some(serde_json::from_slice(reader.data()).expect("valid JSON"));
        }
    }
    None
}

fn fuse(inputs: &[(&str, Vec<u8>)], config: FuserConfig) -> Vec<u8> {
    let mut fuser = Fuser::new(config);
    for (name, bytes) in inputs {
        fuser
            .add_component_named(bytes, Some(name))
            .expect("fixture parses");
    }
    fuser.fuse().expect("fusion succeeds")
}

/// (1) The allocator an export needs must survive #298's pruning — with no
/// manifest involved, because the export is uninvocable either way.
// rivet: verifies SR-81
#[test]
fn a_needed_allocator_is_not_pruned() {
    let Some(provider) = fixture("provider.wasm") else {
        panic!(
            "fixture absent — skipping — every fixture a test reads is tracked in the repository \
             (SR-85); a missing one is a repository error, not a reason to report success"
        );
    };
    let fused = fuse(
        &[("wide", provider)],
        FuserConfig {
            memory_strategy: MemoryStrategy::SharedMemory,
            address_rebasing: true,
            attestation: false,
            reproducible: true,
            ..Default::default()
        },
    );

    let emitted = signature_manifest::emitted_exports(&fused);
    assert!(
        emitted.funcs.keys().any(|name| name.ends_with("#tick")),
        "guard: the lifted export must be present, got {:?}",
        emitted.funcs.keys().collect::<Vec<_>>()
    );
    let allocators: Vec<&String> = emitted
        .funcs
        .iter()
        .filter(|(_, sig)| is_realloc(sig))
        .map(|(name, _)| name)
        .collect();
    assert!(
        !allocators.is_empty(),
        "SR-81: `tick` takes 18 flattened params, so a host must stage them through the \
         callee's allocator — but this module exports none: {:?}",
        emitted.funcs.keys().collect::<Vec<_>>()
    );
}

/// (2) When several components each need one, every export names an allocator
/// that exists — and calling through it produces the callee's real answer.
// rivet: verifies SR-81
#[test]
fn every_export_that_needs_an_allocator_can_call_one() {
    let (Some(a), Some(b)) = (fixture("provider.wasm"), fixture("provider2.wasm")) else {
        panic!(
            "fixtures absent — skipping — every fixture a test reads is tracked in the repository \
             (SR-85); a missing one is a repository error, not a reason to report success"
        );
    };
    let fused = fuse(
        &[("wide", a), ("wide2", b)],
        FuserConfig {
            memory_strategy: MemoryStrategy::SharedMemory,
            attestation: false,
            reproducible: true,
            signature_manifest: true,
            ..Default::default()
        },
    );
    let manifest = read_manifest(&fused).expect("the section is present");
    let emitted = signature_manifest::emitted_exports(&fused);

    let needing: Vec<_> = manifest
        .exports
        .iter()
        .filter(|e| e.needs.realloc)
        .collect();
    assert_eq!(
        needing.len(),
        2,
        "guard: both providers' exports must need an allocator, got {:?}",
        manifest
            .exports
            .iter()
            .map(|e| (&e.export, e.needs.realloc))
            .collect::<Vec<_>>()
    );

    for entry in &needing {
        let name = entry.realloc.as_deref().unwrap_or_else(|| {
            panic!(
                "SR-81: {} needs an allocator and the manifest names none",
                entry.export
            )
        });
        let sig = emitted
            .funcs
            .get(name)
            .unwrap_or_else(|| panic!("{} names `{name}`, which is not exported", entry.export));
        assert!(
            is_realloc(sig),
            "`{name}` is named as an allocator but has the signature {sig:?}"
        );
    }
    assert!(
        needing[0].realloc != needing[1].realloc,
        "two components, two allocators: {:?}",
        needing.iter().map(|e| &e.realloc).collect::<Vec<_>>()
    );

    // Call the one whose allocator exists only because it was added: write the
    // arguments through it, then read the return area the manifest describes.
    let entry = needing
        .iter()
        .find(|e| e.export.starts_with("golden:wide/"))
        .expect("the first provider's export is described");
    let realloc_name = entry.realloc.as_deref().expect("named above");
    let memory_name = entry.memory.as_deref().expect("a memory is named");
    let area = entry
        .return_area
        .as_ref()
        .expect("a return area is described");

    use wasmtime::{Config, Engine, Instance, Module, Store};
    let engine = Engine::new(&Config::new()).expect("engine");
    let module = Module::new(&engine, &fused).expect("fused module loads");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiate");

    let memory = instance
        .get_memory(&mut store, memory_name)
        .expect("the named memory exists");
    let realloc = instance
        .get_typed_func::<(i32, i32, i32, i32), i32>(&mut store, realloc_name)
        .expect("the named allocator is callable");
    let tick = instance
        .get_typed_func::<i32, i32>(&mut store, &entry.export)
        .expect("the export is callable");

    let args: Vec<f32> = (1..=14).chain(1..=4).map(|i| i as f32).collect();
    let ptr = realloc
        .call(&mut store, (0, 0, 4, 4 * args.len() as i32))
        .expect("allocation succeeds");
    let mut buf = Vec::new();
    for v in &args {
        buf.extend_from_slice(&v.to_le_bytes());
    }
    memory
        .write(&mut store, ptr as usize, &buf)
        .expect("write into the named memory");

    let ret = tick.call(&mut store, ptr).expect("call succeeds");
    let mut word = [0u8; 4];
    memory
        .read(
            &store,
            ret as usize + area.layout[0].offset as usize,
            &mut word,
        )
        .expect("read the return area");
    assert_eq!(
        f32::from_le_bytes(word),
        105.0,
        "SR-81: invoking through the allocator the manifest names must produce \
         sum(1..=14); the arguments did not reach the callee"
    );
}
