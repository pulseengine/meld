//! #400 / SR-81 — a host holding only the manifest can invoke a fused export.
//!
//! Every name and number used below comes out of `meld.signature-manifest`:
//! which memory to write into, which allocator to call for the argument area,
//! the export's own name, and the return area's layout. Nothing is looked up
//! by convention, and nothing is derived from the WIT.
//!
//! This is the test that says whether the manifest is *actionable*, rather than
//! merely well-formed. Two components are fused so the callee is not the only
//! one contributing an allocator and a memory: a manifest that named the first
//! of either would send the arguments into the wrong component's memory and
//! allocate out of an arena its owner does not manage, which the Canonical ABI
//! passes as garbage rather than refusing.

use meld_core::signature_manifest::{self, SignatureManifest};
use meld_core::{Fuser, FuserConfig, MemoryStrategy};

/// `tick` folds its arguments: o1 = sum(state), o2 = sum(sp), o3 = state.f1,
/// o4 = sp.r4. With state = 1..=14 and sp = 1..=4 that is (105, 10, 1, 4).
const STATE: [f32; 14] = [
    1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0,
];
const SETPOINT: [f32; 4] = [1.0, 2.0, 3.0, 4.0];
const EXPECTED: [f32; 4] = [105.0, 10.0, 1.0, 4.0];

fn fixtures() -> Option<(Vec<u8>, Vec<u8>)> {
    let dir = format!(
        "{}/../tests/wit_bindgen/fixtures",
        env!("CARGO_MANIFEST_DIR")
    );
    Some((
        std::fs::read(format!("{dir}/compose_record_use_wide/provider.wasm")).ok()?,
        std::fs::read(format!("{dir}/compose_record_use/provider.wasm")).ok()?,
    ))
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

// rivet: verifies SR-81
#[test]
fn a_host_with_only_the_manifest_can_invoke_a_wide_export() {
    let Some((wide, narrow)) = fixtures() else {
        eprintln!("provider fixtures absent — skipping");
        return;
    };

    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        reproducible: true,
        signature_manifest: true,
        ..Default::default()
    });
    fuser
        .add_component_named(&wide, Some("wide"))
        .expect("parses");
    fuser
        .add_component_named(&narrow, Some("narrow"))
        .expect("parses");
    let fused = fuser.fuse().expect("fusion succeeds");

    let manifest = read_manifest(&fused).expect("the section is present");
    let entry = manifest
        .exports
        .iter()
        .find(|e| e.export.ends_with("#tick") && e.export.starts_with("golden:wide"))
        .expect("the wide export is described");

    // Everything below is taken from the manifest.
    assert!(entry.needs.realloc && entry.needs.memory);
    let memory_name = entry.memory.as_deref().expect("a memory is named");
    let realloc_name = entry
        .realloc
        .as_deref()
        .expect("SR-81: the allocator this export's lift names must be reachable");
    let area = entry
        .return_area
        .as_ref()
        .expect("a return area is described");
    assert_eq!(entry.core.params, vec!["i32".to_string()], "pointer-in");

    // Guard: more than one component contributed, so naming the first of
    // either would be wrong rather than accidentally right.
    let emitted = signature_manifest::emitted_exports(&fused);
    assert!(
        emitted.memories.len() >= 2,
        "guard: the fusion must expose several memories, got {:?}",
        emitted.memories
    );

    use wasmtime::{Config, Engine, Instance, Module, Store};
    let mut cfg = Config::new();
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg).expect("engine");
    let module = Module::new(&engine, &fused).expect("fused module loads");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiate");

    let memory = instance
        .get_memory(&mut store, memory_name)
        .unwrap_or_else(|| panic!("the manifest names memory `{memory_name}`, which must exist"));
    let realloc = instance
        .get_typed_func::<(i32, i32, i32, i32), i32>(&mut store, realloc_name)
        .unwrap_or_else(|_| {
            panic!("the manifest names allocator `{realloc_name}`, which must be callable")
        });
    let tick = instance
        .get_typed_func::<i32, i32>(&mut store, &entry.export)
        .expect("the export is callable with the core signature the manifest states");

    // 18 flattened f32 -> a 72-byte argument area, allocated by the callee's
    // own allocator because that is what the Canonical ABI requires.
    let args_len = 4 * (STATE.len() + SETPOINT.len()) as i32;
    let args_ptr = realloc
        .call(&mut store, (0, 0, 4, args_len))
        .expect("allocation succeeds");
    assert!(args_ptr > 0, "allocator returned {args_ptr}");

    let mut buf = Vec::with_capacity(args_len as usize);
    for v in STATE.iter().chain(SETPOINT.iter()) {
        buf.extend_from_slice(&v.to_le_bytes());
    }
    memory
        .write(&mut store, args_ptr as usize, &buf)
        .expect("the named memory is the one the callee reads");

    let ret_ptr = tick.call(&mut store, args_ptr).expect("call succeeds");

    let got: Vec<f32> = area
        .layout
        .iter()
        .map(|slot| {
            let mut word = [0u8; 4];
            memory
                .read(&store, ret_ptr as usize + slot.offset as usize, &mut word)
                .expect("the return area is inside the named memory");
            f32::from_le_bytes(word)
        })
        .collect();

    assert_eq!(
        got,
        EXPECTED.to_vec(),
        "#400: invoking through the manifest must produce the callee's real result; \
         fields {:?}",
        area.layout.iter().map(|s| &s.field).collect::<Vec<_>>()
    );
}
