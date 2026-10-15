//! #463 — `--exports world`: limit the fused core module's export list to the
//! outer component's world.
//!
//! Input is cpetig's three falcon-cascade components composed with `wac` (see
//! `tests/fixtures/issue_463/README.md`). The composition exports only
//! `controller` and `observer`, but the fused module used to export every
//! inner module's exports as well: the internal `estimator` / `flight-control`
//! functions, two allocators, and `__data_end` / `__heap_base`.
//!
//! The assertions are about the EXACT export set, not "contains X" / "lacks Y":
//! an export-set test that only checked for the removal of a few names would
//! pass for a filter that dropped too much.

use meld_core::signature_manifest::{self, SignatureManifest};
use meld_core::{ExportPolicy, Fuser, FuserConfig, MemoryStrategy};
use std::collections::BTreeSet;
use std::path::Path;

const CONTROLLER: &str = "pulseengine:falcon-cascade/controller@0.11.0";
const OBSERVER: &str = "pulseengine:falcon-cascade/observer@0.11.0";
const ESTIMATOR: &str = "pulseengine:falcon-cascade/estimator@0.11.0";
const FLIGHT: &str = "pulseengine:falcon-cascade/flight-control@0.11.0";

fn fixture(name: &str) -> Vec<u8> {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/issue_463")
        .join(name);
    std::fs::read(&p).unwrap_or_else(|e| panic!("fixture {}: {e}", p.display()))
}

fn config(policy: ExportPolicy, manifest: bool) -> FuserConfig {
    FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        attestation: false,
        reproducible: true,
        signature_manifest: manifest,
        export_policy: policy,
        ..Default::default()
    }
}

fn fuse(input: &str, cfg: FuserConfig) -> meld_core::Result<Vec<u8>> {
    let mut fuser = Fuser::new(cfg);
    fuser
        .add_component_named(&fixture(input), Some("composed"))
        .expect("parses");
    fuser.fuse()
}

/// Every export of the module as `kind:name`, so a global named like a
/// function is not mistaken for one.
fn export_set(wasm: &[u8]) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for payload in wasmparser::Parser::new(0).parse_all(wasm) {
        if let Ok(wasmparser::Payload::ExportSection(reader)) = payload {
            for e in reader.into_iter().flatten() {
                let kind = match e.kind {
                    wasmparser::ExternalKind::Func => "func",
                    wasmparser::ExternalKind::Memory => "memory",
                    wasmparser::ExternalKind::Global => "global",
                    wasmparser::ExternalKind::Table => "table",
                    _ => "other",
                };
                out.insert(format!("{kind}:{}", e.name));
            }
        }
    }
    out
}

fn set(items: &[&str]) -> BTreeSet<String> {
    items.iter().map(|s| s.to_string()).collect()
}

fn validate(wasm: &[u8]) {
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(wasm)
        .expect("the fused module validates");
}

fn read_manifest(fused: &[u8]) -> SignatureManifest {
    for payload in wasmparser::Parser::new(0).parse_all(fused) {
        if let Ok(wasmparser::Payload::CustomSection(reader)) = payload
            && reader.name() == signature_manifest::SECTION_NAME
        {
            return serde_json::from_slice(reader.data()).expect("valid JSON");
        }
    }
    panic!("the manifest section is absent");
}

fn world_exports() -> BTreeSet<String> {
    set(&[
        "memory:memory",
        &format!("func:{CONTROLLER}#configure"),
        &format!("func:{CONTROLLER}#step"),
        &format!("func:{OBSERVER}#read-state"),
    ])
}

#[test]
fn the_default_keeps_every_inner_export() {
    // Control: without the flag the export surface is exactly what it was.
    let fused = fuse("composed.wasm", config(ExportPolicy::All, false)).expect("fuses");
    validate(&fused);
    let got = export_set(&fused);
    assert_eq!(
        got,
        set(&[
            "memory:memory",
            "func:cabi_realloc",
            "func:cabi_realloc_wit_bindgen_0_41_0",
            "global:__data_end",
            "global:__heap_base",
            &format!("func:{ESTIMATOR}#configure"),
            &format!("func:{ESTIMATOR}#step"),
            &format!("func:{FLIGHT}#configure"),
            &format!("func:{FLIGHT}#step"),
            &format!("func:{CONTROLLER}#configure"),
            &format!("func:{CONTROLLER}#step"),
            &format!("func:{OBSERVER}#read-state"),
        ])
    );
}

#[test]
fn a_default_config_is_the_all_policy() {
    assert_eq!(FuserConfig::default().export_policy, ExportPolicy::All);
    let default = fuse("composed.wasm", {
        let mut c = config(ExportPolicy::All, false);
        c.export_policy = FuserConfig::default().export_policy;
        c
    })
    .expect("fuses");
    let explicit = fuse("composed.wasm", config(ExportPolicy::All, false)).expect("fuses");
    assert_eq!(
        default, explicit,
        "the default policy is `all`, byte for byte"
    );
}

#[test]
fn world_keeps_exactly_the_outer_interfaces_and_what_they_need() {
    let fused = fuse("composed.wasm", config(ExportPolicy::World, false)).expect("fuses");
    validate(&fused);
    assert_eq!(export_set(&fused), world_exports());
}

#[test]
fn world_drops_exports_only_not_functions() {
    // The filter touches the export LIST. Function bodies stay, so the module
    // is the same size minus the export entries and carries as many functions.
    let all = fuse("composed.wasm", config(ExportPolicy::All, false)).expect("fuses");
    let world = fuse("composed.wasm", config(ExportPolicy::World, false)).expect("fuses");
    let count = |bytes: &[u8]| {
        let mut n = 0u32;
        for p in wasmparser::Parser::new(0).parse_all(bytes) {
            if let Ok(wasmparser::Payload::CodeSectionStart { count, .. }) = p {
                n = count;
            }
        }
        n
    };
    assert_eq!(count(&all), count(&world), "function bodies are untouched");
    assert!(world.len() < all.len());
}

#[test]
fn an_outer_world_that_reexports_an_inner_interface_keeps_it() {
    // `composed_reexport.wasm` exports the estimator interface too, so it is
    // part of the outer world and must survive; flight-control is still
    // internal and must not.
    let fused = fuse("composed_reexport.wasm", config(ExportPolicy::World, false)).expect("fuses");
    validate(&fused);
    let mut want = world_exports();
    want.insert(format!("func:{ESTIMATOR}#configure"));
    want.insert(format!("func:{ESTIMATOR}#step"));
    assert_eq!(export_set(&fused), want);
}

#[test]
fn a_world_export_with_no_fused_counterpart_is_refused_by_name() {
    // `composed_renamed.wasm` exports the estimator as `test:renamed/est@0.1.0`.
    // The fused module keeps the lifted export's own name, so that world export
    // cannot be mapped. Dropping it silently would hand back a module missing an
    // export its world declares.
    let err = fuse("composed_renamed.wasm", config(ExportPolicy::World, false))
        .expect_err("an unmappable world export must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("test:renamed/est@0.1.0"),
        "names the export: {msg}"
    );
    // The same input fuses without the flag: the refusal is the flag's, not the
    // input's.
    fuse("composed_renamed.wasm", config(ExportPolicy::All, false)).expect("fuses without it");
}

#[test]
fn world_with_component_output_is_refused() {
    let mut cfg = config(ExportPolicy::World, false);
    cfg.output_format = meld_core::OutputFormat::Component;
    let err = fuse("composed.wasm", cfg).expect_err("--exports world with --component");
    assert!(err.to_string().contains("--component"), "{err}");
}

#[test]
fn the_manifest_lists_only_kept_exports_and_their_allocators() {
    let all = fuse("composed.wasm", config(ExportPolicy::All, true)).expect("fuses");
    let all_manifest = read_manifest(&all);
    let all_names: BTreeSet<&str> = all_manifest
        .exports
        .iter()
        .map(|e| e.export.as_str())
        .collect();
    // Control: without the flag the manifest does list the internal exports.
    assert!(all_names.contains(format!("{ESTIMATOR}#step").as_str()));
    assert!(all_names.contains(format!("{FLIGHT}#step").as_str()));

    let world = fuse("composed.wasm", config(ExportPolicy::World, true)).expect("fuses");
    validate(&world);
    let manifest = read_manifest(&world);
    let names: BTreeSet<&str> = manifest.exports.iter().map(|e| e.export.as_str()).collect();
    assert_eq!(
        names,
        BTreeSet::from([
            format!("{CONTROLLER}#configure").as_str(),
            format!("{CONTROLLER}#step").as_str(),
            format!("{OBSERVER}#read-state").as_str(),
        ]),
        "the manifest must not list a removed export"
    );
    assert!(
        manifest.omitted.is_empty(),
        "nothing kept is undescribed: {:?}",
        manifest.omitted
    );

    // Every allocator / memory the manifest names must be an export that
    // survived the filter, and the allocators belong to kept exports only.
    let exports = export_set(&world);
    let mut allocators = BTreeSet::new();
    for e in &manifest.exports {
        if let Some(r) = &e.realloc {
            assert!(exports.contains(&format!("func:{r}")), "{r} not exported");
            allocators.insert(r.clone());
        }
        if let Some(m) = &e.memory {
            assert!(exports.contains(&format!("memory:{m}")), "{m} not exported");
        }
    }
    assert_eq!(
        allocators.len(),
        1,
        "controller's allocator only: {allocators:?}"
    );
    let mut want = world_exports();
    want.insert(format!("func:{}", allocators.iter().next().unwrap()));
    assert_eq!(export_set(&world), want);
}

// ---------------------------------------------------------------------------
// Execution: the pruned module computes what the unfused composition computes.
// ---------------------------------------------------------------------------

const CFG: [f32; 9] = [0.5, 100.0, 1.0, 0.1, 0.1, 1.0, 0.5, 0.1, 0.1];
const IMU: [f32; 6] = [0.1, -0.2, 9.8, 0.01, 0.02, -0.03];
const DT: f32 = 0.01;
const POS: [f32; 3] = [1.0, 2.0, -3.0];
const HEADING: f32 = 0.5;
const TARGET: [f32; 4] = [1.0, 1.0, -2.0, 0.0];

/// `controller.step` takes 26 flat values, over the 16-value limit, so a host
/// passes ONE pointer to `(sensors, target)` laid out per the Canonical ABI:
/// sensor-frame is 88 bytes (imu 0..24, dt 24, position-ned 28 (tag, vec3),
/// mag-body 44, heading-rad 60 (tag, f32), motor-rpm 68 (tag, 4 x s32)),
/// followed by waypoint at 88. Here position-ned and heading are `some`,
/// mag-body and motor-rpm are `none`.
fn step_args() -> Vec<u8> {
    let mut buf = vec![0u8; 104];
    let put =
        |buf: &mut Vec<u8>, off: usize, v: f32| buf[off..off + 4].copy_from_slice(&v.to_le_bytes());
    for (i, v) in IMU.iter().enumerate() {
        put(&mut buf, 4 * i, *v);
    }
    put(&mut buf, 24, DT);
    buf[28] = 1;
    for (i, v) in POS.iter().enumerate() {
        put(&mut buf, 32 + 4 * i, *v);
    }
    buf[60] = 1;
    put(&mut buf, 64, HEADING);
    for (i, v) in TARGET.iter().enumerate() {
        put(&mut buf, 88 + 4 * i, *v);
    }
    buf
}

fn run_fused(fused: &[u8]) -> [f32; 4] {
    use wasmtime::{Engine, Instance, Module, Store};
    let manifest = read_manifest(fused);
    let step = manifest
        .exports
        .iter()
        .find(|e| e.export == format!("{CONTROLLER}#step"))
        .expect("step is described");
    let memory_name = step.memory.as_deref().expect("a memory is named");
    let realloc_name = step.realloc.as_deref().expect("an allocator is named");
    let area = step.return_area.as_ref().expect("a return area");
    assert_eq!(area.size, 16);

    let engine = Engine::default();
    let module = Module::new(&engine, fused).expect("the pruned module loads");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiates");

    let configure = instance
        .get_typed_func::<(f32, f32, f32, f32, f32, f32, f32, f32, f32), ()>(
            &mut store,
            &format!("{CONTROLLER}#configure"),
        )
        .expect("configure is callable");
    configure
        .call(
            &mut store,
            (
                CFG[0], CFG[1], CFG[2], CFG[3], CFG[4], CFG[5], CFG[6], CFG[7], CFG[8],
            ),
        )
        .expect("configure runs");

    let memory = instance
        .get_memory(&mut store, memory_name)
        .expect("memory");
    let realloc = instance
        .get_typed_func::<(i32, i32, i32, i32), i32>(&mut store, realloc_name)
        .expect("realloc");
    let args = step_args();
    let ptr = realloc
        .call(&mut store, (0, 0, 4, args.len() as i32))
        .expect("allocates");
    memory
        .write(&mut store, ptr as usize, &args)
        .expect("writes");
    let step_fn = instance
        .get_typed_func::<i32, i32>(&mut store, &step.export)
        .expect("step is callable");
    let ret = step_fn.call(&mut store, ptr).expect("step runs");
    let mut out = [0u8; 16];
    memory.read(&store, ret as usize, &mut out).expect("reads");
    let mut r = [0f32; 4];
    for (i, c) in out.chunks(4).enumerate() {
        r[i] = f32::from_le_bytes(c.try_into().unwrap());
    }
    r
}

fn run_unfused() -> [f32; 4] {
    use wasmtime::Store;
    use wasmtime::component::{Component, Linker, Val};
    let engine = wasmtime::Engine::default();
    let component = Component::new(&engine, fixture("composed.wasm")).expect("component loads");
    let mut linker = Linker::<()>::new(&engine);
    // The composition imports `types`, which declares records only.
    linker
        .instance("pulseengine:falcon-cascade/types@0.11.0")
        .expect("defines the types instance");
    let mut store = Store::new(&engine, ());
    let instance = linker
        .instantiate(&mut store, &component)
        .expect("instantiates");
    let iface = instance
        .get_export_index(&mut store, None, CONTROLLER)
        .expect("controller interface");
    let func = |store: &mut Store<()>, name: &str| {
        let idx = instance
            .get_export_index(&mut *store, Some(&iface), name)
            .unwrap_or_else(|| panic!("{name} exported"));
        instance
            .get_func(&mut *store, idx)
            .unwrap_or_else(|| panic!("{name} is a function"))
    };
    let f = |v: f32| Val::Float32(v);
    let rec = |fields: &[(&str, Val)]| {
        Val::Record(
            fields
                .iter()
                .map(|(n, v)| (n.to_string(), v.clone()))
                .collect(),
        )
    };
    let vec3 = |v: [f32; 3]| rec(&[("x", f(v[0])), ("y", f(v[1])), ("z", f(v[2]))]);

    let cfg = rec(&[
        ("hover-thrust", f(CFG[0])),
        ("loop-rate-hz", f(CFG[1])),
        ("pos-var", f(CFG[2])),
        ("process-floor-vel", f(CFG[3])),
        ("process-floor-pos", f(CFG[4])),
        ("altitude-kp", f(CFG[5])),
        ("altitude-kd", f(CFG[6])),
        ("altitude-ki", f(CFG[7])),
        ("position-ki", f(CFG[8])),
    ]);
    let configure = func(&mut store, "configure");
    configure
        .call(&mut store, &[cfg], &mut [])
        .expect("configure runs");
    configure.post_return(&mut store).expect("post-return");

    let sensors = rec(&[
        (
            "imu",
            rec(&[
                ("ax", f(IMU[0])),
                ("ay", f(IMU[1])),
                ("az", f(IMU[2])),
                ("gx", f(IMU[3])),
                ("gy", f(IMU[4])),
                ("gz", f(IMU[5])),
            ]),
        ),
        ("dt-s", f(DT)),
        ("position-ned", Val::Option(Some(Box::new(vec3(POS))))),
        ("mag-body", Val::Option(None)),
        ("heading-rad", Val::Option(Some(Box::new(f(HEADING))))),
        ("motor-rpm", Val::Option(None)),
    ]);
    let target = rec(&[
        ("north", f(TARGET[0])),
        ("east", f(TARGET[1])),
        ("down", f(TARGET[2])),
        ("yaw", f(TARGET[3])),
    ]);
    let step = func(&mut store, "step");
    let mut results = [Val::Bool(false)];
    step.call(&mut store, &[sensors, target], &mut results)
        .expect("step runs");
    step.post_return(&mut store).expect("post-return");
    let Val::Record(fields) = &results[0] else {
        panic!("step returns a record, got {:?}", results[0]);
    };
    let mut out = [0f32; 4];
    for (i, (_, v)) in fields.iter().enumerate() {
        let Val::Float32(x) = v else {
            panic!("motor value is f32, got {v:?}");
        };
        out[i] = *x;
    }
    out
}

#[test]
fn the_world_pruned_module_computes_what_the_unfused_composition_computes() {
    let unfused = run_unfused();
    assert!(
        unfused.iter().any(|v| v.to_bits() != 0) && unfused.iter().all(|v| v.is_finite()),
        "guard: the oracle must produce a real result, got {unfused:?}"
    );

    let world = fuse("composed.wasm", config(ExportPolicy::World, true)).expect("fuses");
    let all = fuse("composed.wasm", config(ExportPolicy::All, true)).expect("fuses");
    let from_world = run_fused(&world);
    let from_all = run_fused(&all);

    let bits = |a: [f32; 4]| a.map(f32::to_bits);
    assert_eq!(
        bits(from_all),
        bits(unfused),
        "control: today's fused output"
    );
    assert_eq!(
        bits(from_world),
        bits(unfused),
        "--exports world changes nothing observable"
    );
}

// ---------------------------------------------------------------------------
// SR-28: the policy is attested in EVERY build configuration.
// ---------------------------------------------------------------------------

fn attested(policy: ExportPolicy) -> Vec<u8> {
    let mut cfg = config(policy, false);
    cfg.attestation = true;
    fuse("composed.wasm", cfg).expect("fuses")
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    haystack.windows(needle.len()).any(|w| w == needle)
}

/// Default build: the typed `FusionParameters` record.
#[cfg(not(feature = "attestation"))]
#[test]
fn the_attestation_records_the_export_policy_only_when_set() {
    assert!(contains(
        &attested(ExportPolicy::World),
        br#""exports":"world""#
    ));
    assert!(!contains(
        &attested(ExportPolicy::All),
        br#""exports":"world""#
    ));
}

/// wsc-attestation build: a separate builder, which must record it too.
#[cfg(feature = "attestation")]
#[test]
fn the_wsc_attestation_records_the_export_policy_only_when_set() {
    assert!(contains(
        &attested(ExportPolicy::World),
        br#""exports":"world""#
    ));
    assert!(!contains(
        &attested(ExportPolicy::All),
        br#""exports":"world""#
    ));
}
