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
        // The allocator `controller#step`'s lift names. It is internal in the
        // fused module, and a host cannot call `step` without it, so it is
        // exported under the SR-81 name even without `--emit-manifest` (the
        // number is the flattened component that owns it).
        "func:meld:realloc/4",
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
    // ...and the estimator's own allocator, which its lifts name.
    want.insert("func:meld:realloc/0".to_string());
    assert_eq!(export_set(&fused), want);
}

#[test]
fn a_renamed_world_export_is_mapped_through_its_lift_and_exported_under_the_world_name() {
    // `composed_renamed.wasm` exports the estimator as `test:renamed/est@0.1.0`
    // while its core exports are named `…/estimator@0.11.0#…`. The world is
    // found through the lifts, so the rename is no obstacle, and the export
    // carries the WORLD name.
    let fused = fuse("composed_renamed.wasm", config(ExportPolicy::World, false)).expect("fuses");
    validate(&fused);
    let mut want = world_exports();
    want.insert("func:test:renamed/est@0.1.0#configure".to_string());
    want.insert("func:test:renamed/est@0.1.0#step".to_string());
    want.insert("func:meld:realloc/0".to_string());
    assert_eq!(export_set(&fused), want);
}

#[test]
fn a_world_function_no_export_carries_is_refused_by_name() {
    // Under `--memory shared` the merger keeps only ONE of two exports that
    // share a name, and here it keeps the internal service's. The world's
    // `test:x/i#f` is the other function, which no export carries. Exporting it
    // would be safe, but the contract is refusal, not repair: the error names
    // the function.
    let err = fuse("middleware.wasm", config(ExportPolicy::World, false))
        .expect_err("a world function with no carrying export is refused");
    assert!(err.to_string().contains("test:x/i#f"), "{err}");
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

// ---------------------------------------------------------------------------
// Review of #463: the world is found through lifts, per function, and what the
// kept surface and the remaining imports need is kept.
// ---------------------------------------------------------------------------

fn wasmtime_engine() -> wasmtime::Engine {
    let mut cfg = wasmtime::Config::new();
    cfg.wasm_multi_memory(true);
    wasmtime::Engine::new(&cfg).expect("engine")
}

/// Instantiate `fused`, serving every import not in `custom` with a stub that
/// returns zeros.
fn instantiate_with(
    engine: &wasmtime::Engine,
    fused: &[u8],
    mut linker: wasmtime::Linker<()>,
    custom: &[(&str, &str)],
) -> (wasmtime::Store<()>, wasmtime::Instance) {
    let module = wasmtime::Module::new(engine, fused).expect("the fused module loads");
    for imp in module.imports() {
        if custom.contains(&(imp.module(), imp.name())) {
            continue;
        }
        if let wasmtime::ExternType::Func(ft) = imp.ty() {
            let results: Vec<wasmtime::ValType> = ft.results().collect();
            linker
                .func_new(imp.module(), imp.name(), ft, move |_c, _p, out| {
                    for (slot, ty) in out.iter_mut().zip(&results) {
                        *slot = match ty {
                            wasmtime::ValType::I64 => wasmtime::Val::I64(0),
                            wasmtime::ValType::F32 => wasmtime::Val::F32(0),
                            wasmtime::ValType::F64 => wasmtime::Val::F64(0),
                            _ => wasmtime::Val::I32(0),
                        };
                    }
                    Ok(())
                })
                .expect("stub");
        }
    }
    let mut store = wasmtime::Store::new(engine, ());
    let instance = linker
        .instantiate(&mut store, &module)
        .expect("instantiates");
    (store, instance)
}

#[test]
fn the_imports_a_world_still_has_keep_their_memory_and_allocator() {
    // `run` calls two lowered host imports, `log(string)` and `get() -> string`;
    // their `canon lower`s name the memory and the allocator. A world that keeps
    // only `run` used to export neither, so a host could not read the string it
    // was handed or allocate the one it returns.
    use std::sync::{Arc, Mutex};
    use wasmtime::{Caller, FuncType, Linker, ValType};

    // No rebasing: the fixture has no relocations, and its `hi` is addressed by
    // an absolute constant.
    let mut cfg = config(ExportPolicy::World, false);
    cfg.memory_strategy = MemoryStrategy::MultiMemory;
    cfg.address_rebasing = false;
    let fused = fuse("import_needs.wasm", cfg).expect("fuses");
    validate(&fused);
    let exports = export_set(&fused);
    assert!(exports.contains("memory:memory"), "{exports:?}");
    assert!(
        exports.contains("func:cabi_realloc") || exports.contains("func:meld:realloc/0"),
        "the allocator the lowers name: {exports:?}"
    );
    assert!(exports.contains("func:test:x/i#run"));

    // And a host that follows the Canonical ABI can actually service them.
    let engine = wasmtime_engine();
    let logged = Arc::new(Mutex::new(Vec::<String>::new()));
    let sink = logged.clone();
    let mut linker = Linker::<()>::new(&engine);
    linker
        .func_new(
            "test:x/log",
            "log",
            FuncType::new(&engine, [ValType::I32, ValType::I32], []),
            move |mut caller: Caller<'_, ()>, params, _| {
                let mem = caller
                    .get_export("memory")
                    .and_then(|e| e.into_memory())
                    .ok_or_else(|| wasmtime::Error::msg("host: the module exports no memory"))?;
                let (ptr, len) = (
                    params[0].unwrap_i32() as usize,
                    params[1].unwrap_i32() as usize,
                );
                let mut buf = vec![0u8; len];
                mem.read(&caller, ptr, &mut buf)?;
                sink.lock()
                    .unwrap()
                    .push(String::from_utf8_lossy(&buf).into_owned());
                Ok(())
            },
        )
        .unwrap();
    linker
        .func_new(
            "test:x/log",
            "get",
            FuncType::new(&engine, [ValType::I32], []),
            |mut caller: Caller<'_, ()>, params, _| {
                let mem = caller
                    .get_export("memory")
                    .and_then(|e| e.into_memory())
                    .ok_or_else(|| wasmtime::Error::msg("host: the module exports no memory"))?;
                let realloc = ["meld:realloc/0", "cabi_realloc"]
                    .iter()
                    .find_map(|n| caller.get_export(n))
                    .and_then(|e| e.into_func())
                    .ok_or_else(|| wasmtime::Error::msg("host: the module exports no allocator"))?
                    .typed::<(i32, i32, i32, i32), i32>(&caller)?;
                let ptr = realloc.call(&mut caller, (0, 0, 1, 2))?;
                mem.write(&mut caller, ptr as usize, b"ok")?;
                let ret = params[0].unwrap_i32() as usize;
                mem.write(&mut caller, ret, &ptr.to_le_bytes())?;
                mem.write(&mut caller, ret + 4, &2i32.to_le_bytes())?;
                Ok(())
            },
        )
        .unwrap();
    let (mut store, instance) = instantiate_with(
        &engine,
        &fused,
        linker,
        &[("test:x/log", "log"), ("test:x/log", "get")],
    );
    instance
        .get_typed_func::<(), ()>(&mut store, "test:x/i#run")
        .expect("run is exported")
        .call(&mut store, ())
        .expect("run completes against a host that serves both imports");
    assert_eq!(*logged.lock().unwrap(), vec!["hi".to_string()]);
}

#[test]
fn a_world_function_whose_core_export_has_another_name_is_kept_under_the_world_name() {
    // `g`'s core export is `impl_g`. Matching by interface prefix found `#f`,
    // called the interface mapped, and dropped `g` at exit 0.
    let all = fuse("drop_g.wasm", config(ExportPolicy::All, false)).expect("fuses");
    assert!(export_set(&all).contains("func:impl_g"), "control");

    let fused = fuse("drop_g.wasm", config(ExportPolicy::World, false)).expect("fuses");
    validate(&fused);
    assert_eq!(
        export_set(&fused),
        set(&["func:test:x/i#f", "func:test:x/i#g"])
    );

    let engine = wasmtime_engine();
    let (mut store, instance) =
        instantiate_with(&engine, &fused, wasmtime::Linker::<()>::new(&engine), &[]);
    let call = |store: &mut wasmtime::Store<()>, name: &str| {
        instance
            .get_typed_func::<(), i32>(&mut *store, name)
            .unwrap_or_else(|e| panic!("{name}: {e}"))
            .call(&mut *store, ())
            .unwrap()
    };
    assert_eq!(call(&mut store, "test:x/i#f"), 7);
    assert_eq!(call(&mut store, "test:x/i#g"), 9);
}

#[test]
fn the_world_name_runs_the_world_function_not_the_internal_one_sharing_its_name() {
    // `svc` (internal, returns 1) and `mid` (the outer world's, returns the
    // imported value + 100) both have a core export `test:x/i#f`, so the merger
    // names the second `test:x/i#f$1`. Under `world`, the name
    // `test:x/i#f` must run `mid`'s function.
    //
    // The composition is closed (`svc` is plugged into `mid`), yet meld leaves
    // `mid`'s import of `test:x/i` as a HOST import instead of wiring `svc`
    // (#499, pre-existing, not fixed here). So the host serves it, and with a
    // value DISTINCT from `svc`'s (5, not 1): a stub returning 1 would make the
    // internal service and the wired composition look identical and hide that.
    // The world function returns host + 100.
    use wasmtime::{FuncType, Linker, ValType};
    let mut cfg = config(ExportPolicy::World, false);
    cfg.memory_strategy = MemoryStrategy::MultiMemory;
    cfg.address_rebasing = false;
    let fused = fuse("middleware.wasm", cfg).expect("fuses");
    validate(&fused);
    assert_eq!(export_set(&fused), set(&["func:test:x/i#f"]));

    // Structural: the world name is bound to `mid`'s implementation, the
    // function that calls the import, not to `svc`'s constant.
    assert!(
        export_body_calls_a_function(&fused, "test:x/i#f"),
        "the world name must bind to the implementation that calls the import"
    );

    let engine = wasmtime_engine();
    let mut linker = Linker::<()>::new(&engine);
    linker
        .func_new(
            "test:x/i",
            "f",
            FuncType::new(&engine, [], [ValType::I32]),
            |_c, _p, out| {
                out[0] = wasmtime::Val::I32(5);
                Ok(())
            },
        )
        .unwrap();
    let (mut store, instance) = instantiate_with(&engine, &fused, linker, &[("test:x/i", "f")]);
    let got = instance
        .get_typed_func::<(), i32>(&mut store, "test:x/i#f")
        .expect("exported")
        .call(&mut store, ())
        .expect("runs");
    assert_eq!(
        got, 105,
        "host (5) + 100: the world function, not the internal service (1)"
    );
}

/// Does the function the export `name` points at contain a `call`?
fn export_body_calls_a_function(wasm: &[u8], name: &str) -> bool {
    use wasmparser::{ExternalKind, Operator, Parser, Payload, TypeRef};
    let mut imported_funcs = 0u32;
    let mut target = None;
    let mut bodies = Vec::new();
    for payload in Parser::new(0).parse_all(wasm).flatten() {
        match payload {
            Payload::ImportSection(r) => {
                for imp in r.into_imports().flatten() {
                    if matches!(imp.ty, TypeRef::Func(_) | TypeRef::FuncExact(_)) {
                        imported_funcs += 1;
                    }
                }
            }
            Payload::ExportSection(r) => {
                for e in r.into_iter().flatten() {
                    if e.name == name && e.kind == ExternalKind::Func {
                        target = Some(e.index);
                    }
                }
            }
            Payload::CodeSectionEntry(b) => bodies.push(b),
            _ => {}
        }
    }
    let idx = target.expect("the export exists");
    let body = &bodies[(idx - imported_funcs) as usize];
    body.get_operators_reader()
        .unwrap()
        .into_iter()
        .flatten()
        .any(|op| matches!(op, Operator::Call { .. }))
}

#[test]
fn a_nested_instance_in_a_world_interface_is_refused_not_skipped() {
    // `test:y/bag` holds `f` and a nested instance exporting `g`. The unfused
    // component serves `g`; `world` used to keep only `#f` and exit 0.
    let err = fuse("nested.wasm", config(ExportPolicy::World, false))
        .expect_err("an item the walk cannot enumerate must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("test:y/bag") && msg.contains("nested"),
        "names the interface and the item: {msg}"
    );
    // It fuses without the flag, so the refusal is the flag's.
    fuse("nested.wasm", config(ExportPolicy::All, false)).expect("fuses without it");
}

#[test]
fn the_dtors_of_resources_whose_intrinsics_are_still_imported_are_kept() {
    // `resources.wasm` still imports `[export]… [resource-new/rep/drop]`; the
    // wrapper finds a resource's dtor by its export name, so those must stay.
    let path = format!(
        "{}/../tests/wit_bindgen/fixtures/resources.wasm",
        env!("CARGO_MANIFEST_DIR")
    );
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let fused = fuse_bytes(&bytes, ExportPolicy::World);
    validate(&fused);
    let exports = export_set(&fused);
    for dtor in [
        "func:imports#[dtor]y",
        "func:exports#[dtor]x",
        "func:exports#[dtor]z",
        "func:exports#[dtor]kebab-case",
    ] {
        assert!(exports.contains(dtor), "{dtor} dropped: {exports:?}");
    }
}

fn fuse_bytes(bytes: &[u8], policy: ExportPolicy) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        attestation: false,
        reproducible: true,
        export_policy: policy,
        ..Default::default()
    });
    fuser
        .add_component_named(bytes, Some("input"))
        .expect("parses");
    fuser.fuse().expect("fuses")
}

fn module_imports(wasm: &[u8]) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(wasm) {
        if let Ok(wasmparser::Payload::ImportSection(reader)) = payload {
            for imp in reader.into_imports().flatten() {
                out.push((imp.module.to_string(), imp.name.to_string()));
            }
        }
    }
    out
}

#[test]
fn across_the_whole_corpus_a_world_keeps_what_its_imports_and_resources_need() {
    // Every wit-bindgen fixture, fused under `world`. The oracle is the INPUT
    // component and the fused module's own imports, not the pruner's tables:
    //  * if any `canon lower` of the input names a memory (realloc) and a
    //    lowered import remains, the module exports a memory (an allocator);
    //  * for every `[export]…` resource intrinsic still imported, the `[dtor]`
    //    that `all` exports is still exported.
    let dir = format!(
        "{}/../tests/wit_bindgen/fixtures",
        env!("CARGO_MANIFEST_DIR")
    );
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .expect("fixtures dir")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wasm"))
        .collect();
    paths.sort();
    assert!(paths.len() >= 49, "the corpus is {} files", paths.len());

    // 98 debug-build fusions: spread them over a few threads.
    let per_thread = paths.len().div_ceil(8);
    let totals: Vec<(usize, usize, usize)> = std::thread::scope(|scope| {
        let handles: Vec<_> = paths
            .chunks(per_thread)
            .map(|chunk| scope.spawn(move || check_corpus_chunk(chunk)))
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let needing_memory: usize = totals.iter().map(|t| t.0).sum();
    let needing_realloc: usize = totals.iter().map(|t| t.1).sum();
    let dtors_checked: usize = totals.iter().map(|t| t.2).sum();
    // Guards: the oracle must have had something to check.
    assert!(
        needing_memory >= 20,
        "only {needing_memory} fixtures need a memory"
    );
    assert!(
        needing_realloc >= 5,
        "only {needing_realloc} fixtures need a realloc"
    );
    assert!(
        dtors_checked >= 5,
        "only {dtors_checked} dtors were checked"
    );
}

/// Returns (fixtures needing a memory, fixtures needing a realloc, dtors checked).
fn check_corpus_chunk(paths: &[std::path::PathBuf]) -> (usize, usize, usize) {
    let mut needing_memory = 0;
    let mut needing_realloc = 0;
    let mut dtors_checked = 0;
    for path in paths {
        let bytes = std::fs::read(path).unwrap();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let all = fuse_bytes(&bytes, ExportPolicy::All);
        let world = fuse_bytes(&bytes, ExportPolicy::World);
        validate(&world);
        let all_exports = export_set(&all);
        let world_exports = export_set(&world);

        // Nothing appears out of nowhere: a world export was an `all` export
        // or a named allocator.
        for e in &world_exports {
            assert!(
                all_exports.contains(e) || e.starts_with("func:meld:realloc/"),
                "{name}: `{e}` is new"
            );
        }

        let component = meld_core::parser::ComponentParser::new()
            .parse(&bytes)
            .expect("parses");
        // The lowers live in the nested components, not the outer shell.
        fn collect<'a>(
            c: &'a meld_core::parser::ParsedComponent,
            out: &mut Vec<&'a meld_core::parser::CanonicalOptions>,
        ) {
            for e in &c.canonical_functions {
                if let meld_core::parser::CanonicalEntry::Lower { options, .. } = e {
                    out.push(options);
                }
            }
            for sub in &c.sub_components {
                collect(sub, out);
            }
        }
        let mut lowers = Vec::new();
        collect(&component, &mut lowers);
        let imports = module_imports(&world);
        let lowered_remaining = imports.iter().any(|(_, n)| !n.starts_with("[resource-"));
        if lowered_remaining && lowers.iter().any(|o| o.memory.is_some()) {
            needing_memory += 1;
            assert!(
                world_exports.iter().any(|e| e.starts_with("memory:")),
                "{name}: a remaining import's lower names a memory, none is exported"
            );
        }
        if lowered_remaining && lowers.iter().any(|o| o.realloc.is_some()) {
            needing_realloc += 1;
            assert!(
                world_exports
                    .iter()
                    .any(|e| e.starts_with("func:cabi_realloc")
                        || e.starts_with("func:meld:realloc/")),
                "{name}: a remaining import's lower names a realloc, none is exported"
            );
        }
        for (module, field) in &imports {
            for prefix in ["[resource-new]", "[resource-rep]", "[resource-drop]"] {
                if let Some(resource) = field.strip_prefix(prefix) {
                    let iface = module.strip_prefix("[export]").unwrap_or(module);
                    let dtor = format!("func:{iface}#[dtor]{resource}");
                    if all_exports.contains(&dtor) {
                        dtors_checked += 1;
                        assert!(world_exports.contains(&dtor), "{name}: {dtor} dropped");
                    }
                }
            }
        }
    }
    (needing_memory, needing_realloc, dtors_checked)
}

#[test]
fn without_a_manifest_a_kept_lifts_allocator_is_still_exported_and_usable() {
    // Under `--memory shared` the allocator `controller#step`'s lift names is
    // internal; `all` does not export it either. A host cannot pass `step` its
    // 26 flat arguments without it, so `world` exports it as `meld:realloc/N`
    // whether or not `--emit-manifest` is set, and `step` runs with it.
    let fused = fuse("composed.wasm", config(ExportPolicy::World, false)).expect("fuses");
    let exports = export_set(&fused);
    let realloc = exports
        .iter()
        .find_map(|e| e.strip_prefix("func:meld:realloc/"))
        .map(|n| format!("meld:realloc/{n}"))
        .expect("an allocator is exported");

    use wasmtime::{Instance, Module, Store};
    let engine = wasmtime_engine();
    let module = Module::new(&engine, &fused).expect("loads");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiates");
    let memory = instance.get_memory(&mut store, "memory").expect("memory");
    let alloc = instance
        .get_typed_func::<(i32, i32, i32, i32), i32>(&mut store, &realloc)
        .expect("allocator");
    let args = step_args();
    let ptr = alloc
        .call(&mut store, (0, 0, 4, args.len() as i32))
        .expect("allocates");
    memory.write(&mut store, ptr as usize, &args).unwrap();
    let configure = instance
        .get_typed_func::<(f32, f32, f32, f32, f32, f32, f32, f32, f32), ()>(
            &mut store,
            &format!("{CONTROLLER}#configure"),
        )
        .unwrap();
    configure
        .call(
            &mut store,
            (
                CFG[0], CFG[1], CFG[2], CFG[3], CFG[4], CFG[5], CFG[6], CFG[7], CFG[8],
            ),
        )
        .unwrap();
    let ret = instance
        .get_typed_func::<i32, i32>(&mut store, &format!("{CONTROLLER}#step"))
        .unwrap()
        .call(&mut store, ptr)
        .expect("step runs with the exported allocator");
    let mut out = [0u8; 16];
    memory.read(&store, ret as usize, &mut out).unwrap();
    let got: Vec<u32> = out
        .chunks(4)
        .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
        .collect();
    let unfused = run_unfused().map(f32::to_bits);
    assert_eq!(got, unfused.to_vec());
}
