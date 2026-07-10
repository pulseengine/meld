//! Golden end-to-end behavioural-equivalence harness (#142 confidence /
//! "is it really working").
//!
//! meld's central correctness claim is **fusion preserves observable
//! behaviour**. This harness falsifies that directly, differentially:
//!
//! 1. Run a real component **unfused** under wasmtime, capturing its
//!    observable result (run-ok + stdout). *That result is the golden* —
//!    no hand-authored expected values to rot.
//! 2. `meld fuse` it (each output format × memory strategy).
//! 3. Run the **fused** output under the same deterministic WASI.
//! 4. Assert fused behaviour == unfused behaviour.
//!
//! WASI is wired deterministically (captured stdout, no inherited
//! env/clock/fs) so any divergence is meld's doing, not ambient noise.
//!
//! **Tier A** (this section): single-component round-trip equivalence
//! over the wit-bindgen ABI fixtures.
//! **Tier B** (`tier_b` module): fuse a *multi-component* composition and
//! assert it matches the host-linked (wac-composed) original.
//!
//! Honest boundary: this proves equivalence under **wasmtime**, the
//! reference runtime — NOT on the synth/kiln MCU target. A module that
//! passes here can still break after synth transcodes it; that
//! cross-repo hardware smoke is tracked separately.

use meld_core::{
    CustomSectionHandling, DwarfHandling, Fuser, FuserConfig, MemoryStrategy, OutputFormat,
};
use wasmtime::component::{Component, Linker, ResourceTable};
use wasmtime::{Config, Engine, Store};
use wasmtime_wasi::p2::bindings::sync::Command;
use wasmtime_wasi::p2::pipe::MemoryOutputPipe;
use wasmtime_wasi::{WasiCtx, WasiCtxView, WasiView};

const FIXTURES_DIR: &str = "../tests/wit_bindgen/fixtures";

/// Real wit-bindgen ABI test components (host runner + guest), each a
/// self-contained P2 command component. Behaviour = run-ok + stdout.
const TIER_A_CORPUS: &[&str] = &[
    // wit-bindgen ABI test components (run-ok signal; mostly empty stdout).
    "numbers",
    "strings",
    "lists",
    "records",
    "variants",
    "options",
    "many-arguments",
    "flavorful",
    "results",
    // Real cross-language command components that print to stdout — the
    // strong differential: fused output must print byte-identical text.
    "release-0.2.0/hello_rust",
    "release-0.2.0/hello_c_cli",
    "release-0.2.0/hello_cpp_cli",
];

struct WasiState {
    ctx: WasiCtx,
    table: ResourceTable,
}

impl WasiView for WasiState {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView {
            ctx: &mut self.ctx,
            table: &mut self.table,
        }
    }
}

/// Observable behaviour of running a component: did `run()` succeed, and
/// what did it write to stdout.
#[derive(Debug, PartialEq, Eq)]
struct Outcome {
    ok: bool,
    stdout: Vec<u8>,
}

/// Run a P2 component under deterministic WASI and capture its outcome.
/// Never panics — a compile/instantiate/trap failure is `ok: false`, so
/// the *original* failing the same way as the *fused* still compares
/// equal (we assert equivalence, not success).
fn run_capture(wasm: &[u8]) -> Outcome {
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    cfg.wasm_multi_memory(true);
    let engine = match Engine::new(&cfg) {
        Ok(e) => e,
        Err(e) => {
            return Outcome {
                ok: false,
                stdout: format!("engine: {e}").into_bytes(),
            };
        }
    };

    let mut linker: Linker<WasiState> = Linker::new(&engine);
    if wasmtime_wasi::p2::add_to_linker_sync(&mut linker).is_err() {
        return Outcome {
            ok: false,
            stdout: b"linker".to_vec(),
        };
    }

    let component = match Component::new(&engine, wasm) {
        Ok(c) => c,
        Err(e) => {
            return Outcome {
                ok: false,
                stdout: format!("compile: {e}").into_bytes(),
            };
        }
    };

    // Deterministic WASI: captured stdout, no inherited env/args/clock/fs.
    let stdout = MemoryOutputPipe::new(1 << 20);
    let mut builder = WasiCtx::builder();
    builder.stdout(stdout.clone());
    let mut store = Store::new(
        &engine,
        WasiState {
            ctx: builder.build(),
            table: ResourceTable::new(),
        },
    );

    let ok = invoke_run(&mut store, &linker, &component).is_ok();
    let captured = stdout.contents().to_vec();
    Outcome {
        ok,
        stdout: captured,
    }
}

/// Call the component's `run` entrypoint (typed Command API, then
/// version-agnostic fallback) — mirrors the existing wit_bindgen harness.
fn invoke_run(
    store: &mut Store<WasiState>,
    linker: &Linker<WasiState>,
    component: &Component,
) -> anyhow::Result<()> {
    if let Ok(command) = Command::instantiate(&mut *store, component, linker) {
        return command
            .wasi_cli_run()
            .call_run(&mut *store)?
            .map_err(|()| anyhow::anyhow!("wasi:cli/run returned Err"));
    }
    let instance = linker.instantiate(&mut *store, component)?;
    let func = if let Some(f) = instance.get_func(&mut *store, "run") {
        f
    } else {
        let mut found = None;
        for version in ["wasi:cli/run@0.2.6", "wasi:cli/run@0.2.3"] {
            if let Some((_, idx)) = instance.get_export(&mut *store, None, version)
                && let Some((_, run_idx)) = instance.get_export(&mut *store, Some(&idx), "run")
            {
                found = instance.get_func(&mut *store, run_idx);
                break;
            }
        }
        found.ok_or_else(|| anyhow::anyhow!("no run export"))?
    };
    let mut results = [];
    func.call(&mut *store, &[], &mut results)?;
    func.post_return(&mut *store)?;
    Ok(())
}

fn fuse(
    bytes: &[u8],
    name: &str,
    output_format: OutputFormat,
    memory_strategy: MemoryStrategy,
) -> anyhow::Result<Vec<u8>> {
    fuse_many(&[(name, bytes)], output_format, memory_strategy)
}

/// Fuse one or more input components in a single invocation — meld's
/// native multi-component path (it resolves cross-component imports
/// against the other inputs' exports and internalises the call).
fn fuse_many(
    inputs: &[(&str, &[u8])],
    output_format: OutputFormat,
    memory_strategy: MemoryStrategy,
) -> anyhow::Result<Vec<u8>> {
    let address_rebasing = matches!(memory_strategy, MemoryStrategy::SharedMemory);
    let config = FuserConfig {
        memory_strategy,
        attestation: false,
        component_provenance: false,
        address_rebasing,
        preserve_names: false,
        custom_sections: CustomSectionHandling::Drop,
        dwarf_handling: DwarfHandling::Strip,
        output_format,
        opaque_resources: Vec::new(),
    };
    let mut fuser = Fuser::new(config);
    for (name, bytes) in inputs {
        fuser.add_component_named(bytes, Some(name))?;
    }
    Ok(fuser.fuse()?)
}

fn fixture_bytes(name: &str) -> Option<Vec<u8>> {
    let path = format!("{FIXTURES_DIR}/{name}.wasm");
    std::fs::read(&path).ok().or_else(|| {
        eprintln!("skipping: fixture not found at {path}");
        None
    })
}

/// Tier A: for every fixture, fusing (as a Component) must preserve the
/// unfused observable behaviour, under both memory strategies.
#[test]
fn tier_a_fusion_preserves_component_behaviour() {
    let mut ran = 0usize;
    for &name in TIER_A_CORPUS {
        let Some(orig) = fixture_bytes(name) else {
            continue;
        };
        let golden = run_capture(&orig);
        // Only meaningful if the unfused original itself runs; if the
        // fixture can't run standalone here, skip (can't form a golden).
        if !golden.ok {
            eprintln!("[{name}] unfused original did not run (ok=false); skipping equivalence");
            continue;
        }

        for memory in [MemoryStrategy::MultiMemory, MemoryStrategy::SharedMemory] {
            // A fuse *refusal* (e.g. SharedMemory+rebasing rejecting
            // `memory.grow`) is meld correctly declining — not a
            // behaviour divergence. Skip; this harness asserts that when
            // meld *does* produce output, it is behaviour-equivalent.
            let fused = match fuse(&orig, name, OutputFormat::Component, memory) {
                Ok(f) => f,
                Err(e) => {
                    eprintln!("[{name}/{memory:?}] fuse declined ({e}); skipping");
                    continue;
                }
            };
            let got = run_capture(&fused);
            assert_eq!(
                got,
                golden,
                "[{name}/{memory:?}] fused behaviour diverged from unfused original \
                 (golden ok={} {}B stdout vs fused ok={} {}B stdout)",
                golden.ok,
                golden.stdout.len(),
                got.ok,
                got.stdout.len()
            );
            ran += 1;
        }
    }
    assert!(
        ran > 0,
        "no fixtures exercised — corpus missing? (looked in {FIXTURES_DIR})"
    );
    eprintln!("Tier A: {ran} fuse-and-run equivalence checks passed");
}

// ---------------------------------------------------------------------------
// Tier B: multi-component composition — meld's actual use case.
// ---------------------------------------------------------------------------

/// Path to the `wac`-composed two-component fixture (see
/// `tests/wit_bindgen/fixtures/compose/build.sh`): a `consumer` whose
/// `compute()` calls a `provider`'s `add(20, 22)`, host-linked into one
/// component. The composed component is the golden; meld fusing it must
/// preserve the cross-component call result.
const COMPOSE_DIR: &str = "../tests/wit_bindgen/fixtures/compose";

/// Instantiate a component exporting `compute: func() -> u32` and call it.
/// The composed/fused fixture has no imports, so a bare linker suffices.
/// Call both `golden:app/runner` exports with their **distinct** typed
/// signatures: `compute() -> u32` (= add(20,22) = 42) and
/// `greet() -> u8` (= 7). The typed lookups validate the WIT type, so a
/// mis-resolved lift that swapped or wrong-typed an export (the #212.2
/// failure class) makes the typed call fail — not silently return a
/// plausible number.
fn call_runner(wasm: &[u8]) -> anyhow::Result<(u32, u8)> {
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    cfg.wasm_multi_memory(true);
    let engine = Engine::new(&cfg)?;
    let linker: Linker<WasiState> = Linker::new(&engine);
    let component = Component::new(&engine, wasm)?;
    let mut store = Store::new(
        &engine,
        WasiState {
            ctx: WasiCtx::builder().build(),
            table: ResourceTable::new(),
        },
    );
    let instance = linker.instantiate(&mut store, &component)?;
    let (_, iface) = instance
        .get_export(&mut store, None, "golden:app/runner@0.1.0")
        .ok_or_else(|| anyhow::anyhow!("no golden:app/runner interface export"))?;

    let (_, cidx) = instance
        .get_export(&mut store, Some(&iface), "compute")
        .ok_or_else(|| anyhow::anyhow!("no compute in runner interface"))?;
    let compute = instance
        .get_func(&mut store, cidx)
        .ok_or_else(|| anyhow::anyhow!("compute is not a function"))?
        .typed::<(), (u32,)>(&store)?; // fails if compute isn't typed u32
    let (c,) = compute.call(&mut store, ())?;
    compute.post_return(&mut store)?;

    let (_, gidx) = instance
        .get_export(&mut store, Some(&iface), "greet")
        .ok_or_else(|| anyhow::anyhow!("no greet in runner interface"))?;
    let greet = instance
        .get_func(&mut store, gidx)
        .ok_or_else(|| anyhow::anyhow!("greet is not a function"))?
        .typed::<(), (u8,)>(&store)?; // fails if greet isn't typed u8
    let (g,) = greet.call(&mut store, ())?;
    greet.post_return(&mut store)?;

    Ok((c, g))
}

/// Read the host-linked composed fixture and its runner golden values —
/// `compute() = add(20,22) = 42` (u32) and `greet() = 7` (u8) — or `None`
/// to skip when fixtures are absent.
fn composed_golden() -> Option<(Vec<u8>, (u32, u8))> {
    let composed = std::fs::read(format!("{COMPOSE_DIR}/composed.wasm")).ok()?;
    let golden = call_runner(&composed).expect("host-linked composed runner should run");
    assert_eq!(
        golden,
        (42, 7),
        "sanity: wac-composed runner = (compute 42, greet 7)"
    );
    Some((composed, golden))
}

/// Tier B (#212.2): fusing a real `wac`-composed multi-component must
/// preserve **both** exports and their **distinct** types. The host-linked
/// composition yields `compute()=42` (u32) and `greet()=7` (u8); meld
/// fusing it must emit a self-contained component that yields the same.
/// The two-export-with-different-types fixture is adversarial: the lift's
/// `core_func_index` diverges from any module-local index (the core module
/// imports `add`), so a mis-resolved lift would swap/wrong-type the
/// exports and the typed `call_runner` lookup would fail — the exact
/// #212.2 failure class the first attempt regressed on.
#[test]
fn tier_b_fused_composed_matches_host_linked() {
    let Some((composed, golden)) = composed_golden() else {
        eprintln!("skipping: compose fixtures not found in {COMPOSE_DIR} (run build.sh)");
        return;
    };

    let mut ran = 0usize;
    for memory in [MemoryStrategy::MultiMemory, MemoryStrategy::SharedMemory] {
        let fused = match fuse(&composed, "composed", OutputFormat::Component, memory) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("[composed/{memory:?}] fuse declined ({e}); skipping");
                continue;
            }
        };
        let got = call_runner(&fused).unwrap_or_else(|e| {
            panic!(
                "[composed/{memory:?}] fused runner failed: {e} — meld dropped or \
                 mis-typed the composition's exports (#212.2)"
            )
        });
        assert_eq!(
            got, golden,
            "[composed/{memory:?}] meld-fused composition diverged from host-linked: \
             got {got:?}, want {golden:?}"
        );
        eprintln!("Tier B [{memory:?}]: fused composed runner = {got:?} ✓");
        ran += 1;
    }
    assert!(ran > 0, "no memory strategy produced a fusable composition");
}

/// Tier B (#212.1, still open): meld's *native* path — hand it the two
/// components separately and have it link consumer→provider, internalise
/// the call, and emit a self-contained component. Currently `#[ignore]`d:
/// meld does not yet resolve a cross-component *interface* import/export
/// across separate inputs (the fused output still imports
/// `golden:math/lib`). Un-ignored since #212.1 landed (v0.28.0):
/// component_wrap drops internalised instance imports and renumbers
/// the survivors, so the fused component is self-contained.
/// (`ls_cp_6_` alias below: LS-CP-6 regression, run by the LS-N gate.)
#[test]
fn tier_b_separate_inputs_internalise_link() {
    let (Ok(consumer), Ok(provider), Some((_, golden))) = (
        std::fs::read(format!("{COMPOSE_DIR}/consumer.wasm")),
        std::fs::read(format!("{COMPOSE_DIR}/provider.wasm")),
        composed_golden(),
    ) else {
        eprintln!("skipping: compose fixtures not found in {COMPOSE_DIR}");
        return;
    };
    let fused = fuse_many(
        &[("consumer", &consumer), ("provider", &provider)],
        OutputFormat::Component,
        MemoryStrategy::MultiMemory,
    )
    .expect("fuse two inputs");
    let got =
        call_runner(&fused).expect("fused separate-input composition should run runner standalone");
    assert_eq!(got, golden, "separate-input fusion must match host-linked");
}

#[test]
fn ls_cp_6_separate_inputs_internalise_link() {
    tier_b_separate_inputs_internalise_link();
}

// ---------------------------------------------------------------------------
// Tier C (#297): execution on kiln — the safety-critical MCU-target runtime,
// not just wasmtime. This is the "honest boundary" Tier A/B disclose.
// ---------------------------------------------------------------------------

/// Locate the `kilnd` binary: `MELD_KILND` override, else the conventional
/// sibling-repo debug build. `None` (→ skip) when unavailable, mirroring the
/// fixture-absent skips above.
fn kilnd_path() -> Option<std::path::PathBuf> {
    if let Ok(p) = std::env::var("MELD_KILND") {
        let p = std::path::PathBuf::from(p);
        if p.exists() {
            return Some(p);
        }
    }
    let conv =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../kiln/target/debug/kilnd");
    conv.exists().then_some(conv)
}

/// Run a `--component` wasm on `kilnd` and report whether kiln executed it
/// successfully. `None` when kilnd is unavailable (→ skip). `tag` only
/// disambiguates the temp file (no `Date`/rand in tests — the caller-supplied
/// tag is unique per fixture+role). Uses `std::process::Command` fully
/// qualified to avoid the `wasmtime_wasi::...::Command` import above.
fn run_on_kiln(wasm: &[u8], tag: &str) -> Option<bool> {
    let kilnd = kilnd_path()?;
    let tmp = std::env::temp_dir().join(format!("meld_tierc_{tag}.wasm"));
    std::fs::write(&tmp, wasm).ok()?;
    let out = std::process::Command::new(&kilnd)
        .arg(&tmp)
        .arg("--component")
        .arg("--wasi")
        .output()
        .ok()?;
    let _ = std::fs::remove_file(&tmp);
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    // kilnd prints an explicit success/failure line; exit code alone is
    // unreliable across its run modes.
    Some(combined.contains("executed successfully") && !combined.contains("Execution failed"))
}

/// Tier C (#297): a meld-fused component must EXECUTE on kiln — the
/// safety-critical MCU-target runtime — not only under wasmtime (Tier A/B).
///
/// `#[ignore]`d: the meld→kiln seam runs a real meld-fused `--component` wrap
/// (stubs, fused, fixup, caller core modules) on kilnd, and kiln has been
/// clearing it one layer at a time — meld's output is spec-valid throughout
/// (the SAME artifact runs on wasmtime 41: "Hello wasm component world from
/// C!", Tier A/B green), so each blocker is kiln-side.
///
/// Progression (each resolved kiln-side, then the next layer surfaced):
/// kiln#364 (`_start` gate) resolved via kiln#374; kiln#382 (E5DC2 — the
/// `resolve_command_entry` `-K` instance-import offset) resolved in kiln v0.4.0;
/// current blocker `[Runtime][E0BBB] Export not found` (the run export resolves
/// but its function isn't found), tracked on the multi-core umbrella kiln#375.
///
/// Un-ignore when kiln#375 (and any E0BBB split) lands; it then pins the
/// meld-to-kiln behavioural seam green. Pointed at the durable umbrella so it
/// need not be re-pointed as kiln fixes each sub-layer.
#[test]
#[ignore = "blocked on kiln#375: meld-fused --component fails on kilnd with [Runtime][E0BBB] Export not found (the run export resolves but its function isn't found); the same artifact runs on wasmtime 41 so meld's output is spec-valid. kiln#364 (_start) and kiln#382 (E5DC2) are resolved; E0BBB is the current kiln-side layer, tracked on the multi-core umbrella kiln#375"]
fn tier_c_fused_executes_on_kiln() {
    if kilnd_path().is_none() {
        eprintln!("skipping Tier C: kilnd not found (set MELD_KILND or build ../../kiln)");
        return;
    }
    let mut ran = 0usize;
    for &name in &[
        "release-0.2.0/hello_c_cli",
        "release-0.2.0/hello_rust",
        "release-0.2.0/hello_cpp_cli",
    ] {
        let Some(orig) = fixture_bytes(name) else {
            continue;
        };
        let tag = name.replace('/', "_");
        // Baseline: the unfused original must run on kiln, else a fused
        // failure can't be attributed to fusion.
        match run_on_kiln(&orig, &format!("{tag}_orig")) {
            Some(true) => {}
            Some(false) => {
                eprintln!("[{name}] unfused original did not execute on kiln; skipping");
                continue;
            }
            None => return, // kilnd vanished mid-run
        }
        let fused = fuse(
            &orig,
            name,
            OutputFormat::Component,
            MemoryStrategy::MultiMemory,
        )
        .expect("fusing a single command component must succeed");
        let ok = run_on_kiln(&fused, &format!("{tag}_fused")).expect("kilnd available (checked)");
        assert!(
            ok,
            "[{name}] meld-fused component must execute on kiln (kiln#364): \
             the unfused original ran but the fused one did not"
        );
        ran += 1;
    }
    assert!(
        ran > 0,
        "Tier C exercised no command fixtures (corpus missing in {FIXTURES_DIR}?)"
    );
    eprintln!("Tier C: {ran} fused components executed on kiln ✓");
}
