//! Canonical ABI differential: every fixture in `tests/fixtures/abi_diff/`
//! runs once unfused, on wasmtime's component runtime, and once per memory
//! strategy after fusion. The unfused run is the reference: it implements the
//! Canonical ABI's lift, lower, transcode and validation traps, so a fused
//! result that differs from it is a meld bug.
//!
//! Each fixture is a two-component composition whose root exports
//! `run: func() -> u32`. Most were generated to cover string encodings x value
//! shapes (string, char, list, record, variant, option, result, tuple,
//! fixed-length list, params-ptr spills); the `issueNNN-*` ones are the reduced
//! reproductions filed as #597-#603.
//!
//! The outcome of every (fixture, strategy) pair is pinned in
//! `abi_diff/outcomes.tsv`. Any change fails: a fix moves rows to `match`, a
//! regression moves them away, and either way the ledger is updated in the
//! same change (`MELD_BLESS=1`), so the diff shows exactly which shapes moved.
//! The fourth column is a free-form note (usually the issue) and survives a
//! bless for rows whose outcome did not change.
//!
//! `--memory shared` runs WITHOUT `--address-rebase`. The fixtures pass
//! constant pointers and carry no relocations, so a rebased run would measure
//! the missing relocations, not the adapter.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasmtime::{Config, Engine, Instance, Module, Store};

const STRATEGIES: [(&str, MemoryStrategy); 2] = [
    ("multi", MemoryStrategy::MultiMemory),
    ("shared", MemoryStrategy::SharedMemory),
];

fn dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/abi_diff")
}

#[derive(Debug, Clone, PartialEq)]
enum Run {
    Ok(u32),
    Trap,
    /// Not a usable reference or not a usable fused module: the reason.
    Error(String),
}

fn run_unfused(bytes: &[u8]) -> Run {
    let mut c = Config::new();
    c.wasm_component_model(true);
    c.wasm_multi_memory(true);
    c.wasm_component_model_fixed_length_lists(true);
    let engine = Engine::new(&c).unwrap();
    let comp = match wasmtime::component::Component::new(&engine, bytes) {
        Ok(c) => c,
        Err(e) => return Run::Error(format!("unfused-invalid: {e}")),
    };
    let mut store = Store::new(&engine, ());
    let linker = wasmtime::component::Linker::<()>::new(&engine);
    let inst = match linker.instantiate(&mut store, &comp) {
        Ok(i) => i,
        Err(e) => return Run::Error(format!("unfused-invalid: {e}")),
    };
    let Ok(f) = inst.get_typed_func::<(), (u32,)>(&mut store, "run") else {
        return Run::Error("unfused-invalid: no run: func() -> u32".into());
    };
    match f.call(&mut store, ()) {
        Ok((v,)) => Run::Ok(v),
        Err(_) => Run::Trap,
    }
}

/// `Err` is a refusal by meld (with its message); `Ok` is the fused run.
fn run_fused(bytes: &[u8], strategy: MemoryStrategy) -> Result<Run, String> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: strategy,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component(bytes).map_err(|e| e.to_string())?;
    let out = fuser.fuse().map_err(|e| e.to_string())?;
    let mut c = Config::new();
    c.wasm_multi_memory(true);
    let engine = Engine::new(&c).unwrap();
    let module = match Module::new(&engine, &out) {
        Ok(m) => m,
        Err(e) => return Ok(Run::Error(format!("load: {e}"))),
    };
    let mut store = Store::new(&engine, ());
    let inst = match Instance::new(&mut store, &module, &[]) {
        Ok(i) => i,
        Err(e) => return Ok(Run::Error(format!("instantiate: {e}"))),
    };
    let Ok(f) = inst.get_typed_func::<(), u32>(&mut store, "run") else {
        return Ok(Run::Error("no run export".into()));
    };
    Ok(match f.call(&mut store, ()) {
        Ok(v) => Run::Ok(v),
        Err(_) => Run::Trap,
    })
}

/// One word per (reference, fused) pair; these are the ledger's vocabulary.
fn classify(unfused: &Run, fused: &Result<Run, String>) -> &'static str {
    match (unfused, fused) {
        (Run::Error(_), _) => "unfused-invalid",
        (_, Err(msg)) if msg.contains("meld defect") => "refused-defect",
        (_, Err(_)) => "refused",
        (_, Ok(Run::Error(_))) => "not-runnable",
        (Run::Ok(a), Ok(Run::Ok(b))) if a == b => "match",
        (Run::Ok(_), Ok(Run::Ok(_))) => "wrong",
        (Run::Ok(_), Ok(Run::Trap)) => "fused-trap",
        (Run::Trap, Ok(Run::Ok(_))) => "accepts-invalid",
        (Run::Trap, Ok(Run::Trap)) => "match-trap",
    }
}

fn outcomes() -> BTreeMap<(String, String), &'static str> {
    let mut names: Vec<_> = std::fs::read_dir(dir())
        .expect("abi_diff fixtures")
        .flatten()
        .map(|e| e.file_name().to_string_lossy().to_string())
        .filter(|n| n.ends_with(".wat"))
        .collect();
    names.sort();
    let mut out = BTreeMap::new();
    for name in names {
        let bytes = wat::parse_file(dir().join(&name)).unwrap_or_else(|e| panic!("{name}: {e}"));
        let reference = run_unfused(&bytes);
        let stem = name.trim_end_matches(".wat").to_string();
        for (label, strategy) in STRATEGIES {
            let fused = run_fused(&bytes, strategy);
            out.insert(
                (stem.clone(), label.to_string()),
                classify(&reference, &fused),
            );
        }
    }
    out
}

// rivet: verifies SR-122
// rivet: verifies SWV-136
#[test]
fn canonical_abi_differential_matches_the_ledger() {
    let ledger_path = dir().join("outcomes.tsv");
    let text = std::fs::read_to_string(&ledger_path).unwrap_or_default();
    let mut ledger = BTreeMap::new();
    let mut notes = BTreeMap::new();
    for l in text
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
    {
        let c: Vec<&str> = l.split('\t').collect();
        assert!(
            c.len() >= 3,
            "outcomes.tsv: want fixture<TAB>strategy<TAB>outcome[<TAB>note]: {l:?}"
        );
        let key = (c[0].to_string(), c[1].to_string());
        ledger.insert(key.clone(), c[2].to_string());
        if let Some(n) = c.get(3) {
            notes.insert(key, n.to_string());
        }
    }

    let got = outcomes();

    // Potency floor: the differential must actually compare things, and both
    // kinds of verdict must be reachable, or "all rows match the ledger"
    // could mean "nothing ran".
    let count = |o: &str| got.values().filter(|v| **v == o).count();
    assert!(
        count("match") >= 100,
        "only {} matching runs",
        count("match")
    );
    assert!(
        count("wrong") >= 1,
        "no wrong-answer rows: the oracle can no longer see a known bug"
    );

    if std::env::var_os("MELD_BLESS").is_some() {
        let mut body = String::from(
            "# Canonical ABI differential outcomes (tests/abi_differential.rs).\n\
             # fixture\tstrategy\toutcome\tnote. Regenerate with MELD_BLESS=1.\n",
        );
        for (k, v) in &got {
            let note = match (ledger.get(k), notes.get(k)) {
                (Some(old), Some(n)) if old == v => format!("\t{n}"),
                _ => String::new(),
            };
            body.push_str(&format!("{}\t{}\t{v}{note}\n", k.0, k.1));
        }
        std::fs::write(&ledger_path, body).unwrap();
        return;
    }

    let mut diffs = Vec::new();
    for (k, v) in &got {
        match ledger.get(k) {
            Some(old) if old == v => {}
            Some(old) => diffs.push(format!("{} {}: ledger {old}, now {v}", k.0, k.1)),
            None => diffs.push(format!("{} {}: not in ledger, now {v}", k.0, k.1)),
        }
    }
    for k in ledger.keys().filter(|k| !got.contains_key(*k)) {
        diffs.push(format!("{} {}: in ledger, fixture gone", k.0, k.1));
    }
    assert!(
        diffs.is_empty(),
        "{} differential outcome(s) changed. A move to match/match-trap is a fix; \
         anything else is a regression. Re-bless with MELD_BLESS=1 once explained:\n{}",
        diffs.len(),
        diffs.join("\n")
    );
}

#[test]
fn classify_names_each_case() {
    let ok = |v| Ok(Run::Ok(v));
    assert_eq!(classify(&Run::Ok(1), &ok(1)), "match");
    assert_eq!(classify(&Run::Ok(1), &ok(2)), "wrong");
    assert_eq!(classify(&Run::Ok(1), &Ok(Run::Trap)), "fused-trap");
    assert_eq!(classify(&Run::Trap, &ok(1)), "accepts-invalid");
    assert_eq!(classify(&Run::Trap, &Ok(Run::Trap)), "match-trap");
    assert_eq!(
        classify(&Run::Ok(1), &Err("x (meld defect, please report)".into())),
        "refused-defect"
    );
    assert_eq!(classify(&Run::Ok(1), &Err("cannot fuse".into())), "refused");
    assert_eq!(
        classify(&Run::Ok(1), &Ok(Run::Error("instantiate".into()))),
        "not-runnable"
    );
    assert_eq!(classify(&Run::Error("x".into()), &ok(1)), "unfused-invalid");
}
