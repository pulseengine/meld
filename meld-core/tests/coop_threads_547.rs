//! #547 / ADR-9: P3 cooperative threads pass through to the host in the
//! PRODUCER ABI.
//!
//! meld does not lower the nine cooperative built-ins. Each becomes a core
//! import of the fused module under exactly the module/field name and core
//! type that `wit-bindgen c --generate-threading-helpers` + `wit-component`
//! emit, and the host (kiln, pulseengine/kiln#620) owns the semantics. The one
//! thing meld must add is the identity of the funcref table that
//! `thread.new-indirect`'s `fn_idx` indexes: it is exported as
//! `__meld_thread_table`.
//!
//! Fixtures: tests/p3/coop_threads_547/ (origin and sha256 in its README).
//! They are real producer output, not hand-built, so the names asserted here
//! are the ones a host will see.

use std::path::{Path, PathBuf};

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasmparser::{CanonicalFunction, Parser, Payload};

const FIXTURES: [&str; 7] = [
    "t1_new_resume.wasm",
    "t2_yield_index.wasm",
    "t3_suspend_resume.wasm",
    "t4_suspend_then_resume.wasm",
    "t5_yield_then_resume.wasm",
    "t6_promote.wasm",
    "t8_many_threads.wasm",
];

/// Independent of `meld_core::thread_builtins`: the strings and core types as
/// read off the producer output (and listed in kiln#620). `(field, params,
/// results)` with `i` = i32.
const PRODUCER_ABI: [(&str, &str, &str); 9] = [
    ("[thread-new-indirect-v0]", "ii", "i"),
    ("[thread-index]", "", "i"),
    ("[thread-yield]", "", "i"),
    ("[thread-suspend]", "", "i"),
    ("[thread-resume-later]", "i", ""),
    ("[thread-suspend-then-resume]", "i", "i"),
    ("[thread-yield-then-resume]", "i", "i"),
    ("[thread-suspend-then-promote]", "i", "i"),
    ("[thread-yield-then-promote]", "i", "i"),
];

fn fixture(name: &str) -> Vec<u8> {
    let p: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../tests/p3/coop_threads_547")
        .join(name);
    // #405: a missing fixture must FAIL, not turn the test into one that
    // asserts over nothing.
    assert!(
        p.is_file(),
        "fixture missing at {} -- it must be tracked in git (.gitignore exempts tests/p3)",
        p.display()
    );
    std::fs::read(&p).unwrap()
}

fn fuse_with(
    bytes: &[&[u8]],
    strategy: MemoryStrategy,
) -> Result<(Vec<u8>, meld_core::FusionStats), String> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: strategy,
        ..Default::default()
    });
    for b in bytes {
        fuser.add_component(b).map_err(|e| e.to_string())?;
    }
    fuser.fuse_with_stats().map_err(|e| e.to_string())
}

fn fuse(bytes: &[u8]) -> Result<(Vec<u8>, meld_core::FusionStats), String> {
    fuse_with(&[bytes], MemoryStrategy::MultiMemory)
}

/// The validation the CLI applies to every output (`validate_wasm`).
fn validate(core: &[u8]) -> Result<(), String> {
    let features = meld_core::parser::baseline_wasm_features()
        | wasmparser::WasmFeatures::COMPONENT_MODEL
        | wasmparser::WasmFeatures::MULTI_MEMORY
        | wasmparser::WasmFeatures::CM_ASYNC
        | wasmparser::WasmFeatures::CM_FIXED_LENGTH_LISTS;
    wasmparser::Validator::new_with_features(features)
        .validate_all(core)
        .map(|_| ())
        .map_err(|e| e.to_string())
}

fn sig(ty: &wasmparser::FuncType) -> (String, String) {
    let one = |v: &wasmparser::ValType| match v {
        wasmparser::ValType::I32 => 'i',
        other => panic!("unexpected core type {other:?}"),
    };
    (
        ty.params().iter().map(one).collect(),
        ty.results().iter().map(one).collect(),
    )
}

/// `(module, field, params, results)` of every function import of a core module.
fn func_imports(core: &[u8]) -> Vec<(String, String, String, String)> {
    let mut types = Vec::new();
    let mut out = Vec::new();
    for payload in Parser::new(0).parse_all(core) {
        match payload.unwrap() {
            Payload::TypeSection(r) => {
                for g in r {
                    for st in g.unwrap().into_types() {
                        match st.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(f) => types.push(Some(f)),
                            _ => types.push(None),
                        }
                    }
                }
            }
            Payload::ImportSection(r) => {
                for imp in r.into_imports() {
                    let imp = imp.unwrap();
                    if let wasmparser::TypeRef::Func(t) = imp.ty {
                        let f = types[t as usize].as_ref().unwrap();
                        let (p, r) = sig(f);
                        out.push((imp.module.to_string(), imp.name.to_string(), p, r));
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// The cooperative built-ins the INPUT component declares, as the producer
/// field names they must surface as.
fn declared_builtins(component: &[u8]) -> Vec<&'static str> {
    let mut out = Vec::new();
    for payload in Parser::new(0).parse_all(component) {
        if let Payload::ComponentCanonicalSection(r) = payload.unwrap() {
            for c in r {
                let name = match c.unwrap() {
                    CanonicalFunction::ThreadNewIndirect { .. } => "[thread-new-indirect-v0]",
                    CanonicalFunction::ThreadIndex => "[thread-index]",
                    CanonicalFunction::ThreadYield => "[thread-yield]",
                    CanonicalFunction::ThreadSuspend => "[thread-suspend]",
                    CanonicalFunction::ThreadResumeLater => "[thread-resume-later]",
                    CanonicalFunction::ThreadSuspendThenResume => "[thread-suspend-then-resume]",
                    CanonicalFunction::ThreadYieldThenResume => "[thread-yield-then-resume]",
                    CanonicalFunction::ThreadSuspendThenPromote => "[thread-suspend-then-promote]",
                    CanonicalFunction::ThreadYieldThenPromote => "[thread-yield-then-promote]",
                    _ => continue,
                };
                out.push(name);
            }
        }
    }
    out.sort_unstable();
    out
}

// rivet: verifies SWV-122
#[test]
fn clang_thread_components_fuse_validate_and_import_the_producer_names() {
    let mut all_seen = std::collections::BTreeSet::new();
    for name in FIXTURES {
        let input = fixture(name);
        let want = declared_builtins(&input);
        assert!(
            !want.is_empty(),
            "{name}: the fixture declares no cooperative built-in, the test would assert over nothing"
        );
        let (core, _) = fuse(&input).unwrap_or_else(|e| panic!("{name}: must fuse: {e}"));
        validate(&core).unwrap_or_else(|e| panic!("{name}: output must validate: {e}"));

        let mut got: Vec<&str> = Vec::new();
        let imports = func_imports(&core);
        for (m, f, p, r) in &imports {
            if !f.starts_with("[thread-") {
                continue;
            }
            assert_eq!(m, "$root", "{name}: {f} must be filed under $root");
            let (_, ep, er) = PRODUCER_ABI
                .iter()
                .find(|(n, _, _)| n == f)
                .unwrap_or_else(|| panic!("{name}: unknown thread import {f}"));
            assert_eq!(
                (p.as_str(), r.as_str()),
                (*ep, *er),
                "{name}: core type of {f}"
            );
            got.push(PRODUCER_ABI.iter().find(|(n, _, _)| n == f).unwrap().0);
            all_seen.insert(f.clone());
        }
        got.sort_unstable();
        assert_eq!(
            got, want,
            "{name}: fused thread imports must equal the input's built-ins"
        );
    }
    // The seven programs between them exercise all nine built-ins.
    let all: std::collections::BTreeSet<String> =
        PRODUCER_ABI.iter().map(|(n, _, _)| n.to_string()).collect();
    assert_eq!(all_seen, all, "the fixtures must cover all nine built-ins");
}

/// Samples from wasmtime's own cooperative-threading test suite: hand-written
/// components, where the core import names come from the test author, not from
/// wit-bindgen. They must surface under the producer names all the same.
// rivet: verifies SWV-122
#[test]
fn wasmtime_threading_samples_fuse_validate_and_import_the_producer_names() {
    let samples = [
        "corpus/wasmtime_many-threads-indexed_m0.wasm",
        "corpus/wasmtime_promote-ready-threads_m0.wasm",
        // two components, both thread.index: the second is `[thread-index]$1`
        "corpus/wasmtime_threading-builtins_m5.wasm",
        "corpus/wasmtime_yield-cancellable_m0.wasm",
    ];
    for name in samples {
        let input = fixture(name);
        let want = declared_builtins(&input);
        assert!(!want.is_empty(), "{name}: no cooperative built-in declared");
        let (core, stats) = fuse(&input).unwrap_or_else(|e| panic!("{name}: must fuse: {e}"));
        validate(&core).unwrap_or_else(|e| panic!("{name}: output must validate: {e}"));
        // The import map treats `[thread-index]$1` as the built-in it is: no
        // memory/realloc/encoding, and the component it belongs to is known.
        let mapped: Vec<_> = stats
            .import_map
            .iter()
            .filter(|e| e.name.starts_with("[thread-"))
            .collect();
        assert!(
            !mapped.is_empty(),
            "{name}: thread imports in the import map"
        );
        for e in &mapped {
            assert_eq!(
                e.memory,
                meld_core::import_map::LowerOption::Absent,
                "{name}: {}",
                e.name
            );
            assert_eq!(
                e.realloc,
                meld_core::import_map::LowerOption::Absent,
                "{name}: {}",
                e.name
            );
            assert_eq!(
                e.encoding,
                meld_core::import_map::LowerOption::Absent,
                "{name}: {}",
                e.name
            );
            assert!(
                e.component.is_some(),
                "{name}: {} has an owning component",
                e.name
            );
        }
        if name.contains("threading-builtins_m5") {
            assert!(
                mapped.iter().any(|e| e.name == "[thread-index]$1"),
                "the second component's import is the suffixed one: {:?}",
                mapped.iter().map(|e| &e.name).collect::<Vec<_>>()
            );
        }
        let mut got: Vec<String> = Vec::new();
        for (m, f, p, r) in func_imports(&core) {
            if !f.starts_with("[thread-") {
                continue;
            }
            // `--memory multi` suffixes a second component's copy of the same
            // import with `$<component>`, as for every pass-through built-in.
            let base = f.split('$').next().unwrap().to_string();
            assert_eq!(m, "$root", "{name}: {f}");
            let (_, ep, er) = PRODUCER_ABI
                .iter()
                .find(|(n, _, _)| *n == base)
                .unwrap_or_else(|| panic!("{name}: unknown thread import {f}"));
            assert_eq!(
                (p.as_str(), r.as_str()),
                (*ep, *er),
                "{name}: core type of {f}"
            );
            got.push(base);
        }
        got.sort_unstable();
        assert_eq!(got, want, "{name}");
    }
}

/// Table identity, structurally: the exported table is a funcref table whose
/// initialised entries are all `(i32) -> ()` start functions defined in the
/// module (never one of the host imports, which is what the wit-component
/// shim's `$imports` table holds).
// rivet: verifies SWV-122
#[test]
fn thread_table_is_exported_and_holds_the_start_functions() {
    for name in FIXTURES {
        let input = fixture(name);
        if !declared_builtins(&input).contains(&"[thread-new-indirect-v0]") {
            continue;
        }
        let (core, stats) = fuse(&input).unwrap();
        let table = exported_table(&core, "__meld_thread_table")
            .unwrap_or_else(|| panic!("{name}: __meld_thread_table must be exported"));
        assert_eq!(
            stats
                .thread_table
                .as_ref()
                .map(|t| (t.index, t.export.as_str())),
            Some((table, "__meld_thread_table")),
            "{name}: stats must name the same table"
        );
        let (n_imports, funcs_in_table) = table_entries(&core, table);
        assert!(!funcs_in_table.is_empty(), "{name}: the table has entries");
        for f in funcs_in_table {
            assert!(
                f >= n_imports,
                "{name}: entry {f} of the thread table is a host import, so this is the \
                 shim's $imports table, not the table new-indirect indexes"
            );
        }
    }
}

fn exported_table(core: &[u8], export: &str) -> Option<u32> {
    for payload in Parser::new(0).parse_all(core) {
        if let Payload::ExportSection(r) = payload.unwrap() {
            for e in r {
                let e = e.unwrap();
                if e.name == export && e.kind == wasmparser::ExternalKind::Table {
                    return Some(e.index);
                }
            }
        }
    }
    None
}

/// `(function-import count, function indices in active elem segments of `table`)`.
fn table_entries(core: &[u8], table: u32) -> (u32, Vec<u32>) {
    let mut n_imports = 0;
    let mut funcs = Vec::new();
    for payload in Parser::new(0).parse_all(core) {
        match payload.unwrap() {
            Payload::ImportSection(r) => {
                for i in r.into_imports() {
                    if matches!(i.unwrap().ty, wasmparser::TypeRef::Func(_)) {
                        n_imports += 1;
                    }
                }
            }
            Payload::ElementSection(r) => {
                for e in r {
                    let e = e.unwrap();
                    if let wasmparser::ElementKind::Active { table_index, .. } = e.kind
                        && table_index.unwrap_or(0) == table
                        && let wasmparser::ElementItems::Functions(fs) = e.items
                    {
                        for f in fs {
                            funcs.push(f.unwrap());
                        }
                    }
                }
            }
            _ => {}
        }
    }
    (n_imports, funcs)
}

// ---- dynamic proof ---------------------------------------------------------

#[derive(Default)]
struct Host {
    /// (fn_idx, arg) per created thread; handle = position + 1.
    threads: Vec<(i32, i32)>,
    runnable: Vec<usize>,
    /// Which exported table the host uses to resolve `fn_idx`.
    table_export: &'static str,
}

fn run_with_host(core: &[u8], table_export: &'static str) -> Result<i32, String> {
    use wasmtime::{Caller, Config, Engine, Linker, Module, Ref, Store};
    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).map_err(|e| e.to_string())?;
    let module = Module::new(&engine, core).map_err(|e| e.to_string())?;
    let mut linker: Linker<Host> = Linker::new(&engine);
    let l = |e: wasmtime::Error| e.to_string();

    linker
        .func_wrap("$root", "[thread-index]", |_: Caller<'_, Host>| -> i32 {
            0
        })
        .map_err(l)?;
    linker
        .func_wrap(
            "$root",
            "[thread-new-indirect-v0]",
            |mut c: Caller<'_, Host>, fn_idx: i32, arg: i32| -> i32 {
                c.data_mut().threads.push((fn_idx, arg));
                c.data().threads.len() as i32
            },
        )
        .map_err(l)?;
    linker
        .func_wrap(
            "$root",
            "[thread-resume-later]",
            |mut c: Caller<'_, Host>, h: i32| {
                c.data_mut().runnable.push(h as usize - 1);
            },
        )
        .map_err(l)?;
    // `thread.yield` runs every runnable thread to completion, resolving each
    // start function through the table the fused module EXPORTS.
    linker
        .func_wrap(
            "$root",
            "[thread-yield]",
            |mut c: Caller<'_, Host>| -> wasmtime::Result<i32> {
                let name = c.data().table_export;
                let table = c
                    .get_export(name)
                    .and_then(|e| e.into_table())
                    .ok_or_else(|| wasmtime::Error::msg(format!("no table export {name}")))?;
                let todo = std::mem::take(&mut c.data_mut().runnable);
                for t in todo {
                    let (fn_idx, arg) = c.data().threads[t];
                    let func = match table.get(&mut c, fn_idx as u64) {
                        Some(Ref::Func(Some(f))) => f,
                        other => {
                            return Err(wasmtime::Error::msg(format!(
                                "{name}[{fn_idx}] is not a function: {other:?}"
                            )));
                        }
                    };
                    func.typed::<i32, ()>(&c)?.call(&mut c, arg)?;
                }
                Ok(0)
            },
        )
        .map_err(l)?;
    linker
        .func_wrap("$root", "[thread-suspend]", |_: Caller<'_, Host>| -> i32 {
            0
        })
        .map_err(l)?;
    for stub in [
        "[thread-suspend-then-resume]",
        "[thread-yield-then-resume]",
        "[thread-suspend-then-promote]",
        "[thread-yield-then-promote]",
    ] {
        linker
            .func_wrap("$root", stub, |_: Caller<'_, Host>, _: i32| -> i32 { 0 })
            .map_err(l)?;
    }

    let mut store = Store::new(
        &engine,
        Host {
            table_export,
            ..Default::default()
        },
    );
    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| e.to_string())?;
    let run = instance
        .get_typed_func::<(), i32>(&mut store, "run")
        .map_err(|e| e.to_string())?;
    run.call(&mut store, ()).map_err(|e| format!("{e:#}"))
}

/// The fn index a program passes to `thread.new-indirect` really selects its
/// start function in `__meld_thread_table`. The expected values are what
/// wasmtime 51-dev returns for the SAME components (kiln#620 oracle table:
/// new_resume 7, many_threads 36).
// rivet: verifies SWV-122
#[test]
fn new_indirect_resolves_through_the_exported_table() {
    for (name, expected) in [("t1_new_resume.wasm", 7), ("t8_many_threads.wasm", 36)] {
        let (core, _) = fuse(&fixture(name)).unwrap();
        assert_eq!(
            run_with_host(&core, "__meld_thread_table"),
            Ok(expected),
            "{name}"
        );
    }
}

/// Negative control for the test above: resolving `fn_idx` through the OTHER
/// table the fused module exports (the wit-component shim's `$imports`) must
/// fail, otherwise the test would pass for any table.
#[test]
fn negative_control_the_shim_table_is_not_the_thread_table() {
    let (core, _) = fuse(&fixture("t1_new_resume.wasm")).unwrap();
    assert!(
        exported_table(&core, "$imports").is_some(),
        "the fused module exports the shim table as $imports"
    );
    let err = run_with_host(&core, "$imports").expect_err("the shim table must not resolve fn_idx");
    assert!(err.contains("is not a function"), "{err}");
}

// ---- import map and attestation -------------------------------------------

// rivet: verifies SWV-122
#[test]
fn import_map_and_attestation_record_the_thread_table() {
    let (_, stats) = fuse(&fixture("t1_new_resume.wasm")).unwrap();
    let table = stats.thread_table.clone().expect("thread table recorded");
    assert_eq!(table.export, "__meld_thread_table");

    let entry = stats
        .import_map
        .iter()
        .find(|e| e.name == "[thread-new-indirect-v0]")
        .expect("new-indirect is in the import map");
    assert_eq!(entry.thread_table.as_ref(), Some(&table));
    for e in &stats.import_map {
        if e.name != "[thread-new-indirect-v0]" {
            assert!(
                e.thread_table.is_none(),
                "{}: only new-indirect carries a table",
                e.name
            );
        }
        if e.name.starts_with("[thread-") {
            assert_eq!(
                e.memory,
                meld_core::import_map::LowerOption::Absent,
                "{}",
                e.name
            );
        }
    }

    let attestation = meld_core::attestation::FusionAttestationBuilder::new("meld", "0.0.0")
        .memory_strategy("multi")
        .add_input(b"x", "t1.wasm", 1)
        .build(b"out", &stats);
    assert_eq!(attestation.metadata.thread_table.as_ref(), Some(&table));
    let json = attestation.to_json().unwrap();
    assert!(json.contains("\"thread_table\""), "{json}");
    assert!(json.contains("__meld_thread_table"), "{json}");

    // A fuse with no cooperative thread leaves the attestation unchanged.
    let (_, plain) = fuse(&fixture("t2_yield_index.wasm")).unwrap();
    assert!(
        plain.thread_table.is_none(),
        "t2 never calls thread.new-indirect"
    );
    let json = meld_core::attestation::FusionAttestationBuilder::new("meld", "0.0.0")
        .memory_strategy("multi")
        .add_input(b"x", "t2.wasm", 1)
        .build(b"out", &plain)
        .to_json()
        .unwrap();
    assert!(!json.contains("thread_table"), "{json}");
}

// ---- two tables -------------------------------------------------------------

fn two_table_component(second_table_distinct: bool) -> Vec<u8> {
    let wat = format!(
        r#"(component
  (core module $a
    (table (export "t") 1 funcref)
    (func (export "start") (param i32)))
  (core module $b
    (table (export "t") 1 funcref)
    (func (export "start") (param i32)))
  (core module $m
    (import "h" "n1" (func (param i32 i32) (result i32)))
    (import "h" "n2" (func (param i32 i32) (result i32)))
    (func (export "run") (result i32)
      (call 0 (i32.const 0) (i32.const 0))
      (call 1 (i32.const 0) (i32.const 0))
      i32.add))
  (core instance $ia (instantiate $a))
  (core instance $ib (instantiate $b))
  (core type $start (func (param i32)))
  (alias core export $ia "t" (core table $ta))
  (alias core export $ib "t" (core table $tb))
  (core func $n1 (canon thread.new-indirect $start $ta))
  (core func $n2 (canon thread.new-indirect $start {tb}))
  (core instance $h (export "n1" (func $n1)) (export "n2" (func $n2)))
  (core instance $i (instantiate $m (with "h" (instance $h))))
  (func (export "run") (result u32) (canon lift (core func $i "run"))))"#,
        tb = if second_table_distinct { "$tb" } else { "$ta" },
    );
    wat::parse_str(wat).expect("fixture parses")
}

/// Two start-function tables cannot be told apart by a host that only has
/// `__meld_thread_table`: refuse, naming ADR-9.
// rivet: verifies SWV-122
#[test]
fn two_different_new_indirect_tables_are_refused() {
    let err = fuse(&two_table_component(true)).expect_err("two tables must be refused");
    assert!(
        err.contains("two different funcref tables") && err.contains("ADR-9"),
        "{err}"
    );
}

/// Control: two `thread.new-indirect` canons over ONE table are fine, and the
/// export is that table. (Without this the refusal above could be a blanket
/// refusal of anything with two canons.)
#[test]
fn control_two_canons_over_one_table_fuse() {
    let (core, stats) = fuse(&two_table_component(false)).expect("one shared table fuses");
    validate(&core).unwrap();
    let t = stats.thread_table.expect("recorded");
    assert_eq!(exported_table(&core, "__meld_thread_table"), Some(t.index));
}

// ---- unknown built-ins and [cancellable] ------------------------------------

/// `context.get` with slot 1 needs CM_THREADING, which is on, but it is not one
/// of the nine built-ins: it must be refused by name, not mapped to an
/// "unsupported" entry that is merely logged.
// rivet: verifies SWV-122
#[test]
fn unmodelled_canonical_builtin_is_an_error_naming_it() {
    let wat = r#"(component
  (core module $m
    (import "" "g" (func (result i32)))
    (func (export "run") (result i32) (call 0)))
  (core func $g (canon context.get i32 1))
  (core instance $i (instantiate $m (with "" (instance (export "g" (func $g))))))
  (func (export "run") (result u32) (canon lift (core func $i "run"))))"#;
    let err = fuse(&wat::parse_str(wat).unwrap()).expect_err("slot 1 is not modelled");
    assert!(
        err.contains("context.get") && err.contains("slot 1") && err.contains("ADR-9"),
        "{err}"
    );
}

/// wasmparser 0.263 dropped `[cancellable]` (component-model#716): the legacy
/// byte must be 0. A producer that still sets it is refused at decode, loudly,
/// for every built-in that carried it.
// rivet: verifies SWV-122
#[test]
fn legacy_cancellable_byte_is_refused() {
    // thread.yield = 0x0c <cancellable>, thread.suspend = 0x29 <cancellable>
    for (builtin, opcode) in [("yield", 0x0cu8), ("suspend", 0x29u8)] {
        let wat = format!(
            r#"(component
  (core module $m
    (import "" "f" (func (result i32)))
    (func (export "run") (result i32) (call 0)))
  (core func $f (canon thread.{builtin}))
  (core instance $i (instantiate $m (with "" (instance (export "f" (func $f))))))
  (func (export "run") (result u32) (canon lift (core func $i "run"))))"#
        );
        let mut bytes = wat::parse_str(wat).unwrap();
        // Fuses as-is.
        fuse(&bytes).unwrap_or_else(|e| panic!("thread.{builtin} must fuse: {e}"));
        // canonical section: id 8, size 3, one entry `<opcode> <cancellable>`.
        let pos = bytes
            .windows(5)
            .position(|w| w == [0x08, 0x03, 0x01, opcode, 0x00])
            .unwrap_or_else(|| panic!("thread.{builtin} encoding not found"));
        bytes[pos + 4] = 0x01;
        let err = fuse(&bytes).expect_err("cancellable must be refused");
        assert!(err.contains("cancellable"), "thread.{builtin}: {err}");
    }
}

/// Every one of the nine built-ins, hand-written (names come from the canon
/// itself, not from a producer's wrapper), is renamed to the producer ABI.
// rivet: verifies SWV-122
#[test]
fn hand_written_builtins_surface_under_producer_names() {
    let wat = r#"(component
  (core module $a (table (export "t") 4 funcref) (func (export "start") (param i32)))
  (core module $m
    (import "h" "new" (func (param i32 i32) (result i32)))
    (import "h" "index" (func (result i32)))
    (import "h" "yield" (func (result i32)))
    (import "h" "suspend" (func (result i32)))
    (import "h" "resume-later" (func (param i32)))
    (import "h" "s-t-r" (func (param i32) (result i32)))
    (import "h" "y-t-r" (func (param i32) (result i32)))
    (import "h" "s-t-p" (func (param i32) (result i32)))
    (import "h" "y-t-p" (func (param i32) (result i32)))
    (func (export "run") (result i32)
      (call 0 (i32.const 0) (i32.const 0)) drop
      (call 1) drop (call 2) drop (call 3) drop
      (call 4 (i32.const 0))
      (call 5 (i32.const 0)) drop (call 6 (i32.const 0)) drop
      (call 7 (i32.const 0)) drop (call 8 (i32.const 0))))
  (core instance $ia (instantiate $a))
  (core type $start (func (param i32)))
  (alias core export $ia "t" (core table $t))
  (core func $new (canon thread.new-indirect $start $t))
  (core func $index (canon thread.index))
  (core func $yield (canon thread.yield))
  (core func $suspend (canon thread.suspend))
  (core func $rl (canon thread.resume-later))
  (core func $str (canon thread.suspend-then-resume))
  (core func $ytr (canon thread.yield-then-resume))
  (core func $stp (canon thread.suspend-then-promote))
  (core func $ytp (canon thread.yield-then-promote))
  (core instance $h
    (export "new" (func $new)) (export "index" (func $index)) (export "yield" (func $yield))
    (export "suspend" (func $suspend)) (export "resume-later" (func $rl))
    (export "s-t-r" (func $str)) (export "y-t-r" (func $ytr))
    (export "s-t-p" (func $stp)) (export "y-t-p" (func $ytp)))
  (core instance $i (instantiate $m (with "h" (instance $h))))
  (func (export "run") (result u32) (canon lift (core func $i "run"))))"#;
    let (core, stats) = fuse(&wat::parse_str(wat).unwrap()).expect("fuses");
    validate(&core).unwrap();
    let mut got: Vec<_> = func_imports(&core);
    got.sort();
    let mut want: Vec<_> = PRODUCER_ABI
        .iter()
        .map(|(n, p, r)| {
            (
                "$root".to_string(),
                n.to_string(),
                p.to_string(),
                r.to_string(),
            )
        })
        .collect();
    want.sort();
    assert_eq!(got, want);
    assert_eq!(stats.thread_table.unwrap().export, "__meld_thread_table");
}

// ---- alias chains (Mythos finding) ------------------------------------------

/// A non-lower built-in reached through bag -> alias -> bag must be named after
/// the BUILT-IN, not after the import the core module happens to use. The
/// module here imports it as `$root::[thread-index]`; it is `thread.yield`.
// rivet: verifies SWV-122
#[test]
fn alias_chained_yield_keeps_its_own_name_and_semantics() {
    let (core, _) = fuse(&fixture("alias_chain/yield_via_alias_chain.wasm")).unwrap();
    validate(&core).unwrap();
    let names: Vec<String> = func_imports(&core).into_iter().map(|i| i.1).collect();
    assert!(names.contains(&"[thread-yield]".to_string()), "{names:?}");
    assert!(
        !names.contains(&"[thread-index]".to_string()),
        "the module's own (wrong) name must not survive: {names:?}"
    );
    // composed on wasmtime 51-dev this component returns 7
    assert_eq!(
        run_with_host(&core, "__meld_thread_table"),
        Ok(7),
        "{names:?}"
    );
}

// rivet: verifies SWV-122
#[test]
fn alias_chained_context_get_is_not_misnamed_as_waitable_set_new() {
    let (core, _) = fuse(&fixture("alias_chain/context_get_via_alias_chain.wasm")).unwrap();
    let names: Vec<String> = func_imports(&core).into_iter().map(|i| i.1).collect();
    assert_eq!(names, vec!["[context-get-0]".to_string()]);
}

// ---- --memory shared -------------------------------------------------------

/// Two components (`c` then `d`, as in the wasmtime threading-builtins test)
/// where `d` always calls `thread.index` and `c` does only when `c_threaded`.
fn two_component_threads(c_threaded: bool) -> Vec<u8> {
    let (c_import, c_with, c_func) = if c_threaded {
        (
            r#"(import "" "thread.index" (func $ti (result i32)))"#,
            r#"(core func $ti (canon thread.index))
    (core instance (export "thread.index" (func $ti)))"#,
            "call $ti",
        )
    } else {
        ("", "", "i32.const 1")
    };
    let c_inst = if c_threaded {
        r#"(core instance $m (instantiate $m (with "" (instance 0))))"#
    } else {
        "(core instance $m (instantiate $m))"
    };
    let wat = format!(
        r#"(component
  (component $c
    (core module $m
      {c_import}
      (func (export "run") (result i32) {c_func}))
    {c_with}
    {c_inst}
    (func (export "run") (result u32) (canon lift (core func $m "run"))))
  (instance $c (instantiate $c))
  (component $d
    (type (instance (export "run" (func (result u32)))))
    (import "c" (instance $c (type 0)))
    (alias export $c "run" (func $crun))
    (core func $run (canon lower (func $crun)))
    (core module $m
      (import "" "thread.index" (func $ti (result i32)))
      (import "" "run" (func $run (result i32)))
      (func (export "run") (result i32) call $ti drop call $run))
    (core func $ti (canon thread.index))
    (core instance $i (export "thread.index" (func $ti)) (export "run" (func $run)))
    (core instance $m (instantiate $m (with "" (instance $i))))
    (func (export "run") (result u32) (canon lift (core func $m "run"))))
  (instance $d (instantiate $d (with "c" (instance $c))))
  (alias export $d "run" (func $drun))
  (export "run" (func $drun)))"#
    );
    wat::parse_str(&wat).unwrap_or_else(|e| panic!("{e}\n{wat}"))
}

/// Two components using cooperative-thread built-ins would be merged into one
/// host import per built-in under one shared address space, losing the instance
/// each call comes from: refused, citing ADR-9.
// rivet: verifies SWV-122
#[test]
fn shared_memory_refuses_two_threaded_components() {
    let bytes = two_component_threads(true);
    let err = fuse_with(&[&bytes], MemoryStrategy::SharedMemory)
        .expect_err("two threaded components under --memory shared must be refused");
    assert!(
        err.contains("ADR-9") && err.contains("cooperative"),
        "{err}"
    );
    // the real wasmtime component, too
    let err = fuse_with(
        &[&fixture("corpus/wasmtime_threading-builtins_m5.wasm")],
        MemoryStrategy::SharedMemory,
    )
    .expect_err("same for the wasmtime fixture");
    assert!(err.contains("ADR-9"), "{err}");
}

/// Controls: the refusal is not a blanket one. --memory multi fuses the same
/// input and names each import's owning component; one threaded component among
/// two fuses under shared; a single threaded component fuses under shared.
#[test]
fn control_multi_attributes_components_and_single_threaded_shared_fuses() {
    let both = two_component_threads(true);
    let (core, stats) = fuse_with(&[&both], MemoryStrategy::MultiMemory).expect("multi fuses");
    validate(&core).unwrap();
    let mut owners: Vec<(String, Option<usize>)> = stats
        .import_map
        .iter()
        .filter(|e| e.name.starts_with("[thread-"))
        .map(|e| (e.name.clone(), e.component))
        .collect();
    owners.sort();
    assert_eq!(owners.len(), 2, "{owners:?}");
    // distinct owners, and the `$N` suffix names the owner
    assert_ne!(owners[0].1, owners[1].1, "{owners:?}");
    for (name, comp) in &owners {
        if let Some(n) = name.split('$').nth(1) {
            assert_eq!(comp, &Some(n.parse::<usize>().unwrap()), "{owners:?}");
        }
    }

    // only `d` threaded: the import belongs to d, not to component 0
    let only_d = two_component_threads(false);
    let (core, stats) = fuse_with(&[&only_d], MemoryStrategy::MultiMemory).unwrap();
    validate(&core).unwrap();
    let threads: Vec<_> = stats
        .import_map
        .iter()
        .filter(|e| e.name.starts_with("[thread-"))
        .collect();
    assert_eq!(threads.len(), 1);
    assert_ne!(
        threads[0].component,
        Some(0),
        "owned by the second component"
    );
    fuse_with(&[&only_d], MemoryStrategy::SharedMemory).expect("one threaded component is fine");

    let (core, _) = fuse_with(
        &[&fixture("t1_new_resume.wasm")],
        MemoryStrategy::SharedMemory,
    )
    .expect("a single threaded component fuses under shared");
    validate(&core).unwrap();
}
