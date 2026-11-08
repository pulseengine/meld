//! #562 -- the upstream Component Model reference tests as a fusion oracle.
//!
//! `tests/spec/component-model/` vendors `WebAssembly/component-model`'s
//! `test/` directory at the commit in `COMMIT`. `MODULE.bazel` must pin
//! the same commit. Every file is checked against `SHA256SUMS`.
//!
//! For every component a WAST defines, this test records what meld does
//! with it alone, and compares the result with a checked-in ratchet
//! baseline (`component-model-fuse-baseline.tsv`):
//!
//! * `fused`: meld fuses it and the output validates.
//! * `refused`: meld refuses it, loudly. The detail is the issues the error
//!   cites, so a change in the reason for a refusal is also a diff.
//! * `meld-invalid`: meld built output that fails validation and refused
//!   to return it (#545, `Error::InvalidOutput`). Loud, so never shipped,
//!   but still a meld bug, kept apart from `refused` so the count of
//!   adapter defects stays visible. Fixing one moves its row to `fused`.
//! * `fused-invalid`, `panic`: bugs. They are listed with their reason so
//!   the baseline makes them visible; they are never "fine". Since #545
//!   `fused-invalid` means the library's own validation let invalid output
//!   through (this test re-validates with every feature enabled), so it
//!   should stay at zero.
//! * For components inside `assert_invalid` / `assert_malformed`:
//!   `invalid-refused` (meld rejects it, as it must), `invalid-fused` (a
//!   bug: meld accepted an invalid component), or `invalid-unencodable`
//!   (the text never becomes a binary, so meld never sees it).
//!
//! Any difference from the baseline fails the test, in both directions: a
//! component that newly fuses must be re-baselined as deliberately as one
//! that newly breaks. `MELD_BLESS=1` rewrites the baseline.
//!
//! Running the WAST assertions is not done here. meld's output is a core
//! module, and the assertions name component-level exports. kiln's runner
//! (kiln SR-93) executes them on the fused output. With
//! `MELD_CM_WAST_OUT=<dir>` this test writes each fused module plus a
//! `manifest.json` that maps every WAST command to the component it
//! targets.

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use sha2::{Digest, Sha256};
use wast::parser::{self, ParseBuffer};
use wast::{QuoteWat, Wast, WastDirective, WastExecute, Wat};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
}

fn suite_dir() -> PathBuf {
    root().join("tests/spec/component-model")
}

fn baseline_path() -> PathBuf {
    root().join("tests/spec/component-model-fuse-baseline.tsv")
}

/// The vendored files and their digests, from `SHA256SUMS`.
fn vendored_files() -> Vec<(String, String)> {
    let sums = std::fs::read_to_string(suite_dir().join("SHA256SUMS")).expect("SHA256SUMS");
    sums.lines()
        .map(|l| {
            let (hash, path) = l.split_once("  ").expect("`<sha256>  <path>` line");
            (hash.to_string(), path.to_string())
        })
        .collect()
}

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Module,
    Definition,
    AssertInvalid,
    AssertMalformed,
    AssertUnlinkable,
    AssertTrapInstantiate,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Kind::Module => "component",
            Kind::Definition => "component-definition",
            Kind::AssertInvalid => "assert_invalid",
            Kind::AssertMalformed => "assert_malformed",
            Kind::AssertUnlinkable => "assert_unlinkable",
            Kind::AssertTrapInstantiate => "assert_trap-instantiate",
        }
    }
    fn must_be_rejected(self) -> bool {
        matches!(self, Kind::AssertInvalid | Kind::AssertMalformed)
    }
}

struct Entry {
    directive: usize,
    line: usize,
    kind: Kind,
    id: Option<String>,
    outcome: &'static str,
    detail: String,
    fused: Option<Vec<u8>>,
    input: Option<Vec<u8>>,
}

struct Command {
    directive: usize,
    line: usize,
    kind: &'static str,
    target: Option<usize>,
}

struct FileResult {
    entries: Vec<Entry>,
    commands: Vec<Command>,
    registers: Vec<(String, Option<usize>)>,
    parse_error: Option<String>,
}

/// The issues an error cites, e.g. `#548,#560`, or a short normalised
/// message when it cites none.
fn reason(err: &str) -> String {
    let mut issues: Vec<String> = Vec::new();
    let bytes = err.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'#' {
            let start = i + 1;
            let mut j = start;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            if j > start {
                let n = format!("#{}", &err[start..j]);
                if !issues.contains(&n) {
                    issues.push(n);
                }
            }
            i = j.max(i + 1);
        } else {
            i += 1;
        }
    }
    if !issues.is_empty() {
        return issues.join(",");
    }
    // No citation: keep the message, minus digits (offsets, indices), so
    // the baseline is stable across unrelated renumbering.
    let mut first = err.lines().next().unwrap_or("");
    if let Some(at) = first.find(" (at offset ") {
        first = &first[..at];
    }
    let mut s: String = first
        .chars()
        .map(|c| if c.is_ascii_digit() { 'N' } else { c })
        .map(|c| if c == '\t' { ' ' } else { c })
        .collect();
    s.truncate(120);
    format!("msg:{s}")
}

fn fuse_alone(bytes: &[u8]) -> (&'static str, String, Option<Vec<u8>>) {
    let bytes = bytes.to_vec();
    let run = std::panic::catch_unwind(move || {
        let mut fuser = Fuser::new(FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: false,
            ..Default::default()
        });
        fuser
            .add_component(&bytes)
            .map_err(|e| (false, e.to_string()))?;
        fuser.fuse().map_err(|e| match e {
            meld_core::Error::InvalidOutput(msg) => (true, msg),
            e => (false, e.to_string()),
        })
    });
    match run {
        Err(p) => {
            let msg = p
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default();
            ("panic", reason(&msg), None)
        }
        Ok(Err((true, e))) => ("meld-invalid", reason(&e), None),
        Ok(Err((false, e))) => ("refused", reason(&e), None),
        Ok(Ok(out)) => {
            let mut v = wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all());
            match v.validate_all(&out) {
                Ok(_) => ("fused", String::new(), Some(out)),
                Err(e) => ("fused-invalid", reason(&e.to_string()), Some(out)),
            }
        }
    }
}

fn is_component(q: &QuoteWat<'_>) -> bool {
    matches!(
        q,
        QuoteWat::Wat(Wat::Component(_)) | QuoteWat::QuoteComponent(..)
    )
}

fn quote_id(q: &QuoteWat<'_>) -> Option<String> {
    match q {
        QuoteWat::Wat(Wat::Component(c)) => c.id.map(|i| i.name().to_string()),
        _ => None,
    }
}

fn run_file(text: &str) -> FileResult {
    let mut res = FileResult {
        entries: Vec::new(),
        commands: Vec::new(),
        registers: Vec::new(),
        parse_error: None,
    };
    let buf = match ParseBuffer::new(text) {
        Ok(b) => b,
        Err(e) => {
            res.parse_error = Some(reason(&e.message()));
            return res;
        }
    };
    let wast: Wast<'_> = match parser::parse(&buf) {
        Ok(w) => w,
        Err(e) => {
            res.parse_error = Some(reason(&e.message()));
            return res;
        }
    };

    let line_of = |span: wast::token::Span| span.linecol_in(text).0 + 1;
    // Index into `res.entries` of the component a bare command targets,
    // and of each named component or instance.
    let mut current: Option<usize> = None;
    let mut named: HashMap<String, usize> = HashMap::new();

    for (di, directive) in wast.directives.into_iter().enumerate() {
        let line = line_of(directive.span());
        let push = |res: &mut FileResult, mut q: QuoteWat<'_>, kind: Kind| -> usize {
            let id = quote_id(&q);
            let mut input = None;
            let (outcome, detail, fused) = match q.encode() {
                Err(e) => {
                    if kind.must_be_rejected() {
                        ("invalid-unencodable", String::new(), None)
                    } else {
                        ("unencodable", reason(&e.message()), None)
                    }
                }
                Ok(bytes) => {
                    let (o, d, f) = fuse_alone(&bytes);
                    input = Some(bytes);
                    if kind.must_be_rejected() {
                        match o {
                            "refused" => ("invalid-refused", String::new(), None),
                            "panic" => ("panic", d, None),
                            _ => ("invalid-fused", d, f),
                        }
                    } else {
                        (o, d, f)
                    }
                }
            };
            res.entries.push(Entry {
                directive: di,
                line,
                kind,
                id,
                outcome,
                detail,
                fused,
                input,
            });
            res.entries.len() - 1
        };
        let target = |m: Option<wast::token::Id<'_>>,
                      current: Option<usize>,
                      named: &HashMap<String, usize>| {
            match m {
                Some(id) => named.get(id.name()).copied(),
                None => current,
            }
        };
        match directive {
            WastDirective::Module(q) if is_component(&q) => {
                let idx = push(&mut res, q, Kind::Module);
                if let Some(id) = res.entries[idx].id.clone() {
                    named.insert(id, idx);
                }
                current = Some(idx);
            }
            WastDirective::ModuleDefinition(q) if is_component(&q) => {
                let idx = push(&mut res, q, Kind::Definition);
                if let Some(id) = res.entries[idx].id.clone() {
                    named.insert(id, idx);
                }
            }
            WastDirective::ModuleInstance {
                instance, module, ..
            } => {
                let t = target(module, current, &named);
                if let (Some(i), Some(t)) = (instance, t) {
                    named.insert(i.name().to_string(), t);
                }
                current = t;
                res.commands.push(Command {
                    directive: di,
                    line,
                    kind: "instance",
                    target: t,
                });
            }
            WastDirective::AssertInvalid { module, .. } if is_component(&module) => {
                push(&mut res, module, Kind::AssertInvalid);
            }
            WastDirective::AssertMalformed { module, .. } if is_component(&module) => {
                push(&mut res, module, Kind::AssertMalformed);
            }
            WastDirective::AssertUnlinkable { module, .. }
                if matches!(module, Wat::Component(_)) =>
            {
                push(&mut res, QuoteWat::Wat(module), Kind::AssertUnlinkable);
            }
            WastDirective::Register { name, module, .. } => {
                let t = target(module, current, &named);
                res.registers.push((name.to_string(), t));
                res.commands.push(Command {
                    directive: di,
                    line,
                    kind: "register",
                    target: t,
                });
            }
            WastDirective::Invoke(inv) => {
                let t = target(inv.module, current, &named);
                res.commands.push(Command {
                    directive: di,
                    line,
                    kind: "invoke",
                    target: t,
                });
            }
            WastDirective::AssertReturn { exec, .. }
            | WastDirective::AssertTrap { exec, .. }
            | WastDirective::AssertException { exec, .. }
            | WastDirective::AssertSuspension { exec, .. } => {
                let kind = "assert";
                match exec {
                    WastExecute::Invoke(inv) => {
                        let t = target(inv.module, current, &named);
                        res.commands.push(Command {
                            directive: di,
                            line,
                            kind,
                            target: t,
                        });
                    }
                    WastExecute::Wat(w) if matches!(w, Wat::Component(_)) => {
                        let idx = push(&mut res, QuoteWat::Wat(w), Kind::AssertTrapInstantiate);
                        res.commands.push(Command {
                            directive: di,
                            line,
                            kind: "assert-instantiate",
                            target: Some(idx),
                        });
                    }
                    _ => {}
                }
            }
            WastDirective::AssertExhaustion { call, .. } => {
                let t = target(call.module, current, &named);
                res.commands.push(Command {
                    directive: di,
                    line,
                    kind: "assert",
                    target: t,
                });
            }
            // Core modules, threads and custom-section assertions are not
            // component inputs for meld.
            _ => {}
        }
    }
    res
}

fn bazel_pin() -> String {
    let module = std::fs::read_to_string(root().join("MODULE.bazel")).expect("MODULE.bazel");
    let start = module
        .find("name = \"component_model_spec\"")
        .expect("component_model_spec repo in MODULE.bazel");
    let rest = &module[start..];
    let c = rest
        .find("commit = \"")
        .expect("commit for component_model_spec")
        + 10;
    rest[c..c + rest[c..].find('"').unwrap()].to_string()
}

#[test]
fn bazel_pin_matches_the_vendored_suite() {
    let vendored = std::fs::read_to_string(suite_dir().join("COMMIT")).expect("COMMIT");
    assert_eq!(
        bazel_pin(),
        vendored.trim(),
        "MODULE.bazel's component_model_spec commit and tests/spec/component-model/COMMIT \
         must name the same upstream commit"
    );
}

#[test]
fn vendored_suite_matches_its_checksums() {
    let files = vendored_files();
    let wasts = files.iter().filter(|(_, p)| p.ends_with(".wast")).count();
    assert_eq!(wasts, 78, "the vendored suite at c818a1925e has 78 WASTs");
    for (hash, path) in &files {
        let bytes = std::fs::read(suite_dir().join(path)).unwrap_or_else(|e| panic!("{path}: {e}"));
        let got = format!("{:x}", Sha256::digest(&bytes));
        assert_eq!(&got, hash, "{path} differs from SHA256SUMS");
    }
}

// rivet: verifies SWV-127
#[test]
fn every_reference_component_matches_the_fuse_baseline() {
    let commit = std::fs::read_to_string(suite_dir().join("COMMIT"))
        .expect("COMMIT")
        .trim()
        .to_string();
    let out_dir = std::env::var_os("MELD_CM_WAST_OUT").map(PathBuf::from);
    let mut rows: Vec<String> = Vec::new();
    let mut seen_wasts = 0usize;
    let mut manifest = Vec::new();

    for (_, path) in vendored_files() {
        if !path.ends_with(".wast") {
            continue;
        }
        seen_wasts += 1;
        let text = std::fs::read_to_string(suite_dir().join(&path)).expect("wast text");
        let res = run_file(&text);
        if let Some(e) = &res.parse_error {
            rows.push(format!("{path}\t-\t-\tfile\tparse-error\t{e}"));
            continue;
        }
        if res.entries.is_empty() {
            rows.push(format!("{path}\t-\t-\tfile\tno-components\t-"));
        }
        let mut comps = Vec::new();
        for (ci, e) in res.entries.iter().enumerate() {
            rows.push(format!(
                "{path}\t{}\t{}\t{}\t{}\t{}",
                e.directive,
                e.line,
                e.kind.name(),
                e.outcome,
                if e.detail.is_empty() { "-" } else { &e.detail }
            ));
            let write = |suffix: &str, bytes: &Option<Vec<u8>>| -> serde_json::Value {
                match (&out_dir, bytes) {
                    (Some(dir), Some(bytes)) => {
                        let rel = format!("{}.{ci}.{suffix}", path.trim_end_matches(".wast"));
                        let p = dir.join(&rel);
                        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
                        std::fs::write(&p, bytes).unwrap();
                        rel.into()
                    }
                    _ => serde_json::Value::Null,
                }
            };
            let fused_path = write("fused.wasm", &e.fused);
            let input_path = write("input.wasm", &e.input);
            comps.push(serde_json::json!({
                "component_index": ci,
                "directive_index": e.directive,
                "line": e.line,
                "id": e.id,
                "kind": e.kind.name(),
                "outcome": e.outcome,
                "detail": e.detail,
                "fused_path": fused_path,
                "input_path": input_path,
            }));
        }
        let commands: Vec<_> = res
            .commands
            .iter()
            .map(|c| {
                serde_json::json!({
                    "index": c.directive, "line": c.line, "kind": c.kind,
                    "target_component": c.target,
                })
            })
            .collect();
        let registers: Vec<_> = res
            .registers
            .iter()
            .map(|(n, t)| serde_json::json!({"name": n, "component_index": t}))
            .collect();
        manifest.push(serde_json::json!({
            "wast": format!("test/{}", path.trim_start_matches("test/")),
            "components": comps, "commands": commands, "registers": registers,
        }));
    }
    assert_eq!(seen_wasts, 78, "every vendored WAST was visited");

    if let Some(dir) = &out_dir {
        let doc = serde_json::json!({
            "component_model_commit": commit,
            "meld_version": env!("CARGO_PKG_VERSION"),
            "files": manifest,
        });
        std::fs::create_dir_all(dir).unwrap();
        std::fs::write(
            dir.join("manifest.json"),
            serde_json::to_string_pretty(&doc).unwrap(),
        )
        .unwrap();
    }

    rows.sort();
    let actual = rows.join("\n") + "\n";
    let header = "# #562 ratchet: meld's outcome for every component in the vendored\n\
                  # component-model test suite. Columns: wast, directive index, line,\n\
                  # kind, outcome, detail. Regenerate with MELD_BLESS=1 and review the diff.\n";
    if std::env::var_os("MELD_BLESS").is_some() {
        std::fs::write(baseline_path(), format!("{header}{actual}")).unwrap();
        return;
    }
    let baseline = std::fs::read_to_string(baseline_path()).unwrap_or_default();
    let expected: Vec<&str> = baseline.lines().filter(|l| !l.starts_with('#')).collect();
    let got: Vec<&str> = actual.lines().collect();
    if expected != got {
        let exp: BTreeMap<&str, ()> = expected.iter().map(|l| (*l, ())).collect();
        let act: BTreeMap<&str, ()> = got.iter().map(|l| (*l, ())).collect();
        let gone: Vec<_> = exp.keys().filter(|l| !act.contains_key(*l)).collect();
        let new: Vec<_> = act.keys().filter(|l| !exp.contains_key(*l)).collect();
        panic!(
            "component-model fuse outcomes differ from the baseline \
             (MELD_BLESS=1 regenerates it).\n--- baseline only:\n{}\n+++ now:\n{}",
            gone.iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
            new.iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
        );
    }
}
