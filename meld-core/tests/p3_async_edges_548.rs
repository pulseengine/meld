//! ADR-10 step 3 (#548): async-lower calls between fused components become
//! `pulseengine:async-edges` entries with a start and a return adapter.
//!
//! The runtime half (kiln-async driving the subtask) is not in this repo, so
//! the execution oracle here runs the adapters themselves under wasmtime: the
//! start adapter must hand the callee's packed i32 back unchanged, the callee's
//! `[task-return]` must receive the computed result, and the return adapter
//! must store it into the caller's memory at `retptr`.

use std::sync::{Arc, Mutex};

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

/// Callee: `add: async func(a: u32, b: u32) -> u32`, callback ABI. The lift
/// calls `task.return(a + b)` and returns 0 (EXIT).
const CALLEE: &str = r#"
(component
  (core module $m
    (import "" "task-return" (func $tr (param i32)))
    (func (export "[async-lift]local:t/i#add") (param i32 i32) (result i32)
      (call $tr (i32.add (local.get 0) (local.get 1)))
      i32.const 0)
    (func (export "[callback][async-lift]local:t/i#add")
      (param i32 i32 i32) (result i32) i32.const 0))
  (core func $tr (canon task.return (result u32)))
  (core instance $trs (export "task-return" (func $tr)))
  (core instance $ci (instantiate $m (with "" (instance $trs))))
  (type $ft (func async (param "a" u32) (param "b" u32) (result u32)))
  (func $f (type $ft)
    (canon lift (core func $ci "[async-lift]local:t/i#add") async
      (callback (core func $ci "[callback][async-lift]local:t/i#add"))))
  (instance $inst (export "add" (func $f)))
  (export "local:t/i" (instance $inst)))
"#;

/// The same callee lifted without `callback` (stackful async).
const STACKFUL_CALLEE: &str = r#"
(component
  (core module $m
    (func (export "[async-lift-stackful]local:t/i#add") (param i32 i32)))
  (core instance $ci (instantiate $m))
  (type $ft (func async (param "a" u32) (param "b" u32) (result u32)))
  (func $f (type $ft)
    (canon lift (core func $ci "[async-lift-stackful]local:t/i#add") async))
  (instance $inst (export "add" (func $f)))
  (export "local:t/i" (instance $inst)))
"#;

/// Caller: lowers `add` with the async option. Core import
/// `[async-lower]add: (a, b, retptr) -> status`.
const CALLER: &str = r#"
(component
  (import "local:t/i" (instance $i
    (export "add" (func async (param "a" u32) (param "b" u32) (result u32)))))
  (alias export $i "add" (func $f))
  (core module $mm (memory (export "mem") 1))
  (core instance $mi (instantiate $mm))
  (alias core export $mi "mem" (core memory $mem))
  (core func $lf (canon lower (func $f) async (memory $mem)))
  (core module $m
    (import "local:t/i" "[async-lower]add" (func (param i32 i32 i32) (result i32)))
    (import "env" "mem" (memory 1))
    (func (export "run")))
  (core instance $imp (export "[async-lower]add" (func $lf)))
  (core instance $env (export "mem" (memory $mem)))
  (core instance $ci (instantiate $m
    (with "local:t/i" (instance $imp))
    (with "env" (instance $env)))))
"#;

fn fuse_with(config: FuserConfig, components: &[&str]) -> Result<Vec<u8>, String> {
    let mut fuser = Fuser::new(FuserConfig {
        attestation: false,
        ..config
    });
    for wat in components {
        let bytes = wat::parse_str(wat).expect("fixture parses");
        fuser.add_component(&bytes).map_err(|e| e.to_string())?;
    }
    fuser.fuse().map_err(|e| e.to_string())
}

fn fuse(components: &[&str]) -> Result<Vec<u8>, String> {
    fuse_with(
        FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            ..Default::default()
        },
        components,
    )
}

fn section(core: &[u8]) -> Option<Vec<u8>> {
    wasmparser::Parser::new(0)
        .parse_all(core)
        .find_map(|p| match p {
            Ok(wasmparser::Payload::CustomSection(c)) if c.name() == "pulseengine:async-edges" => {
                Some(c.data().to_vec())
            }
            _ => None,
        })
}

/// A minimal reader for the v1 layout (meld#548, seam meld-kiln/async-edges),
/// written from the spec rather than from meld's encoder.
struct Reader<'a> {
    b: &'a [u8],
    at: usize,
}

impl Reader<'_> {
    fn u8(&mut self) -> u8 {
        let v = self.b[self.at];
        self.at += 1;
        v
    }
    fn uleb(&mut self) -> u32 {
        let (mut v, mut shift) = (0u32, 0);
        loop {
            let byte = self.u8();
            v |= u32::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return v;
            }
            shift += 7;
        }
    }
    fn name(&mut self) -> String {
        let len = self.uleb() as usize;
        let s = std::str::from_utf8(&self.b[self.at..self.at + len])
            .expect("utf-8")
            .to_string();
        self.at += len;
        s
    }
}

#[derive(Debug, PartialEq)]
struct Edge {
    caller: u32,
    import: (String, String),
    callee: u32,
    start: String,
    callback: String,
    ret: String,
    param_kind: u8,
    param_count: u32,
    retptr: u8,
    results: Vec<u8>,
}

fn decode(b: &[u8]) -> ([u32; 5], Vec<Edge>, u32) {
    let mut r = Reader { b, at: 0 };
    let header = [r.uleb(), r.uleb(), r.uleb(), r.uleb(), r.uleb()];
    let n = r.uleb();
    let edges = (0..n)
        .map(|_| Edge {
            caller: r.uleb(),
            import: (r.name(), r.name()),
            callee: r.uleb(),
            start: r.name(),
            callback: r.name(),
            ret: r.name(),
            param_kind: r.u8(),
            param_count: r.uleb(),
            retptr: r.u8(),
            results: {
                let k = r.uleb();
                (0..k).map(|_| r.u8()).collect()
            },
        })
        .collect();
    let types = r.uleb();
    assert_eq!(r.at, b.len(), "no trailing bytes");
    (header, edges, types)
}

// rivet: verifies SWV-149
#[test]
fn edge_section_is_versioned_and_names_exports() {
    let core = fuse(&[CALLER, CALLEE]).expect("fuses");
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&core)
        .expect("fused module validates");
    let (header, edges, types) = decode(&section(&core).expect("section present"));
    assert_eq!(
        header,
        [1, 1, 8, 4, 16],
        "version, max_edges, default bounds"
    );
    assert_eq!(types, 0);
    assert_eq!(
        edges,
        vec![Edge {
            caller: 0,
            import: ("local:t/i".into(), "[async-lower]add".into()),
            callee: 1,
            start: "pulseengine:async-edge/0/start".into(),
            callback: "pulseengine:async-edge/0/callback".into(),
            ret: "pulseengine:async-edge/0/return".into(),
            param_kind: 0,
            param_count: 2,
            retptr: 1,
            results: vec![0x7f],
        }]
    );

    // Every name the section gives is exported with the core type kiln checks.
    let module = wasmparser::Parser::new(0);
    let mut exports = Vec::new();
    let mut imports = Vec::new();
    for p in module.parse_all(&core) {
        match p.expect("parses") {
            wasmparser::Payload::ExportSection(r) => {
                for e in r {
                    let e = e.unwrap();
                    exports.push(e.name.to_string());
                }
            }
            wasmparser::Payload::ImportSection(r) => {
                for i in r.into_imports() {
                    let i = i.unwrap();
                    imports.push((i.module.to_string(), i.name.to_string()));
                }
            }
            _ => {}
        }
    }
    for name in [&edges[0].start, &edges[0].callback, &edges[0].ret] {
        assert!(exports.contains(name), "{name} exported: {exports:?}");
    }
    assert!(
        imports.contains(&edges[0].import),
        "the section's import is an import of the module, exactly: {imports:?}"
    );
}

// rivet: verifies SWV-149
#[test]
fn start_adapter_returns_the_packed_code_unchanged() {
    use wasmtime::{Config, Engine, Linker, Module, Store, Val};

    let core = fuse(&[CALLER, CALLEE]).expect("fuses");
    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let module = Module::new(&engine, &core).unwrap();

    // Every import traps, except the callee's `[task-return]`, which records
    // its argument: that is what kiln routes to the return adapter.
    let returned: Arc<Mutex<Vec<i32>>> = Arc::default();
    let mut linker: Linker<()> = Linker::new(&engine);
    for imp in module.imports() {
        let wasmtime::ExternType::Func(ty) = imp.ty() else {
            panic!(
                "unexpected non-function import {}::{}",
                imp.module(),
                imp.name()
            );
        };
        let name = format!("{}::{}", imp.module(), imp.name());
        let record = name.contains("task-return");
        let returned = returned.clone();
        linker
            .func_new(imp.module(), imp.name(), ty, move |_, args, _| {
                if record {
                    returned.lock().unwrap().push(args[0].unwrap_i32());
                    Ok(())
                } else {
                    Err(wasmtime::Error::msg(format!("unexpected call to {name}")))
                }
            })
            .unwrap();
    }
    let mut store = Store::new(&engine, ());
    let instance = linker.instantiate(&mut store, &module).unwrap();

    let start = instance
        .get_func(&mut store, "pulseengine:async-edge/0/start")
        .unwrap();
    let mut out = [Val::I32(-1)];
    start
        .call(&mut store, &[Val::I32(40), Val::I32(2)], &mut out)
        .unwrap();
    assert_eq!(out[0].unwrap_i32(), 0, "the callee's EXIT code, unchanged");
    assert_eq!(*returned.lock().unwrap(), vec![42], "task.return got a + b");

    // The return adapter stores the result into the caller's memory.
    let ret = instance
        .get_func(&mut store, "pulseengine:async-edge/0/return")
        .unwrap();
    ret.call(&mut store, &[Val::I32(64), Val::I32(42)], &mut [])
        .unwrap();
    let memories: Vec<_> = instance
        .exports(&mut store)
        .filter_map(|e| e.into_memory())
        .collect();
    let written: Vec<_> = memories
        .iter()
        .filter(|m| {
            let mut b = [0u8; 4];
            m.read(&store, 64, &mut b).is_ok() && i32::from_le_bytes(b) == 42
        })
        .collect();
    assert_eq!(
        written.len(),
        1,
        "exactly one exported memory holds the result at retptr ({} exported)",
        memories.len()
    );
}

// rivet: verifies SWV-149
#[test]
fn non_callback_async_lift_edge_is_refused() {
    // meld's parser does not enable the stackful-async feature, so the callee
    // is refused when it is added, before resolution reaches the edge check
    // (`extract_async_edges` refuses a callback-less lift as well, should the
    // parser ever accept one).
    let err = fuse(&[CALLER, STACKFUL_CALLEE]).expect_err("stackful callee refused");
    assert!(err.contains("stackful"), "{err}");
}

// rivet: verifies SWV-149
#[test]
fn cross_domain_async_edge_is_refused() {
    let err = fuse_with(
        FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            domains: vec![vec![0], vec![1]],
            ..Default::default()
        },
        &[CALLER, CALLEE],
    )
    .expect_err("an edge across domains is refused");
    assert!(err.contains("--domain"), "{err}");
}

// rivet: verifies SWV-149
#[test]
fn zero_bound_is_refused() {
    let err = fuse_with(
        FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            async_bounds: meld_core::async_edges::AsyncBounds {
                subtasks: 0,
                ..Default::default()
            },
            ..Default::default()
        },
        &[CALLER, CALLEE],
    )
    .expect_err("a zero bound is refused");
    assert!(err.contains("--async-subtasks"), "{err}");
}

// rivet: verifies SWV-149
#[test]
fn edge_output_is_deterministic() {
    assert_eq!(fuse(&[CALLER, CALLEE]), fuse(&[CALLER, CALLEE]));
}
