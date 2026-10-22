//! #513: `--emit-import-map` tells a host, per import, which component owns it,
//! which memory its pointers index, which `cabi_realloc` it allocates with and
//! which string encoding it speaks.
//!
//! Every assertion is made against the REAL fused module: the named exports
//! must exist and carry the stated indices, and each import's answer must be the
//! one its own source `canon lower` asked for, not the per-component default.

use meld_core::import_map::{ImportMapEntry, LowerOption};
use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasmparser::{ExternalKind, Parser, Payload, TypeRef};

/// What the fused core module really contains.
#[derive(Default, Debug)]
struct Core {
    func_imports: Vec<(String, String)>,
    memories: usize,
    exports: Vec<(String, ExternalKind, u32)>,
    /// `cabi_realloc` bodies' constant, keyed by fused function index: lets a
    /// test tell WHICH allocator an index is (each returns a distinct constant).
    i32_const_result: std::collections::HashMap<u32, i32>,
}

fn inspect(bytes: &[u8]) -> Core {
    let mut c = Core::default();
    let mut n_func_imports = 0u32;
    let mut defined = 0u32;
    for p in Parser::new(0).parse_all(bytes) {
        match p.unwrap() {
            Payload::ImportSection(r) => {
                for i in r.into_imports() {
                    let i = i.unwrap();
                    match i.ty {
                        TypeRef::Func(_) | TypeRef::FuncExact(_) => {
                            c.func_imports
                                .push((i.module.to_string(), i.name.to_string()));
                            n_func_imports += 1;
                        }
                        TypeRef::Memory(_) => c.memories += 1,
                        _ => {}
                    }
                }
            }
            Payload::MemorySection(r) => c.memories += r.count() as usize,
            Payload::ExportSection(r) => {
                for e in r.into_iter() {
                    let e = e.unwrap();
                    c.exports.push((e.name.to_string(), e.kind, e.index));
                }
            }
            Payload::CodeSectionEntry(body) => {
                let idx = n_func_imports + defined;
                defined += 1;
                let mut ops = body.get_operators_reader().unwrap();
                if let Ok(wasmparser::Operator::I32Const { value }) = ops.read() {
                    c.i32_const_result.insert(idx, value);
                }
            }
            _ => {}
        }
    }
    c
}

fn fuse_core(
    components: &[(&str, Vec<u8>)],
    strategy: MemoryStrategy,
) -> (Vec<u8>, Vec<ImportMapEntry>) {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: strategy,
        attestation: false,
        output_format: OutputFormat::CoreModule,
        ..Default::default()
    });
    for (name, bytes) in components {
        fuser.add_component_named(bytes, Some(name)).unwrap();
    }
    let (out, stats) = fuser.fuse_with_stats().unwrap();
    (out, stats.import_map)
}

/// A component that lowers WASI `write(string) -> u32` with the options
/// `lower_opts`. Three core modules in `order`: M (memory + realloc returning
/// `m_alloc`), B (memory + realloc returning `b_alloc`) and A (the caller). The
/// lower always names M's memory and M's realloc, so the per-component default
/// (first module with a memory / first realloc) is WRONG whenever B comes first.
fn component(order: &str, lower_opts: &str, m_alloc: i32, b_alloc: i32) -> Vec<u8> {
    let m = format!(
        r#"(core module $M
        (memory (export "mem") 1)
        (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const {m_alloc}))"#
    );
    let b = format!(
        r#"(core module $B
        (memory (export "memb") 1)
        (func (export "cabi_reallocb") (param i32 i32 i32 i32) (result i32) i32.const {b_alloc}))"#
    );
    let a = r#"(core module $A
        (import "env" "mem" (memory 1))
        (import "wasi:io/streams@0.2.12" "write" (func $w (param i32 i32) (result i32)))
        (func (export "run") (result i32) i32.const 0 i32.const 0 call $w))"#
        .to_string();
    let mods: Vec<String> = order
        .chars()
        .map(|c| match c {
            'M' => m.clone(),
            'B' => b.clone(),
            _ => a.clone(),
        })
        .collect();
    let wat = format!(
        r#"(component
  (import "wasi:io/streams@0.2.12" (instance $h
    (export "write" (func (param "s" string) (result u32)))))
  {mods}
  (core instance $m (instantiate $M))
  (core instance $b (instantiate $B))
  (alias export $h "write" (func $w))
  (core func $low (canon lower (func $w) {lower_opts}
      (memory (core memory $m "mem")) (realloc (core func $m "cabi_realloc"))))
  (core instance $host (export "write" (func $low)))
  (core instance $envi (export "mem" (memory $m "mem")))
  (core instance $a (instantiate $A (with "env" (instance $envi))
      (with "wasi:io/streams@0.2.12" (instance $host))))
  (func $run (result u32) (canon lift (core func $a "run")))
  (export "run" (func $run)))"#,
        mods = mods.join("\n  ")
    );
    wat::parse_str(wat).unwrap()
}

fn export(core: &Core, name: &str, kind: ExternalKind) -> Option<u32> {
    core.exports
        .iter()
        .find(|(n, k, _)| n == name && *k == kind)
        .map(|(_, _, i)| *i)
}

/// The memory/realloc a `write` entry names, checked against the fused module:
/// the export exists and carries exactly the stated index.
fn resolved(core: &Core, e: &ImportMapEntry) -> (u32, String, u32, String) {
    let LowerOption::Present(m) = &e.memory else {
        panic!("{}: memory is {:?}", e.name, e.memory)
    };
    let LowerOption::Present(r) = &e.realloc else {
        panic!("{}: realloc is {:?}", e.name, e.realloc)
    };
    let mname = m.export.clone().expect("memory export is named");
    let rname = r.export.clone().expect("realloc export is named");
    assert_eq!(
        export(core, &mname, ExternalKind::Memory),
        Some(m.index),
        "{}: memory export `{mname}` does not point at memory {}",
        e.name,
        m.index
    );
    assert_eq!(
        export(core, &rname, ExternalKind::Func),
        Some(r.func),
        "{}: realloc export `{rname}` does not point at function {}",
        e.name,
        r.func
    );
    assert!((m.index as usize) < core.memories);
    (m.index, mname, r.func, rname)
}

/// A WASI import lowered by BOTH components is duplicated (`write`, `write$1`)
/// under `--memory multi`. Each copy must report ITS OWN lower's memory and
/// realloc, not the per-component default and not the other copy's.
///
/// Component 0 lists B before M, so the per-component default ("first module's
/// memory 0") is B's memory, while the lower names M's. Each M allocator
/// returns a distinct constant (100 / 300), so the test can tell from the
/// fused bodies WHICH component's allocator an index is.
#[test]
fn duplicated_wasi_import_reports_its_own_lowers_memory_and_realloc() {
    let c0 = component("BMA", "", 100, 200);
    let c1 = component("MBA", "", 300, 400);
    let (out, map) = fuse_core(&[("c0", c0), ("c1", c1)], MemoryStrategy::MultiMemory);
    let core = inspect(&out);
    wasmparser::validate(&out).expect("fused module is valid");

    // The import list the map describes IS the module's, in order.
    assert_eq!(map.len(), core.func_imports.len());
    for (i, (e, (m, n))) in map.iter().zip(&core.func_imports).enumerate() {
        assert_eq!((&e.module, &e.name, e.index as usize), (m, n, i));
    }
    assert_eq!(map.len(), 2, "{map:#?}");

    let mut seen = Vec::new();
    for e in &map {
        assert_eq!(e.module, "wasi:io/streams@0.2.12");
        // `write$N` is component N's; the unsuffixed one is the other's.
        let comp = e.component.expect("component named");
        if let Some(n) = e.name.strip_prefix("write$") {
            assert_eq!(comp, n.parse::<usize>().unwrap(), "{}", e.name);
        } else {
            assert_eq!(e.name, "write");
        }
        let (mem, mem_name, func, _real_name) = resolved(&core, e);

        // Which lower did this come from? Its allocator returns that
        // component's M constant.
        let want_alloc = if comp == 0 { 100 } else { 300 };
        assert_eq!(
            core.i32_const_result.get(&func),
            Some(&want_alloc),
            "{}: realloc func {func} is not component {comp}'s M allocator",
            e.name
        );
        // The memory is M's (exported `mem*`), never B's (`memb*`) ...
        assert!(
            mem_name.starts_with("mem") && !mem_name.starts_with("memb"),
            "{}: memory export {mem_name}",
            e.name
        );
        // ... B's memories are different indices, which is what the
        // per-component default would have returned for component 0.
        let b = core
            .exports
            .iter()
            .filter(|(n, k, _)| n.starts_with("memb") && *k == ExternalKind::Memory)
            .map(|(_, _, i)| *i)
            .collect::<Vec<_>>();
        assert_eq!(b.len(), 2);
        assert!(!b.contains(&mem), "{}: names a B memory", e.name);
        assert_eq!(e.encoding, LowerOption::Present("utf8"));
        seen.push((comp, mem));
    }
    seen.sort();
    assert_eq!(seen.iter().map(|s| s.0).collect::<Vec<_>>(), vec![0, 1]);
    assert_ne!(seen[0].1, seen[1].1, "two components, one memory: {seen:?}");
}

/// Resolution does not depend on which module the merger numbered first.
#[test]
fn memory_follows_the_lower_in_every_module_order() {
    for order in ["MBA", "MAB", "BMA", "BAM", "AMB", "ABM"] {
        let (out, map) = fuse_core(
            &[("c", component(order, "", 100, 200))],
            MemoryStrategy::MultiMemory,
        );
        let core = inspect(&out);
        assert_eq!(map.len(), 1);
        let (_, mname, func, _) = resolved(&core, &map[0]);
        assert!(!mname.starts_with("memb"), "order {order}: {mname}");
        assert_eq!(
            core.i32_const_result.get(&func),
            Some(&100),
            "order {order}"
        );
    }
}

#[test]
fn string_encoding_is_reported_per_lower() {
    for (opts, want) in [
        ("string-encoding=utf16", "utf16"),
        ("string-encoding=latin1+utf16", "latin1+utf16"),
        ("string-encoding=utf8", "utf8"),
        ("", "utf8"),
    ] {
        let (_, map) = fuse_core(
            &[("c", component("MBA", opts, 100, 200))],
            MemoryStrategy::MultiMemory,
        );
        assert_eq!(map[0].encoding, LowerOption::Present(want), "{opts:?}");
    }
}

/// A lower with no memory / realloc option reports `null` (Absent): it cannot
/// touch a memory. Never a per-component default.
#[test]
fn absent_options_are_null_not_a_default() {
    let wat = |opts: &str| {
        wat::parse_str(format!(
            r#"(component
  (import "wasi:cli/exit@0.2.12" (instance $h (export "exit" (func (param "c" u32)))))
  (core module $M (memory (export "mem") 1)
     (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 0))
  (core module $A
     (import "host" "exit" (func $e (param i32)))
     (func (export "run") i32.const 0 call $e))
  (core instance $m (instantiate $M))
  (alias export $h "exit" (func $x))
  (core func $low (canon lower (func $x) {opts}))
  (core instance $host (export "exit" (func $low)))
  (core instance $a (instantiate $A (with "host" (instance $host))))
  (func $run (canon lift (core func $a "run")))
  (export "run" (func $run)))"#
        ))
        .unwrap()
    };
    // No options at all: both null, although the component has a memory and a
    // `cabi_realloc` a per-component default would have supplied.
    let (_, map) = fuse_core(&[("c", wat(""))], MemoryStrategy::MultiMemory);
    assert_eq!(map.len(), 1);
    assert_eq!(map[0].memory, LowerOption::Absent);
    assert_eq!(map[0].realloc, LowerOption::Absent);
    assert_eq!(map[0].encoding, LowerOption::Present("utf8"));

    // Memory but no realloc: only the realloc is null.
    let (out, map) = fuse_core(
        &[("c", wat(r#"(memory (core memory $m "mem"))"#))],
        MemoryStrategy::MultiMemory,
    );
    let core = inspect(&out);
    let LowerOption::Present(m) = &map[0].memory else {
        panic!("{:?}", map[0].memory)
    };
    assert_eq!(
        export(&core, m.export.as_ref().unwrap(), ExternalKind::Memory),
        Some(m.index)
    );
    assert_eq!(map[0].realloc, LowerOption::Absent);
}

/// Resource intrinsics are canonical builtins: no memory/realloc, but the
/// component, the resource type and the `[dtor]` export they belong to.
#[test]
fn resource_intrinsics_name_component_resource_and_dtor() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../tests/wit_bindgen/fixtures/resources.wasm"
    );
    let bytes = std::fs::read(path).unwrap();
    let (out, map) = fuse_core(&[("resources.wasm", bytes)], MemoryStrategy::MultiMemory);
    let core = inspect(&out);

    let mut with_dtor = 0;
    for e in &map {
        let Some(r) = &e.resource else {
            assert!(
                !e.name.starts_with("[resource-"),
                "{}: an intrinsic with no resource info",
                e.name
            );
            continue;
        };
        assert!(e.component.is_some(), "{}: no component", e.name);
        assert_eq!(e.memory, LowerOption::Absent, "{}", e.name);
        assert_eq!(e.realloc, LowerOption::Absent, "{}", e.name);
        assert!(e.name.contains(&format!("[resource-{}]", r.operation)));
        assert!(e.name.contains(&r.resource), "{} vs {}", e.name, r.resource);
        if let Some(d) = &r.dtor_export {
            // The named dtor really is an exported function, of this resource.
            assert!(
                export(&core, d, ExternalKind::Func).is_some(),
                "{}: dtor export `{d}` does not exist",
                e.name
            );
            assert!(d.contains(&format!("#[dtor]{}", r.resource)), "{d}");
            with_dtor += 1;
        }
    }
    let new_x = map
        .iter()
        .find(|e| e.name.starts_with("[resource-new]x"))
        .unwrap();
    let r = new_x.resource.as_ref().unwrap();
    assert_eq!(
        (
            r.operation,
            r.resource.as_str(),
            r.interface.as_str(),
            r.definer
        ),
        ("new", "x", "exports", true)
    );
    assert_eq!(r.dtor_export.as_deref(), Some("exports#[dtor]x"));
    assert!(with_dtor >= 4, "{with_dtor}");
    // A host-owned resource (WASI) has no dtor in the fused module.
    let wasi = map
        .iter()
        .find(|e| e.name == "[resource-drop]output-stream")
        .unwrap();
    assert!(!wasi.resource.as_ref().unwrap().definer);
    assert_eq!(wasi.resource.as_ref().unwrap().dtor_export, None);
}

/// Under `--memory shared` there is one memory; a traced lower still reports
/// its realloc and encoding, and the memory is index 0 of that single memory.
#[test]
fn shared_memory_reports_the_single_memory() {
    let (out, map) = fuse_core(
        &[("c", component("BMA", "string-encoding=utf16", 100, 200))],
        MemoryStrategy::SharedMemory,
    );
    let core = inspect(&out);
    assert_eq!(core.memories, 1);
    assert_eq!(map.len(), 1);
    assert_eq!(map[0].encoding, LowerOption::Present("utf16"));
    let LowerOption::Present(m) = &map[0].memory else {
        panic!("{:?}", map[0].memory)
    };
    assert_eq!(m.index, 0);
    let LowerOption::Present(r) = &map[0].realloc else {
        panic!("{:?}", map[0].realloc)
    };
    assert!((r.func as usize) >= core.func_imports.len());
}
