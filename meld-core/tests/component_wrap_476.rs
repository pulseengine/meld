//! #476: `--component` on a component that `use`s types from an imported
//! interface. wit-bindgen emits each such type as an `alias export <instance>`
//! of the imported interface; the wrapper failed with "cannot find source type
//! definition". Its lifts also lacked the `memory`/`realloc` a spilled
//! parameter list (> 16 flat values) or a return area needs.
//!
//! Validation is not the oracle here: the wrapped component must COMPUTE the
//! same thing. Every exported function of the original and of the fused
//! component is called on wasmtime, in the same order, with the same
//! generated arguments, and every result must match.

use std::path::Path;

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};
use wasmtime::component::types::ComponentItem;
use wasmtime::component::{Component, Linker, Val};
use wasmtime::{Config, Engine, Store};

fn fixture(name: &str) -> Vec<u8> {
    std::fs::read(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/issue_461")
            .join(name),
    )
    .expect("fixture")
}

/// A deterministic, non-trivial value of `ty`. `n` varies the scalars so two
/// fields of one record never carry the same number.
fn sample(ty: &wasmtime::component::Type, n: &mut u32) -> Val {
    use wasmtime::component::Type as T;
    *n += 1;
    let k = *n;
    match ty {
        T::Bool => Val::Bool(k % 2 == 1),
        T::S8 => Val::S8(k as i8),
        T::U8 => Val::U8(k as u8),
        T::S16 => Val::S16(-(k as i16)),
        T::U16 => Val::U16(k as u16),
        T::S32 => Val::S32(-(k as i32) * 3),
        T::U32 => Val::U32(k * 7),
        T::S64 => Val::S64(-(k as i64) * 11),
        T::U64 => Val::U64(k as u64 * 13),
        T::Float32 => Val::Float32(k as f32 * 0.25 + 0.5),
        T::Float64 => Val::Float64(k as f64 * 0.125 + 1.0),
        T::Char => Val::Char('a'),
        T::String => Val::String(format!("s{k}")),
        T::List(l) => Val::List(vec![sample(&l.ty(), n), sample(&l.ty(), n)]),
        T::Record(r) => Val::Record(
            r.fields()
                .map(|f| (f.name.to_string(), sample(&f.ty, n)))
                .collect(),
        ),
        T::Tuple(t) => Val::Tuple(t.types().map(|t| sample(&t, n)).collect()),
        T::Variant(v) => {
            let c = v.cases().next().expect("variant has a case");
            Val::Variant(c.name.to_string(), c.ty.map(|t| Box::new(sample(&t, n))))
        }
        T::Enum(e) => {
            let names: Vec<_> = e.names().collect();
            Val::Enum(names[k as usize % names.len()].to_string())
        }
        T::Option(o) => Val::Option(Some(Box::new(sample(&o.ty(), n)))),
        T::Result(r) => Val::Result(Ok(r.ok().map(|t| Box::new(sample(&t, n))))),
        T::Flags(f) => Val::Flags(f.names().take(1).map(str::to_string).collect()),
        other => panic!("no sample for {other:?}"),
    }
}

/// Call every exported function, interface by interface in name order, and
/// return a transcript of `name(args) -> results`.
fn transcript(bytes: &[u8]) -> Vec<String> {
    let mut config = Config::new();
    config.wasm_component_model(true);
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let component = Component::new(&engine, bytes).expect("component loads");
    let mut linker = Linker::<()>::new(&engine);
    linker
        .define_unknown_imports_as_traps(&component)
        .expect("stub imports");
    let mut store = Store::new(&engine, ());
    let instance = linker
        .instantiate(&mut store, &component)
        .expect("instantiates");

    let mut out = Vec::new();
    let ctype = component.component_type();
    let mut ifaces: Vec<_> = ctype.exports(&engine).collect();
    ifaces.sort_by(|a, b| a.0.cmp(b.0));
    for (iface, item) in ifaces {
        let ComponentItem::ComponentInstance(it) = item.ty else {
            continue;
        };
        let mut funcs: Vec<_> = it
            .exports(&engine)
            .filter_map(|(n, i)| match i.ty {
                ComponentItem::ComponentFunc(f) => Some((n.to_string(), f)),
                _ => None,
            })
            .collect();
        funcs.sort_by(|a, b| a.0.cmp(&b.0));
        let iface_idx = instance
            .get_export_index(&mut store, None, iface)
            .expect("interface export");
        for (fname, fty) in funcs {
            let idx = instance
                .get_export_index(&mut store, Some(&iface_idx), &fname)
                .expect("func export");
            let func = instance.get_func(&mut store, idx).expect("func");
            let mut n = 0;
            let args: Vec<Val> = fty.params().map(|(_, t)| sample(&t, &mut n)).collect();
            let mut results = vec![Val::Bool(false); fty.results().len()];
            let outcome = match func.call(&mut store, &args, &mut results) {
                Ok(()) => format!("{results:?}"),
                Err(e) => format!("trap: {}", e.root_cause()),
            };
            out.push(format!("{iface}#{fname}({args:?}) -> {outcome}"));
        }
    }
    out
}

fn fuse_component(input: &[u8], strategy: MemoryStrategy) -> Vec<u8> {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: strategy,
        output_format: OutputFormat::Component,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component(input).unwrap();
    fuser.fuse().expect("--component fuses (#476)")
}

// rivet: verifies SR-123
// rivet: verifies SWV-137
#[test]
fn component_output_using_imported_interface_types_computes_the_same() {
    for name in [
        "falcon_cascade_estimator_cm.wasm",
        "falcon_cascade_control_cm.wasm",
    ] {
        let original = fixture(name);
        let expected = transcript(&original);
        // Potency: the transcript must exercise spilled params and records,
        // or a match would say little.
        assert!(
            expected.len() >= 2,
            "{name}: only {} calls in the transcript",
            expected.len()
        );
        assert!(
            expected.iter().any(|l| l.contains("Record(")),
            "{name}: no record crossed the boundary"
        );
        let fused = fuse_component(&original, MemoryStrategy::MultiMemory);
        assert_eq!(
            transcript(&fused),
            expected,
            "{name}: fused component differs"
        );
    }
}

// rivet: verifies SR-123
#[test]
fn split_with_imported_interfaces_wraps_and_validates() {
    // The split also imports two function interfaces, which the stub linker
    // cannot answer meaningfully, so this checks wrapping and validation only.
    let fused = fuse_component(
        &fixture("falcon_cascade_split_cm.wasm"),
        MemoryStrategy::MultiMemory,
    );
    let mut config = Config::new();
    config.wasm_component_model(true);
    config.wasm_multi_memory(true);
    Component::new(&Engine::new(&config).unwrap(), &fused).expect("wrapped split loads");
}
