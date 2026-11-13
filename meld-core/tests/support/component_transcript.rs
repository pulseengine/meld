//! Shared oracle for `--component` tests (#476, #605): call every exported
//! function of a component on wasmtime with deterministic generated arguments
//! and return a transcript, so an original and a wrapped component can be
//! compared call for call.

use wasmtime::component::types::ComponentItem;
use wasmtime::component::{Component, Linker, Val};
use wasmtime::{Config, Engine, Store};

/// A deterministic, non-trivial value of `ty`. `n` varies the scalars so two
/// fields of one record never carry the same number.
pub fn sample(ty: &wasmtime::component::Type, n: &mut u32) -> Val {
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
pub fn transcript(bytes: &[u8]) -> Vec<String> {
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
