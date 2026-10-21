//! ADR-8: wasmtime-environ as a pinned, dev-only DIFFERENTIAL ORACLE for
//! meld's component resolution.
//!
//! meld resolves components with its own parser, resolver, merger and
//! wrapper (`component_wrap.rs`). wasmtime-environ's component translator
//! (`wasmtime_environ::component::Translator`) is a second, independent
//! implementation of the same resolution: it inlines a component into a flat
//! list of `GlobalInitializer`s and records, for every lift and lower, the
//! `CanonicalOptions` it resolved (memory, realloc, post-return, callback,
//! string encoding, async).
//!
//! The comparison runs the ORACLE ON BOTH SIDES:
//!
//! - **expected** — translate the SOURCE component; for each exported lift and
//!   each lowered host import, resolve every option to the core module that
//!   DEFINES the entity (chasing imports through the instantiation graph in
//!   wasmtime's own model, independent of meld's resolver), then map that
//!   `(module, index)` through meld's merger index maps to a fused index;
//! - **actual** — translate meld's `--component` OUTPUT the same way, giving
//!   the fused memory / function index each lift and lower really names.
//!
//! A disagreement means meld's output names a different memory, allocator,
//! post-return, callback, core function or encoding than the source did —
//! the #481 / #484 / #485 class, where meld exits 0 with a component that
//! returns the wrong answer, or that the oracle (a validating translator)
//! rejects outright.
//!
//! What this does NOT detect: a bug in meld's index maps THEMSELVES — the join
//! trusts `memory_index_map` / `function_index_map` (see ADR-8, "Risks"); nor,
//! yet, internal component-to-component call options (#489) or core-module
//! export naming (#499).
//!
//! Gated behind the `oracle` cargo feature (`required-features` in
//! Cargo.toml), so the default suite does not compile it; `--all-features`
//! (the CI coverage job) does, so it is never a dark test.

use meld_core::{
    Fuser, FuserConfig, MemoryStrategy, OracleIndexMaps, OutputFormat, ParsedComponent,
};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use wasmtime_environ::component::{
    ComponentTranslation, ComponentTypesBuilder, CoreDef, Export, ExportItem, GlobalInitializer,
    InstantiateModule, StringEncoding, Trampoline, Translator,
};
use wasmtime_environ::wasmparser::{Validator, WasmFeatures};
use wasmtime_environ::{
    EntityIndex, Initializer, ModuleTranslation, PrimaryMap, ScopeVec, StaticModuleIndex, Tunables,
};

// ---------------------------------------------------------------------------
// Oracle side: what wasmtime-environ resolves.
// ---------------------------------------------------------------------------

/// Where a canonical option (or a lifted core function) resolves to.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Loc {
    /// Defined in static module `module` at module-local absolute index
    /// `index` (imports first, as in the wasm index space).
    Def { module: usize, index: u32 },
    /// Not a core-module entity (a trampoline, an instance-flags global, an
    /// export of an imported core module, ...). Carried as a description; it
    /// is compared only for equality of kind.
    Other(String),
}

/// One resolved set of canonical options.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Opts<L> {
    memory: Option<L>,
    realloc: Option<L>,
    post_return: Option<L>,
    callback: Option<L>,
    encoding: &'static str,
    async_: bool,
}

/// Everything the oracle reports for one component.
struct OracleFacts {
    /// Bytes of every static module (wasmtime numbering), to join to meld's
    /// `(component, module)` identities. Includes wasmtime's own FACT adapter
    /// modules, which match nothing in meld and are therefore never joined.
    module_bytes: Vec<Vec<u8>>,
    /// Exported lifts, keyed by export path (`iface/func` or `func`).
    lifts: BTreeMap<String, (Loc, Opts<Loc>)>,
    /// Lowered host imports: (import path, options), one per trampoline.
    lowers: Vec<(String, Opts<Loc>)>,
    /// For every statically instantiated module, each IMPORTED memory /
    /// function and the definition it is bound to:
    /// `(module, space, module-local index) -> definition`. meld's wrapper
    /// hands the fused module its memories from a separate memory-provider
    /// module, so the output's options name the provider's memory; this is
    /// how such a memory is read back as the fused module's own index.
    import_bindings: Vec<(usize, Space, u32, Loc)>,
}

fn encoding_name(e: StringEncoding) -> &'static str {
    match e {
        StringEncoding::Utf8 => "utf8",
        StringEncoding::Utf16 => "utf16",
        StringEncoding::CompactUtf16 => "latin1+utf16",
    }
}

/// Translate `bytes` with wasmtime-environ (no compiler, no engine) and read
/// back the resolution facts. The translator validates, so an invalid
/// component is an `Err` here.
fn try_oracle(bytes: &[u8]) -> Result<OracleFacts, String> {
    let mut validator = Validator::new_with_features(WasmFeatures::all());
    let mut types = ComponentTypesBuilder::new(&validator);
    let tunables = Tunables::default_host();
    let scope = ScopeVec::new();
    let (translation, modules) = Translator::new(&tunables, &mut validator, &mut types, &scope)
        .translate(bytes)
        .map_err(|e| format!("{e:#}"))?;
    Ok(facts(&translation, &modules))
}

/// The oracle on a SOURCE fixture, which must be valid.
fn oracle(bytes: &[u8]) -> OracleFacts {
    try_oracle(bytes).unwrap_or_else(|e| panic!("wasmtime-environ rejected a source fixture: {e}"))
}

fn facts(
    t: &ComponentTranslation,
    modules: &PrimaryMap<StaticModuleIndex, ModuleTranslation<'_>>,
) -> OracleFacts {
    let c = &t.component;

    // RuntimeInstanceIndex -> (static module, instantiation args). The
    // instance index space is exactly the order of `InstantiateModule`s.
    let mut instances: Vec<Option<(StaticModuleIndex, &[CoreDef])>> = Vec::new();
    let mut memories = HashMap::new();
    let mut reallocs = HashMap::new();
    let mut post_returns = HashMap::new();
    let mut callbacks = HashMap::new();
    let mut lowered_imports = HashMap::new();
    for init in &c.initializers {
        match init {
            GlobalInitializer::InstantiateModule(InstantiateModule::Static(m, args), _) => {
                instances.push(Some((*m, &args[..])))
            }
            GlobalInitializer::InstantiateModule(InstantiateModule::Import(..), _) => {
                instances.push(None)
            }
            GlobalInitializer::ExtractMemory(e) => {
                memories.insert(
                    e.index,
                    CoreDef::Export(e.export.clone().map_index(EntityIndex::Memory)),
                );
            }
            GlobalInitializer::ExtractRealloc(e) => {
                reallocs.insert(e.index, e.def.clone());
            }
            GlobalInitializer::ExtractPostReturn(e) => {
                post_returns.insert(e.index, e.def.clone());
            }
            GlobalInitializer::ExtractCallback(e) => {
                callbacks.insert(e.index, e.def.clone());
            }
            GlobalInitializer::LowerImport { index, import } => {
                lowered_imports.insert(*index, *import);
            }
            _ => {}
        }
    }

    let resolver = Resolve {
        modules,
        instances: &instances,
    };
    let opts = |idx| {
        let o = &c.options[idx];
        Opts {
            memory: o.memory().map(|m| resolver.def(&memories[&m])),
            realloc: o.data_model_realloc().map(|r| resolver.def(&reallocs[&r])),
            post_return: o.post_return.map(|p| resolver.def(&post_returns[&p])),
            callback: o.callback.map(|cb| resolver.def(&callbacks[&cb])),
            encoding: encoding_name(o.string_encoding),
            async_: o.async_,
        }
    };

    let mut lifts = BTreeMap::new();
    let mut stack: Vec<(String, wasmtime_environ::component::ExportIndex)> = c
        .exports
        .raw_iter()
        .map(|(n, (i, _))| (n.to_string(), *i))
        .collect();
    while let Some((path, idx)) = stack.pop() {
        match &c.export_items[idx] {
            Export::LiftedFunction { func, options, .. } => {
                lifts.insert(path, (resolver.def(func), opts(*options)));
            }
            Export::Instance { exports, .. } => {
                for (n, (i, _)) in exports.raw_iter() {
                    stack.push((format!("{path}/{n}"), *i));
                }
            }
            _ => {}
        }
    }

    let mut lowers = Vec::new();
    for (_, tramp) in t.trampolines.iter() {
        if let Trampoline::LowerImport { index, options, .. } = tramp {
            let (import, names) = &c.imports[lowered_imports[index]];
            let mut path = c.import_types[*import].0.clone();
            for n in names {
                path.push('/');
                path.push_str(n);
            }
            lowers.push((path, opts(*options)));
        }
    }

    let mut import_bindings = Vec::new();
    for (m, args) in instances.iter().flatten() {
        let module = &modules[*m].module;
        for (pos, init) in module.initializers.iter().enumerate() {
            let Initializer::Import { index, .. } = init;
            let (space, i) = match index {
                EntityIndex::Memory(i) => (Space::Memory, i.as_u32()),
                EntityIndex::Function(i) => (Space::Function, i.as_u32()),
                _ => continue,
            };
            import_bindings.push((m.as_u32() as usize, space, i, resolver.def(&args[pos])));
        }
    }

    OracleFacts {
        module_bytes: modules.values().map(|m| m.wasm.to_vec()).collect(),
        lifts,
        lowers,
        import_bindings,
    }
}

/// Small extension: the realloc option lives inside the linear-memory data
/// model in wasmtime-environ 41.
trait ReallocOpt {
    fn data_model_realloc(&self) -> Option<wasmtime_environ::component::RuntimeReallocIndex>;
}
impl ReallocOpt for wasmtime_environ::component::CanonicalOptions {
    fn data_model_realloc(&self) -> Option<wasmtime_environ::component::RuntimeReallocIndex> {
        match self.data_model {
            wasmtime_environ::component::CanonicalOptionsDataModel::LinearMemory(m) => m.realloc,
            wasmtime_environ::component::CanonicalOptionsDataModel::Gc {} => None,
        }
    }
}

struct Resolve<'a, 'd> {
    modules: &'a PrimaryMap<StaticModuleIndex, ModuleTranslation<'d>>,
    instances: &'a [Option<(StaticModuleIndex, &'a [CoreDef])>],
}

impl Resolve<'_, '_> {
    /// Resolve a `CoreDef` to the module that DEFINES the entity, following
    /// imports through the instantiation arguments (wasmtime's graph, not
    /// meld's).
    fn def(&self, d: &CoreDef) -> Loc {
        match d {
            CoreDef::Export(e) => {
                let Some((m, args)) = self.instances[e.instance.as_u32() as usize] else {
                    return Loc::Other("export of an imported core module".into());
                };
                let module = &self.modules[m].module;
                let ent = match &e.item {
                    ExportItem::Index(i) => *i,
                    ExportItem::Name(n) => {
                        let atom = module
                            .strings
                            .get_atom(n.as_str())
                            .expect("export name is interned in the module's string pool");
                        module.exports[&atom]
                    }
                };
                // Imported? Then the instantiation argument at that import's
                // position is the real definition.
                for (pos, init) in module.initializers.iter().enumerate() {
                    let Initializer::Import { index, .. } = init;
                    if *index == ent {
                        return self.def(&args[pos]);
                    }
                }
                let index = match ent {
                    EntityIndex::Function(i) => i.as_u32(),
                    EntityIndex::Memory(i) => i.as_u32(),
                    EntityIndex::Table(i) => i.as_u32(),
                    EntityIndex::Global(i) => i.as_u32(),
                    EntityIndex::Tag(i) => i.as_u32(),
                };
                Loc::Def {
                    module: m.as_u32() as usize,
                    index,
                }
            }
            CoreDef::Trampoline(_) => Loc::Other("trampoline".into()),
            CoreDef::InstanceFlags(_) => Loc::Other("instance-flags".into()),
            CoreDef::UnsafeIntrinsic(_) => Loc::Other("unsafe-intrinsic".into()),
        }
    }
}
// ---------------------------------------------------------------------------
// The join: map the source's resolution through meld's index maps and
// compare with the oracle's resolution of meld's output.
// ---------------------------------------------------------------------------

/// A resolved location expressed in FUSED terms.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Fused {
    /// A memory or function index in the fused core module's index space.
    Index(u32),
    /// The source entity's module could not be joined to a single meld
    /// module, or its index is not in meld's map. Never compared.
    Unjoinable(String),
    Other(String),
}

/// Result of comparing one fixture.
#[derive(Debug, Default)]
struct Report {
    /// Individual facts (one option of one lift/lower) that agreed.
    agreed: usize,
    /// Human-readable disagreements.
    disagreements: Vec<String>,
    /// Facts the join could not express (meld-synthesised core function,
    /// unjoinable module, inert extra option). Counted, never silently dropped.
    not_comparable: Vec<String>,
    /// Options the output supplies and the source omits (see `Cmp::InertExtra`).
    inert: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Space {
    Memory,
    Function,
}

struct Join<'a> {
    /// Source static module -> meld (component, module).
    src_module: HashMap<usize, (usize, usize)>,
    maps: &'a OracleIndexMaps,
    /// The static module of meld's output that holds the fused code.
    fused_module: usize,
    /// The output's import bindings (see `OracleFacts::import_bindings`).
    out_bindings: &'a [(usize, Space, u32, Loc)],
}

impl Join<'_> {
    /// The source's resolution, mapped through meld's index maps.
    fn expected(&self, l: &Loc, space: Space) -> Fused {
        match l {
            Loc::Def { module, index } => {
                let Some(&(c, m)) = self.src_module.get(module) else {
                    return Fused::Unjoinable(format!("source module {module} has no meld twin"));
                };
                let map = match space {
                    Space::Memory => &self.maps.memory,
                    Space::Function => &self.maps.function,
                };
                match map.get(&(c, m, *index)) {
                    Some(&f) => Fused::Index(f),
                    None => Fused::Unjoinable(format!("({c},{m},{index}) not in meld's map")),
                }
            }
            Loc::Other(s) => Fused::Other(s.clone()),
        }
    }

    /// The output's resolution, as an index of the fused core module: either
    /// defined there, or defined elsewhere and imported by it.
    fn actual(&self, l: &Loc, space: Space) -> Fused {
        if let Loc::Def { module, index } = l
            && *module == self.fused_module
        {
            return Fused::Index(*index);
        }
        let bound: Vec<u32> = self
            .out_bindings
            .iter()
            .filter(|(m, s, _, d)| *m == self.fused_module && *s == space && d == l)
            .map(|(_, _, i, _)| *i)
            .collect();
        match (bound.as_slice(), l) {
            ([i], _) => Fused::Index(*i),
            (_, Loc::Def { module, index }) => Fused::Other(format!(
                "module {module}#{index}, not visible to the fused module"
            )),
            (_, Loc::Other(s)) => Fused::Other(s.clone()),
        }
    }

    fn opts(&self, o: &Opts<Loc>, expected: bool) -> Opts<Fused> {
        let f = |l: &Option<Loc>, s| {
            l.as_ref().map(|l| {
                if expected {
                    self.expected(l, s)
                } else {
                    self.actual(l, s)
                }
            })
        };
        Opts {
            memory: f(&o.memory, Space::Memory),
            realloc: f(&o.realloc, Space::Function),
            post_return: f(&o.post_return, Space::Function),
            callback: f(&o.callback, Space::Function),
            encoding: o.encoding,
            async_: o.async_,
        }
    }
}

/// Outcome of comparing one option.
enum Cmp {
    Agree,
    /// The source omits the option and the output supplies one. Validation
    /// requires every option the function's type needs, so an option the
    /// source omits is one the canonical ABI never consults for this type:
    /// inert, not a disagreement. (meld puts memory + realloc on every lower.)
    InertExtra,
    Unjoinable(String),
    Disagree,
}

fn cmp(e: &Option<Fused>, a: &Option<Fused>) -> Cmp {
    match (e, a) {
        (Some(Fused::Unjoinable(why)), _) => Cmp::Unjoinable(why.clone()),
        (None, Some(_)) => Cmp::InertExtra,
        (e, a) if e == a => Cmp::Agree,
        _ => Cmp::Disagree,
    }
}

/// Compare two resolved option sets field by field.
fn compare_opts(what: &str, exp: &Opts<Fused>, act: &Opts<Fused>, r: &mut Report) {
    for (name, e, a) in [
        ("memory", &exp.memory, &act.memory),
        ("realloc", &exp.realloc, &act.realloc),
        ("post-return", &exp.post_return, &act.post_return),
        ("callback", &exp.callback, &act.callback),
    ] {
        match cmp(e, a) {
            Cmp::Agree => r.agreed += 1,
            Cmp::InertExtra => r.inert += 1,
            Cmp::Unjoinable(why) => r
                .not_comparable
                .push(format!("{what} {name}: unjoinable ({why})")),
            Cmp::Disagree => r.disagreements.push(format!(
                "{what} {name}: source names {e:?}, meld's output names {a:?}"
            )),
        }
    }
    if exp.encoding == act.encoding {
        r.agreed += 1;
    } else {
        r.disagreements.push(format!(
            "{what} string-encoding: source {}, output {}",
            exp.encoding, act.encoding
        ));
    }
    if exp.async_ == act.async_ {
        r.agreed += 1;
    } else {
        r.disagreements.push(format!(
            "{what} async: source {}, output {}",
            exp.async_, act.async_
        ));
    }
}

/// True when an output lowering is an acceptable realisation of a source one:
/// every option agrees or is an inert extra; nothing disagrees.
fn lower_compatible(e: &Opts<Fused>, a: &Opts<Fused>) -> bool {
    [
        (&e.memory, &a.memory),
        (&e.realloc, &a.realloc),
        (&e.post_return, &a.post_return),
        (&e.callback, &a.callback),
    ]
    .iter()
    .all(|(e, a)| matches!(cmp(e, a), Cmp::Agree | Cmp::InertExtra))
        && e.encoding == a.encoding
        && e.async_ == a.async_
}

/// meld's `(flattened component, module)` identities, keyed by module bytes.
fn meld_modules(comps: &[ParsedComponent]) -> HashMap<&[u8], Vec<(usize, usize)>> {
    let mut by_bytes: HashMap<&[u8], Vec<(usize, usize)>> = HashMap::new();
    for (c, comp) in comps.iter().enumerate() {
        for (m, module) in comp.core_modules.iter().enumerate() {
            by_bytes.entry(&module.bytes[..]).or_default().push((c, m));
        }
    }
    by_bytes
}

/// Join wasmtime's static modules to meld's by bytes. A byte-identical module
/// meld holds more than once (multiply-instantiated, duplicated by RFC-46 Q1)
/// is ambiguous and left unjoined: honest, not guessed. wasmtime's own FACT
/// adapter modules match nothing and stay unjoined too.
fn join_modules(
    src: &OracleFacts,
    meld_by_bytes: &HashMap<&[u8], Vec<(usize, usize)>>,
) -> HashMap<usize, (usize, usize)> {
    src.module_bytes
        .iter()
        .enumerate()
        .filter_map(|(i, b)| match meld_by_bytes.get(&b[..])?.as_slice() {
            [one] => Some((i, *one)),
            _ => None,
        })
        .collect()
}

/// meld knobs the oracle fuses with. Always explicit `MultiMemory`: under a
/// shared memory every option is memory 0 and the comparison proves nothing.
fn fuse(inputs: &[&[u8]], output_format: OutputFormat) -> (Vec<u8>, Fuser) {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        output_format,
        ..Default::default()
    });
    for (i, b) in inputs.iter().enumerate() {
        fuser
            .add_component_named(b, Some(&format!("input{i}.wasm")))
            .expect("meld rejected the input");
    }
    let fused = fuser.fuse().expect("meld failed to fuse");
    (fused, fuser)
}

/// Fuse `inputs` with meld (`--memory multi --component`), run the oracle on
/// each input and on the output, and compare.
fn differential(inputs: &[&[u8]]) -> Report {
    let (fused, fuser) = fuse(inputs, OutputFormat::Component);
    let maps = fuser
        .oracle_index_maps()
        .expect("fuse succeeded but left no index-map snapshot");

    // meld's module identities by bytes, in flattened order.
    let meld_by_bytes = meld_modules(fuser.components());

    // meld's output must itself be a component the oracle accepts; one it
    // rejects (an invalid component emitted at exit 0) is the bluntest
    // disagreement there is.
    let act = match try_oracle(&fused) {
        Ok(a) => a,
        Err(e) => {
            return Report {
                disagreements: vec![format!(
                    "meld exited 0 but wasmtime-environ rejects its output: {e}"
                )],
                ..Report::default()
            };
        }
    };
    // The fused core module: the static module of the output that the most
    // lifts resolve into.
    let mut votes: HashMap<usize, usize> = HashMap::new();
    for (l, _) in act.lifts.values() {
        if let Loc::Def { module, .. } = l {
            *votes.entry(*module).or_default() += 1;
        }
    }
    let fused_module = votes
        .into_iter()
        .max_by_key(|(m, n)| (*n, usize::MAX - m))
        .map(|(m, _)| m)
        .expect("meld's output exports no lifted function the oracle can resolve");

    let mut report = Report::default();
    let fused_funcs: BTreeSet<u32> = maps.function.values().copied().collect();
    let mut seen_lifts = BTreeSet::new();
    let mut exp_lowers: BTreeSet<(String, Opts<Fused>)> = BTreeSet::new();

    for input in inputs {
        let src = oracle(input);
        let src_module = join_modules(&src, &meld_by_bytes);
        let join = Join {
            src_module,
            maps: &maps,
            fused_module,
            out_bindings: &act.import_bindings,
        };

        for (name, (func, opts)) in &src.lifts {
            seen_lifts.insert(name.clone());
            let Some((afunc, aopts)) = act.lifts.get(name) else {
                report.disagreements.push(format!(
                    "lift `{name}`: in the source, absent from meld's output"
                ));
                continue;
            };
            let what = format!("lift `{name}`");
            // The lifted core function itself (export binding).
            let e = join.expected(func, Space::Function);
            let a = join.actual(afunc, Space::Function);
            match (&e, &a) {
                (Fused::Unjoinable(why), _) => report
                    .not_comparable
                    .push(format!("{what} core func: unjoinable ({why})")),
                (Fused::Index(_), Fused::Index(ai)) if !fused_funcs.contains(ai) => {
                    // meld lifts a function it synthesised (adapter, wrapper):
                    // the source function is not directly the lifted one.
                    report
                        .not_comparable
                        .push(format!("{what} core func: meld-synthesised #{ai}"))
                }
                (e, a) if e == a => report.agreed += 1,
                (e, a) => report.disagreements.push(format!(
                    "{what} core func: source lifts {e:?}, meld's output lifts {a:?}"
                )),
            }
            compare_opts(
                &what,
                &join.opts(opts, true),
                &join.opts(aopts, false),
                &mut report,
            );
        }

        for (path, opts) in &src.lowers {
            exp_lowers.insert((path.clone(), join.opts(opts, true)));
        }
    }

    for name in act.lifts.keys() {
        if !seen_lifts.contains(name) {
            report
                .disagreements
                .push(format!("lift `{name}`: in meld's output, in no input"));
        }
    }

    // Lowers. meld deduplicates identical lowers and adds inert options, so
    // the relation is: every distinct source lowering is realised by SOME
    // compatible output lowering of the same import, and every output
    // lowering realises SOME source lowering of that import.
    let join = Join {
        src_module: HashMap::new(),
        maps: &maps,
        fused_module,
        out_bindings: &act.import_bindings,
    };
    let act_lowers: BTreeSet<(String, Opts<Fused>)> = act
        .lowers
        .iter()
        .map(|(p, o)| (p.clone(), join.opts(o, false)))
        .collect();
    for (path, e) in &exp_lowers {
        if [&e.memory, &e.realloc, &e.post_return, &e.callback]
            .iter()
            .any(|f| matches!(f, Some(Fused::Unjoinable(_))))
        {
            report
                .not_comparable
                .push(format!("lower `{path}`: unjoinable option {e:?}"));
            continue;
        }
        if let Some((_, a)) = act_lowers
            .iter()
            .find(|(p, a)| p == path && lower_compatible(e, a))
        {
            // Counts each agreeing option; compatibility rules out a
            // disagreement here.
            compare_opts(&format!("lower `{path}`"), e, a, &mut report);
        } else {
            let got: Vec<_> = act_lowers.iter().filter(|(p, _)| p == path).collect();
            report.disagreements.push(format!(
                "lower `{path}`: source resolves {e:?}; meld's output lowers it as {got:?}"
            ));
        }
    }
    for (path, a) in &act_lowers {
        if !exp_lowers
            .iter()
            .any(|(p, e)| p == path && lower_compatible(e, a))
        {
            report.disagreements.push(format!(
                "lower `{path}` {a:?}: in meld's output, realises no source lowering"
            ));
        }
    }

    report
}

/// The INPUT-side comparison: meld's own resolver's reading of every source
/// `canon lift` (`resolver::core_func_sources` / `core_memory_sources`, the
/// functions `component_wrap` and the #400 signature manifest resolve options
/// with) against wasmtime-environ's reading of the same component, both
/// expressed as fused indices through the merger's maps.
///
/// It needs no `--component` output, so it also covers inputs the wrapper
/// cannot yet wrap (the #461 falcon trio) — the fuse here is a plain
/// core-module fuse.
fn resolver_differential(inputs: &[&[u8]]) -> Report {
    let (_, fuser) = fuse(inputs, OutputFormat::CoreModule);
    let maps = fuser
        .oracle_index_maps()
        .expect("fuse succeeded but left no index-map snapshot");
    let comps = fuser.components();

    // meld's claims: for every lift in every flattened component, the fused
    // lifted function and its options. `None` in a slot = meld could not
    // trace it (recorded, never guessed).
    let resolve_func = |c: usize, f: u32| -> Option<u32> {
        let (m, name) = meld_core::resolver::core_func_sources(&comps[c])
            .get(&f)
            .cloned()?;
        let local = comps[c].core_modules[m]
            .exports
            .iter()
            .find(|e| e.name == name && e.kind == meld_core::parser::ExportKind::Function)?
            .index;
        maps.function.get(&(c, m, local)).copied()
    };
    let resolve_mem = |c: usize, i: u32| -> Option<u32> {
        let (m, name) = meld_core::resolver::core_memory_sources(&comps[c])
            .get(&i)
            .cloned()?;
        let local = comps[c].core_modules[m]
            .exports
            .iter()
            .find(|e| e.name == name && e.kind == meld_core::parser::ExportKind::Memory)?
            .index;
        maps.memory.get(&(c, m, local)).copied()
    };
    let as_fused = |v: Option<u32>, what: &str| match v {
        Some(i) => Fused::Index(i),
        None => Fused::Unjoinable(format!("meld's resolver cannot trace this {what}")),
    };
    let mut meld_lifts: HashMap<u32, Vec<Opts<Fused>>> = HashMap::new();
    let mut untraced_lifts = 0usize;
    for (c, comp) in comps.iter().enumerate() {
        for entry in &comp.canonical_functions {
            let meld_core::parser::CanonicalEntry::Lift {
                core_func_index,
                options: o,
                ..
            } = entry
            else {
                continue;
            };
            let Some(lifted) = resolve_func(c, *core_func_index) else {
                untraced_lifts += 1;
                continue;
            };
            meld_lifts.entry(lifted).or_default().push(Opts {
                memory: o.memory.map(|m| as_fused(resolve_mem(c, m), "memory")),
                realloc: o.realloc.map(|f| as_fused(resolve_func(c, f), "realloc")),
                post_return: o
                    .post_return
                    .map(|f| as_fused(resolve_func(c, f), "post-return")),
                callback: o.callback.map(|f| as_fused(resolve_func(c, f), "callback")),
                encoding: match o.string_encoding {
                    meld_core::parser::CanonStringEncoding::Utf8 => "utf8",
                    meld_core::parser::CanonStringEncoding::Utf16 => "utf16",
                    meld_core::parser::CanonStringEncoding::CompactUtf16 => "latin1+utf16",
                },
                async_: o.async_,
            });
        }
    }

    let meld_by_bytes = meld_modules(comps);

    let mut report = Report::default();
    if untraced_lifts > 0 {
        report.not_comparable.push(format!(
            "{untraced_lifts} meld lift(s) whose core function meld's resolver cannot trace"
        ));
    }
    for input in inputs {
        let src = oracle(input);
        let src_module = join_modules(&src, &meld_by_bytes);
        let join = Join {
            src_module,
            maps: &maps,
            fused_module: usize::MAX, // unused: no output side here
            out_bindings: &[],
        };
        for (name, (func, opts)) in &src.lifts {
            let what = format!("lift `{name}`");
            let Fused::Index(lifted) = join.expected(func, Space::Function) else {
                report
                    .not_comparable
                    .push(format!("{what}: lifted function unjoinable"));
                continue;
            };
            let Some(candidates) = meld_lifts.get(&lifted) else {
                report.disagreements.push(format!(
                    "{what}: wasmtime lifts fused func #{lifted}; meld's resolver traces no \
                     lift to it"
                ));
                continue;
            };
            report.agreed += 1;
            let exp = join.opts(opts, true);
            // A function lifted more than once (several exports) has several
            // option sets; the oracle's must be one of them, exactly.
            match candidates.iter().find(|m| **m == exp) {
                Some(m) => compare_opts(&what, &exp, m, &mut report),
                None if candidates.len() == 1 => {
                    compare_opts(&what, &exp, &candidates[0], &mut report)
                }
                None => report.disagreements.push(format!(
                    "{what}: wasmtime resolves {exp:?}; meld's resolver has only {candidates:?}"
                )),
            }
        }
    }
    report
}

/// Assert a fixture compared at least `min_facts` facts and agreed on all.
fn assert_agrees(label: &str, r: &Report, min_facts: usize) {
    eprintln!(
        "[oracle] {label}: {} agreed, {} disagreements, {} not comparable, {} inert extras",
        r.agreed,
        r.disagreements.len(),
        r.not_comparable.len(),
        r.inert
    );
    for n in &r.not_comparable {
        eprintln!("[oracle]   not comparable: {n}");
    }
    assert!(
        r.disagreements.is_empty(),
        "{label}: meld and wasmtime-environ disagree:\n  {}",
        r.disagreements.join("\n  ")
    );
    assert!(
        r.agreed >= min_facts,
        "{label}: only {} facts compared (want >= {min_facts}); the oracle is not looking",
        r.agreed
    );
}

// ---------------------------------------------------------------------------
// Fixtures.
// ---------------------------------------------------------------------------

/// #481 (copied from `lift_memory_481.rs`): two memory-owning modules, the
/// lift names A's memory and post-return; `importer_first` decides which
/// module merges first.
fn fixture_481(importer_first: bool) -> Vec<u8> {
    let a = r#"(core module $A
        (import "b" "f" (func $f (param i32) (result i32)))
        (memory (export "mem") 1)
        (data (i32.const 16) "hello")
        (func (export "run") (result i32)
          (drop (call $f (i32.const 0)))
          (i32.store (i32.const 0) (i32.const 16))
          (i32.store (i32.const 4) (i32.const 5))
          i32.const 0)
        (func (export "cabi_post_run") (param i32)))"#;
    let b = r#"(core module $B
        (memory (export "mem") 1)
        (data (i32.const 16) "WORLD")
        (func (export "f") (param i32) (result i32) local.get 0))"#;
    let mods = if importer_first {
        format!("{a}\n{b}")
    } else {
        format!("{b}\n{a}")
    };
    wat::parse_str(format!(
        r#"(component
      {mods}
      (core instance $b (instantiate $B))
      (alias core export $b "f" (core func $lf))
      (core instance $fi (export "f" (func $lf)))
      (core instance $a (instantiate $A (with "b" (instance $fi))))
      (alias core export $a "mem" (core memory $m))
      (alias core export $a "run" (core func $run))
      (alias core export $a "cabi_post_run" (core func $pr))
      (func (export "run") (result string) (canon lift (core func $run) (memory $m) (post-return $pr))))"#
    ))
    .unwrap()
}

/// #484 (copied from `lower_memory_484.rs`): the lower names M's memory; A
/// imports that memory; B owns an unrelated one. `order` is the source order.
fn fixture_484(order: &str, lower_opts: &str) -> Vec<u8> {
    let m = r#"(core module $M
        (memory (export "mem") 1)
        (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 0))"#;
    let b = r#"(core module $B
        (memory (export "mem") 1)
        (data (i32.const 0) "WORLD"))"#;
    let a = r#"(core module $A
        (import "env" "mem" (memory 1))
        (import "host" "log" (func $log (param i32 i32) (result i32)))
        (data (i32.const 0) "hello")
        (func (export "run") (result i32) i32.const 0 i32.const 5 call $log))"#;
    let mods: Vec<&str> = order
        .chars()
        .map(|c| match c {
            'M' => m,
            'B' => b,
            _ => a,
        })
        .collect();
    wat::parse_str(format!(
        r#"(component
  (import "my:h/host" (instance $h
    (export "log" (func (param "s" string) (result u32)))))
  {mods}
  (core instance $m (instantiate $M))
  (core instance $b (instantiate $B))
  (alias export $h "log" (func $log))
  (core func $low (canon lower (func $log) {lower_opts} (memory (core memory $m "mem"))))
  (core instance $host (export "log" (func $low)))
  (core instance $envi (export "mem" (memory $m "mem")))
  (core instance $a (instantiate $A (with "env" (instance $envi)) (with "host" (instance $host))))
  (func $run (result u32) (canon lift (core func $a "run")))
  (export "run" (func $run)))"#,
        mods = mods.join("\n  ")
    ))
    .unwrap()
}

/// #484 realloc variant (copied from `lower_memory_484.rs`): the lower names
/// B's memory AND B's realloc; M has a decoy realloc.
fn fixture_484_realloc(order: &str) -> Vec<u8> {
    let m = r#"(core module $M
        (memory (export "mem") 1)
        (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 0))"#;
    let b = r#"(core module $B
        (memory (export "mem") 1)
        (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 100))"#;
    let a = r#"(core module $A
        (import "env" "mem" (memory 1))
        (import "host" "get" (func $get (param i32)))
        (func (export "run") (result i32)
          (local $p i32)
          (call $get (i32.const 8))
          (local.set $p (i32.load (i32.const 8)))
          (i32.add (local.get $p) (i32.load8_u (local.get $p)))))"#;
    let mods: Vec<&str> = order
        .chars()
        .map(|c| match c {
            'M' => m,
            'B' => b,
            _ => a,
        })
        .collect();
    wat::parse_str(format!(
        r#"(component
  (import "my:h/host" (instance $h
    (export "get" (func (result string)))))
  {mods}
  (core instance $m (instantiate $M))
  (core instance $b (instantiate $B))
  (alias export $h "get" (func $get))
  (core func $low (canon lower (func $get) (memory (core memory $b "mem")) (realloc (core func $b "cabi_realloc"))))
  (core instance $host (export "get" (func $low)))
  (core instance $envi (export "mem" (memory $b "mem")))
  (core instance $a (instantiate $A (with "env" (instance $envi)) (with "host" (instance $host))))
  (func $run (result u32) (canon lift (core func $a "run")))
  (export "run" (func $run)))"#,
        mods = mods.join("\n  ")
    ))
    .unwrap()
}

/// #490 (the #484 fix PR) alias-tracing shape, copied from
/// `lower_memory_484.rs::chain_fixture`: the lowered function reaches the
/// importing module through `hops` re-exporting core-instance bags, with a
/// utf16 lower naming M's memory.
fn fixture_alias_chain(hops: usize) -> Vec<u8> {
    let mut bags = String::from("(core instance $b0 (export \"log\" (func $low)))\n");
    for k in 1..=hops {
        bags.push_str(&format!(
            "(core instance $b{k} (export \"log\" (func $b{} \"log\")))\n",
            k - 1
        ));
    }
    wat::parse_str(format!(
        r#"(component
  (import "my:h/host" (instance $h (export "log" (func (param "s" string) (result u32)))))
  (core module $B (memory (export "mem") 1) (data (i32.const 0) "WORLD"))
  (core module $M (memory (export "mem") 1) (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 0))
  (core module $A
    (import "env" "mem" (memory 1))
    (import "my:h/host" "log" (func $log (param i32 i32) (result i32)))
    (data (i32.const 0) "h\00i\00")
    (func (export "run") (result i32) i32.const 0 i32.const 2 call $log))
  (core instance $b (instantiate $B))
  (core instance $m (instantiate $M))
  (alias export $h "log" (func $log))
  (core func $low (canon lower (func $log) string-encoding=utf16 (memory (core memory $m "mem"))))
  {bags}
  (core instance $envi (export "mem" (memory $m "mem")))
  (core instance $a (instantiate $A (with "env" (instance $envi)) (with "my:h/host" (instance $b{hops}))))
  (func $run (result u32) (canon lift (core func $a "run")))
  (export "run" (func $run)))"#
    ))
    .unwrap()
}

/// #485 (copied from the issue): a component func alias BEFORE the first core
/// module. meld's wrapper did not count the replayed alias, so the export
/// `run` names the imported `log` instead of the lift.
fn fixture_485() -> Vec<u8> {
    wat::parse_str(
        r#"(component
  (import "my:h/host" (instance $h
    (export "log" (func (param "s" string) (result u32)))))
  (alias export $h "log" (func $log))
  (core module $M
    (memory (export "mem") 1)
    (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 0))
  (core module $A
    (import "env" "mem" (memory 1))
    (import "host" "log" (func $log (param i32 i32) (result i32)))
    (data (i32.const 0) "hello")
    (func (export "run") (result i32) i32.const 0 i32.const 5 call $log))
  (core instance $m (instantiate $M))
  (core func $low (canon lower (func $log) (memory (core memory $m "mem"))))
  (core instance $host (export "log" (func $low)))
  (core instance $envi (export "mem" (memory $m "mem")))
  (core instance $a (instantiate $A (with "env" (instance $envi)) (with "host" (instance $host))))
  (func $run (result u32) (canon lift (core func $a "run")))
  (export "run" (func $run)))"#,
    )
    .unwrap()
}

/// A tracked fixture; missing is a hard failure, never a skip (#405).
fn fixture(rel: &str) -> Vec<u8> {
    let p = format!("{}/{rel}", env!("CARGO_MANIFEST_DIR"));
    std::fs::read(&p).unwrap_or_else(|e| panic!("fixture {p} missing ({e}); it is tracked"))
}

/// #484 was hash-order dependent (a fresh `HashMap` seed per fuse), so a
/// single fuse can pass by luck: compare several independent fusions.
const RUNS: usize = 10;

#[test]
fn oracle_lift_memory_481_both_module_orders() {
    for importer_first in [true, false] {
        let bytes = fixture_481(importer_first);
        let label = format!("481 importer_first={importer_first}");
        for _ in 0..RUNS {
            // core func + memory/realloc/post-return/callback + enc + async
            assert_agrees(&label, &differential(&[&bytes]), 7);
        }
        assert_agrees(&label, &resolver_differential(&[&bytes]), 7);
    }
}

#[test]
fn oracle_lower_memory_484_every_module_order() {
    for order in ["MBA", "MAB", "BMA", "BAM", "AMB", "ABM"] {
        let bytes = fixture_484(order, "");
        for _ in 0..RUNS {
            // one lift (7 facts) + one lower (memory, callback, post-return,
            // encoding, async agree; meld's extra realloc is inert)
            assert_agrees(&format!("484 order {order}"), &differential(&[&bytes]), 12);
        }
    }
}

#[test]
fn oracle_lower_encoding_484_utf16() {
    for order in ["MBA", "ABM"] {
        let bytes = fixture_484(order, "string-encoding=utf16");
        for _ in 0..RUNS {
            assert_agrees(&format!("484 utf16 {order}"), &differential(&[&bytes]), 12);
        }
    }
}

#[test]
fn oracle_lower_realloc_484() {
    for order in ["MBA", "BMA", "ABM"] {
        let bytes = fixture_484_realloc(order);
        for _ in 0..RUNS {
            assert_agrees(
                &format!("484 realloc {order}"),
                &differential(&[&bytes]),
                13,
            );
        }
    }
}

/// wit-bindgen runtime fixtures. Each is a runner + test guest composed with
/// the WASI preview1 adapter, so the top level exports only `run` and imports
/// WASI; what makes them useful is TWO memory-owning modules with two
/// `cabi_realloc`s, and WASI lowers naming each. (Their string/list/record
/// traffic is between the inner components — wasmtime FACT adapters, not yet
/// compared; see ADR-8 "What is compared later".)
const WIT_BINDGEN: [&str; 5] = [
    "strings",
    "lists",
    "records",
    "flavorful",
    "resource_aggregates",
];

#[test]
fn oracle_wit_bindgen_single_components() {
    for name in WIT_BINDGEN {
        let bytes = fixture(&format!("../tests/wit_bindgen/fixtures/{name}.wasm"));
        assert_agrees(&format!("{name} (output)"), &differential(&[&bytes]), 7);
        assert_agrees(
            &format!("{name} (resolver)"),
            &resolver_differential(&[&bytes]),
            7,
        );
    }
}

#[test]
fn oracle_wit_bindgen_composed() {
    // wac compositions (nested provider + consumer; their static modules join
    // to meld's flattened components by bytes).
    for (rel, min) in [
        ("compose/composed.wasm", 14),
        ("compose_record/composed_record.wasm", 7),
    ] {
        let bytes = fixture(&format!("../tests/wit_bindgen/fixtures/{rel}"));
        assert_agrees(&format!("{rel} (output)"), &differential(&[&bytes]), min);
        assert_agrees(
            &format!("{rel} (resolver)"),
            &resolver_differential(&[&bytes]),
            min,
        );
    }
}

/// The record-exporting provider of `compose_record`, on its own: its lift of
/// `tick` names `(memory $memory)` (the record result is returned through
/// memory). The resolver side agrees with the oracle.
#[test]
fn oracle_wit_bindgen_record_provider_resolver() {
    let bytes = fixture("../tests/wit_bindgen/fixtures/compose_record/provider.wasm");
    assert_agrees(
        "compose_record/provider.wasm (resolver)",
        &resolver_differential(&[&bytes]),
        7,
    );
}

/// Found by this oracle on its first run: `--memory multi --component` on the
/// tracked provider fixture exits 0 and emits `(canon lift (core func 0))` with
/// NO options, which wasmtime-environ rejects ("canonical option `memory` is
/// required"). Same root cause as meld#486 (export lifts drop the source's
/// `memory`/`realloc` unless a post-return or async forces them), reached by a
/// record RESULT rather than a string parameter.
#[test]
#[ignore = "meld#486: --component drops the export lift's memory option; the output is invalid"]
fn oracle_wit_bindgen_record_provider_output() {
    let bytes = fixture("../tests/wit_bindgen/fixtures/compose_record/provider.wasm");
    assert_agrees(
        "compose_record/provider.wasm (output)",
        &differential(&[&bytes]),
        7,
    );
}

const FALCON: [&str; 3] = [
    "falcon_cascade_estimator_cm",
    "falcon_cascade_control_cm",
    "falcon_cascade_split_cm",
];

fn falcon() -> Vec<Vec<u8>> {
    FALCON
        .iter()
        .map(|n| fixture(&format!("tests/fixtures/issue_461/{n}.wasm")))
        .collect()
}

#[test]
fn oracle_issue_461_falcon_cascade_resolver() {
    // cpetig's relay components (#461): each alone, then all three fused.
    let all = falcon();
    for (n, b) in FALCON.iter().zip(&all) {
        assert_agrees(
            &format!("461 {n} (resolver)"),
            &resolver_differential(&[b]),
            7,
        );
    }
    let refs: Vec<&[u8]> = all.iter().map(|b| &b[..]).collect();
    assert_agrees("461 cascade (resolver)", &resolver_differential(&refs), 21);
}

#[test]
#[ignore = "--component refuses these nested-component inputs (`cannot find source type \
            definition at index 1`): the same error class as meld#476, root cause not \
            confirmed; no output to compare, the resolver-side test covers them meanwhile"]
fn oracle_issue_461_falcon_cascade_output() {
    for (n, b) in FALCON.iter().zip(&falcon()) {
        assert_agrees(&format!("461 {n} (output)"), &differential(&[b]), 7);
    }
}

#[test]
fn oracle_lower_alias_chain_490() {
    for hops in [1usize, 3, 256] {
        let bytes = fixture_alias_chain(hops);
        assert_agrees(
            &format!("490 alias chain hops={hops}"),
            &differential(&[&bytes]),
            12,
        );
    }
}

#[test]
fn oracle_export_binding_485_resolver() {
    // meld's resolver reads the source lift correctly; the bug is in how the
    // wrapper numbers the export (below).
    assert_agrees(
        "485 (resolver)",
        &resolver_differential(&[&fixture_485()]),
        7,
    );
}

/// Caught by this oracle on `main` (8060df3): meld exits 0, and its output's
/// `run` export names the imported `log` instead of the lift. wasmtime-environ
/// rejects it: "component export `run` is a reexport of an imported function
/// which is not implemented".
#[test]
#[ignore = "meld#485: the wrapper's export index ignores replayed func aliases"]
fn oracle_export_binding_485_output() {
    assert_agrees("485 (output)", &differential(&[&fixture_485()]), 12);
}
