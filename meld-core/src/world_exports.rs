//! `--exports world` (#463): limit the fused core module's export list to the
//! outer component's world.
//!
//! A composition's fused module otherwise exports everything every inner
//! module exported: the internal interfaces the composition wired together,
//! each module's `__data_end` / `__heap_base` (one input's unrebased values,
//! #475) and its allocators. Consumers prune those by hand before the next
//! tool.
//!
//! **Export list only.** Function bodies stay, so a downstream tool can drop
//! whatever the shorter list leaves unreachable; nothing here renumbers.
//!
//! # How the world is found: through lifts, per function
//!
//! Membership is decided by *which function*, never by a name or prefix. For
//! every export of every input the outer component is walked structurally:
//!
//! * a world function export resolves, through the component's function index
//!   space, to the `canon lift` that defines it;
//! * a world instance export resolves to the bag of named functions that
//!   builds it, and each of those resolves the same way. A function that is an
//!   alias of another component's export (a composition) is followed into the
//!   sub-component that instantiates it.
//!
//! Each lift names a core function of some flattened component; the merger's
//! numbering gives its fused function index. That index — not a name — is what
//! is kept. If a world function cannot be traced to a fused function that some
//! export carries, the whole operation is an error naming it.
//!
//! # The world name
//!
//! The kept export carries the **world** name (`<instance>#<func>`, or the bare
//! function name). The core module's own export name for that function can
//! differ — the merger disambiguates colliding names with a `$N` suffix, and a
//! component may lift a core export of any name — so the export is emitted
//! under the world name, and any other export of the same name that points at a
//! different (internal) function is dropped. A world name is never left bound
//! to a non-world function.
//!
//! # What else is kept
//!
//! Everything the kept surface and the imports the module still has need, each
//! resolved through the merger's numbering and an error when it cannot be:
//!
//! * from each kept lift: its memory, realloc and post-return;
//! * from each remaining function import: the memory and realloc of the
//!   `canon lower` behind it;
//! * for each resource whose `new` / `rep` / `drop` intrinsics are still
//!   imported, and for each world interface: its `[dtor]` exports;
//! * the start function.
//!
//! A needed realloc nothing exports is exported as `meld:realloc/<component>`
//! (the SR-81 name), with or without `--emit-manifest`.
//!
//! Everything else — including every global and table export — is dropped.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use wasm_encoder::{EntityType, ExportKind};
use wasmparser::ComponentExternalKind;

use crate::merger::{MergedExport, MergedModule};
use crate::parser::{
    CanonicalEntry, CanonicalOptions, ComponentAliasEntry, ComponentFuncDef, ComponentInstanceDef,
    ComponentLevelInstance, ParsedComponent,
};
use crate::signature_manifest::{fused_index_of, locate_core_func};
use crate::{Error, Result};

/// What pruning decided, for the signature manifest to follow.
#[derive(Debug, Default)]
pub struct WorldPlan {
    /// `(flattened component, core func of the lift)` -> world export name, for
    /// every lift that implements a world function.
    pub lifts: HashMap<(usize, u32), String>,
}

fn refuse(msg: impl Into<String>) -> Error {
    Error::InvalidExports(msg.into())
}

/// One component of an input, in the original (un-flattened) form, with the
/// index its own content (if any) has in the flattened list.
struct Node<'a> {
    comp: &'a ParsedComponent,
    /// Flattened index of this component's own core modules.
    own: Option<usize>,
    subs: Vec<Node<'a>>,
}

/// How many flattened components `c` contributes. Mirrors
/// `flatten_nested_components`: a leaf is one; otherwise the outer itself (only
/// if it has core modules) followed by each sub-component's flattening.
fn flat_len(c: &ParsedComponent) -> usize {
    if c.sub_components.is_empty() {
        1
    } else {
        usize::from(!c.core_modules.is_empty())
            + c.sub_components.iter().map(flat_len).sum::<usize>()
    }
}

fn build_node(c: &ParsedComponent, start: usize) -> Node<'_> {
    if c.sub_components.is_empty() {
        return Node {
            comp: c,
            own: Some(start),
            subs: Vec::new(),
        };
    }
    let has_content = !c.core_modules.is_empty();
    let mut offset = start + usize::from(has_content);
    let mut subs = Vec::with_capacity(c.sub_components.len());
    for sub in &c.sub_components {
        subs.push(build_node(sub, offset));
        offset += flat_len(sub);
    }
    Node {
        comp: c,
        own: has_content.then_some(start),
        subs,
    }
}

type Items = [(String, ComponentExternalKind, u32)];

/// One level of "which instantiation are we inside": the component that
/// instantiated the current one, and the arguments it passed. A component's
/// imports are bound by the innermost frame.
#[derive(Clone, Copy)]
struct Frame<'a> {
    parent: &'a Node<'a>,
    args: &'a Items,
}

enum Inst<'a> {
    /// An instantiation of a sub-component, made by `parent`.
    Instantiated {
        sub: &'a Node<'a>,
        args: &'a Items,
        parent: &'a Node<'a>,
        env: Vec<Frame<'a>>,
    },
    /// An instance built from named exports of `node`.
    Bag {
        node: &'a Node<'a>,
        items: &'a Items,
        env: Vec<Frame<'a>>,
    },
}

/// A lift reached from a world export.
struct LiftRef<'a> {
    flat: usize,
    core_func: u32,
    options: &'a CanonicalOptions,
}

fn with_frame<'a>(env: &[Frame<'a>], parent: &'a Node<'a>, args: &'a Items) -> Vec<Frame<'a>> {
    let mut v = env.to_vec();
    v.push(Frame { parent, args });
    v
}

type Bound<'a> = (&'a Node<'a>, Vec<Frame<'a>>, u32);

/// Follow a component import of `node` to what the instantiating parent passed.
fn bound_arg<'a>(
    node: &'a Node<'a>,
    env: &[Frame<'a>],
    import: usize,
    kind: ComponentExternalKind,
) -> std::result::Result<Bound<'a>, String> {
    let Some((frame, up)) = env.split_last() else {
        return Err(
            "it re-exports an import of the outer component, which has no \
                    implementation here"
                .into(),
        );
    };
    let name = &node
        .comp
        .imports
        .get(import)
        .ok_or_else(|| format!("no import {import}"))?
        .name;
    let (_, _, idx) = frame
        .args
        .iter()
        .find(|(k, kd, _)| k == name && *kd == kind)
        .ok_or_else(|| format!("the instantiation passes no `{name}`"))?;
    Ok((frame.parent, up.to_vec(), *idx))
}

enum RealInstance<'a> {
    Def(&'a ComponentInstanceDef),
    /// The instance index bound by an `(export .. (instance N))`: an alias of `N`.
    Export(u32),
}

/// The definition behind a REAL component-instance index.
/// `component_instance_defs` has no slot for the index an instance export binds
/// (giving it one would shift every other lookup), so they are interleaved back
/// in from `instance_export_slots`.
fn real_instance_def(c: &ParsedComponent, real: u32) -> Option<RealInstance<'_>> {
    let mut r = 0u32;
    let mut slot = 0usize;
    let mut def = 0usize;
    loop {
        while let Some(&(pos, target)) = c.instance_export_slots.get(slot)
            && pos == def
        {
            if r == real {
                return Some(RealInstance::Export(target));
            }
            r += 1;
            slot += 1;
        }
        let d = c.component_instance_defs.get(def)?;
        if r == real {
            return Some(RealInstance::Def(d));
        }
        r += 1;
        def += 1;
    }
}

fn resolve_instance<'a>(
    node: &'a Node<'a>,
    env: &[Frame<'a>],
    idx: u32,
    depth: usize,
) -> std::result::Result<Inst<'a>, String> {
    if depth > 32 {
        return Err("instance chain too deep".into());
    }
    let c = node.comp;
    let def = match real_instance_def(c, idx) {
        Some(RealInstance::Export(target)) => {
            return resolve_instance(node, env, target, depth + 1);
        }
        Some(RealInstance::Def(d)) => Some(d),
        None => None,
    };
    match def {
        Some(ComponentInstanceDef::Instance(ci)) => match c.component_instances.get(*ci) {
            Some(ComponentLevelInstance::Instantiate {
                component_index,
                args,
            }) => Ok(Inst::Instantiated {
                sub: node
                    .subs
                    .get(*component_index as usize)
                    .ok_or_else(|| format!("instance {idx} instantiates unknown component"))?,
                args,
                parent: node,
                env: env.to_vec(),
            }),
            Some(ComponentLevelInstance::FromExports(items)) => Ok(Inst::Bag {
                node,
                items,
                env: env.to_vec(),
            }),
            None => Err(format!("instance {idx} has no definition")),
        },
        Some(ComponentInstanceDef::InstanceExportAlias(a)) => {
            let Some(ComponentAliasEntry::InstanceExport {
                instance_index,
                name,
                ..
            }) = c.component_aliases.get(*a)
            else {
                return Err(format!("instance {idx} alias is not an instance export"));
            };
            match resolve_instance(node, env, *instance_index, depth + 1)? {
                Inst::Instantiated {
                    sub,
                    args,
                    parent,
                    env: e0,
                } => {
                    let e = sub
                        .comp
                        .exports
                        .iter()
                        .find(|e| e.name == *name && e.kind == ComponentExternalKind::Instance)
                        .ok_or_else(|| {
                            format!("sub-component does not export instance `{name}`")
                        })?;
                    resolve_instance(sub, &with_frame(&e0, parent, args), e.index, depth + 1)
                }
                Inst::Bag {
                    node: n,
                    items,
                    env: e1,
                } => {
                    let (_, _, i) = items
                        .iter()
                        .find(|(k, kind, _)| k == name && *kind == ComponentExternalKind::Instance)
                        .ok_or_else(|| format!("instance has no instance export `{name}`"))?;
                    resolve_instance(n, &e1, *i, depth + 1)
                }
            }
        }
        Some(ComponentInstanceDef::Import(i)) => {
            let (p, up, arg) = bound_arg(node, env, *i, ComponentExternalKind::Instance)?;
            resolve_instance(p, &up, arg, depth + 1)
        }
        None => Err(format!("no instance with index {idx}")),
    }
}

fn resolve_func<'a>(
    node: &'a Node<'a>,
    env: &[Frame<'a>],
    idx: u32,
    depth: usize,
) -> std::result::Result<LiftRef<'a>, String> {
    if depth > 32 {
        return Err("function alias chain too deep".into());
    }
    let c = node.comp;
    match c.component_func_defs.get(idx as usize) {
        Some(ComponentFuncDef::Lift(canon)) => match c.canonical_functions.get(*canon) {
            Some(CanonicalEntry::Lift {
                core_func_index,
                options,
                ..
            }) => Ok(LiftRef {
                flat: node
                    .own
                    .ok_or_else(|| "its lift's component has no core modules".to_string())?,
                core_func: *core_func_index,
                options,
            }),
            _ => Err("its definition is not a canon lift".into()),
        },
        Some(ComponentFuncDef::ExportAlias(n)) => resolve_func(node, env, *n, depth + 1),
        Some(ComponentFuncDef::InstanceExportAlias(a)) => {
            let Some(ComponentAliasEntry::InstanceExport {
                instance_index,
                name,
                ..
            }) = c.component_aliases.get(*a)
            else {
                return Err("its alias is not an instance export".into());
            };
            match resolve_instance(node, env, *instance_index, depth + 1)? {
                Inst::Instantiated {
                    sub,
                    args,
                    parent,
                    env: e0,
                } => {
                    let e = sub
                        .comp
                        .exports
                        .iter()
                        .find(|e| e.name == *name && e.kind == ComponentExternalKind::Func)
                        .ok_or_else(|| {
                            format!("sub-component does not export function `{name}`")
                        })?;
                    resolve_func(sub, &with_frame(&e0, parent, args), e.index, depth + 1)
                }
                Inst::Bag {
                    node: n,
                    items,
                    env: e1,
                } => {
                    let (_, _, i) = items
                        .iter()
                        .find(|(k, kind, _)| k == name && *kind == ComponentExternalKind::Func)
                        .ok_or_else(|| format!("instance has no function `{name}`"))?;
                    resolve_func(n, &e1, *i, depth + 1)
                }
            }
        }
        Some(ComponentFuncDef::Import(i)) => {
            let (p, up, arg) = bound_arg(node, env, *i, ComponentExternalKind::Func)?;
            resolve_func(p, &up, arg, depth + 1)
        }
        None => Err(format!("no component function with index {idx}")),
    }
}

/// Prune `merged.exports` to the outer world of `original_components`.
///
/// `component_to_input` maps each flattened component to the input it came
/// from, which gives each input's first flattened index.
pub fn prune_to_world(
    merged: &mut MergedModule,
    components: &[ParsedComponent],
    original_components: &[ParsedComponent],
    component_to_input: &[usize],
) -> Result<WorldPlan> {
    // ---- 1. The world's functions, each traced to its lift ------------------
    // (world name, instance name or None, lift)
    let mut world: Vec<(String, Option<String>, LiftRef<'_>)> = Vec::new();
    let nodes: Vec<Node<'_>> = original_components
        .iter()
        .enumerate()
        .map(|(inp, orig)| {
            let base = component_to_input
                .iter()
                .position(|&i| i == inp)
                .ok_or_else(|| refuse(format!("input {inp} contributed no components")))?;
            Ok(build_node(orig, base))
        })
        .collect::<Result<_>>()?;

    for node in &nodes {
        for export in &node.comp.exports {
            match export.kind {
                ComponentExternalKind::Func => {
                    let lift = resolve_func(node, &[], export.index, 0).map_err(|why| {
                        refuse(format!("world function `{}`: {why}", export.name))
                    })?;
                    world.push((export.name.clone(), None, lift));
                }
                ComponentExternalKind::Instance => {
                    let inst = resolve_instance(node, &[], export.index, 0).map_err(|why| {
                        refuse(format!("world interface `{}`: {why}", export.name))
                    })?;
                    // The functions of the interface, each with the component
                    // and environment to resolve it in.
                    type IfaceFunc<'a> = (String, &'a Node<'a>, Vec<Frame<'a>>, u32);
                    let mut funcs: Vec<IfaceFunc<'_>> = Vec::new();
                    match inst {
                        Inst::Bag {
                            node: n,
                            items,
                            env,
                        } => {
                            for (fname, kind, fidx) in items {
                                if *kind == ComponentExternalKind::Func {
                                    funcs.push((fname.clone(), n, env.clone(), *fidx));
                                }
                            }
                        }
                        Inst::Instantiated {
                            sub,
                            args,
                            parent,
                            env,
                        } => {
                            let env2 = with_frame(&env, parent, args);
                            for e in &sub.comp.exports {
                                if e.kind == ComponentExternalKind::Func {
                                    funcs.push((e.name.clone(), sub, env2.clone(), e.index));
                                }
                            }
                        }
                    }
                    for (fname, n, env, fidx) in funcs {
                        let full = format!("{}#{fname}", export.name);
                        let lift = resolve_func(n, &env, fidx, 0)
                            .map_err(|why| refuse(format!("world function `{full}`: {why}")))?;
                        world.push((full, Some(export.name.clone()), lift));
                    }
                }
                // Types, modules, components and values have no core export.
                _ => {}
            }
        }
    }

    // ---- 2. Each world function's fused index; the world names are unique ---
    let mut targets: BTreeMap<String, u32> = BTreeMap::new();
    let mut plan = WorldPlan::default();
    let mut needed_memories: BTreeSet<u32> = BTreeSet::new();
    // (owner component, fused function index)
    let mut needed_reallocs: BTreeSet<(usize, u32)> = BTreeSet::new();
    let mut support_funcs: BTreeSet<u32> = BTreeSet::new();
    let fused_memory_count = merged.memories.len();

    for (name, _, lift) in &world {
        let owner = components.get(lift.flat).ok_or_else(|| {
            refuse(format!(
                "world function `{name}`: lift in unknown component"
            ))
        })?;
        let (_, m, l) = locate_core_func(owner, lift.core_func).ok_or_else(|| {
            refuse(format!(
                "world function `{name}` is lifted from a core function that is not defined by a \
                 core module of its component"
            ))
        })?;
        let fused = fused_index_of(merged, (lift.flat, m, l)).ok_or_else(|| {
            refuse(format!(
                "world function `{name}` has no counterpart in the fused module"
            ))
        })?;
        if let Some(prev) = targets.insert(name.clone(), fused)
            && prev != fused
        {
            return Err(refuse(format!(
                "world function `{name}` is implemented by two different functions \
                 ({prev} and {fused}); refusing to pick one"
            )));
        }
        plan.lifts.insert((lift.flat, lift.core_func), name.clone());

        if let Some(mem) = lift.options.memory {
            let fused_mem = crate::component_wrap::resolve_source_memory(
                owner,
                components,
                merged,
                fused_memory_count,
                mem,
            )
            .map_err(|e| refuse(format!("world function `{name}`: {e}")))?;
            needed_memories.insert(fused_mem);
        }
        if let Some(r) = lift.options.realloc {
            let fr = crate::component_wrap::resolve_source_realloc(owner, lift.flat, merged, r)
                .map_err(|e| refuse(format!("world function `{name}`: {e}")))?;
            needed_reallocs.insert((lift.flat, fr));
        }
        if let Some(p) = lift.options.post_return {
            let fp = crate::component_wrap::resolve_source_realloc(owner, lift.flat, merged, p)
                .map_err(|e| refuse(format!("world function `{name}`: post-return: {e}")))?;
            support_funcs.insert(fp);
        }
    }

    // Every target must be carried by some existing export of the fused module.
    for (name, &fused) in &targets {
        if !merged
            .exports
            .iter()
            .any(|e| matches!(e.kind, ExportKind::Func) && e.index == fused)
        {
            return Err(refuse(format!(
                "world function `{name}` is fused function {fused}, which no export of the \
                 fused module carries"
            )));
        }
    }

    // ---- 3. What the remaining imports need ---------------------------------
    let mut dtor_names: HashSet<String> = HashSet::new();
    let mut func_import = 0usize;
    for import in &merged.imports {
        if !matches!(import.entity_type, EntityType::Function(_)) {
            continue;
        }
        let slot = merged.import_lower_sites.get(func_import);
        func_import += 1;
        let who = format!("{}::{}", import.module, import.name);

        for prefix in ["[resource-new]", "[resource-rep]", "[resource-drop]"] {
            if let Some(resource) = import.name.strip_prefix(prefix) {
                let iface = import
                    .module
                    .strip_prefix("[export]")
                    .unwrap_or(&import.module);
                dtor_names.insert(format!("{iface}#[dtor]{resource}"));
            }
        }

        let Some(slot) = slot else { continue };
        // Resource intrinsics are not `canon lower`s of a function: nothing to
        // trace, and no memory or realloc to keep.
        if import.name.starts_with("[resource-") {
            continue;
        }
        if let Some(first) = slot.untraced.first() {
            return Err(refuse(format!(
                "the canon lower behind fused import {who} ({first}) could not be traced, so \
                 the memory and realloc it needs cannot be kept"
            )));
        }
        if slot.sites.is_empty() {
            continue;
        }
        let spec = crate::component_wrap::resolve_lower_spec(
            components,
            merged,
            fused_memory_count,
            &slot.sites,
        )
        .map_err(|e| refuse(format!("import {who}: {e}")))?;
        if let Some(spec) = spec {
            if let Some(m) = spec.memory {
                needed_memories.insert(m);
            }
            if let Some(r) = spec.realloc {
                let owner = slot.sites[0].0;
                needed_reallocs.insert((owner, r));
            }
        }
    }
    for iface in world.iter().filter_map(|(_, i, _)| i.as_ref()) {
        // `[dtor]` of an interface the world exports (a resource it hands out).
        dtor_names.insert(format!("{iface}#[dtor]"));
    }
    let is_dtor = |name: &str| {
        dtor_names.contains(name)
            || dtor_names
                .iter()
                .any(|d| d.ends_with("#[dtor]") && name.starts_with(d.as_str()))
    };
    // (A dtor entry ending in `#[dtor]` is an interface prefix; one with a
    // resource name after it is an exact export name.)

    for (_, r) in &needed_reallocs {
        support_funcs.insert(*r);
    }
    if let Some(start) = merged.start_function {
        support_funcs.insert(start);
    }

    // ---- 4. Assemble the export list ----------------------------------------
    let world_names: HashSet<&str> = targets.keys().map(String::as_str).collect();
    let mut out: Vec<MergedExport> = Vec::new();
    for e in &merged.exports {
        let keep = match e.kind {
            ExportKind::Func => {
                if world_names.contains(e.name.as_str()) {
                    // The world name stays only on the world function.
                    targets.get(&e.name) == Some(&e.index)
                } else {
                    // A dtor or a support function stays. Anything else —
                    // including an internal alias of a world function — is
                    // dropped: the world name is the one that survives.
                    is_dtor(&e.name) || support_funcs.contains(&e.index)
                }
            }
            ExportKind::Memory => needed_memories.contains(&e.index),
            _ => false,
        };
        if keep {
            out.push(e.clone());
        }
    }
    // A world name the fused module did not already carry on the right
    // function: export it, so the world name never points elsewhere.
    for (name, &fused) in &targets {
        if !out
            .iter()
            .any(|e| matches!(e.kind, ExportKind::Func) && e.name == *name && e.index == fused)
        {
            out.push(MergedExport {
                name: name.clone(),
                kind: ExportKind::Func,
                index: fused,
            });
        }
    }
    // A needed realloc nothing exports gets the SR-81 name, manifest or not.
    for &(owner, fused) in &needed_reallocs {
        if !out
            .iter()
            .any(|e| matches!(e.kind, ExportKind::Func) && e.index == fused)
        {
            let mut name = format!("meld:realloc/{owner}");
            let mut n = 0;
            while out.iter().any(|e| e.name == name) {
                n += 1;
                name = format!("meld:realloc/{owner}_{n}");
            }
            out.push(MergedExport {
                name,
                kind: ExportKind::Func,
                index: fused,
            });
        }
    }
    // A needed memory nothing exports is an error: the host could not reach it.
    for &mem in &needed_memories {
        if !out
            .iter()
            .any(|e| matches!(e.kind, ExportKind::Memory) && e.index == mem)
        {
            return Err(refuse(format!(
                "memory {mem} is named by a kept lift or a remaining import's lower but the \
                 fused module exports it under no name; a host could not service them"
            )));
        }
    }

    merged.exports = out;
    Ok(plan)
}
