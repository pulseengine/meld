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
//! # What is kept
//!
//! * every fused export implementing a world export: a world function export
//!   `f` keeps the core export named `f`; a world instance export `i` keeps
//!   every core export named `i#…` — which includes that interface's
//!   `[dtor]` exports;
//! * for each kept lifted export, found **through the lift, not by guessing a
//!   name**: its `post-return`, its `realloc`, and the memory its lift names;
//! * the canonical-ABI `cabi_post_<export>` of each kept export (by name, the
//!   spelling wit-bindgen uses);
//! * the start function's export, if any.
//!
//! Everything else — including every global and table export — is dropped.
//!
//! # Refusals
//!
//! A world export with no fused counterpart is an error naming it; it is
//! never silently dropped. The mapping is by name (the fused module keeps the
//! lifted export's name), so a composition that *renames* an export on the way
//! out (`export x as "y"`) is refused rather than guessed at.

use std::collections::{HashMap, HashSet};

use wasm_encoder::ExportKind;
use wasmparser::ComponentExternalKind;

use crate::merger::MergedModule;
use crate::parser::ParsedComponent;
use crate::signature_manifest::{fused_index_of, locate_core_func};
use crate::{Error, Result};

/// Prune `merged.exports` to the outer world of `original_components`.
///
/// Returns the set of kept *lifted export names* (the world exports
/// themselves, not their support), which the signature manifest uses to
/// restrict itself to the same set.
pub fn prune_to_world(
    merged: &mut MergedModule,
    components: &[ParsedComponent],
    original_components: &[ParsedComponent],
) -> Result<HashSet<String>> {
    // 1. The world: the exports of every input. With one input this is its
    //    world; with several it is their union, because every input's exports
    //    are exports of the fused output.
    let mut unmapped: Vec<String> = Vec::new();
    let mut kept_names: HashMap<String, u32> = HashMap::new();

    for original in original_components {
        for world_export in &original.exports {
            let matches = |name: &str| match world_export.kind {
                ComponentExternalKind::Func => name == world_export.name,
                ComponentExternalKind::Instance => name
                    .strip_prefix(world_export.name.as_str())
                    .is_some_and(|rest| rest.starts_with('#')),
                // Types, modules, components and values have no core export.
                _ => false,
            };
            if !matches!(
                world_export.kind,
                ComponentExternalKind::Func | ComponentExternalKind::Instance
            ) {
                continue;
            }
            let mut found = false;
            for e in &merged.exports {
                if matches!(e.kind, ExportKind::Func) && matches(&e.name) {
                    kept_names.insert(e.name.clone(), e.index);
                    found = true;
                }
            }
            if !found {
                unmapped.push(world_export.name.clone());
            }
        }
    }

    if !unmapped.is_empty() {
        unmapped.sort();
        unmapped.dedup();
        return Err(Error::InvalidExports(format!(
            "the outer world exports {} with no matching export in the fused module. The \
             fused module keeps each lifted export's own name, so a world export that is \
             renamed on the way out, or an interface that exports only types, cannot be \
             mapped and is refused rather than dropped. Fuse without --exports world to keep \
             every export.",
            unmapped
                .iter()
                .map(|n| format!("`{n}`"))
                .collect::<Vec<_>>()
                .join(", ")
        )));
    }

    // 2. What those exports need, through their lifts.
    let mut keep_funcs: HashSet<u32> = kept_names.values().copied().collect();
    let mut keep_memories: HashSet<u32> = HashSet::new();
    let mut keep_all_memories = false;

    for (comp_idx, component) in components.iter().enumerate() {
        for (lift_func, (_, options)) in component.lift_info_by_core_func() {
            let Some((export_name, mod_idx, local_idx)) = locate_core_func(component, lift_func)
            else {
                continue;
            };
            let Some(&kept_idx) = kept_names.get(&export_name) else {
                continue;
            };
            // The name matched, but is it THIS component's function? A name
            // shared by two components must not drag in the other's support.
            if fused_index_of(merged, (comp_idx, mod_idx, local_idx)) != Some(kept_idx) {
                continue;
            }

            for support in [options.realloc, options.post_return].into_iter().flatten() {
                if let Some((_, m, l)) = locate_core_func(component, support)
                    && let Some(idx) = fused_index_of(merged, (comp_idx, m, l))
                {
                    keep_funcs.insert(idx);
                }
            }

            if let Some(core_mem) = options.memory {
                let fused_mem = crate::resolver::core_memory_sources(component)
                    .get(&core_mem)
                    .and_then(|(m, export_name)| {
                        let l = component
                            .core_modules
                            .get(*m)?
                            .exports
                            .iter()
                            .find(|e| &e.name == export_name)?
                            .index;
                        merged.memory_index_map.get(&(comp_idx, *m, l)).copied()
                    });
                match fused_mem {
                    Some(i) => {
                        keep_memories.insert(i);
                    }
                    // Cannot say which memory this lift uses: keep them all
                    // rather than pick one.
                    None => keep_all_memories = true,
                }
            }
        }
    }

    if let Some(start) = merged.start_function {
        keep_funcs.insert(start);
    }

    // 3. `cabi_post_<export>` by the spelling wit-bindgen uses, in case a lift
    //    does not name it.
    let post_names: HashSet<String> = kept_names
        .keys()
        .map(|n| format!("cabi_post_{n}"))
        .collect();

    merged.exports.retain(|e| match e.kind {
        ExportKind::Func => keep_funcs.contains(&e.index) || post_names.contains(&e.name),
        ExportKind::Memory => keep_all_memories || keep_memories.contains(&e.index),
        _ => false,
    });

    Ok(kept_names.into_keys().collect())
}
