//! #461: passes that run after the merge regenerate a module's function bodies
//! from its original bytes. They build their `IndexMaps` only through
//! [`index_maps_for_rerewrite`], which replays the record the main merge loop
//! left in [`MergedModule::rewrite_params`]. These tests pin the property that
//! makes that safe: replaying the record reproduces the merged bodies exactly,
//! for every merged module, including ones placed at a non-zero shared-memory
//! base with a relocation plan.

use super::*;
use wasm_encoder::Encode;

const FIXTURES: [&str; 3] = [
    "falcon_cascade_estimator_cm.wasm",
    "falcon_cascade_control_cm.wasm",
    "falcon_cascade_split_cm.wasm",
];

/// cpetig's three components from #461, merged under shared memory with
/// address rebasing. Returns the fuser (which owns the flattened components)
/// alongside the merge result.
fn merged_461() -> (crate::Fuser, MergedModule) {
    let mut fuser = crate::Fuser::new(crate::FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        ..Default::default()
    });
    for name in FIXTURES {
        let path = format!(
            "{}/tests/fixtures/issue_461/{name}",
            env!("CARGO_MANIFEST_DIR")
        );
        let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
        fuser
            .add_component_named(&bytes, Some(name))
            .unwrap_or_else(|e| panic!("add {name}: {e}"));
    }
    let graph = crate::resolver::Resolver::with_strategy(MemoryStrategy::SharedMemory)
        .with_domains(fuser.component_domains())
        .resolve_with_hints(&fuser.components, &fuser.wiring_hints)
        .expect("resolve");
    let merged = Merger::new(MemoryStrategy::SharedMemory, true)
        .with_domains(fuser.component_domains())
        .merge(&fuser.components, &graph)
        .expect("merge");
    (fuser, merged)
}

fn encoded(body: &Function) -> Vec<u8> {
    let mut out = Vec::new();
    body.encode(&mut out);
    out
}

/// Regenerate every defined function of one module with `maps`, the way the
/// post-merge passes do, and pair each with the body the merge produced.
fn regenerated_vs_merged(
    merged: &MergedModule,
    comp_idx: usize,
    mod_idx: usize,
    module: &CoreModule,
    maps: &IndexMaps,
) -> Vec<(Vec<u8>, Vec<u8>)> {
    let import_func_count = module
        .imports
        .iter()
        .filter(|i| matches!(i.kind, ImportKind::Function(_)))
        .count() as u32;
    let mut pairs = Vec::new();
    for (old_idx, &type_idx) in module.functions.iter().enumerate() {
        let param_count = module
            .types
            .get(type_idx as usize)
            .map(|ty| ty.params.len() as u32)
            .unwrap_or(0);
        let regenerated =
            extract_function_body(module, old_idx, param_count, maps).expect("regenerate body");
        let origin = (comp_idx, mod_idx, import_func_count + old_idx as u32);
        let merged_fn = merged
            .functions
            .iter()
            .find(|f| f.origin == origin)
            .unwrap_or_else(|| panic!("no merged function with origin {origin:?}"));
        pairs.push((encoded(&regenerated), encoded(&merged_fn.body)));
    }
    pairs
}

/// The modules the old passes got wrong: placed above 0, with a reloc plan.
fn rebased_modules(merged: &MergedModule) -> Vec<(usize, usize)> {
    let mut keys: Vec<_> = merged
        .rewrite_params
        .iter()
        .filter(|(_, p)| p.memory_base_offset != 0 && p.code_addr_relocs.is_some())
        .map(|(k, _)| *k)
        .collect();
    keys.sort();
    keys
}

#[test]
fn replaying_the_record_reproduces_every_merged_body() {
    let (fuser, merged) = merged_461();
    assert!(
        !rebased_modules(&merged).is_empty(),
        "no module was placed above 0 with a reloc plan, so this test could not \
         tell a correct replay from the zero-base one that caused #461"
    );

    let mut keys: Vec<_> = merged.rewrite_params.keys().copied().collect();
    keys.sort();
    let mut compared = 0usize;
    for (comp_idx, mod_idx) in keys {
        let module = &fuser.components[comp_idx].core_modules[mod_idx];
        let maps = index_maps_for_rerewrite(comp_idx, mod_idx, module, &merged)
            .expect("every merged module has a record");
        for (i, (regenerated, original)) in
            regenerated_vs_merged(&merged, comp_idx, mod_idx, module, &maps)
                .into_iter()
                .enumerate()
        {
            assert_eq!(
                regenerated, original,
                "component {comp_idx} module {mod_idx} function {i}: replaying the \
                 recorded rewrite parameters did not reproduce the merged body"
            );
            compared += 1;
        }
    }
    assert!(compared > 0, "no function bodies were compared");
}

/// Control: the parameters the post-merge passes used to hand-pick (the
/// module's real strategy and rebasing flag, but base 0 and no reloc plan) do
/// NOT reproduce a rebased module's bodies. Without this the test above could
/// pass because the comparison is insensitive to rebasing.
#[test]
fn the_old_zero_base_parameters_do_not_reproduce_a_rebased_module() {
    let (fuser, merged) = merged_461();
    let (comp_idx, mod_idx) = rebased_modules(&merged)[0];
    let module = &fuser.components[comp_idx].core_modules[mod_idx];
    let p = &merged.rewrite_params[&(comp_idx, mod_idx)];
    let old = build_index_maps_for_module(
        comp_idx,
        mod_idx,
        module,
        &merged,
        p.memory_strategy,
        p.address_rebasing,
        0,
        p.memory64,
        p.memory_initial_pages,
        p.data_segment_base,
        p.elem_segment_base,
        None,
    );
    let differing = regenerated_vs_merged(&merged, comp_idx, mod_idx, module, &old)
        .into_iter()
        .filter(|(regenerated, original)| regenerated != original)
        .count();
    assert!(
        differing > 0,
        "component {comp_idx} module {mod_idx} sits at base {} yet the zero-base \
         replay reproduced all its bodies; the comparison cannot see rebasing",
        p.memory_base_offset
    );
}

#[test]
fn a_module_without_a_record_is_an_error_not_a_default() {
    let (fuser, merged) = merged_461();
    let module = &fuser.components[0].core_modules[0];
    let err = index_maps_for_rerewrite(usize::MAX, 0, module, &merged)
        .expect_err("a missing record must not fall back to base 0");
    assert!(
        err.to_string().contains("no recorded rewrite parameters"),
        "unexpected error: {err}"
    );
}
