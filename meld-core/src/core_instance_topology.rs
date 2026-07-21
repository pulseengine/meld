//! Core-instance topology normalization (ADR-7 path-H, increment 3 — RFC-46 Q1).
//!
//! RFC-46 open question Q1 is *multiply-instantiated modules*: what does a fuser
//! do when a component instantiates the same core module more than once? The RFC
//! options are **reject**, **duplicate**, or **multi-module output**. meld
//! shipped "reject" first (SR-31, `DuplicateModuleInstantiation`); this module is
//! the **"duplicate"** resolution.
//!
//! ## The idea: turn N instances into N distinct modules
//!
//! The merger's index-space machinery is already proven correct for **N distinct
//! modules** — it allocates each module its own functions / memories / tables /
//! globals and rebases every index, keying its merge maps by
//! `(component_idx, module_idx, local_idx)`. "The same module instantiated N
//! times" is just a special case: give each instantiation its **own** module
//! identity and the existing machinery does the rest.
//!
//! [`expand_multiply_instantiated_modules`] does exactly that — for each 2nd..Nth
//! instantiation of a core module it appends a deep clone of that module (a fresh
//! `module_idx`) and rewrites the instantiation to reference the clone. After the
//! pass **no core module is instantiated more than once**, so:
//!
//! - each instance gets **independent** functions/memory/tables/globals — two
//!   instances cannot share mutable state (the STPA **H-1** hazard the "duplicate"
//!   option must avoid); and
//! - every `(component, module)`-keyed merge map (`segment_bases`, `realloc_map`,
//!   the resource maps, the five index maps) gets a **distinct key per instance**,
//!   so the second instance can never overwrite the first (the silent-corruption
//!   failure mode of naïve duplication).
//!
//! A component that instantiates each module at most once is returned unchanged.
//!
//! ## Status — mechanism only (activation gated)
//!
//! This pass is the *mechanism*. Wiring it into the fuse pipeline (and dropping
//! the [`crate::Error::DuplicateModuleInstantiation`] reject) flips a **verified
//! safety requirement** (SR-31) and must be gated on a differential
//! *execution* oracle proving two instances of one module keep **independent
//! mutable state** end-to-end — identical-content module duplication can stress
//! export-name and segment handling that a structural test cannot see. Until that
//! oracle lands, meld still rejects multiply-instantiated modules at fuse time;
//! this module is exercised only by its own structural unit tests.

use crate::parser::{InstanceKind, ParsedComponent};
use std::collections::HashSet;

/// Expand each 2nd..Nth instantiation of a core module into its own distinct
/// [`CoreModule`](crate::parser::CoreModule), rewriting that instantiation to
/// reference the fresh module index. Returns the number of duplicate modules
/// synthesized (0 = the component was left unchanged).
///
/// See the module docs for why this reuses the merger's proven per-module
/// machinery and cannot share mutable state or overwrite merge-map entries.
pub fn expand_multiply_instantiated_modules(component: &mut ParsedComponent) -> usize {
    let mut seen: HashSet<u32> = HashSet::new();
    let mut duplicates = 0usize;

    for i in 0..component.instances.len() {
        // Copy the instantiated module index out so the borrow is released
        // before we mutate `core_modules` / `instances` below.
        let module_idx = match &component.instances[i].kind {
            InstanceKind::Instantiate { module_idx, .. } => *module_idx,
            InstanceKind::FromExports(_) => continue,
        };

        // First instantiation of this module — nothing to do.
        if seen.insert(module_idx) {
            continue;
        }

        // Nth instantiation (N >= 2): clone the source module under a fresh
        // index. Locate the source by its recorded `.index` rather than by
        // position, so this is robust even if `core_modules` is ever non-dense.
        let Some(src_pos) = component
            .core_modules
            .iter()
            .position(|m| m.index == module_idx)
        else {
            // No matching module (malformed input) — leave it for the merger's
            // own validation to reject; don't paper over it here.
            continue;
        };

        let new_index = component.core_modules.len() as u32;
        let mut dup = component.core_modules[src_pos].clone();
        dup.index = new_index;
        component.core_modules.push(dup);
        seen.insert(new_index);

        // Point this instantiation at the fresh module so the merger sees a
        // distinct module identity for it.
        if let InstanceKind::Instantiate { module_idx, .. } = &mut component.instances[i].kind {
            *module_idx = new_index;
        }
        duplicates += 1;
    }

    duplicates
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{ComponentInstance, CoreModule, InstanceKind};

    fn mk_module(index: u32) -> CoreModule {
        CoreModule {
            index,
            bytes: vec![index as u8], // distinct marker so clones are traceable
            types: vec![],
            imports: vec![],
            exports: vec![],
            functions: vec![],
            memories: vec![],
            tables: vec![],
            globals: vec![],
            start: None,
            data_count: None,
            element_count: 0,
            custom_sections: vec![],
            code_section_range: None,
            global_section_range: None,
            element_section_range: None,
            data_section_range: None,
        }
    }

    fn instantiate(index: u32, module_idx: u32) -> ComponentInstance {
        ComponentInstance {
            index,
            kind: InstanceKind::Instantiate {
                module_idx,
                args: vec![],
            },
        }
    }

    fn mk_component(
        modules: Vec<CoreModule>,
        instances: Vec<ComponentInstance>,
    ) -> ParsedComponent {
        ParsedComponent {
            name: None,
            core_modules: modules,
            imports: vec![],
            exports: vec![],
            types: vec![],
            instances,
            canonical_functions: vec![],
            sub_components: vec![],
            component_aliases: vec![],
            component_instances: vec![],
            core_entity_order: vec![],
            component_func_defs: vec![],
            component_instance_defs: vec![],
            component_type_defs: vec![],
            original_size: 0,
            original_hash: String::new(),
            depth_0_sections: vec![],
            p3_async_features: vec![],
        }
    }

    fn module_idxs(c: &ParsedComponent) -> Vec<u32> {
        c.instances
            .iter()
            .filter_map(|i| match &i.kind {
                InstanceKind::Instantiate { module_idx, .. } => Some(*module_idx),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn single_instantiation_unchanged() {
        let mut c = mk_component(vec![mk_module(0)], vec![instantiate(0, 0)]);
        assert_eq!(expand_multiply_instantiated_modules(&mut c), 0);
        assert_eq!(c.core_modules.len(), 1);
        assert_eq!(module_idxs(&c), vec![0]);
    }

    #[test]
    fn distinct_modules_unchanged() {
        // Two different modules, each instantiated once — no duplication.
        let mut c = mk_component(
            vec![mk_module(0), mk_module(1)],
            vec![instantiate(0, 0), instantiate(1, 1)],
        );
        assert_eq!(expand_multiply_instantiated_modules(&mut c), 0);
        assert_eq!(c.core_modules.len(), 2);
        assert_eq!(module_idxs(&c), vec![0, 1]);
    }

    #[test]
    fn double_instantiation_creates_one_distinct_module() {
        let mut c = mk_component(
            vec![mk_module(0)],
            vec![instantiate(0, 0), instantiate(1, 0)],
        );
        assert_eq!(expand_multiply_instantiated_modules(&mut c), 1);
        // A fresh module was appended; the two instances now point at distinct
        // module identities.
        assert_eq!(c.core_modules.len(), 2);
        assert_eq!(module_idxs(&c), vec![0, 1]);
        // The clone is an independent deep copy of the source (same content).
        assert_eq!(c.core_modules[1].bytes, c.core_modules[0].bytes);
        assert_eq!(c.core_modules[1].index, 1);
    }

    #[test]
    fn triple_instantiation_creates_two_distinct_modules() {
        let mut c = mk_component(
            vec![mk_module(0)],
            vec![instantiate(0, 0), instantiate(1, 0), instantiate(2, 0)],
        );
        assert_eq!(expand_multiply_instantiated_modules(&mut c), 2);
        assert_eq!(c.core_modules.len(), 3);
        assert_eq!(module_idxs(&c), vec![0, 1, 2]);
    }

    #[test]
    fn interleaved_duplicate_gets_fresh_index() {
        // modules 0 and 1; instantiate 0, then 1, then 0 again.
        let mut c = mk_component(
            vec![mk_module(0), mk_module(1)],
            vec![
                instantiate(0, 0),
                instantiate(1, 1),
                instantiate(2, 0), // second instantiation of module 0
            ],
        );
        assert_eq!(expand_multiply_instantiated_modules(&mut c), 1);
        assert_eq!(c.core_modules.len(), 3);
        // Only the repeated instantiation is rewritten; it points at the clone
        // (new index 2), which is a copy of module 0.
        assert_eq!(module_idxs(&c), vec![0, 1, 2]);
        assert_eq!(c.core_modules[2].bytes, c.core_modules[0].bytes);
    }

    #[test]
    fn from_exports_instances_are_ignored() {
        // A FromExports instance is not an instantiation and must not count.
        let mut c = mk_component(
            vec![mk_module(0)],
            vec![
                instantiate(0, 0),
                ComponentInstance {
                    index: 1,
                    kind: InstanceKind::FromExports(vec![]),
                },
                instantiate(2, 0), // the real second instantiation of module 0
            ],
        );
        assert_eq!(expand_multiply_instantiated_modules(&mut c), 1);
        assert_eq!(c.core_modules.len(), 2);
    }
}
