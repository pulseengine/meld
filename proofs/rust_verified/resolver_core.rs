/// Resolver index arithmetic for rocq-of-rust translation.
///
/// This module extracts the essential index decomposition and function index
/// map computation from meld-core/src/merger.rs in a simplified form suitable
/// for formal verification with Rocq via rocq-of-rust.
///
/// The functions here use `Vec<u32>` instead of `ParsedComponent`/`CoreModule`
/// to keep the translation tractable. They capture the exact same arithmetic as
/// the real code.
///
/// Corresponding specs:
///   - proofs/transformations/merge/merge_defs.v (compute_offset, gen_remaps_for_space)
///   - proofs/rust_verified/merger_core_proofs.v (bridge lemmas)

/// Import counts for the merged module, broken down by entity kind.
#[derive(Debug, Clone, Copy, Default)]
pub struct ImportCounts {
    pub func: u32,
    pub table: u32,
    pub memory: u32,
    pub global: u32,
}

/// Decompose a flat component-level core function index into
/// (module_index, module_local_index).
///
/// `func_counts[i]` is the total function count (imports + defined) for
/// module `i` within the component.
///
/// This mirrors `decompose_component_core_func_index` in merger.rs:1049-1067.
pub fn decompose_func_index(func_counts: &[u32], index: u32) -> Option<(usize, u32)> {
    let mut running: u32 = 0;
    let mut i: usize = 0;
    while i < func_counts.len() {
        let count = func_counts[i];
        if index < running.saturating_add(count) {
            return Some((i, index - running));
        }
        running = running.saturating_add(count);
        i += 1;
    }
    None
}

/// Reconstruct a flat index from (module_index, module_local_index).
///
/// Returns `prefix_sum(func_counts[0..mod_idx]) + local_idx`.
pub fn reconstruct_func_index(func_counts: &[u32], mod_idx: usize, local_idx: u32) -> u32 {
    let mut sum: u32 = 0;
    let mut i: usize = 0;
    while i < mod_idx && i < func_counts.len() {
        sum = sum.saturating_add(func_counts[i]);
        i += 1;
    }
    sum + local_idx
}

/// Build a function index map for defined functions across all modules.
///
/// `import_count` is the number of merged (unresolved) function imports.
/// `defined_counts[i]` is the number of *defined* functions in module `i`.
///
/// Returns a flat vector of absolute wasm indices. Entry `j` in the output
/// corresponds to the `j`-th defined function in module-order traversal.
/// The absolute index is: `import_count + prefix_sum(defined_counts[0..mod]) + local_pos`.
///
/// This mirrors the core loop in `Merger::build_function_index_map` (merger.rs).
pub fn build_function_index_map(import_count: u32, defined_counts: &[u32]) -> Vec<u32> {
    let mut result = Vec::new();
    let mut cumulative_offset: u32 = 0;

    let mut mod_idx: usize = 0;
    while mod_idx < defined_counts.len() {
        let count = defined_counts[mod_idx];
        let mut pos: u32 = 0;
        while pos < count {
            result.push(import_count + cumulative_offset + pos);
            pos += 1;
        }
        cumulative_offset = cumulative_offset.saturating_add(count);
        mod_idx += 1;
    }

    result
}

/// Convert an absolute wasm function index to a defined-function array position.
///
/// Returns `None` if the index refers to an imported function (below `import_count`).
///
/// This mirrors `MergedModule::defined_func` in merger.rs:160-167.
pub fn defined_func(import_count: u32, wasm_idx: u32) -> Option<u32> {
    if wasm_idx < import_count {
        None
    } else {
        Some(wasm_idx - import_count)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decompose_roundtrip() {
        let counts = vec![3, 5, 2, 4];
        let total: u32 = counts.iter().sum();
        for index in 0..total {
            let result = decompose_func_index(&counts, index);
            assert!(result.is_some());
            let (mod_idx, local_idx) = result.unwrap();
            let reconstructed = reconstruct_func_index(&counts, mod_idx, local_idx);
            assert_eq!(reconstructed, index);
        }
    }

    #[test]
    fn test_decompose_out_of_range() {
        let counts = vec![3, 5];
        let total: u32 = counts.iter().sum();
        assert!(decompose_func_index(&counts, total).is_none());
    }

    #[test]
    fn test_build_function_index_map() {
        let import_count = 2;
        let defined_counts = vec![3, 2]; // module 0 has 3 defined, module 1 has 2
        let map = build_function_index_map(import_count, &defined_counts);
        // Module 0: indices 2, 3, 4
        // Module 1: indices 5, 6
        assert_eq!(map, vec![2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_build_function_index_map_bounded() {
        let import_count = 5u32;
        let defined_counts = vec![3, 4, 2];
        let total_defined: u32 = defined_counts.iter().sum();
        let map = build_function_index_map(import_count, &defined_counts);

        assert_eq!(map.len(), total_defined as usize);
        for &idx in &map {
            assert!(idx >= import_count);
            assert!(idx < import_count + total_defined);
        }
    }

    #[test]
    fn test_defined_func_roundtrip() {
        let import_count = 5u32;
        for pos in 0..10u32 {
            assert_eq!(defined_func(import_count, import_count + pos), Some(pos));
        }
        for idx in 0..import_count {
            assert_eq!(defined_func(import_count, idx), None);
        }
    }

    #[test]
    fn test_function_index_map_injective() {
        let import_count = 3;
        let defined_counts = vec![4, 3, 5];
        let map = build_function_index_map(import_count, &defined_counts);

        // All indices should be unique
        for i in 0..map.len() {
            for j in (i + 1)..map.len() {
                assert_ne!(map[i], map[j], "collision at positions {} and {}", i, j);
            }
        }
    }
}
