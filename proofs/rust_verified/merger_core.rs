/// Core merger logic for rocq-of-rust translation.
///
/// This module extracts the essential offset and memory layout computation
/// from meld-core/src/merger.rs in a simplified form suitable for formal
/// verification with Rocq.
///
/// Corresponding spec: proofs/transformations/merge/merge_spec.v

/// Wasm page size: 64 KiB
pub const WASM_PAGE_SIZE: u64 = 65536;

/// Represents the count of items in each index space for a module.
/// This mirrors the per-module counts used in merge offset calculation.
#[derive(Debug, Clone, Copy, Default)]
pub struct SpaceCounts {
    pub types: u32,
    pub funcs: u32,
    pub tables: u32,
    pub mems: u32,
    pub globals: u32,
}

impl SpaceCounts {
    pub fn new(types: u32, funcs: u32, tables: u32, mems: u32, globals: u32) -> Self {
        SpaceCounts {
            types,
            funcs,
            tables,
            mems,
            globals,
        }
    }
}

/// Represents the running offsets during merge.
/// Each field tracks the next available index in that space.
#[derive(Debug, Clone, Copy, Default)]
pub struct SpaceOffsets {
    pub types: u32,
    pub funcs: u32,
    pub tables: u32,
    pub mems: u32,
    pub globals: u32,
}

impl SpaceOffsets {
    pub fn new() -> Self {
        SpaceOffsets::default()
    }

    /// Advance offsets by adding the counts from a module.
    /// Returns the new offsets after incorporating the module.
    pub fn advance(&self, counts: SpaceCounts) -> SpaceOffsets {
        SpaceOffsets {
            types: self.types + counts.types,
            funcs: self.funcs + counts.funcs,
            tables: self.tables + counts.tables,
            mems: self.mems + counts.mems,
            globals: self.globals + counts.globals,
        }
    }
}

/// Compute the offset for module at position `mod_idx` given counts for all prior modules.
/// This corresponds to `compute_offset` in merge_spec.v.
///
/// # Arguments
/// * `prior_counts` - Slice of SpaceCounts for modules 0..mod_idx
///
/// # Returns
/// The SpaceOffsets representing where this module's indices start.
pub fn compute_offsets(prior_counts: &[SpaceCounts]) -> SpaceOffsets {
    let mut offsets = SpaceOffsets::new();
    for counts in prior_counts {
        offsets = offsets.advance(*counts);
    }
    offsets
}

/// Memory layout for a single module in shared memory mode.
#[derive(Debug, Clone, Copy)]
pub struct MemoryLayout {
    /// Base address in the fused memory (in bytes)
    pub base_address: u64,
    /// Size of this module's memory region (in bytes)
    pub size: u64,
}

/// Compute memory layout for rebased shared memory.
/// Each module gets a contiguous region starting after the previous module.
///
/// # Arguments
/// * `memory_sizes` - Initial memory sizes for each module (in pages)
///
/// # Returns
/// A vector of MemoryLayout, one per module, or None if overflow occurs.
pub fn compute_memory_layout(memory_sizes: &[u64]) -> Option<Vec<MemoryLayout>> {
    let mut layouts = Vec::new();
    let mut current_base: u64 = 0;

    for &pages in memory_sizes {
        let size = pages.checked_mul(WASM_PAGE_SIZE)?;
        layouts.push(MemoryLayout {
            base_address: current_base,
            size,
        });
        current_base = current_base.checked_add(size)?;
    }

    Some(layouts)
}

/// Compute the total memory size needed for shared memory with rebasing.
///
/// # Arguments
/// * `memory_sizes` - Initial memory sizes for each module (in pages)
///
/// # Returns
/// Total pages needed, or None if overflow occurs.
pub fn compute_total_memory_pages(memory_sizes: &[u64]) -> Option<u64> {
    let mut total: u64 = 0;
    for &pages in memory_sizes {
        total = total.checked_add(pages)?;
    }
    Some(total)
}

/// Check if a memory base offset is valid for 32-bit addressing.
pub fn is_valid_32bit_base(base_bytes: u64) -> bool {
    base_bytes <= u64::from(u32::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compute_offsets_empty() {
        let offsets = compute_offsets(&[]);
        assert_eq!(offsets.types, 0);
        assert_eq!(offsets.funcs, 0);
    }

    #[test]
    fn test_compute_offsets_single() {
        let counts = [SpaceCounts::new(3, 5, 1, 1, 2)];
        let offsets = compute_offsets(&counts);
        assert_eq!(offsets.types, 3);
        assert_eq!(offsets.funcs, 5);
        assert_eq!(offsets.tables, 1);
        assert_eq!(offsets.mems, 1);
        assert_eq!(offsets.globals, 2);
    }

    #[test]
    fn test_compute_offsets_multiple() {
        let counts = [
            SpaceCounts::new(2, 3, 1, 1, 1),
            SpaceCounts::new(4, 2, 0, 0, 3),
        ];
        let offsets = compute_offsets(&counts);
        assert_eq!(offsets.types, 6);  // 2 + 4
        assert_eq!(offsets.funcs, 5);  // 3 + 2
        assert_eq!(offsets.tables, 1); // 1 + 0
        assert_eq!(offsets.mems, 1);   // 1 + 0
        assert_eq!(offsets.globals, 4); // 1 + 3
    }

    #[test]
    fn test_compute_memory_layout() {
        let sizes = [2, 3]; // 2 pages, 3 pages
        let layouts = compute_memory_layout(&sizes).unwrap();

        assert_eq!(layouts.len(), 2);
        assert_eq!(layouts[0].base_address, 0);
        assert_eq!(layouts[0].size, 2 * WASM_PAGE_SIZE);
        assert_eq!(layouts[1].base_address, 2 * WASM_PAGE_SIZE);
        assert_eq!(layouts[1].size, 3 * WASM_PAGE_SIZE);
    }

    #[test]
    fn test_compute_total_memory_pages() {
        let sizes = [2, 3, 5];
        let total = compute_total_memory_pages(&sizes).unwrap();
        assert_eq!(total, 10);
    }

    #[test]
    fn test_is_valid_32bit_base() {
        assert!(is_valid_32bit_base(0));
        assert!(is_valid_32bit_base(u64::from(u32::MAX)));
        assert!(!is_valid_32bit_base(u64::from(u32::MAX) + 1));
    }
}
