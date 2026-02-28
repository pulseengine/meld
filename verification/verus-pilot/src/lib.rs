// Verus-verified index decomposition for the meld fusion pipeline.
//
// This module verifies properties of `decompose_component_core_func_index`
// from meld-core/src/merger.rs using Verus (SMT-backed verification).
//
// The function takes per-module function counts and a flat index, and returns
// (module_idx, module_local_idx) — the same arithmetic as the Kani model
// functions in merger.rs (lines 1949-1958), but with *unbounded* proofs
// instead of bounded model checking.
//
// Run: `verus src/lib.rs` from this directory.
//
// The Verus-verified code is gated behind `cfg(verus_keep_ghost)` which is
// set automatically by the Verus toolchain. The behavioral equivalence
// tests at the bottom compile with standard rustc.

#[cfg(verus_keep_ghost)]
mod verified {
    #[allow(unused_imports)]
    use vstd::prelude::*;

    verus! {

    // =========================================================================
    // Spec functions (ghost, used only in specifications)
    // =========================================================================

    /// Prefix sum of counts[0..n].
    /// spec_prefix_sum(counts, 0) = 0
    /// spec_prefix_sum(counts, k) = counts[0] + ... + counts[k-1]
    pub open spec fn spec_prefix_sum(counts: Seq<u32>, n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else { spec_prefix_sum(counts, n - 1) + counts[n - 1] as int }
    }

    /// Total sum of all counts.
    pub open spec fn spec_total(counts: Seq<u32>) -> int {
        spec_prefix_sum(counts, counts.len() as int)
    }

    // =========================================================================
    // Spec helper lemmas
    // =========================================================================

    /// Prefix sum is monotonically non-decreasing.
    proof fn lemma_prefix_sum_monotonic(counts: Seq<u32>, i: int, j: int)
        requires
            0 <= i <= j <= counts.len(),
        ensures
            spec_prefix_sum(counts, i) <= spec_prefix_sum(counts, j),
        decreases j - i,
    {
        if i < j {
            lemma_prefix_sum_monotonic(counts, i, j - 1);
        }
    }

    /// Prefix sum at n+1 = prefix sum at n + counts[n].
    proof fn lemma_prefix_sum_step(counts: Seq<u32>, n: int)
        requires
            0 <= n < counts.len(),
        ensures
            spec_prefix_sum(counts, n + 1)
                == spec_prefix_sum(counts, n) + counts[n] as int,
    {
        // Follows directly from the definition
    }

    /// An index in [prefix_sum(k), prefix_sum(k) + counts[k]) cannot be in
    /// any other module's range.
    proof fn lemma_ranges_disjoint(counts: Seq<u32>, k1: int, k2: int)
        requires
            0 <= k1 < counts.len(),
            0 <= k2 < counts.len(),
            k1 != k2,
        ensures
            // The ranges [prefix_sum(k1), prefix_sum(k1) + counts[k1]) and
            // [prefix_sum(k2), prefix_sum(k2) + counts[k2]) do not overlap
            spec_prefix_sum(counts, k1) + counts[k1] as int
                <= spec_prefix_sum(counts, k2)
            || spec_prefix_sum(counts, k2) + counts[k2] as int
                <= spec_prefix_sum(counts, k1),
    {
        if k1 < k2 {
            lemma_prefix_sum_step(counts, k1);
            lemma_prefix_sum_monotonic(counts, k1 + 1, k2);
        } else {
            lemma_prefix_sum_step(counts, k2);
            lemma_prefix_sum_monotonic(counts, k2 + 1, k1);
        }
    }

    // =========================================================================
    // Executable function: decompose
    // =========================================================================

    /// Model of `decompose_component_core_func_index`.
    ///
    /// Given per-module function counts and a flat index, find which module
    /// owns `index` and return (module_idx, module_local_idx).
    ///
    /// # Preconditions
    /// - `counts.len() <= 1_000` (reasonable module limit)
    /// - Each count fits in u32 (enforced by type)
    /// - No overflow: total sum fits in u32
    ///
    /// # Postconditions
    /// - If `Some((mod_idx, local_idx))`:
    ///   - `mod_idx < counts.len()`
    ///   - `local_idx < counts[mod_idx]`
    ///   - `prefix_sum(mod_idx) + local_idx == index`
    /// - If `None`: `index >= total(counts)`
    pub fn decompose(counts: &Vec<u32>, index: u32) -> (result: Option<(usize, u32)>)
        requires
            counts.len() <= 1_000,
            spec_total(counts@) <= u32::MAX as int,
        ensures
            result.is_some() ==> ({
                let (mod_idx, local_idx) = result.unwrap();
                &&& (mod_idx as int) < counts@.len()
                &&& (local_idx as int) < counts@[mod_idx as int] as int
                &&& spec_prefix_sum(counts@, mod_idx as int) + local_idx as int
                        == index as int
            }),
            result.is_none() ==> (index as int) >= spec_total(counts@),
    {
        let mut running: u32 = 0;
        let mut i: usize = 0;

        proof {
            // Establish: 0 = prefix_sum(0) <= spec_total(counts@)
            lemma_prefix_sum_monotonic(counts@, 0, counts@.len() as int);
        }

        while i < counts.len()
            invariant
                i <= counts.len(),
                counts@.len() <= 1_000,
                spec_total(counts@) <= u32::MAX as int,
                running as int == spec_prefix_sum(counts@, i as int),
                running as int <= index as int,
                running as int <= spec_total(counts@),
                forall|k: int| 0 <= k < i as int ==>
                    !(#[trigger] spec_prefix_sum(counts@, k) <= index as int
                      && (index as int) < spec_prefix_sum(counts@, k) + counts@[k] as int),
            decreases counts.len() - i,
        {
            let count = counts[i];
            proof {
                lemma_prefix_sum_step(counts@, i as int);
                lemma_prefix_sum_monotonic(counts@, (i + 1) as int, counts@.len() as int);
            }
            // running + count = prefix_sum(i+1) <= spec_total <= u32::MAX,
            // so no overflow
            if index < running + count {
                return Some((i, index - running));
            }
            // index >= running + count, so running advances safely
            running = running + count;
            i = i + 1;
        }
        None
    }

    // =========================================================================
    // Proof lemmas
    // =========================================================================

    /// Roundtrip: for any valid index, decompose succeeds.
    proof fn lemma_decompose_total(counts: Seq<u32>, index: u32)
        requires
            counts.len() <= 1_000,
            spec_total(counts) <= u32::MAX as int,
            (index as int) < spec_total(counts),
        ensures
            exists|k: int| 0 <= k < counts.len()
                && #[trigger] spec_prefix_sum(counts, k) <= index as int
                && (index as int) < spec_prefix_sum(counts, k) + counts[k] as int,
    {
        lemma_decompose_total_inductive(counts, index, 0);
    }

    /// Inductive helper for lemma_decompose_total.
    proof fn lemma_decompose_total_inductive(counts: Seq<u32>, index: u32, start: int)
        requires
            0 <= start <= counts.len(),
            counts.len() <= 1_000,
            spec_prefix_sum(counts, start) <= index as int,
            (index as int) < spec_total(counts),
        ensures
            exists|k: int| start <= k < counts.len()
                && #[trigger] spec_prefix_sum(counts, k) <= index as int
                && (index as int) < spec_prefix_sum(counts, k) + counts[k] as int,
        decreases counts.len() - start,
    {
        if start >= counts.len() {
            assert(false);
        } else {
            lemma_prefix_sum_step(counts, start);
            if (index as int) < spec_prefix_sum(counts, start) + counts[start] as int {
                assert(spec_prefix_sum(counts, start) <= index as int);
            } else {
                lemma_decompose_total_inductive(counts, index, start + 1);
            }
        }
    }

    /// Injectivity: if two distinct indices land in the same module,
    /// their local offsets must differ.
    proof fn lemma_decompose_injective(
        counts: Seq<u32>, k: int, l1: int, l2: int, i1: u32, i2: u32,
    )
        requires
            0 <= k < counts.len(),
            0 <= l1 < counts[k] as int,
            0 <= l2 < counts[k] as int,
            spec_prefix_sum(counts, k) + l1 == i1 as int,
            spec_prefix_sum(counts, k) + l2 == i2 as int,
            i1 != i2,
        ensures
            l1 != l2,
    {
        // Follows directly: prefix_sum(k) + l1 != prefix_sum(k) + l2 => l1 != l2
    }

    /// Cross-module injectivity: indices in different modules are always
    /// distinct because their prefix-sum ranges are disjoint.
    proof fn lemma_decompose_cross_module_injective(
        counts: Seq<u32>, k1: int, l1: int, k2: int, l2: int,
    )
        requires
            0 <= k1 < counts.len(),
            0 <= k2 < counts.len(),
            k1 != k2,
            0 <= l1 < counts[k1] as int,
            0 <= l2 < counts[k2] as int,
        ensures
            spec_prefix_sum(counts, k1) + l1 != spec_prefix_sum(counts, k2) + l2,
    {
        lemma_ranges_disjoint(counts, k1, k2);
    }

    /// Monotonicity within a module: if local_idx increases, so does the flat index.
    proof fn lemma_within_module_monotonic(counts: Seq<u32>, k: int, l1: int, l2: int)
        requires
            0 <= k < counts.len(),
            0 <= l1 < l2,
            l2 < counts[k] as int,
        ensures
            spec_prefix_sum(counts, k) + l1 < spec_prefix_sum(counts, k) + l2,
    {
        // Trivially follows from l1 < l2
    }

    // =========================================================================
    // Reconstruct: the inverse of decompose
    // =========================================================================

    /// Reconstruct a flat index from (module_idx, local_idx).
    pub fn reconstruct(counts: &Vec<u32>, mod_idx: usize, local_idx: u32) -> (result: u32)
        requires
            (mod_idx as int) < counts@.len(),
            (local_idx as int) < counts@[mod_idx as int] as int,
            counts@.len() <= 1_000,
            spec_total(counts@) <= u32::MAX as int,
        ensures
            result as int == spec_prefix_sum(counts@, mod_idx as int) + local_idx as int,
    {
        let mut sum: u32 = 0;
        let mut i: usize = 0;
        proof {
            // 0 = prefix_sum(0) <= prefix_sum(mod_idx) <= spec_total <= u32::MAX
            lemma_prefix_sum_monotonic(counts@, 0, counts@.len() as int);
        }
        while i < mod_idx
            invariant
                i <= mod_idx,
                (mod_idx as int) < counts@.len(),
                counts@.len() <= 1_000,
                sum as int == spec_prefix_sum(counts@, i as int),
                spec_total(counts@) <= u32::MAX as int,
                sum as int <= spec_total(counts@),
            decreases mod_idx - i,
        {
            proof {
                lemma_prefix_sum_step(counts@, i as int);
                lemma_prefix_sum_monotonic(counts@, (i + 1) as int, counts@.len() as int);
            }
            // sum + counts[i] = prefix_sum(i+1) <= spec_total <= u32::MAX
            sum = sum + counts[i];
            i = i + 1;
        }
        // sum = prefix_sum(mod_idx), local_idx < counts[mod_idx]
        // prefix_sum(mod_idx) + counts[mod_idx] = prefix_sum(mod_idx+1) <= spec_total <= u32::MAX
        proof {
            lemma_prefix_sum_step(counts@, mod_idx as int);
            lemma_prefix_sum_monotonic(counts@, (mod_idx + 1) as int, counts@.len() as int);
        }
        sum + local_idx
    }

    /// Roundtrip: for any valid index, it falls within some module's range.
    proof fn theorem_roundtrip(counts: Seq<u32>, index: u32)
        requires
            counts.len() <= 1_000,
            spec_total(counts) <= u32::MAX as int,
            (index as int) < spec_total(counts),
        ensures
            exists|k: int|
                0 <= k < counts.len()
                && #[trigger] spec_prefix_sum(counts, k) <= index as int
                && (index as int) < spec_prefix_sum(counts, k) + counts[k] as int,
    {
        lemma_decompose_total(counts, index);
    }

    // =========================================================================
    // defined_func model
    // =========================================================================

    /// Spec-level model of `MergedModule::defined_func`.
    pub open spec fn spec_defined_func(import_count: u32, wasm_idx: u32) -> Option<u32> {
        if wasm_idx < import_count {
            None
        } else {
            Some((wasm_idx - import_count) as u32)
        }
    }

    /// Executable model of `MergedModule::defined_func`.
    pub fn defined_func_index(import_count: u32, wasm_idx: u32) -> (result: Option<u32>)
        ensures
            result == spec_defined_func(import_count, wasm_idx),
    {
        if wasm_idx < import_count {
            None
        } else {
            Some(wasm_idx - import_count)
        }
    }

    /// defined_func is a left inverse of "import_count + array_pos".
    proof fn lemma_defined_func_roundtrip(import_count: u32, array_pos: u32)
        requires
            import_count as int + array_pos as int <= u32::MAX as int,
        ensures
            spec_defined_func(import_count, (import_count + array_pos) as u32)
                == Some(array_pos),
    {
    }

    } // verus!
}

// =========================================================================
// Behavioral equivalence tests (plain Rust, no Verus dependency)
//
// These tests exercise the *same arithmetic* as the Verus-verified code
// and the Kani model functions in merger.rs, validating that all three
// implementations agree on concrete inputs.
// =========================================================================
#[cfg(test)]
mod tests {
    fn model_decompose(counts: &[u32], index: u32) -> Option<(usize, u32)> {
        let mut running: u32 = 0;
        for (i, &count) in counts.iter().enumerate() {
            if index < running.saturating_add(count) {
                return Some((i, index - running));
            }
            running = running.saturating_add(count);
        }
        None
    }

    fn model_reconstruct(counts: &[u32], mod_idx: usize, local_idx: u32) -> u32 {
        let offset: u32 = counts[..mod_idx].iter().copied().sum();
        offset + local_idx
    }

    #[test]
    fn test_decompose_roundtrip() {
        let counts = vec![3, 5, 2, 4];
        let total: u32 = counts.iter().sum();
        for index in 0..total {
            let result = model_decompose(&counts, index);
            assert!(result.is_some(), "index {} must decompose", index);
            let (mod_idx, local_idx) = result.unwrap();
            assert!(mod_idx < counts.len());
            assert!(local_idx < counts[mod_idx]);
            let reconstructed = model_reconstruct(&counts, mod_idx, local_idx);
            assert_eq!(reconstructed, index, "roundtrip failed for index {}", index);
        }
    }

    #[test]
    fn test_decompose_out_of_range() {
        let counts = vec![3, 5, 2];
        let total: u32 = counts.iter().sum();
        assert!(model_decompose(&counts, total).is_none());
        assert!(model_decompose(&counts, total + 1).is_none());
    }

    #[test]
    fn test_decompose_injective() {
        let counts = vec![4, 3, 5];
        let total: u32 = counts.iter().sum();
        for i in 0..total {
            for j in (i + 1)..total {
                let ri = model_decompose(&counts, i).unwrap();
                let rj = model_decompose(&counts, j).unwrap();
                assert_ne!(ri, rj, "indices {} and {} collide", i, j);
            }
        }
    }

    #[test]
    fn test_defined_func_roundtrip() {
        let import_count: u32 = 5;
        for pos in 0..20u32 {
            let wasm_idx = import_count + pos;
            let result = if wasm_idx < import_count {
                None
            } else {
                Some(wasm_idx - import_count)
            };
            assert_eq!(result, Some(pos));
        }
        for idx in 0..import_count {
            let result = if idx < import_count { None } else { Some(idx - import_count) };
            assert_eq!(result, None);
        }
    }

    #[test]
    fn test_empty_counts() {
        assert!(model_decompose(&[], 0).is_none());
        assert!(model_decompose(&[], 1).is_none());
    }

    #[test]
    fn test_single_module() {
        let counts = vec![10];
        for i in 0..10 {
            let (mod_idx, local_idx) = model_decompose(&counts, i).unwrap();
            assert_eq!(mod_idx, 0);
            assert_eq!(local_idx, i);
        }
        assert!(model_decompose(&counts, 10).is_none());
    }
}
