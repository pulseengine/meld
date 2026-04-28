//! Kani bounded-verification harnesses for merger index remapping and
//! component-ordering invariants.
//!
//! The in-source `merger::kani_proofs` module already covers function
//! index decompose/reconstruct round-trips and remap injectivity.  These
//! tests-directory harnesses add coverage for adjacent properties called
//! out by issue #102:
//!
//! - cyclic-dependency detection in the merger's component-order pre-pass
//! - index remapping preserves references up to a small bound
//!
//! Both are *model* harnesses: they re-implement the exact arithmetic /
//! cycle-detection algorithm the merger relies on, applied to symbolic
//! bounded inputs.  This is the standard Kani pattern for code that
//! consumes complex structs (the structs themselves can't be `kani::any`
//! cheaply, but the arithmetic kernel can).
//!
//! Run: `cargo kani --package meld-core --harness kani_merger_*`
//!
//! Tracks issue #102.

#![cfg(kani)]

/// Maximum number of components Kani will explore.  Keep this small (the
/// state space grows as O(MAX_COMPONENTS!)).
const MAX_COMPONENTS: usize = 4;
/// Maximum number of dependency edges between components.
const MAX_EDGES: usize = 6;

// ---------------------------------------------------------------------------
// Model: cycle-free DAG via Kahn's algorithm (mirrors resolver::topological_sort
// when run on acyclic edge sets — the merger consumes the result).
// ---------------------------------------------------------------------------

/// Returns `Some(order)` if the directed graph on `n` nodes with the given
/// `edges` is acyclic, where `order` is a topological sort.  Returns `None`
/// if a cycle is detected (i.e., the algorithm cannot fully drain the queue).
fn model_topological_sort(n: usize, edges: &[(usize, usize)]) -> Option<[usize; MAX_COMPONENTS]> {
    let mut in_degree = [0usize; MAX_COMPONENTS];
    for &(_from, to) in edges {
        if to < n {
            in_degree[to] += 1;
        }
    }

    let mut order = [0usize; MAX_COMPONENTS];
    let mut visited = [false; MAX_COMPONENTS];
    let mut produced: usize = 0;

    // Kahn's algorithm: repeatedly emit a zero-in-degree node and decrement
    // its successors. Bounded: at most n iterations.
    for _ in 0..MAX_COMPONENTS {
        if produced >= n {
            break;
        }
        let mut found = false;
        for i in 0..MAX_COMPONENTS {
            if i < n && !visited[i] && in_degree[i] == 0 {
                visited[i] = true;
                order[produced] = i;
                produced += 1;
                for &(from, to) in edges {
                    if from == i && to < n {
                        in_degree[to] -= 1;
                    }
                }
                found = true;
                break;
            }
        }
        if !found {
            break;
        }
    }

    if produced == n { Some(order) } else { None }
}

// ---------------------------------------------------------------------------
// Harness 1: Cycle detection — a self-loop is always reported as a cycle.
// ---------------------------------------------------------------------------

#[kani::proof]
#[kani::unwind(8)]
fn kani_merger_self_loop_is_cycle() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= MAX_COMPONENTS);

    let node: usize = kani::any();
    kani::assume(node < n);

    // Single edge: node -> node (self-loop).
    let edges = [(node, node)];
    let result = model_topological_sort(n, &edges);

    assert!(
        result.is_none() || n == 0,
        "self-loops must be reported as cycles"
    );
}

// ---------------------------------------------------------------------------
// Harness 2: Acyclic chain always sorts.
// ---------------------------------------------------------------------------

/// A linear chain 0 -> 1 -> 2 -> ... -> (n-1) is acyclic and must yield a
/// valid topological order in which `0` comes first and `n-1` comes last.
#[kani::proof]
#[kani::unwind(8)]
fn kani_merger_linear_chain_sorts() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= MAX_COMPONENTS);

    let mut edges = [(0usize, 0usize); MAX_EDGES];
    let mut edge_count = 0;
    for i in 0..(MAX_COMPONENTS - 1) {
        if i + 1 < n && edge_count < MAX_EDGES {
            edges[edge_count] = (i, i + 1);
            edge_count += 1;
        }
    }

    let result = model_topological_sort(n, &edges[..edge_count]);
    assert!(result.is_some(), "linear chain must sort");

    let order = result.unwrap();
    // `0` must be the first node emitted (only zero-in-degree node).
    assert_eq!(order[0], 0, "node 0 must come first in linear chain");
    if n > 1 {
        // The last emitted node must be `n - 1`.
        assert_eq!(
            order[n - 1],
            n - 1,
            "tail node must come last in linear chain"
        );
    }
}

// ---------------------------------------------------------------------------
// Harness 3: Index remapping preserves references.
//
// Models the merger's "rebase per-module function indices into a global
// index space" operation.  For each module `m` with offset `offsets[m]`,
// a local function index `i < counts[m]` maps to the global index
// `offsets[m] + i`.  Two distinct (module, local) pairs must not collide,
// and every reference can be inverted.
// ---------------------------------------------------------------------------

const MAX_MODS: usize = 3;
const MAX_FUNCS: u32 = 4;

#[kani::proof]
#[kani::unwind(5)]
fn kani_merger_remap_preserves_references() {
    let num_modules: usize = kani::any();
    kani::assume(num_modules > 0 && num_modules <= MAX_MODS);

    let mut counts = [0u32; MAX_MODS];
    let mut offsets = [0u32; MAX_MODS];
    let mut running: u32 = 0;
    for i in 0..MAX_MODS {
        if i < num_modules {
            counts[i] = kani::any();
            kani::assume(counts[i] > 0 && counts[i] <= MAX_FUNCS);
            offsets[i] = running;
            running = running.saturating_add(counts[i]);
        }
    }

    let total = running;
    kani::assume(total <= (MAX_MODS as u32) * MAX_FUNCS);

    // Pick any local reference (mod_idx, local_idx) and assert that the
    // forward map (compute global index) and the inverse (find which
    // module owns the global index) are consistent.
    let mod_idx: usize = kani::any();
    kani::assume(mod_idx < num_modules);
    let local_idx: u32 = kani::any();
    kani::assume(local_idx < counts[mod_idx]);

    let global = offsets[mod_idx] + local_idx;
    assert!(global < total, "remapped index in range");

    // Inverse: find which module covers `global`.
    let mut found_mod: Option<usize> = None;
    let mut found_local: u32 = 0;
    for i in 0..MAX_MODS {
        if i < num_modules && global >= offsets[i] && global < offsets[i].saturating_add(counts[i])
        {
            found_mod = Some(i);
            found_local = global - offsets[i];
            break;
        }
    }

    assert_eq!(
        found_mod,
        Some(mod_idx),
        "inverse map recovers source module"
    );
    assert_eq!(
        found_local, local_idx,
        "inverse map recovers source local index"
    );
}
