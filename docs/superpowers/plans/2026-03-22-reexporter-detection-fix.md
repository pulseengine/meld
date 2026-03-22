# Fix Re-exporter Detection for own<T> Result Transfers

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix `callee_defines_resource` detection for re-exporting intermediates so own<T> result transfers work in 3-component chains, unblocking resource_floats and xcrate fixtures.

**Architecture:** Replace `is_reexporter()` (checks graph edge type, fails for cross-name re-exports) with `imports_resource_from_definer()` (follows ResolvesTo edges to check if import target is a known definer). The synthesis and merger wiring already handle `callee_defines_resource=false` correctly — they just need the right value.

**Tech Stack:** Rust, petgraph

---

## Task 1: Add `imports_resource_from_definer` to ResourceGraph

**Files:**
- Modify: `meld-core/src/resource_graph.rs` (after `is_reexporter`, ~line 385)

- [ ] **Step 1: Add the method**

After `is_reexporter`, add:

```rust
/// Does this component import the given resource from a component that IS
/// the known definer? If so, this component is a re-exporter — not a definer.
///
/// Follows `ResolvesTo` edges from this component to find target components,
/// then checks if any target is in `defines_cache` for this resource name.
/// Correctly distinguishes:
/// - resource_floats comp 3: imports "float" from comp 0 (definer) → true
/// - xcrate comp 0: imports from another comp that is NOT the "x" definer → false
pub fn imports_resource_from_definer(&self, comp_idx: usize, resource_name: &str) -> bool {
    if let Some(&comp_node) = self.comp_nodes.get(&comp_idx) {
        for edge in self
            .graph
            .edges_directed(comp_node, petgraph::Direction::Outgoing)
        {
            if let GraphEdge::ResolvesTo { .. } = edge.weight() {
                if let GraphNode::Component(target_comp) = self.graph[edge.target()] {
                    if target_comp == comp_idx {
                        continue; // skip self-imports
                    }
                    let target_defines = self
                        .defines_cache
                        .keys()
                        .any(|(idx, _, rn)| *idx == target_comp && rn == resource_name);
                    if target_defines {
                        return true;
                    }
                }
            }
        }
    }
    false
}
```

- [ ] **Step 2: Build to verify**

Run: `cargo build 2>&1 | tail -3`
Expected: Clean build

- [ ] **Step 3: Commit**

## Task 2: Use `imports_resource_from_definer` in graph override (per-function path)

**Files:**
- Modify: `meld-core/src/resolver.rs:2116-2131` (per-function path graph override)

- [ ] **Step 1: Replace `is_reexporter` with `imports_resource_from_definer`**

At line ~2116 and ~2128, change:

```rust
// BEFORE:
} else if rg.is_reexporter(*to_comp, iface, rn) {
    op.callee_defines_resource = false;
}

// AFTER:
} else if rg.imports_resource_from_definer(*to_comp, rn) {
    op.callee_defines_resource = false;
}
```

Do this for BOTH the params loop (~2116) and results loop (~2128).

- [ ] **Step 2: Build to verify**

Run: `cargo build 2>&1 | tail -3`

- [ ] **Step 3: Commit**

## Task 3: Use `imports_resource_from_definer` in graph override (fallback path)

**Files:**
- Modify: `meld-core/src/resolver.rs:2325,2336` (fallback path graph override)

- [ ] **Step 1: Replace `is_reexporter` with `imports_resource_from_definer`**

Same change as Task 2, but in the fallback path at lines ~2325 and ~2336.

- [ ] **Step 2: Build to verify**

- [ ] **Step 3: Commit**

## Task 4: Promote resource_floats to runtime test and verify

**Files:**
- Modify: `meld-core/tests/wit_bindgen_runtime.rs:653`

- [ ] **Step 1: Change resource_floats from fuse_only to runtime**

```rust
// BEFORE:
fuse_only_test!(test_fuse_wit_bindgen_resource_floats, "resource_floats");

// AFTER:
runtime_test!(test_runtime_wit_bindgen_resource_floats, "resource_floats");
```

- [ ] **Step 2: Run resource_floats test**

Run: `cargo test --package meld-core --test wit_bindgen_runtime test_runtime_wit_bindgen_resource_floats -- --nocapture 2>&1 | tail -5`
Expected: PASS (if synthesis+wiring works) or FAIL with different error (adapter can't find rep/new func)

- [ ] **Step 3: If FAIL — check if synthesis produced the imports**

Run: `RUST_LOG=warn cargo test --package meld-core --test wit_bindgen_runtime test_runtime_wit_bindgen_resource_floats -- --nocapture 2>&1 | grep -i 'resource\|own.*result\|no callee'`

If "no callee [resource-rep]" warning appears, the synthesis didn't generate the callee's rep for the re-exporter adapters. Check that the synthesis loop at resolver.rs:1141-1147 fires for the newly-downgraded `callee_defines_resource=false` results.

**KEY ISSUE:** The synthesis runs AFTER identify_adapter_sites. Since the graph override sets `callee_defines_resource=false` during adapter site identification, the synthesis at line 1143 should automatically pick it up. If it doesn't, check whether the adapter sites are being re-created or whether the requirements are populated before the graph override runs.

- [ ] **Step 4: If PASS — run full suite for regressions**

Run: `cargo test 2>&1 | grep -E 'FAILED|test result:'`
Expected: All pass (xcrate may also be fixed by the same change)

- [ ] **Step 5: Run clippy**

Run: `cargo +stable clippy --all-targets -- -D warnings 2>&1 | tail -5`
Expected: Clean

- [ ] **Step 6: If resource_floats passes and no regressions — commit**

If xcrate also passes, update the comment at line 653 to remove resource_floats from the known failures list.

## Task 5: Final verification and PR

- [ ] **Step 1: Run full test suite**

Run: `cargo test 2>&1`
Expected: All tests pass

- [ ] **Step 2: Commit all changes**

```bash
git checkout -b fix/reexporter-detection
git add meld-core/src/resource_graph.rs meld-core/src/resolver.rs meld-core/tests/wit_bindgen_runtime.rs
git commit -m "fix: detect re-exporters via composition DAG for own<T> result transfers

Replace is_reexporter (checks graph edge type) with imports_resource_from_definer
(follows ResolvesTo edges to verify import target is a known definer). This
correctly distinguishes:
- resource_floats comp 3: imports from definer → re-exporter → callee_defines=false
- xcrate comp 0: imports from non-definer → bridge → callee_defines unchanged

The synthesis and merger wiring already handle callee_defines=false correctly.

Fixes: resource_floats, potentially xcrate"
```

- [ ] **Step 3: Push and create PR**

- [ ] **Step 4: Merge PR**
