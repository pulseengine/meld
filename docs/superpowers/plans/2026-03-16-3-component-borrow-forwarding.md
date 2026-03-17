# 3-Component Borrow Forwarding Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix `borrow<T>` forwarding when T is defined by a third component (neither caller nor callee). The adapter must: (1) call the caller's `[resource-rep]` to extract the representation, (2) call the callee's `[resource-new]` to create a handle in the callee's table, and (3) pass the new handle to the callee.

**Scenario:** In `resource_floats` (6 components, 3 main: runner -> intermediate -> leaf), a borrow parameter on `float` crosses runner -> intermediate, but `float` is defined by `leaf`. The fused module has 3 separate `[resource-rep]float` imports:
- func 3: `[export]imports` (leaf's)
- func 28: `[export]exports` (intermediate's)
- func 69: `[export]test:resource-floats/test` (runner's)

The adapter for runner -> intermediate must use func 69 (runner's rep) and func N (intermediate's new), but the current code cannot identify func 69 as belonging to the runner.

**Root Cause:** `build_resource_import_maps` (fact.rs:49) builds a flat `(module, field) -> merged_func_idx` map with no component ownership information. When `analyze_call_site` (fact.rs:262) tries to find "a DIFFERENT module than callee's" `[resource-rep]`, it picks the first match, which may be the wrong component's import. With 3 candidates, the heuristic of "not the callee's module" is insufficient.

**Architecture:** Add a `resource_rep_by_component` field to `MergedModule` that maps `(component_idx, resource_name) -> merged_func_idx`, and a corresponding `resource_new_by_component`. Populate these during `add_unresolved_imports` when processing `[resource-rep]` / `[resource-new]` function imports. Use them in `analyze_call_site` to look up the caller's `[resource-rep]` via `site.from_component` and the callee's `[resource-new]` via `site.to_component`.

**Tech Stack:** Rust, wasmparser, wasm-encoder

---

## Problem Analysis

### Current Flow (2-component case, working)

1. **Resolver** (`resolver.rs:877-929`): `resolve_resource_positions` resolves callee's resource params to `(import_module, import_field)` pairs. Sets `callee_defines_resource = true` when callee defines T.

2. **Adapter** (`fact.rs:236-249`): `analyze_call_site` finds the callee's `[resource-rep]` by exact `(import_module, import_field)` lookup in `resource_rep_imports`. Emits `ResourceBorrowTransfer { rep_func, new_func: None }`.

3. **Codegen** (`fact.rs:68-78`): `emit_resource_borrow_phase0` calls `rep_func(handle) -> rep`, passes rep to callee.

### Current Flow (3-component case, BROKEN)

1. **Resolver** (`resolver.rs:877-929`): `resolve_resource_positions` resolves callee's resource params. Sets `callee_defines_resource = false` because callee imports T. Also resolves `caller_resource_params` against caller's resource map.

2. **Adapter** (`fact.rs:250-299`): `analyze_call_site` enters the `else` branch (line 250). Extracts `resource_name` from the callee's `import_field`. Then does:
   - **Primary search** (line 263): iterates ALL `[resource-rep]` imports looking for one with matching resource name from a DIFFERENT module than callee's. **BUG:** with 3+ components, multiple `[resource-rep]float` exist from different modules. The `.find()` picks the first match, which may be leaf's (func 3) instead of runner's (func 69).
   - **Fallback** (line 270): tries `caller_resource_params` to look up by exact `(caller_op.import_module, caller_op.import_field)`. This CAN work when `caller_resource_params` is populated, but the lookup is against `resource_rep_imports` which is a flat `(module, field) -> func_idx` map, and the caller's `(module, field)` may not have been synthesized.

3. **Synthesis gap** (`resolver.rs:1033-1114`): `synthesize_missing_resource_imports` only synthesizes imports for `resource_params` (callee-side) and `resource_results`, NOT for `caller_resource_params`. So the caller's `[resource-rep]` might not exist in the merged module's imports if no core module originally imported it.

### Three Bugs to Fix

1. **`build_resource_import_maps` has no component ownership** — cannot distinguish caller's `[resource-rep]` from leaf's.
2. **`synthesize_missing_resource_imports` ignores caller-side** — caller's `[resource-rep]` may not be synthesized.
3. **`analyze_call_site` uses heuristic matching** — "different module than callee's" is ambiguous with 3+ candidates.

---

## Chunk 1: Add Per-Component Resource Import Tracking to MergedModule

### Task 1: Add `resource_rep_by_component` and `resource_new_by_component` fields

**Files:**
- Modify: `meld-core/src/merger.rs:57-124` (MergedModule struct)

- [ ] **Step 1: Add two new fields to MergedModule**

In `meld-core/src/merger.rs`, after `import_realloc_indices` (line 123), add:

```rust
/// Maps (component_idx, resource_name) → merged function index for [resource-rep].
/// Populated during add_unresolved_imports when processing [resource-rep] function imports.
/// Used by adapter generation to find the correct component's [resource-rep].
pub resource_rep_by_component: HashMap<(usize, String), u32>,

/// Maps (component_idx, resource_name) → merged function index for [resource-new].
/// Populated during add_unresolved_imports when processing [resource-new] function imports.
/// Used by adapter generation to find the correct component's [resource-new].
pub resource_new_by_component: HashMap<(usize, String), u32>,
```

- [ ] **Step 2: Initialize the new fields in merge() constructor**

In `meld-core/src/merger.rs:428-449`, add to the `MergedModule { ... }` constructor:

```rust
resource_rep_by_component: HashMap::new(),
resource_new_by_component: HashMap::new(),
```

- [ ] **Step 3: Initialize the new fields in test helpers**

Search for other `MergedModule { ... }` constructions in test code (line ~2455) and add the fields there too:

```rust
resource_rep_by_component: HashMap::new(),
resource_new_by_component: HashMap::new(),
```

- [ ] **Step 4: Build to verify compilation**

Run: `cargo build 2>&1`
Expected: Clean build

### Task 2: Populate the maps during `add_unresolved_imports`

**Files:**
- Modify: `meld-core/src/merger.rs:1283-1417` (add_unresolved_imports method)

The key insight: `add_unresolved_imports` iterates `graph.unresolved_imports` and emits function imports. At line 1412, when it pushes a `MergedImport`, it knows:
- `unresolved.component_idx` — which component this import belongs to
- `name` — the field name (e.g., `[resource-rep]float` or `[resource-rep]float$5`)
- `func_position - 1` — the merged function index (0-based among imports)

We need to extract the resource name from the field and record the mapping.

- [ ] **Step 1: Add resource tracking after each function import is emitted**

In `meld-core/src/merger.rs`, inside the `ImportKind::Function` branch of `add_unresolved_imports`, after the `merged.imports.push(MergedImport { ... })` at line 1416, add:

```rust
// Track per-component resource import indices for adapter generation.
// The merged function index is (func_position - 1) because we
// incremented func_position before reaching this point.
let merged_func_idx = func_position - 1;
let eff_field_str = &dedup_key.1;  // effective field name (no $N suffix)
if let Some(resource_name) = eff_field_str.strip_prefix("[resource-rep]") {
    merged.resource_rep_by_component.insert(
        (unresolved.component_idx, resource_name.to_string()),
        merged_func_idx,
    );
} else if let Some(resource_name) = eff_field_str.strip_prefix("[resource-new]") {
    merged.resource_new_by_component.insert(
        (unresolved.component_idx, resource_name.to_string()),
        merged_func_idx,
    );
}
```

**Important:** Use `eff_field_str` (from `dedup_key.1`), not `name` (which may have `$N` suffix in multi-memory mode). The dedup key's field is the effective field before suffixing.

Also important: `func_position` is incremented BEFORE the import is pushed (line 1373), and its value at that point is `previous_count + 1`. But the merged function index is `func_position - 1` (0-based). Actually, re-examine: `func_position` starts at 0 and is incremented to 1 before the first import is emitted. So `func_position - 1 = 0` for the first import. This is correct.

Wait, let me re-read the flow. At line 1373, `func_position += 1` is executed. At this point `func_position` has been incremented past the import being processed. The import's merged index is `func_position - 1`. But we should double-check: the merged function index for an import at position P is simply P (since imports occupy indices 0..import_counts.func - 1). And `func_position` after increment equals P+1. So `func_position - 1 = P`. Correct.

- [ ] **Step 2: Handle dedup — when an import is deduped, also record it**

When dedup fires (line 1358, `!emitted_func.insert(dedup_key.clone())` returns false), the code `continue`s without emitting a new import. But the same merged function index should still be recorded for this component. We need to look up the deduped position.

In `compute_unresolved_import_assignments` (line 2210-2255), the dedup logic assigns the SAME position to duplicate entries. But `add_unresolved_imports` skips emitting for dupes and does `continue`. We need to add tracking before the `continue`:

```rust
if !is_type_mismatch && !emitted_func.insert(dedup_key.clone()) {
    // Duplicate with matching type — skip emitting, but still
    // record per-component resource tracking.
    // Look up the already-assigned position from the pre-computed assignments.
    if let Some(&position) = unresolved_assignments_ref.func.get(&(
        unresolved.component_idx,
        unresolved.module_idx,
        unresolved.module_name.clone(),
        unresolved.field_name.clone(),
    )) {
        let eff_field_str = &dedup_key.1;
        if let Some(resource_name) = eff_field_str.strip_prefix("[resource-rep]") {
            merged.resource_rep_by_component.insert(
                (unresolved.component_idx, resource_name.to_string()),
                position,
            );
        } else if let Some(resource_name) = eff_field_str.strip_prefix("[resource-new]") {
            merged.resource_new_by_component.insert(
                (unresolved.component_idx, resource_name.to_string()),
                position,
            );
        }
    }
    continue;
}
```

**Problem:** `add_unresolved_imports` currently does NOT have access to `unresolved_assignments`. It only takes `dedup_info`. We need to pass `unresolved_assignments` through.

- [ ] **Step 3: Pass UnresolvedImportAssignments to add_unresolved_imports**

In `meld-core/src/merger.rs`, update the `add_unresolved_imports` signature (line 1283):

```rust
fn add_unresolved_imports(
    &self,
    graph: &DependencyGraph,
    merged: &mut MergedModule,
    shared_memory_plan: Option<&SharedMemoryPlan>,
    dedup_info: &ImportDedupInfo,
    unresolved_assignments: &UnresolvedImportAssignments,  // NEW
) -> Result<()> {
```

Update the call site in `merge()` (line 466):

```rust
self.add_unresolved_imports(
    graph,
    &mut merged,
    shared_memory_plan.as_ref(),
    &dedup_info,
    &unresolved_assignments,  // NEW
)?;
```

- [ ] **Step 4: Build and run existing tests**

Run: `cargo test 2>&1`
Expected: All existing tests pass. The new fields are populated but not yet consumed.

---

## Chunk 2: Synthesize Caller-Side Resource Imports

### Task 3: Extend `synthesize_missing_resource_imports` for caller-side

**Files:**
- Modify: `meld-core/src/resolver.rs:1033-1114` (synthesize_missing_resource_imports)

Currently, `synthesize_missing_resource_imports` only collects needs from `site.requirements.resource_params` and `site.requirements.resource_results`, using `site.to_component` as the component_idx. For the 3-component case, the caller's `[resource-rep]` (from `caller_resource_params`) also needs to be synthesized.

- [ ] **Step 1: Add caller-side resource needs**

In `meld-core/src/resolver.rs`, inside `synthesize_missing_resource_imports`, after the loop that collects callee-side needs (line 1041-1056), add:

```rust
// Also collect caller-side resource imports needed for 3-component chains.
// When callee_defines_resource is false, the adapter uses the CALLER's
// [resource-rep] and the CALLEE's [resource-new]. The callee's [resource-new]
// is already covered above (via resource_params with "[resource-rep]" →
// we need to also synthesize the [resource-new] counterpart and the
// caller's [resource-rep]).
for site in &graph.adapter_sites {
    for op in &site.requirements.caller_resource_params {
        needed.push((
            op.import_module.clone(),
            op.import_field.clone(),
            site.from_component,  // CALLER component
        ));
    }
    // For 3-component chains, also synthesize callee's [resource-new]
    // (the callee's resource_params has [resource-rep] entries, but
    // the adapter also needs [resource-new] for the same resource).
    for op in &site.requirements.resource_params {
        if !op.is_owned && !op.callee_defines_resource {
            let new_field = op.import_field.replace("[resource-rep]", "[resource-new]");
            needed.push((
                op.import_module.clone(),
                new_field,
                site.to_component,
            ));
        }
    }
}
```

- [ ] **Step 2: Build and verify**

Run: `cargo build 2>&1`
Expected: Clean build

- [ ] **Step 3: Run tests**

Run: `cargo test 2>&1`
Expected: All existing tests pass

---

## Chunk 3: Use Per-Component Maps in Adapter Generation

### Task 4: Write failing test for 3-component borrow forwarding

**Files:**
- Modify: `meld-core/tests/wit_bindgen_runtime.rs`

- [ ] **Step 1: Promote resource_floats to runtime_test**

In `meld-core/tests/wit_bindgen_runtime.rs`, find:

```rust
// resource_floats: 3-component borrow forwarding needs caller→callee handle transfer
fuse_only_test!(test_fuse_wit_bindgen_resource_floats, "resource_floats");
```

Replace with:

```rust
runtime_test!(test_runtime_wit_bindgen_resource_floats, "resource_floats");
```

- [ ] **Step 2: Run the test to confirm it fails**

Run: `cargo test --package meld-core --test wit_bindgen_runtime resource_floats -- --nocapture 2>&1`
Expected: FAIL (runtime trap or wrong resource handle). This is our regression test.

### Task 5: Refactor `analyze_call_site` to use per-component maps

**Files:**
- Modify: `meld-core/src/adapter/fact.rs:132-303` (analyze_call_site)

The current approach passes flat `resource_rep_imports` / `resource_new_imports` maps. We need to also pass (or access) the per-component maps from `MergedModule`.

- [ ] **Step 1: Simplify the 3-component branch in analyze_call_site**

Replace the entire `else` block (lines 250-299) with a direct lookup using the per-component maps:

```rust
} else {
    // 3-component case: neither caller nor callee defines the resource.
    //
    // Step 1: caller's [resource-rep](handle) → rep
    //   Use merged.resource_rep_by_component keyed by (from_component, resource_name)
    //
    // Step 2: callee's [resource-new](rep) → new_handle
    //   Use merged.resource_new_by_component keyed by (to_component, resource_name)
    //
    // Step 3: pass new_handle to callee
    let resource_name = op
        .import_field
        .strip_prefix("[resource-rep]")
        .unwrap_or(&op.import_field);

    // Look up caller's [resource-rep] by component index
    let caller_rep_func = merged
        .resource_rep_by_component
        .get(&(site.from_component, resource_name.to_string()))
        .copied()
        .or_else(|| {
            // Fallback: try caller_resource_params exact match
            caller_ops.get(&op.flat_idx).and_then(|caller_op| {
                resource_rep_imports
                    .get(&(caller_op.import_module.clone(), caller_op.import_field.clone()))
                    .copied()
            })
        })
        .or_else(|| {
            // Last resort: original heuristic (different module than callee's)
            resource_rep_imports
                .iter()
                .find(|((module, field), _)| {
                    field.ends_with(resource_name)
                        && field.starts_with("[resource-rep]")
                        && *module != op.import_module
                })
                .map(|(_, &idx)| idx)
        });

    // Look up callee's [resource-new] by component index
    let callee_new_func = merged
        .resource_new_by_component
        .get(&(site.to_component, resource_name.to_string()))
        .copied()
        .or_else(|| {
            // Fallback: original lookup
            let new_field = op.import_field.replace("[resource-rep]", "[resource-new]");
            resource_new_imports
                .get(&(op.import_module.clone(), new_field))
                .copied()
        });

    if let Some(rep_func) = caller_rep_func {
        options
            .resource_rep_calls
            .push(super::ResourceBorrowTransfer {
                param_idx: op.flat_idx,
                rep_func,
                new_func: callee_new_func,
            });
    } else {
        log::warn!(
            "3-component borrow forwarding: no caller [resource-rep] found for \
             resource '{}' (from_component={}, to_component={})",
            resource_name,
            site.from_component,
            site.to_component,
        );
    }
}
```

**Layered fallback strategy:**
1. **Primary:** `resource_rep_by_component` with exact `(from_component, resource_name)` key.
2. **Secondary:** `caller_resource_params` exact `(module, field)` from resolver data.
3. **Tertiary:** Original heuristic ("different module") for backward compatibility.

The primary path is the new, correct behavior. Fallbacks ensure no regression for edge cases where the new maps might not be populated (e.g., if synthesis was skipped).

- [ ] **Step 2: Build and verify compilation**

Run: `cargo build 2>&1`
Expected: Clean build

### Task 6: Verify the fix works end-to-end

- [ ] **Step 1: Run the promoted resource_floats test**

Run: `cargo test --package meld-core --test wit_bindgen_runtime resource_floats -- --nocapture 2>&1`
Expected: PASS

- [ ] **Step 2: Run the full test suite**

Run: `cargo test 2>&1`
Expected: All tests pass

- [ ] **Step 3: Run clippy**

Run: `cargo clippy --all-targets 2>&1`
Expected: No warnings

---

## Chunk 4: Edge Cases and Robustness

### Task 7: Handle P2 wrapper components

**Context:** In the `resource_floats` fixture, runner (comp 5) has NO `[resource-rep]` canonical entry. Its handles live in the P2 wrapper's `[export]test:resource-floats/test` instance (func 69). The P2 wrapper is a DIFFERENT component than the runner's main module.

The `caller_resource_map` (built by `build_resource_type_to_import` in the resolver) may not find a resource entry for the runner component because the canonical `ResourceRep` is in the wrapper component, not in the runner's component.

- [ ] **Step 1: Verify that unresolved import tracking handles the wrapper case**

During `add_unresolved_imports`, the unresolved import for `[resource-rep]float` with `component_idx` matching the runner should exist (either originally or via synthesis). Check that `resource_rep_by_component` is populated correctly.

Add a debug log in the population code (Task 2, Step 1):

```rust
log::debug!(
    "resource_rep_by_component: comp={}, resource={}, merged_func={}",
    unresolved.component_idx,
    resource_name,
    merged_func_idx,
);
```

Run: `RUST_LOG=debug cargo test --package meld-core --test wit_bindgen_runtime resource_floats -- --nocapture 2>&1`

Examine logs to verify the runner's component index maps to the correct `[resource-rep]float` merged function index.

- [ ] **Step 2: If runner's [resource-rep] is not being tracked correctly**

The issue may be that the unresolved import for runner's `[resource-rep]float` has `component_idx` equal to the P2 WRAPPER's component index, not the runner's main component index. In that case, the lookup `(site.from_component, "float")` would fail because `site.from_component` is the runner and the import is registered under the wrapper.

**Fix:** In `add_unresolved_imports`, when recording `resource_rep_by_component`, also check if this import's module name matches a known wrapper pattern (e.g., `[export]test:*`) and record it under the wrapped component's index as well.

Alternative (simpler): In `analyze_call_site`, when the primary lookup fails, iterate all entries in `resource_rep_by_component` with matching resource_name and pick the one whose component was "imported by" `from_component`. This requires no new data but is less precise.

**Decision:** Defer this to runtime testing. If the unresolved imports' `component_idx` already correctly identifies the wrapper's component index as the runner's environment (which is likely since the P2 wrapper component is composed to provide the runner's imports), then `resource_rep_by_component` keyed by the wrapper's comp_idx would need a different lookup. The fallback chain in Task 5 handles this case.

### Task 8: Unit test for per-component resource map population

**Files:**
- Modify: `meld-core/src/merger.rs` (test module, line ~2700+)

- [ ] **Step 1: Write a unit test that verifies resource_rep_by_component is populated**

Add a test that creates a DependencyGraph with unresolved imports containing `[resource-rep]foo` for two different components, merges them, and checks that `resource_rep_by_component` has the correct mapping:

```rust
#[test]
fn test_resource_rep_by_component_populated() {
    // Create a graph with two components, each having a [resource-rep]foo import
    // from different modules. Verify that after merge, resource_rep_by_component
    // maps (comp_0, "foo") and (comp_1, "foo") to different merged func indices.

    // Setup: two components with minimal core modules...
    // (follow existing test patterns in the file, e.g., test_unresolved_import_dedup)

    // Assert:
    // assert!(merged.resource_rep_by_component.contains_key(&(0, "foo".to_string())));
    // assert!(merged.resource_rep_by_component.contains_key(&(1, "foo".to_string())));
    // assert_ne!(
    //     merged.resource_rep_by_component[&(0, "foo".to_string())],
    //     merged.resource_rep_by_component[&(1, "foo".to_string())],
    // );
}
```

- [ ] **Step 2: Run the test**

Run: `cargo test --package meld-core test_resource_rep_by_component -- --nocapture 2>&1`
Expected: PASS

---

## Chunk 5: Final Verification and Cleanup

### Task 9: Verify all resource fixtures

- [ ] **Step 1: Run all resource-related fixture tests**

```bash
cargo test --package meld-core --test wit_bindgen_runtime resource -- --nocapture 2>&1
```

Expected: All resource tests pass (resources, resource_alias, resource_aggregates, resource_floats, resource_borrow_in_record, etc.)

- [ ] **Step 2: Run the full test suite**

```bash
cargo test 2>&1
```

Expected: All tests pass

- [ ] **Step 3: Run clippy**

```bash
cargo clippy --all-targets 2>&1
```

Expected: No warnings

### Task 10: Commit

- [ ] **Step 1: Stage and commit**

```bash
git add \
    meld-core/src/merger.rs \
    meld-core/src/resolver.rs \
    meld-core/src/adapter/fact.rs \
    meld-core/tests/wit_bindgen_runtime.rs
git commit -m "fix: 3-component borrow forwarding with per-component resource tracking

When borrow<T> crosses an adapter where neither caller nor callee defines
T (T defined by a third component), the adapter must use the caller's
[resource-rep] to extract the representation and the callee's [resource-new]
to create a handle in the callee's table.

Previously, the adapter generator used a flat (module, field) map for
resource imports and a heuristic ('different module than callee') to find
the caller's [resource-rep]. With 3+ components, multiple [resource-rep]
imports exist and the heuristic picked the wrong one.

Changes:
- Add resource_rep_by_component and resource_new_by_component fields to
  MergedModule, mapping (component_idx, resource_name) to merged func idx
- Populate these maps during add_unresolved_imports
- Extend synthesize_missing_resource_imports to synthesize caller-side
  [resource-rep] and callee-side [resource-new] for 3-component chains
- Refactor analyze_call_site to use per-component maps with layered
  fallback for backward compatibility

Fixes: resource_floats fixture (3-component borrow forwarding)"
```

---

## Appendix: Key File Locations

| File | Lines | What to Change |
|------|-------|---------------|
| `meld-core/src/merger.rs` | 57-124 | Add `resource_rep_by_component`, `resource_new_by_component` to MergedModule |
| `meld-core/src/merger.rs` | 428-449 | Initialize new fields in merge() constructor |
| `meld-core/src/merger.rs` | 1283-1417 | Populate maps in add_unresolved_imports; pass assignments through |
| `meld-core/src/merger.rs` | ~2455 | Initialize new fields in test helper |
| `meld-core/src/resolver.rs` | 1033-1114 | Extend synthesize_missing_resource_imports for caller-side |
| `meld-core/src/adapter/fact.rs` | 250-299 | Replace heuristic with per-component map lookup |
| `meld-core/tests/wit_bindgen_runtime.rs` | ~654 | Promote resource_floats to runtime_test |

## Appendix: Data Flow Diagram

```
                    RESOLVER (resolve)
                        │
                        ├─ resolve_resource_positions(callee_map, ...) → resource_params
                        ├─ resolve_resource_positions(caller_map, ...) → caller_resource_params
                        └─ synthesize_missing_resource_imports
                              ├─ callee: resource_params → [resource-rep] imports
                              ├─ callee: resource_params (non-owned, !callee_defines) → [resource-new] imports  ← NEW
                              └─ caller: caller_resource_params → [resource-rep] imports  ← NEW

                    MERGER (merge)
                        │
                        ├─ compute_unresolved_import_assignments → positions
                        └─ add_unresolved_imports
                              ├─ emit MergedImport for each unresolved
                              ├─ populate import_memory_indices, import_realloc_indices
                              └─ populate resource_rep_by_component, resource_new_by_component  ← NEW

                    ADAPTER (generate)
                        │
                        ├─ build_resource_import_maps → flat (module, field) → func_idx  (EXISTING, kept as fallback)
                        └─ analyze_call_site
                              └─ 3-component branch:
                                    ├─ PRIMARY:  merged.resource_rep_by_component[(from_comp, name)]  ← NEW
                                    ├─ FALLBACK: caller_resource_params exact match  (EXISTING)
                                    └─ LAST:     heuristic "different module"  (EXISTING)
```
