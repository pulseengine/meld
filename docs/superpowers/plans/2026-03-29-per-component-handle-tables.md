# Per-Component Resource Handle Tables Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement per-component resource handle tables in the fused module's linear memory so that 3-component chains with re-exported resources work at runtime.

**Architecture:** Instead of relying on the P2 wrapper's canonical `resource.new`/`resource.rep` (which return sequential indices incompatible with wit-bindgen's internal ResourceTable), implement simple handle tables as i32 arrays in each component's linear memory. The handle IS a 4-byte-aligned memory address, satisfying wit-bindgen's alignment checks. The P2 wrapper routes canonical resource operations for re-exporting components to these in-memory tables.

**Tech Stack:** Rust, wasm-encoder, wasmparser, wasm-tools (for validation)

---

## Background: Why This Is Needed

The component model spec says each component instance has a per-component handle table managed by the runtime. `resource.new(rep)` stores a rep and returns a handle index. `resource.rep(handle)` retrieves the rep.

Meld replaces the runtime with the P2 wrapper's canonical resource types, which return sequential indices (1, 2, 3...). wit-bindgen 0.52.0 re-exporting components wrap these canonical functions with an internal `ResourceTable` slab. The slab allocates heap entries and uses **memory addresses** as handles. The slab code validates handles with a 4-byte alignment check (`value & 3 == 0`). Sequential canonical indices fail this check.

**Fix**: Implement handle tables as i32 arrays in each re-exporter's linear memory. Handles are byte offsets into this array (always 4-byte aligned). The P2 wrapper maps the re-exporter's `[export]::[resource-new/rep/drop]` imports to custom wasm functions that operate on these in-memory tables, rather than wasmtime's canonical types.

## File Structure

| File | Responsibility |
|------|---------------|
| `meld-core/src/merger.rs` | Allocate handle table space + globals per re-exporting component |
| `meld-core/src/adapter/fact.rs` | Emit inline handle table operations in adapters; set `caller_already_converted` for re-exporter→definer adapters |
| `meld-core/src/component_wrap.rs` | Route re-exporter canonical imports to custom handle table functions instead of `canon resource.new/rep/drop` |
| `meld-core/src/resolver.rs` | Expose re-exporter component info so merger/adapter/wrapper know which components need custom tables |
| `meld-core/tests/wit_bindgen_runtime.rs` | Promote `resource_floats` from `fuse_only_test!` to `runtime_test!` |

## Key Data Structures

### Handle Table Layout (in component's linear memory)

```
base_addr + 0:  [rep_0: i32]   ← handle = base_addr + 0 (but slot 0 reserved)
base_addr + 4:  [rep_1: i32]   ← handle = base_addr + 4
base_addr + 8:  [rep_2: i32]   ← handle = base_addr + 8
...
```

- Each entry is one i32 (4 bytes)
- Handle = absolute memory address of the entry (always 4-byte aligned)
- `resource.new(rep)`: store rep at `next_ptr`, return `next_ptr`, advance by 4
- `resource.rep(handle)`: `i32.load(handle)` from component's memory → rep
- `resource.drop(handle)`: `i32.store(handle, 0)` (mark as free; simple approach)
- Initial capacity: 256 entries = 1024 bytes (can grow via realloc if needed)

### Per-Component Handle Table Info

```rust
// New struct in resolver.rs or merger.rs
pub struct HandleTableInfo {
    /// Component index of the re-exporter
    pub component_idx: usize,
    /// Module index within the component (usually 0)
    pub module_idx: usize,
    /// Merged memory index for this component
    pub memory_idx: u32,
    /// Merged global index for the next-allocation pointer
    pub next_ptr_global: u32,
    /// Base address in linear memory where the table starts
    pub table_base_addr: u32,
    /// Number of entry slots
    pub capacity: u32,
}
```

---

### Task 1: Identify Re-Exporter Components in the Resolver

**Files:**
- Modify: `meld-core/src/resolver.rs`
- Modify: `meld-core/src/resolver.rs` (DependencyGraph struct)

The resolver already has a `resource_graph` that knows which components define vs re-export resources. Expose a list of re-exporter component indices on the DependencyGraph so downstream code can allocate handle tables for them.

- [ ] **Step 1: Add `reexporter_components` field to `DependencyGraph`**

In `meld-core/src/resolver.rs`, add to the `DependencyGraph` struct:

```rust
/// Component indices that re-export resources (need per-component handle tables).
/// These components have callee_defines_resource=false adapter sites targeting them.
pub reexporter_components: Vec<usize>,
```

- [ ] **Step 2: Populate `reexporter_components` in `resolve_with_hints`**

After `identify_adapter_sites` completes, scan adapter sites to find re-exporters:

```rust
// After identify_intra_component_adapter_sites
let mut reexporter_set: HashSet<usize> = HashSet::new();
for site in &graph.adapter_sites {
    for op in &site.requirements.resource_params {
        if !op.callee_defines_resource {
            reexporter_set.insert(site.to_component);
        }
    }
    for op in &site.requirements.resource_results {
        if !op.callee_defines_resource {
            reexporter_set.insert(site.to_component);
        }
    }
}
graph.reexporter_components = reexporter_set.into_iter().collect();
```

- [ ] **Step 3: Run tests to verify no regression**

Run: `cargo test --package meld-core`
Expected: All 73 tests pass (no behavioral change, just new field).

- [ ] **Step 4: Commit**

```
feat: identify re-exporter components in resolver
```

---

### Task 2: Allocate Handle Table Space in Merger

**Files:**
- Modify: `meld-core/src/merger.rs` (MergedModule struct, merge function)

For each re-exporter component, allocate a region in its linear memory for the handle table. Add a global variable to track the next allocation pointer.

- [ ] **Step 1: Add handle table fields to MergedModule**

```rust
/// Per-component handle table info for re-exporters.
/// Maps component_idx → HandleTableInfo.
pub handle_tables: HashMap<usize, HandleTableInfo>,
```

Where `HandleTableInfo` is:
```rust
pub struct HandleTableInfo {
    pub memory_idx: u32,
    pub next_ptr_global: u32,
    pub table_base_addr: u32,
    pub capacity: u32,
}
```

- [ ] **Step 2: After merging, allocate handle table for each re-exporter**

After all components are merged, for each re-exporter:

1. Find the component's memory index from `memory_index_map[(comp_idx, 0, 0)]`
2. Determine the memory's current data end (scan data segments for this memory to find the highest `offset + data.len()`)
3. Round up to 4-byte alignment → this is `table_base_addr`
4. Add a mutable i32 global initialized to `table_base_addr + 4` (skip slot 0 — handles start at base+4 to avoid handle=0)
5. Add a data segment for the table region (zero-initialized, `capacity * 4` bytes) — OR simply ensure the memory has enough pages
6. Store the `HandleTableInfo` in `merged.handle_tables`

- [ ] **Step 3: Emit the handle table global and ensure memory size**

The global is a `(global (mut i32) (i32.const table_base_addr+4))`. The memory might need extra pages to fit the table — check `data_end + capacity*4` vs `memory_pages * 64KB` and grow if needed.

- [ ] **Step 4: Run tests**

Run: `cargo test --package meld-core`
Expected: All 73 tests pass (new code only activates for re-exporters).

- [ ] **Step 5: Commit**

```
feat: allocate per-component handle tables in merger
```

---

### Task 3: Generate Handle Table Functions in the Fused Module

**Files:**
- Modify: `meld-core/src/merger.rs` or new file `meld-core/src/handle_table.rs`

For each re-exporter, generate three wasm functions in the fused core module:

```wasm
;; resource_new: store rep, return aligned handle
(func $ht_new_compN (param $rep i32) (result i32)
  (local $handle i32)
  global.get $ht_next_compN    ;; next allocation address
  local.set $handle
  local.get $handle
  local.get $rep
  i32.store offset=0           ;; store rep at handle address (in memory N)
  local.get $handle
  i32.const 4
  i32.add
  global.set $ht_next_compN    ;; advance by 4
  local.get $handle            ;; return handle (4-byte aligned address)
)

;; resource_rep: load rep from handle address
(func $ht_rep_compN (param $handle i32) (result i32)
  local.get $handle
  i32.load offset=0            ;; load from memory N at handle address
)

;; resource_drop: zero out entry (simple free)
(func $ht_drop_compN (param $handle i32)
  local.get $handle
  i32.const 0
  i32.store offset=0           ;; mark as freed in memory N
)
```

Note: the `i32.load`/`i32.store` instructions must specify the correct **memory index** for multi-memory mode.

- [ ] **Step 1: Create handle table function generation**

Add a function that generates the three wasm functions for a given re-exporter and appends them to `merged.functions`. Record the merged function indices in `HandleTableInfo`.

- [ ] **Step 2: Add function indices to HandleTableInfo**

```rust
pub struct HandleTableInfo {
    pub memory_idx: u32,
    pub next_ptr_global: u32,
    pub table_base_addr: u32,
    pub capacity: u32,
    pub new_func: u32,   // merged function index of ht_new
    pub rep_func: u32,   // merged function index of ht_rep
    pub drop_func: u32,  // merged function index of ht_drop
}
```

- [ ] **Step 3: Run tests**

Run: `cargo test --package meld-core`
Expected: All 73 pass (functions generated but not yet wired).

- [ ] **Step 4: Commit**

```
feat: generate per-component handle table functions
```

---

### Task 4: Route Re-Exporter Resource Imports to Handle Table Functions

**Files:**
- Modify: `meld-core/src/component_wrap.rs`

Currently, ALL `[export]interface::[resource-new/rep/drop]resource` imports are mapped to `canon resource.new/rep/drop` on a shared type. For re-exporter components, map them to the custom handle table functions instead.

- [ ] **Step 1: Pass handle table info to the P2 wrapper**

The `wrap_as_component` function needs access to `merged.handle_tables` to know which imports should use custom functions. Thread this through the existing function parameters.

- [ ] **Step 2: In `LocalResource` import resolution, check for handle table**

When processing a `LocalResource` import from a re-exporter component, instead of emitting `canon resource.new/rep/drop`, emit `core func` aliases to the custom handle table functions:

```rust
// Pseudocode for the change in component_wrap.rs
if let Some(ht_info) = handle_tables.get(&component_idx) {
    // Route to custom handle table function
    match operation {
        ResourceOp::New => alias_core_func(ht_info.new_func),
        ResourceOp::Rep => alias_core_func(ht_info.rep_func),
        ResourceOp::Drop => alias_core_func(ht_info.drop_func),
    }
} else {
    // Use canonical resource type (existing path)
    canon.resource_new(res_type_idx) / canon.resource_rep(res_type_idx) / ...
}
```

- [ ] **Step 3: Determine component_idx for each import**

The P2 wrapper processes imports in merged order. The merger's `UnresolvedImport` has `component_idx`. Thread this through the import resolution so the wrapper can check `handle_tables.contains_key(component_idx)`.

- [ ] **Step 4: Run tests**

Run: `cargo test --package meld-core`
Expected: All 73 pass. Re-exporter resource functions now use in-memory tables.

- [ ] **Step 5: Commit**

```
feat: route re-exporter resource imports to handle table functions
```

---

### Task 5: Fix Adapter `caller_already_converted` for Re-Exporter Chains

**Files:**
- Modify: `meld-core/src/resolver.rs` (double borrow detection)
- Modify: `meld-core/src/adapter/fact.rs` (analyze_call_site)

With custom handle tables, the re-exporter's code chains: slab_lookup → custom resource.rep → raw_ptr. The downstream adapter (re-exporter → definer) must NOT call resource.rep again.

- [ ] **Step 1: Set `caller_already_converted` for re-exporter→definer adapters**

In the double borrow detection section of `resolve_with_hints`, after the existing name-matching detection, add:

```rust
// For adapters FROM a re-exporter TO the definer: the re-exporter's
// code calls resource.rep internally (through its slab management).
// The downstream adapter must not call resource.rep again.
for site in &mut graph.adapter_sites {
    if graph.reexporter_components.contains(&site.from_component) {
        for op in &mut site.requirements.resource_params {
            if !op.is_owned && op.callee_defines_resource {
                op.caller_already_converted = true;
            }
        }
    }
}
```

- [ ] **Step 2: Verify with diagnostic**

Temporarily add an eprintln to verify `caller_already_converted=true` is set for the right adapter sites (comp3→comp0 for resource_floats). Remove after verification.

- [ ] **Step 3: Run tests**

Run: `cargo test --package meld-core`
Expected: All 73 pass.

- [ ] **Step 4: Commit**

```
feat: set caller_already_converted for re-exporter chains
```

---

### Task 6: Re-Enable Resource Graph Propagation (Targeted)

**Files:**
- Modify: `meld-core/src/resource_graph.rs`

The resource graph propagation (reverted due to xcrate regression) is needed to correctly set `callee_defines_resource=false` for runner→intermediate adapters. Re-implement with the `is_reexport_target` guard to prevent regressions.

- [ ] **Step 1: Add targeted propagation**

After the existing removal pass in `ResourceGraph::build`, add propagation that only activates for confirmed re-exporters:

```rust
// Only propagate when from_comp is a confirmed re-export target
// (some other component imports from it) AND the export interface
// differs from the import interface.
```

Guard: `resolved_imports.values().any(|(target, _)| *target == *from_comp)` AND `stripped_export_iface != import_name`.

- [ ] **Step 2: Run ALL tests including xcrate**

Run: `cargo test --package meld-core`
Expected: All 73 pass (including xcrate).

- [ ] **Step 3: Commit**

```
feat: propagate resource definers through re-export chains
```

---

### Task 7: Promote resource_floats to Runtime Test

**Files:**
- Modify: `meld-core/tests/wit_bindgen_runtime.rs`

- [ ] **Step 1: Change test macro**

```rust
// Before:
fuse_only_test!(test_fuse_wit_bindgen_resource_floats, "resource_floats");
// After:
runtime_test!(test_runtime_wit_bindgen_resource_floats, "resource_floats");
```

- [ ] **Step 2: Run the specific test**

Run: `cargo test --package meld-core test_runtime_wit_bindgen_resource_floats -- --nocapture`
Expected: PASS with runtime execution succeeding.

- [ ] **Step 3: Run full test suite**

Run: `cargo test --package meld-core`
Expected: All 74 tests pass (73 existing + 1 promoted).

- [ ] **Step 4: Commit**

```
feat: promote resource_floats to runtime test (3-component resource chain)
```

---

### Task 8: Test resource_with_lists Fixture

**Files:**
- Modify: `meld-core/tests/wit_bindgen_runtime.rs`

The `resource_with_lists` fixture likely has the same root cause as `resource_floats`. Try promoting it.

- [ ] **Step 1: Change test macro**

```rust
// Before:
fuse_only_test!(test_fuse_wit_bindgen_resource_with_lists, "resource_with_lists");
// After:
runtime_test!(test_runtime_wit_bindgen_resource_with_lists, "resource_with_lists");
```

- [ ] **Step 2: Run and evaluate**

Run: `cargo test --package meld-core test_runtime_wit_bindgen_resource_with_lists -- --nocapture`
If it passes: great, commit. If it fails with a different error: revert to `fuse_only_test` and document the new error.

- [ ] **Step 3: Commit (if passing)**

```
feat: promote resource_with_lists to runtime test
```

---

## Self-Review

1. **Spec coverage**: Tasks 1-6 implement per-component handle tables (the spec's per-instance table). Task 7-8 validate at runtime.

2. **Placeholder scan**: Each task has specific code changes. Task 3 has pseudocode for wasm generation — the implementor will need to use `wasm_encoder::Function` and `wasm_encoder::Instruction` to emit the actual instructions, following the existing patterns in `adapter/fact.rs`.

3. **Type consistency**: `HandleTableInfo` is defined in Task 2, referenced in Tasks 3-4. `reexporter_components` is defined in Task 1, used in Tasks 2, 5.

4. **Risk**: Task 4 (P2 wrapper routing) is the most complex — it requires threading component_idx through the import resolution pipeline. The existing code resolves imports by position, not by component. This may require adding component_idx to the import resolution data structures.
