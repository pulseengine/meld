# Remaining Resource Fixtures Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix all 6 remaining wit-bindgen resource fixture failures, bringing runtime coverage from 39/45 to 45/45.

**Architecture:** Three independent workstreams that can run in parallel worktrees:
- **Stream A (SR-33):** own\<T\> result conversion — adapter emits resource.new for own results
- **Stream B (SR-37):** P2 wrapper per-component resource types — fixes 3-component resource table mismatch
- **Stream C (SR-32):** Nested resource detection — borrow\<T\> inside records/lists

**Tech Stack:** Rust, wasmparser, wasm-encoder

**Parallelism:** Streams A, B, C are fully independent — different files, different code paths. Stream A is the quickest win (resolver data already collected, just needs adapter codegen). Stream B is medium (localized to component_wrap.rs). Stream C is hardest (parser + resolver + adapter changes).

---

## Stream A: SR-33 — own\<T\> Result Conversion (resource_aggregates, ownership)

**Root cause:** `resource_results` is populated by the resolver but **never consumed** by the adapter generator. The comment at fact.rs:221 incorrectly states "Results are never converted." For cross-component calls, the adapter must call `[resource-new]` to create a handle in the caller's table from the callee's representation.

**Fixtures:** resource_aggregates, ownership

### Task A1: Add ResourceOwnResultTransfer to AdapterOptions

**Files:**
- Modify: `meld-core/src/adapter/mod.rs`

- [ ] **Step 1: Add the struct and field**

After `ResourceBorrowTransfer`, add:

```rust
/// Describes how to convert an own<T> result across an adapter boundary.
#[derive(Debug, Clone)]
pub struct ResourceOwnResultTransfer {
    /// Flat result index (for non-retptr) or byte offset in return area (for retptr)
    pub position: u32,
    /// Whether this is a byte offset (retptr) vs flat index (non-retptr)
    pub is_byte_offset: bool,
    /// Merged function index of [resource-new] to create handle in caller's table
    pub new_func: u32,
}
```

Add to `AdapterOptions`:
```rust
/// Resource own<T> results needing rep→handle conversion.
pub resource_new_calls: Vec<ResourceOwnResultTransfer>,
```

Initialize in `Default`: `resource_new_calls: Vec::new(),`

- [ ] **Step 2: Build to verify**

### Task A2: Populate resource_new_calls in analyze_call_site

**Files:**
- Modify: `meld-core/src/adapter/fact.rs` (analyze_call_site, ~line 220)

- [ ] **Step 1: Remove incorrect comment and add result loop**

Remove the comment "Results are never converted" (line 221-222).

After the borrow params loop, add:

```rust
// Resolve resource OWN results → [resource-new] merged function indices.
// When own<T> results cross a component boundary, the callee's core
// function returns a rep (via internal resource.new). The adapter must
// call [resource-new] to create a handle in the caller's table.
for op in &site.requirements.resource_results {
    if !op.is_owned {
        continue; // borrows cannot appear in results
    }
    let new_field = op.import_field.replace("[resource-rep]", "[resource-new]");
    if let Some(&new_func) = resource_new_imports
        .get(&(op.import_module.clone(), new_field.clone()))
        .or_else(|| resource_new_imports.get(&(op.import_module.clone(), op.import_field.clone())))
    {
        options.resource_new_calls.push(super::ResourceOwnResultTransfer {
            position: op.flat_idx, // or byte_offset for retptr
            is_byte_offset: false, // will be overridden for retptr path
            new_func,
        });
    }
}
```

- [ ] **Step 2: Build to verify**

### Task A3: Emit result conversion in generate_direct_adapter

**Files:**
- Modify: `meld-core/src/adapter/fact.rs` (generate_direct_adapter)

- [ ] **Step 1: Add result conversion after call**

In `generate_direct_adapter`, the `has_resource_ops` check (line ~284) should also consider `!options.resource_new_calls.is_empty()`. After the callee call and before post-return, add result conversion:

```rust
let has_result_resource_ops = !options.resource_new_calls.is_empty();
```

Update the condition to: `if has_resource_ops || has_result_resource_ops || (has_post_return && result_count > 0)`

After `func.instruction(&Instruction::Call(target_func));`, if `has_result_resource_ops` and result_count > 0:
- Save results to locals
- For each resource_new_call, load the result local, call new_func, store back
- Push results back to stack

- [ ] **Step 2: Build and test**

### Task A4: Emit result conversion in generate_memory_copy_adapter

**Files:**
- Modify: `meld-core/src/adapter/fact.rs`

- [ ] **Step 1: Update early-return guard**

The "no copying needed" early return (~line 495) must also check `!options.resource_new_calls.is_empty()`.

- [ ] **Step 2: Add result conversion in the cross-memory path**

After the callee call in the cross-memory path, before result copy-back, convert own results via resource.new.

- [ ] **Step 3: Build and test**

### Task A5: Emit result conversion in generate_retptr_adapter

**Files:**
- Modify: `meld-core/src/adapter/fact.rs`

- [ ] **Step 1: For retptr results, use byte_offset**

When writing return area slots to caller's retptr, if a slot corresponds to an own\<T\> result, call resource.new between load and store:
- Load rep from callee's return area
- Call [resource-new](rep) → handle
- Store handle to caller's retptr

- [ ] **Step 2: Build and test**

### Task A6: Promote fixtures and verify

- [ ] **Step 1: Promote resource_aggregates to runtime_test**
- [ ] **Step 2: Run test — expect pass or different error**
- [ ] **Step 3: If ownership also passes, promote it too**
- [ ] **Step 4: Run full suite**
- [ ] **Step 5: Commit**

---

## Stream B: SR-37 — P2 Wrapper Per-Component Resource Types (resource_floats, resource-import-and-export)

**Root cause:** `component_wrap.rs` uses `(interface_name, resource_name)` as dedup key for `local_resource_types` (line 1044). With 3+ components, multiple components' `[export]<interface>` imports share one resource type, causing "handle used with wrong type" at runtime.

**Fix:** Change dedup key to include component identity, so each component gets its own resource type for the same interface.

**Fixtures:** resource_floats, resource-import-and-export

### Task B1: Add component index to local_resource_types key

**Files:**
- Modify: `meld-core/src/component_wrap.rs` (~line 1044)

- [ ] **Step 1: Determine component index from import position**

The `import_memory_indices` field maps import position → merged memory index. This serves as a component identity proxy (each component has its own memory in multi-memory mode). Use it to derive a component index for each resource import.

- [ ] **Step 2: Change dedup key**

Change `local_resource_types` from:
```rust
HashMap<(String, String), u32>  // (interface, resource_name) → type_idx
```
to:
```rust
HashMap<(u32, String, String), u32>  // (memory_idx, interface, resource_name) → type_idx
```

Each `[export]<interface>` import with a different memory index gets its own resource type.

- [ ] **Step 3: Update all lookups**

Every place that reads from `local_resource_types` must include the memory index in the key.

- [ ] **Step 4: Build and verify existing tests still pass**

### Task B2: Handle Category B imports (non-[export] resource drops)

- [ ] **Step 1: Category B imports share the [export] type from the same component**

When a non-`[export]` import like `exports/[resource-drop]float` needs a resource type, look up the type from the `[export]exports` resource type for the SAME component (same memory index).

- [ ] **Step 2: Build and test**

### Task B3: Promote fixtures and verify

- [ ] **Step 1: Promote resource_floats to runtime_test**
- [ ] **Step 2: Run test**
- [ ] **Step 3: Test resource-import-and-export (may need separate toplevel-import fix)**
- [ ] **Step 4: Run full suite**
- [ ] **Step 5: Commit**

---

## Stream C: SR-32 — Nested Resource Detection (resource_borrow_in_record, resource_with_lists)

**Root cause:** `resource_param_positions` only detects top-level resource params. `borrow<T>` inside `record`/`list` in linear memory gets bulk-copied without handle conversion. `element_inner_pointers` (existing code for string/list fixup) skips `Own`/`Borrow` types.

**Fixtures:** resource_borrow_in_record, resource_with_lists (possibly — may be a different issue)

### Task C1: Add element_inner_resources to parser

**Files:**
- Modify: `meld-core/src/parser.rs`

- [ ] **Step 1: Create element_inner_resources function**

Parallel to `element_inner_pointers` (line 2417). Recurses into Record/Tuple fields and returns `Vec<(byte_offset, resource_type_id, is_owned)>` for each `Own`/`Borrow` found within an element.

- [ ] **Step 2: Build and verify**

### Task C2: Extend CopyLayout with inner_resources

**Files:**
- Modify: `meld-core/src/resolver.rs`

- [ ] **Step 1: Add InnerResourceHandle struct**

```rust
pub struct InnerResourceHandle {
    pub byte_offset: u32,
    pub resource_type_id: u32,
    pub is_owned: bool,
}
```

- [ ] **Step 2: Add inner_resources to CopyLayout::Elements**

```rust
Elements {
    element_size: u32,
    inner_pointers: Vec<(u32, CopyLayout)>,
    inner_resources: Vec<InnerResourceHandle>,  // NEW
}
```

- [ ] **Step 3: Populate inner_resources during adapter site creation**

In the per-function path (~line 1940) and fallback path, call `element_inner_resources` and store results.

- [ ] **Step 4: Build and verify**

### Task C3: Add emit_inner_resource_fixup to adapter

**Files:**
- Modify: `meld-core/src/adapter/fact.rs`

- [ ] **Step 1: Create emit_inner_resource_fixup function**

Similar to `emit_inner_pointer_fixup` but simpler — no allocation. For each element:
1. Load handle from `dst_base + loop_idx * element_size + byte_offset`
2. Call `[resource-rep](handle)` → rep
3. (If 3-component: call `[resource-new](rep)` → new_handle)
4. Store back to same location

- [ ] **Step 2: Insert after bulk copy in generate_memory_copy_adapter and generate_retptr_adapter**

After the existing inner_pointer_fixup calls, also call inner_resource_fixup for each copy layout that has non-empty inner_resources.

- [ ] **Step 3: Build and test**

### Task C4: Promote fixtures and verify

- [ ] **Step 1: Promote resource_borrow_in_record to runtime_test**
- [ ] **Step 2: Run test**
- [ ] **Step 3: Test resource_with_lists (may need separate investigation)**
- [ ] **Step 4: Run full suite**
- [ ] **Step 5: Commit**

---

## Execution Order (for serial execution)

If running serially, priority order:
1. **Stream A (SR-33)** — quickest win, data already collected, 2 fixtures
2. **Stream B (SR-37)** — medium effort, localized change, 1-2 fixtures
3. **Stream C (SR-32)** — hardest, multi-file change, 1-2 fixtures

For parallel execution, all 3 streams can run simultaneously in separate git worktrees since they modify different code:
- Stream A: `adapter/mod.rs`, `adapter/fact.rs` (analyze_call_site + generators)
- Stream B: `component_wrap.rs`
- Stream C: `parser.rs`, `resolver.rs`, `adapter/fact.rs` (emit_inner_resource_fixup)

Note: Streams A and C both modify `adapter/fact.rs` but in different functions (A: result handling in generators; C: new fixup function + Phase 1 insertion). They can be merged cleanly.
