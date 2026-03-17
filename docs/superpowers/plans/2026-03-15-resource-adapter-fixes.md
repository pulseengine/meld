# Resource Adapter Fixes Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix two bugs that cause 5 wit-bindgen fixtures to fail at runtime: ambiguous adapter matching (3 fixtures) and missing resource detection in the fallback resolver path (2 fixtures).

**Architecture:** Bug 1 adds an `import_module` field to `AdapterSite` so the merger disambiguates same-named functions from different interfaces. Bug 2 upgrades the fallback single-export resolver path to use `lift_info_by_core_func` (which provides the component type index) and then populate `resource_params`/`resource_results` on `AdapterRequirements`.

**Tech Stack:** Rust, wasmparser, wasm-encoder

---

## Chunk 1: Bug 1 — AdapterSite import_module disambiguation

### Task 1: Add `import_module` field to `AdapterSite`

**Files:**
- Modify: `meld-core/src/resolver.rs:55-80` (AdapterSite struct)
- Modify: `meld-core/src/resolver.rs:1914-1925` (per-function path — set import_module)
- Modify: `meld-core/src/resolver.rs:2051-2062` (fallback path — set import_module)

- [ ] **Step 1: Add the field to AdapterSite**

In `meld-core/src/resolver.rs`, add a new field after `import_name`:

```rust
pub struct AdapterSite {
    pub from_component: usize,
    pub from_module: usize,
    pub import_name: String,
    /// The core import's module name (e.g., "test:dep/test@0.1.0").
    /// Used to disambiguate when multiple interfaces export the same function name.
    pub import_module: String,
    pub import_func_type_idx: Option<u32>,
    // ... rest unchanged
}
```

- [ ] **Step 2: Set import_module in per-function path (line ~1914)**

The per-function path iterates `interface_func_imports` which filters `imp.module == *import_name`. So the import_module is `import_name` (the resolved interface name):

```rust
graph.adapter_sites.push(AdapterSite {
    from_component: *from_comp,
    from_module: from_mod_idx,
    import_name: (*func_name).to_string(),
    import_module: import_name.clone(),  // NEW
    import_func_type_idx: caller_import_type_idx,
    // ... rest unchanged
});
```

- [ ] **Step 3: Set import_module in fallback path (line ~2051)**

The fallback path matches imports where `imp.name == *import_name || imp.module == *import_name`. The import_module is `import_name` here too:

```rust
graph.adapter_sites.push(AdapterSite {
    from_component: *from_comp,
    from_module: from_mod_idx,
    import_name: import_name.clone(),
    import_module: import_name.clone(),  // NEW
    import_func_type_idx: fallback_import_type_idx,
    // ... rest unchanged
});
```

- [ ] **Step 4: Set import_module in intra-component path**

Search for other `AdapterSite` constructions (grep for `adapter_sites.push`) and add `import_module` there too. The intra-component path (around line 2130+) should set it from the available import info.

- [ ] **Step 5: Build to verify compilation**

Run: `cargo build 2>&1`
Expected: Clean build (no errors)

### Task 2: Use `import_module` in merger matching

**Files:**
- Modify: `meld-core/src/merger.rs:869-873` (adapter site lookup)

- [ ] **Step 1: Update the `.find()` predicate**

In `meld-core/src/merger.rs` at line 869, add `imp.module` check:

```rust
let resolved = graph.adapter_sites.iter().find(|site| {
    site.from_component == comp_idx
        && site.from_module == mod_idx
        && (imp.name == site.import_name || imp.module == site.import_name)
        && (imp.module == site.import_module || imp.name == site.import_module)
});
```

The double-or handles both orientations: in per-function imports, `imp.module` is the interface name and `imp.name` is the function name; in fallback imports, either could match.

- [ ] **Step 2: Build and run resource_alias test**

Run: `cargo test --package meld-core test_fuse_wit_bindgen_resource_alias -- --nocapture 2>&1`
Expected: PASS (core fusion)

### Task 3: Use `import_module` in adapter wiring (lib.rs)

**Files:**
- Modify: `meld-core/src/lib.rs:369` (adapter wiring)

- [ ] **Step 1: Update the adapter wiring match**

In `meld-core/src/lib.rs` at line 369:

```rust
if (imp.name == site.import_name || imp.module == site.import_name)
    && (imp.module == site.import_module || imp.name == site.import_module)
{
```

- [ ] **Step 2: Build and verify**

Run: `cargo build 2>&1`
Expected: Clean build

### Task 4: Promote fixtures to runtime tests

**Files:**
- Modify: `meld-core/tests/wit_bindgen_runtime.rs`

- [ ] **Step 1: Change resource_alias, with-and-resources, versions from fuse_only_test to runtime_test**

Replace `fuse_only_test!` with `runtime_test!` for:
- `test_fuse_wit_bindgen_resource_alias` → `test_runtime_wit_bindgen_resource_alias`
- `test_fuse_wit_bindgen_with_and_resources` → `test_runtime_wit_bindgen_with_and_resources`
- `test_fuse_wit_bindgen_versions` → `test_runtime_wit_bindgen_versions`

Remove the corresponding comment lines explaining the known failures.

- [ ] **Step 2: Run the three promoted tests**

Run: `cargo test --package meld-core --test wit_bindgen_runtime resource_alias with_and_resources versions -- --nocapture 2>&1`
Expected: All 3 PASS

- [ ] **Step 3: Run full test suite**

Run: `cargo test 2>&1`
Expected: All tests pass (0 failures)

- [ ] **Step 4: Commit**

```bash
git add meld-core/src/resolver.rs meld-core/src/merger.rs meld-core/src/lib.rs meld-core/tests/wit_bindgen_runtime.rs
git commit -m "fix: disambiguate adapter matching with import_module field

AdapterSite now tracks the caller's core import module name (e.g.,
\"test:dep/test@0.1.0\") in addition to the bare function name. The
merger and adapter wiring use both fields to avoid wiring same-named
functions from different interfaces to the same adapter.

Fixes: resource_alias, with-and-resources, versions fixtures"
```

---

## Chunk 2: Bug 2 — Fallback resolver path resource detection

### Task 5: Upgrade fallback path to use `lift_info_by_core_func`

**Files:**
- Modify: `meld-core/src/resolver.rs:1974-1992` (fallback path callee-side)

- [ ] **Step 1: Replace `lift_options_by_core_func` with `lift_info_by_core_func`**

In the fallback single-export matching path (line ~1979), change:

```rust
// BEFORE:
let callee_lift_map = to_component.lift_options_by_core_func();
// ...
if let Some(lift_opts) =
    fb_comp_core_idx.and_then(|idx| callee_lift_map.get(idx))
{
    requirements.callee_encoding = Some(lift_opts.string_encoding);
    requirements.callee_post_return = lift_opts
        .post_return
        .and_then(|pr_idx| fb_core_to_local.get(&pr_idx).copied());
    requirements.callee_realloc = lift_opts.realloc;
}
```

```rust
// AFTER:
let callee_lift_map = to_component.lift_info_by_core_func();
// ...
if let Some((comp_type_idx, lift_opts)) =
    fb_comp_core_idx.and_then(|idx| callee_lift_map.get(idx))
{
    requirements.callee_encoding = Some(lift_opts.string_encoding);
    requirements.callee_post_return = lift_opts
        .post_return
        .and_then(|pr_idx| fb_core_to_local.get(&pr_idx).copied());
    requirements.callee_realloc = lift_opts.realloc;

    // Populate layout and resource info from component function type
    // (mirrors per-function path at line ~1820)
    if let Some(ct) = to_component.get_type_definition(*comp_type_idx)
        && let ComponentTypeKind::Function {
            params: comp_params,
            results,
        } = &ct.kind
    {
        let size = to_component.return_area_byte_size(results);
        if size > 4 {
            requirements.return_area_byte_size = Some(size);
        }
        requirements.pointer_pair_positions =
            to_component.pointer_pair_param_positions(comp_params);
        requirements.result_pointer_pair_offsets =
            to_component.pointer_pair_result_offsets(results);
        requirements.param_copy_layouts =
            collect_param_copy_layouts(to_component, comp_params);
        requirements.result_copy_layouts =
            collect_result_copy_layouts(to_component, results);
        requirements.conditional_pointer_pairs =
            to_component.conditional_pointer_pair_positions(comp_params);
        requirements.conditional_result_pointer_pairs =
            to_component.conditional_pointer_pair_result_positions(results);
        requirements.conditional_result_flat_pairs =
            to_component.conditional_pointer_pair_result_flat_positions(results);
        requirements.return_area_slots =
            to_component.return_area_slots(results);

        let callee_resource_map = build_resource_type_to_import(to_component);
        requirements.resource_params = resolve_resource_positions(
            &callee_resource_map,
            &to_component.resource_param_positions(comp_params),
            "[resource-rep]",
        );
        requirements.resource_results = resolve_resource_positions(
            &callee_resource_map,
            &to_component.resource_result_positions(results),
            "[resource-new]",
        );
    }
}
```

- [ ] **Step 2: Build to verify compilation**

Run: `cargo build 2>&1`
Expected: Clean build

### Task 6: Promote resource_floats and xcrate to runtime tests

**Files:**
- Modify: `meld-core/tests/wit_bindgen_runtime.rs`

- [ ] **Step 1: Change resource_floats and xcrate from fuse_only_test to runtime_test**

Replace `fuse_only_test!` with `runtime_test!` for:
- `test_fuse_wit_bindgen_resource_floats` → `test_runtime_wit_bindgen_resource_floats`
- `test_fuse_wit_bindgen_xcrate` → `test_runtime_wit_bindgen_xcrate`

Remove or update the corresponding comment lines.

- [ ] **Step 2: Run the promoted tests**

Run: `cargo test --package meld-core --test wit_bindgen_runtime resource_floats xcrate -- --nocapture 2>&1`
Expected: Both PASS

- [ ] **Step 3: Run full test suite**

Run: `cargo test 2>&1`
Expected: All tests pass (0 failures)

- [ ] **Step 4: Commit**

```bash
git add meld-core/src/resolver.rs meld-core/tests/wit_bindgen_runtime.rs
git commit -m "fix: populate resource params in fallback resolver path

The single-export fallback matching path now uses lift_info_by_core_func
(which provides the component type index) instead of lift_options_by_core_func.
This enables populating resource_params, pointer pair positions, copy layouts,
and all other AdapterRequirements fields that were previously only set in
the per-function interface matching path.

Fixes: resource_floats, xcrate fixtures"
```

### Task 7: Final verification and PR

- [ ] **Step 1: Run full test suite**

Run: `cargo test 2>&1`
Expected: All tests pass

- [ ] **Step 2: Run clippy**

Run: `cargo clippy --all-targets 2>&1`
Expected: No warnings

- [ ] **Step 3: Create branch and PR**

```bash
git checkout -b fix/resource-adapter-disambiguation
git push -u origin fix/resource-adapter-disambiguation
gh pr create --title "fix: disambiguate adapter matching and populate resource params in fallback path" --body "..."
```
