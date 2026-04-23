# Can wasmtime reuse `meld-core/src/adapter/fact.rs`?

> Memo for Christof Petig — drafted 2026-04-22 by avrabe + Claude Opus 4.7

## TL;DR

Christof is right to be skeptical of the claim that "meld's fact.rs cannot
be used from wasmtime." The architectural shape of the two emitters is
nearly identical (both consume canonical-ABI options and emit
`wasm_encoder` bytecode), and a substantial fraction of meld's emission
logic is semantically equivalent to wasmtime's. **The pure emission core
is portable; the resolution/typing layer above it is not.** Sharing
through a third crate of canonical-ABI emission primitives is feasible
and probably the right outcome — but a literal "wasmtime imports
meld_core" would not work.

## The two systems compared

| Aspect | wasmtime FACT (43.0.1) | meld `adapter/fact.rs` |
|---|---|---|
| LOC | 5596 (5 files in `wasmtime-environ/src/fact/`) | 4543 (1 file) |
| Output crate | `wasm_encoder` | `wasm_encoder` |
| Output unit | A separate adapter MODULE per fused instance, instantiated and JITed at runtime | Adapter FUNCTIONS directly inlined into the fused merged module |
| Trigger point | Component instantiation (runtime) | Static fusion (build-time) |
| Type context | `&ComponentTypesBuilder`, `&Tunables`, `Adapter`, `AdapterOptionsDfg` | `&MergedModule`, `&AdapterSite`, `AdapterOptions` |
| Memory model | Multi-memory (since 2024) | Multi-memory native; also legacy shared-memory mode |
| GC types | `GcStruct`, `GcArray` lifting/lowering | Not implemented |
| Variant lifting | `VariantCase` / `variant_info` helpers | `ConditionalPointerPair`-driven |
| Resource handles | `resource.rep` / `resource.new` / `resource.drop` | Same — `ResourceBorrowTransfer` / `ResourceOwnResultTransfer` |
| Async (P3) | Recently added; `prepare_call` builtin trampoline | `generate_async_callback_adapter` + `generate_stabilizing_shim` |

Layout of the two packages (per-file LOC):

```
wasmtime-environ/src/fact.rs         1037   (Module + AdapterOptions wiring)
wasmtime-environ/src/fact/core_types.rs   26
wasmtime-environ/src/fact/signature.rs  243   (flattening, retptr/params-ptr)
wasmtime-environ/src/fact/trampoline.rs 4200  (the actual emission)
wasmtime-environ/src/fact/transcode.rs    90  (string-encoding helpers)

meld-core/src/adapter/fact.rs        4543   (everything in one file)
meld-core/src/adapter/mod.rs          211   (trait + AdapterOptions)
```

The same logical surface — wasmtime just split it across files earlier.

## What's portable

The **pure emission primitives** are semantically identical and depend
only on (a) an `AdapterOptions`-like input and (b) function/memory/global
indices in the output module. Both code-bases have direct equivalents:

| meld function | wasmtime equivalent |
|---|---|
| `emit_utf8_to_utf16_transcode` | `Compiler::translate_string` (utf8↔utf16 path) |
| `emit_utf16_to_utf8_transcode` | same |
| `emit_latin1_to_utf8_transcode` | same |
| `emit_inner_pointer_fixup` | `Compiler::translate_list` (per-element walk) |
| `generate_memory_copy_adapter` (bulk path) | `Compiler::translate` for `list<scalar>` |
| `emit_resource_borrow_phase0` | wasmtime's resource-rep/new emission in trampoline.rs |
| `cabi_size_align`, `collect_indirections` | flattening logic in `signature.rs` |
| `emit_checked_realloc`, `emit_overflow_guard` | **absent in wasmtime** — see "Bugs we found that wasmtime probably has too" below |

If you took the meld functions, replaced `&MergedModule` with a generic
`fn realloc_for(&self, comp: ComponentIdx) -> u32` trait callback, and
replaced `&AdapterSite` with wasmtime's `Adapter`, the bodies would
compile against wasmtime's environment after type translation.

## What's NOT portable

1. **Resolution layer** (`fact.rs::analyze_call_site`,
   `resolve_target_function`, plus most of `meld-core/src/resolver.rs`).
   This walks the merged module, builds `CopyLayout`s, computes
   `pointer_pair_positions`, etc. Wasmtime has its own equivalent
   computed during component translation; they're not interchangeable.

2. **Index spaces.** Meld's `function_index_map` is `(comp_idx,
   mod_idx, src_func_idx) → merged_func_idx`. Wasmtime resolves to
   runtime function pointers via its own `Adapter` graph. Different
   coordinates entirely.

3. **Module composition strategy.** Meld inlines adapters into one
   merged module; wasmtime emits a separate adapter module that imports
   functions from the component instances and is wired up at
   instantiation. Even if the adapter bodies were identical bytecode,
   they'd live in different modules with different signatures.

4. **Output target.** Wasmtime FACT's output is consumed by Cranelift
   to JIT machine code. Meld's output is the final wasm shipped to a
   downstream runtime. Both are byte-identical wasm, but the *consumer
   contract* differs (wasmtime FACT may rely on host-side trampolines
   that meld can't reference).

## Bugs we found that wasmtime probably has too

The Mythos pipeline run on meld this April found **LS-A-7**: every
`cabi_realloc` call site in the transcoders + 16 other emission sites
was missing both an overflow guard on the size multiplication and a
null-check on the realloc return. Both are required by the Canonical
ABI ("trap on realloc failure") and by wasm semantics (`i32.mul` is
mod 2^32).

A grep of `wasmtime-environ-43.0.1/src/fact/trampoline.rs` for
`Call(realloc)` followed by an absent `I32Eqz`/`If`/`Unreachable` may
reveal the same class. Worth asking Christof whether wasmtime's FACT
has the equivalent guards — if not, meld's
`tests/realloc_safety.rs` byte-scan gate is portable.

## What sharing would actually look like

Option **A — third crate** (cleanest):

```
canonical-abi-emit/   (new crate)
  - emit_transcode_utf8_to_utf16(&mut Function, opts: &TranscodeOpts, indices: &Indices)
  - emit_list_copy(&mut Function, ...)
  - emit_record_lift_lower(&mut Function, ...)
  - emit_checked_realloc(&mut Function, realloc_fn: u32, result_local: u32)
  - cabi_size_align(ty: &CanonicalAbiType) -> (u32, u32)

meld-core depends on canonical-abi-emit
wasmtime-environ depends on canonical-abi-emit
```

The `Indices` and `*Opts` structs would be plain data — caller's
responsibility to populate them from their respective resolution layers.
The crate would also export the `cabi_size_align` / `collect_indirections`
type-walking primitives, and the `emit_checked_realloc` /
`emit_overflow_guard` safety helpers. This crate would be ~1500 LOC
extracted from meld's fact.rs (the leaf emission functions).

Option **B — meld imports wasmtime's FACT** (heavy):

Possible but requires depending on `wasmtime-environ` (heavy), translating
`MergedModule` into `ComponentTypesBuilder`, and inlining wasmtime's
emitted adapter module into meld's output. The `wasmtime-environ`
dependency would bring Cranelift transitively.

Option **C — wasmtime imports meld** (not feasible):

Wasmtime can't take a dependency on meld because meld's API is built
around static fusion (its "Adapter" is a `&MergedModule` + `&AdapterSite`
+ a function-index map), and wasmtime needs runtime-resolved indices.

## Recommendation

Pursue **Option A** when there's collaboration appetite from both
projects. The size of the shareable surface (~1500 LOC) and the bug-class
overlap (LS-A-7) make a single canonical-ABI emission library a real
win for both consumers and the broader component-model ecosystem.

Until then, the practical claim is "meld's `fact.rs` cannot be **dropped
in** to wasmtime as-is" — that's true, but it's a much weaker claim than
"the emission logic is unshareable." The emission logic IS shareable, and
the bugs in our 19-site audit are very likely present in wasmtime too.
