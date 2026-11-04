---
id: ADR-9
type: design-question
title: Threads in meld's scope -- wasi-threads (P1) and shared-everything threads are out, P3 cooperative threads are in and pass through to the host (kiln)
status: resolved
gating-fixtures:
  # Run with `cargo test -p meld-core --test threads_scope_adr9 --test coop_threads_547`
  # and `cargo test -p meld-cli --test coop_threads_547`.
  - threads_scope_adr9::shared_everything_thread_spawn_is_refused
  - threads_scope_adr9::thread_available_parallelism_is_refused
  - threads_scope_adr9::wasi_threads_shared_memory_is_refused
  - threads_scope_adr9::imported_shared_memory_is_refused
  - threads_scope_adr9::cooperative_thread_builtins_pass_through_as_producer_imports
  # meld-core/tests/coop_threads_547.rs
  - coop_threads_547::clang_thread_components_fuse_validate_and_import_the_producer_names
  - coop_threads_547::new_indirect_resolves_through_the_exported_table
  - coop_threads_547::two_different_new_indirect_tables_are_refused
  - coop_threads_547::unmodelled_canonical_builtin_is_an_error_naming_it
  # meld-cli/tests/coop_threads_547.rs (same name, binary-driven)
  - coop_threads_547::cli_fuses_a_cooperative_thread_component_and_records_the_table
design-paths:
  - path-T0 -- support wasi-threads (P1: `wasi:thread-spawn` + a `shared` memory) (rejected -- decision 2026-11-03)
  - path-T1 -- support shared-everything threads (thread.spawn-ref, thread.spawn-indirect, thread.available-parallelism) (rejected -- decision 2026-11-03: not a target for meld)
  - path-T2 -- support P3 cooperative threads (the nine `thread.*` built-ins below) by lowering them to meld-defined host intrinsics (rejected -- superseded 2026-11-04 by T3)
  - path-T3 -- pass P3 cooperative threads through to the host in the PRODUCER ABI (`$root::[thread-*]`), meld adds only the identity of the `thread.new-indirect` table (accepted -- decision 2026-11-04, #547; host side kiln#620)
---

# ADR-9 -- Threads in meld's scope

## Decision (2026-11-03, contract amended 2026-11-04)

Three different things are called "threads":

0. **wasi-threads (P1)**: `wasi:thread-spawn` plus a `shared` linear memory.
   **Out of scope for meld.**
1. **Shared-everything threads** (`thread.spawn-ref`, `thread.spawn-indirect`,
   `thread.available-parallelism`, `shared` types): real parallelism over shared
   memory. **Out of scope for meld.** No work is planned on it.
2. **P3 cooperative threads**: green threads inside one component instance,
   scheduled cooperatively. kiln runs these, so **meld fuses components that use
   them** (#547). The contract is the **producer ABI** (below).

Plain P3 async (tasks, subtasks, streams, futures, waitables, `thread.yield`
as an async yield) is unaffected and stays supported.

## The contract: the producer ABI (2026-11-04)

meld does **not** lower the cooperative built-ins to its own intrinsics. Each
becomes a plain core import of the fused module, under exactly the module/field
name and core type the producers (`wit-bindgen c --generate-threading-helpers`
+ `wit-component`) emit. The host implements the semantics (kiln:
pulseengine/kiln#620). Names and types were read off real producer output (the
seven clang C components in `tests/p3/coop_threads_547/`) and agree with the
table in kiln#620 with no discrepancy:

| import (module `$root`) | core type | canonical built-in |
|---|---|---|
| `[thread-new-indirect-v0]` | `(fn_idx: i32, arg: i32) -> i32` | `thread.new-indirect` |
| `[thread-index]` | `() -> i32` | `thread.index` |
| `[thread-yield]` | `() -> i32` | `thread.yield` |
| `[thread-suspend]` | `() -> i32` | `thread.suspend` |
| `[thread-resume-later]` | `(i32) -> ()` | `thread.resume-later` |
| `[thread-suspend-then-resume]` | `(i32) -> i32` | `thread.suspend-then-resume` |
| `[thread-yield-then-resume]` | `(i32) -> i32` | `thread.yield-then-resume` |
| `[thread-suspend-then-promote]` | `(i32) -> i32` | `thread.suspend-then-promote` |
| `[thread-yield-then-promote]` | `(i32) -> i32` | `thread.yield-then-promote` |

(The strings live in `meld_core::thread_builtins`; `import-map` classifies all
nine as `p3-builtin` with `memory`, `realloc` and `encoding` all `null`: they
take only opaque i32s.)

Points a host must know:

- **Hand-written components get the same names.** A component that gives its
  core import some other name (`""`/`"thread.index"`) is renamed to the table
  above by the same canon-to-import-name pass that names `[waitable-set-*]`.
- **`$N` suffix.** Under `--memory multi`, a second component's copy of the same
  import is emitted as `[thread-index]$1` (the component index), exactly as for
  every other pass-through built-in, so that `(module, field)` stays unique. The
  suffix names which component's thread state the call belongs to; strip it to
  get the built-in. The `$N` alone does not identify the owner (the unsuffixed
  import belongs to whichever component imports it first, not necessarily
  component 0): **hosts must attribute each thread import to its component from
  the `--emit-import-map` `component` field**, which names the owning component
  of every import including all nine thread built-ins. (The attestation records
  the thread table, not a per-import owner.) A cooperative thread's identity and
  table belong to a component INSTANCE, so this attribution is not optional.
- **`--memory shared` refuses two threaded components.** Under one shared
  address space the host-import dedup merges the same built-in from two
  components into ONE import with no suffix, and the instance a call comes from
  is lost (measured on a two-component `thread.index` fixture; the wasmtime test
  `during-sync-call-no-sibling-resume` fused at exit 0 that way). meld therefore
  refuses, citing this ADR, when more than one component in a shared fusion
  declares any cooperative-thread built-in other than `thread.yield`
  (`thread.yield` is also the plain P3 async yield, predates #547 and is left
  alone). Single-component fusions and `--memory multi` are unchanged.
- **Names reached through alias chains.** A built-in wired into a core module
  through bag -> `alias core export` -> bag is named after the built-in, found by
  following the alias chain to its end, not after whatever name the core module
  imports it under (the module's name can be another built-in's producer name;
  meld used to keep it, so a host would have bound the wrong built-in, for
  `task.*`, `context.*`, `waitable*`, `subtask.*`, `backpressure.*` and `thread.*`
  alike). An alias that names an instance that is neither an export bag nor an
  instantiated module is refused.
- **The names the old design used are gone.** `thread.switch-to` and
  `thread.yield-to` no longer exist in the canonical ABI (replaced by
  `thread.suspend-then-resume` / `thread.yield-then-resume` and the
  `-promote` forms); `[cancellable]` variants are gone too (below).
- **`--component` output** refuses (`cannot resolve fused import
  $root::[thread-index] to a component instance`), as it does for the other
  host-provided built-ins (checked with `[waitable-set-wait]`); the
  pass-through is for the core-module output.

## The table `thread.new-indirect` indexes

`thread.new-indirect(fn_idx, arg)` names a start function by index into a
funcref table (the table operand of the canon). A host cannot start the thread
unless it knows which table that is, and after fusion the module has several
(wit-component's shim also contributes an `$imports` table, which is NOT the
one). meld resolves the canon's table through its table index map and:

- exports it from the fused module as **`__meld_thread_table`**;
- records it in `--emit-import-map` on every `[thread-new-indirect-v0]` import
  (`"thread_table": {"index": N, "export": "__meld_thread_table"}`);
- records it in the attestation (`metadata.thread_table`, omitted when the
  artifact creates no threads, so every other attestation is unchanged).

If two `thread.new-indirect` canons name two DIFFERENT fused tables
(multi-component fusion with a table each), meld **refuses** with an error citing
this ADR: the host would have one export name for two tables and could not tell
which one a given `fn_idx` belongs to. (Measured on a 504-component corpus: 2
components. A per-component `__meld_thread_table$N` export would lift this; it
is not needed yet.) A canon whose table cannot be traced to a merged table is
refused the same way; it is never guessed.

The start function's own type is `(func (param i32))`; wasmparser validates it
against the canon.

## Refusals that remain

- Any `shared` memory, defined or imported (wasi-threads and shared-everything
  alike): `Error` citing this ADR.
- `thread.spawn-ref`, `thread.spawn-indirect`, `thread.available-parallelism`:
  refused by the validator (shared types are not enabled) AND, defensively, by
  `convert_canonical_function`, which now returns `Error::UnsupportedFeature`
  naming the built-in for ANY canonical built-in meld does not model. It used to
  map them to `CanonicalEntry::Unsupported`, which was only logged: enabling a
  validator gate would have turned a loud refusal into silent pass-through. That
  variant is deleted.
- `stream.forward` / `future.forward` (and any built-in a later wasmparser
  adds): before #547 these reached the logged placeholder when the parser ran
  without validation (`ComponentParser::without_validation`); with validation
  they were refused by the validator (`CM_FORWARD` is off) and still are. Now
  an error either way. (`resource.drop async` no longer decodes in
  wasmparser 0.263.)
- `context.get`/`context.set` with slot 1 (needs the threading feature, is not
  one of the nine, kiln#620 does not list it): refused by name. Acceptance does
  not widen beyond the nine built-ins.
- `[cancellable]` variants: wasmparser 0.263 follows component-model#716 and has
  no such flag; the legacy byte must be 0 and a producer that still sets it
  fails to decode ("... historically accepted as `cancellable`"). That is loud;
  none of the refusals on the 504-component corpus mentions it.

## Feature gate

`baseline_wasm_features()` enables `CM_THREADING` (and nothing else for this):
the flag wasmparser 0.263 requires for `thread.index`, `thread.new-indirect`,
`thread.resume-later`, `thread.suspend` and the four `-then-` built-ins
(`thread.yield` needs only `CM_ASYNC`). It is the same set the CLI uses to
validate the fused output. `SHARED_EVERYTHING_THREADS` stays off.

## `pulseengine:async::thread_*` retired

`HostIntrinsic::{ThreadNew, ThreadSwitchTo, ThreadYield, ThreadExit}` and
`p3_async::thread` (SR-32 / #140) matched nothing a producer emits and nothing
consumed them. They and their pinning test are deleted (kiln#620 records the
same). The stackful trampoline never used them (ADR-1).

## State when decided (measured on meld 0.66.0)

- A wasi-threads component fused at exit 0 under both `--memory multi` and
  `--memory shared`, keeping the `shared` memory and exporting
  `wasi_thread_start`. **Changed 2026-11-03:** any `shared` memory is refused.
- A `thread.spawn-ref` component was refused at parse; a `thread.index`
  component was refused at parse ("requires the component model threading
  feature"). Both refusals were incidental. **Changed 2026-11-04** for the
  cooperative family: of the 67 components of a 504-component corpus that
  were refused at parse for the threading feature or a slot-1 `context.*`
  immediate, 48 now fuse and validate under `--memory multi`. The other 19 are
  refused for a different, named reason (4 `subtask.cancel` async form, 4
  `context.get`/`set` slot 1, 4 async-stackful, 2 two start-function tables,
  2 `thread.new-indirect` with a non-`(i32)` start type, 2 same-memory
  signature pair #390, 1 64-bit table). The 333 components that already fused
  produce byte-identical output.

## Consequences

- wasi-threads and shared-everything threads: stay refused. The gating tests
  must keep passing.
- Cooperative threads: fuse and pass through; the host implements them
  (kiln#620). Until kiln does, it refuses the unresolved `$root::[thread-*]`
  imports loudly (E21A0).
- meld does not model thread scheduling, so nothing in the fused module's
  adapters, stack handling or rebasing is thread-aware. Cooperative threads run
  on one wasm instance's linear memory, switched by the host; meld's
  single-thread assumptions (one shadow stack per module, non-reentrant
  adapters) hold only if the host switches at the built-ins and not inside an
  adapter. That is the host's obligation and is NOT verified by meld.
