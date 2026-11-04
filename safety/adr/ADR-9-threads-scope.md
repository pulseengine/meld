---
id: ADR-9
type: design-question
title: Threads in meld's scope -- wasi-threads (P1) and shared-everything threads are out, P3 cooperative threads are in (kiln)
status: resolved
gating-fixtures:
  # Run with `cargo test -p meld-core --test threads_scope_adr9`.
  - threads_scope_adr9::shared_everything_thread_spawn_is_refused
  - threads_scope_adr9::cooperative_thread_builtins_are_refused_until_supported
  - threads_scope_adr9::wasi_threads_shared_memory_is_refused
  - threads_scope_adr9::imported_shared_memory_is_refused
design-paths:
  - path-T0 -- support wasi-threads (P1: `wasi:thread-spawn` + a `shared` memory) (rejected -- decision 2026-11-03)
  - path-T1 -- support shared-everything threads (thread.spawn-ref, thread.spawn-indirect, thread.available-parallelism) (rejected -- decision 2026-11-03: not a target for meld)
  - path-T2 -- support P3 cooperative threads (thread.new-indirect, thread.switch-to, thread.suspend, thread.resume-later, thread.yield-to, thread.index) (accepted -- kiln runs them; implementation tracked separately)
---

# ADR-9 -- Threads in meld's scope

## Decision (2026-11-03)

Three different things are called "threads":

0. **wasi-threads (P1)**: `wasi:thread-spawn` plus a `shared` linear memory.
   **Out of scope for meld.**
1. **Shared-everything threads** (`thread.spawn-ref`, `thread.spawn-indirect`,
   `thread.available-parallelism`, `shared` types): real parallelism over shared
   memory. **Out of scope for meld.** No work is planned on it.
2. **P3 cooperative threads** (`thread.new-indirect`, `thread.switch-to`,
   `thread.suspend`, `thread.resume-later`, `thread.yield-to`, `thread.index`):
   green threads inside one component instance, scheduled cooperatively. kiln
   runs these, so **meld must be able to fuse components that use them.**

Plain P3 async (tasks, subtasks, streams, futures, waitables, `thread.yield`
as an async yield) is unaffected and stays supported.

## State when decided (measured on meld 0.66.0)

- A wasi-threads component (defined `shared` memory, `wasi:thread-spawn`)
  **fused at exit 0** under both `--memory multi` and `--memory shared`, keeping
  the `shared` memory and exporting `wasi_thread_start`. Nothing in meld is
  built for more than one thread (one shadow stack per module, non-reentrant
  adapters, rebasing), so this was a silent unsupported fusion. **Changed:** any
  `shared` memory, defined or imported, is now refused with an error citing
  this ADR. Every threads variant needs one, so the check covers wasi-threads
  and shared-everything threads alike.

- A `thread.spawn-ref` component is refused at parse: a valid spawn needs a
  `shared` function type, which meld's parser does not enable
  ("Failed to parse ... spawn type must be shared").
- A `thread.index` component is refused at parse: "`thread.index` requires the
  component model threading feature". The same holds for the other
  cooperative-thread built-ins. If the feature were enabled, the parser would
  map them to `CanonicalEntry::Unsupported`, which is only logged
  (`parser.rs` fallback), so enabling the feature without implementing the
  lowering would turn a loud refusal into a silent one.

Both refusals are loud today, but only incidentally. The gating tests pin them,
so a parser-feature or wasmparser upgrade cannot quietly start accepting either
family before meld handles it.

## Consequences

- wasi-threads and shared-everything threads: stay refused. The tests must
  keep passing.
- Cooperative threads: an implementation (lowering to kiln's host intrinsics,
  building on the `thread_*` entries in `p3_async::HostIntrinsic`) replaces the
  second test with positive fuse-and-run tests when it lands. Until then it
  stays refused, never mapped to `Unsupported` silently.
