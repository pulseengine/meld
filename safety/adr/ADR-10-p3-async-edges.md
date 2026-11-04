---
id: ADR-10
type: design-question
title: P3 async calls between fused components -- meld owns data (edge table + copy adapters), kiln-async owns control (tasks, subtasks, waitables), gale owns time, wake and isolation
status: open
gating-fixtures:
  # Planned; none exist yet. Names are fixed here so the record can cite them.
  - p3_async_edges_548::async_lower_caller_produces_one_edge_per_import (planned)
  - p3_async_edges_548::edge_section_is_versioned_and_names_exports (planned)
  - p3_async_edges_548::start_adapter_returns_the_packed_code_unchanged (planned)
  - p3_async_edges_548::cross_domain_async_edge_is_refused (planned)
  - p3_async_edges_548::non_callback_async_lift_edge_is_refused (planned)
  - p3_async_edges_548::share_stack_with_stackful_or_threads_is_refused (planned)
  - p3_async_edges_548::corpus_19_pairs_fuse_with_edges_and_no_host_left_import (planned)
  # Runtime acceptance (kiln side): the same 19 pairs, fused, run on the kiln
  # interpreter with wasmtime 51-dev's unfused result.
design-paths:
  - path-A0 -- leave async-lower imports to the host (status quo at v0.67.0) (rejected -- silent, 26/26 corpus pairs unfused at exit 0)
  - path-A1 -- drive the callee to completion inside the call and return RETURNED (rejected -- deadlocks ping-pong, see Context)
  - path-A2 -- meld emits an in-module scheduler (virtual subtasks, waitable sets) (rejected -- duplicates the runtime's task model and adds a second arbiter for events)
  - path-A3 -- meld emits a static edge table and copy adapters; the kiln-async runtime runs subtasks; gale provides wake, time and isolation (proposed -- joint meld/kiln/gale design 2026-11-04)
---

# ADR-10 -- P3 async calls between fused components

**Status: open (draft for review by kiln and gale).** The design below was
agreed in principle by the kiln and gale sessions on 2026-11-04. It is not yet
accepted by the maintainer.

## Context (measured)

- **The defect (#548).** In a corpus of 504 P3 components (meld main 21536f0),
  26 natural caller/callee pairs fuse at exit 0 with **zero** fused calls
  between components. In every one, the caller lowers the import with
  `canon lower ... async`.
  - Its core import is `[async-lower]f`, with signature
    `(flat params | params ptr, retptr) -> i32 status`.
  - The caller expects `RETURNED`, or `STARTED | subtask<<4` and a later
    `SUBTASK` event through `[waitable-set-wait]`.
  - meld only bridges a **sync** caller to an `[async-lift]` callee, so these
    imports are left to the host. Neither `--explain` nor the attestation
    mentions them.
  - **The fused output also drops the prefix.** The producer's core import is
    `[async-lower]ping`, but meld emits it as plain `my:test/i::ping` with the
    async-lower signature `(i32 i32 i32 i32) -> i32`. The name no longer says
    the call is async. Under this ADR the edge table is keyed by the exact
    emitted import, so the edge itself does not depend on the name. But any
    import meld leaves to the host must keep the producer's field name. That is
    a separate meld defect (#557).
- **kiln on a real fused pair** (ping-pong, meld 21536f0, kiln 1adce1b4): it
  refuses the module at load with E21A0, listing 65 of 102 imports as
  unresolved:
  - 2 async-lower leftovers;
  - 21 WASI imports with a `$N` suffix (kiln SR-81);
  - 1 WASI function kiln doesn't implement (`subscribe-duration`);
  - 20 P3 built-ins kiln doesn't serve at all (future and stream families,
    `[subtask-*]`), so they are refused at load. Subtasks are served from step
    4, streams and futures from step 6. Step 2 covers a different set: the
    built-ins kiln serves today but fakes;
  - 8 unresolved `actual::0-5` shim imports (a separate meld defect, #558);
  - 13 `pulseengine:async` intrinsics (retired by §6).

  So the module is refused loudly at run time; what is silent is meld's
  exit 0.
- **Completing inside the call is not valid (path-A1).** wit-bindgen
  `ping-pong/runner.rs` passes future `rx` into `ping` and writes `tx` only
  after `ping` has returned `STARTED` (`futures::join!(f1, f2)`). Driving
  `ping` to completion inside the call waits on a future its own caller has not
  written yet. Subtasks have to outlive the call.
- **Oracle.** 19 of the 26 pairs compose unfused (wac 0.12) and pass under
  wasmtime 51-dev `-Wcomponent-model-async`. The other 7 need host functions
  that only wasmtime's test harness provides.
- **The existing sync→async trampoline is defective (#555).** It reads the
  wait result in an outdated format, writes scratch data at address 0 of the
  callee's memory, and picks the first `[waitable-set-poll]` import whatever
  its owner. It has never run. gale treats the address-0 write as blocking for
  any P3 use: under `--domain`/`--pack-rebase` it is a cross-domain write.
- **kiln (main 1adce1b4).** kiln runs meld's core output. Its P3 built-ins are
  stubs: `[waitable-set-poll]` returns 0, and `join`, `drop` and `task-cancel`
  are no-ops. Those stubs live in the engine and in kiln-builtins.
  `kiln-async` is no_std and further along than its header says: `poll_round`
  and every P3 intrinsic have a real backing (task, future, waitable-set,
  stream with credit backpressure, error-context; `kiln-async/src/intrinsics.rs:11-41`).
  But nothing links it yet, and it has no subtask concept. The kiln work is
  wiring it in and adding subtasks, not building it from scratch.
- **gale (main 23dd0b4).** gale ships meld → loom → synth → native code. Its
  gust executor is verified: `MAX_TASKS = 8`, a `ready` bitmask, `wake(h)`,
  `set_deadline`, and `poll_round`, which terminates on ready-popcount.
  `dispatch_one`'s `ready == old.ready` is **assumed**, not proven. Every gale
  image uses `--share-stack`.

## Decision (proposed): path-A3

The split: **meld = data, kiln-async = control, gale = time, wake and
isolation.**

### 1. meld emits a static, versioned edge table

meld emits a custom section `pulseengine:async-edges`, `version: 1`, keyed by
**original instance**. kiln refuses to load a module whose section is missing
or malformed. The section has three entry kinds.

- **Edge.** One per `[async-lower]` import that resolves to a fused callee.
  Each edge has a **stable index** in the section (0..n, in section order).
  - The caller's original-instance index, and its exact import
    `(module, field)` including any `$N` suffix. The import is resolved to the
    edge at link time, never by guessing from its name.
  - The callee's original-instance index.
  - The **export names** of the start adapter, the callee's `[callback]` and
    the return adapter. Names are used, not indices, because loom renumbers
    functions on gale's path.
  - The parameter shape (flat i32 count, or a params pointer) and the position
    of `retptr`. kiln stores `retptr` per subtask and passes it to the return
    adapter.
  - The flat result types of the return adapter (see §2).
- **Stream or future type.** One per element type crossing an instance. It
  names the copy adapter's export (preferred), or gives
  `{elem size, align, owning memory}`.
- **Bounds.** Maximum edges, and maximum concurrent subtasks per instance.
  kiln-async and gale use fixed-capacity tables, which refuse loudly when full.

The `$N` suffixes on `$root::[...]` built-ins decode through the same table to
an owning instance, which is what kiln SR-81 needs.

**Encoding.** Binary, in Wasm's own style: a LEB128 version **first** (unknown
versions are refused), then counts, then length-prefixed UTF-8 names and u32
indices. kiln-decoder already parses this format in no_std. CBOR would add a
parser to the trusted code base for no gain.

**Three consumers.**
- **kiln interpreter.** It resolves the named exports at load.
- **loom.** It must keep the section and every named export intact. A fixture
  must prove that.
- **synth (gale's path).** kiln-builtins cannot look up exports at run time:
  synth-compiled code calls fixed `__p3_*` symbols. So synth reads the section
  and turns each edge's adapter and callback names into a dispatch table, which
  kiln-builtins receives at init.
- **The edge index travels in the table, not in the import name.** The caller's
  import keeps the producer's exact `(module, field)`, including any `$N`, and
  each edge entry maps that import to its index. The interpreter resolves
  import → edge once at load. synth resolves the same entry at compile time and
  emits a per-edge stub that calls kiln-builtins with the constant index.
  Renaming imports per edge would create a second naming scheme next to the
  producer's (the reason `pulseengine:async` was rejected). It would also break
  the rule that an import is resolved by an exact table match, never by parsing
  its name.

### 2. meld generates two copy adapters per edge, and no control flow

- **Start adapter.** It runs inside the callee's instance and uses the callee's
  realloc. It copies the caller's parameters into the callee's memory,
  transcoding if needed, calls `[async-lift]`, and returns the packed i32
  **unchanged**: exactly one i32 result, checked at load.
  - It does not decode the code, loop on `YIELD`, or call `[callback]`.
    kiln-async is the only arbiter.
  - The waitable-set index in `WAIT | set<<4` belongs to the **callee's**
    instance.
- **Return adapter.** It is the target kiln routes the callee's
  `[task-return]` to, for this edge only. It copies the results into the
  caller's memory at the stored `retptr`. Its signature is pinned:
  `(retptr: i32, flat results...) -> ()`, with the flat result types listed in
  the edge entry. kiln passes it exactly the `[task-return]` arguments and
  checks arity and types at load, as it does for the start adapter's single
  i32.
- **`[task-return]` stays a runtime built-in.** meld does not rewire it
  statically: the same `[async-lift]` export can be the root task of a host
  call or a subtask of an edge, and only the runtime knows which task is
  current.

### 3. kiln-async runs tasks, subtasks and events

- kiln-async is one library used by both paths: the kiln interpreter's
  `P3Builtin` arms, and kiln-builtins' `__p3_*` on the synth/gale path.
- It owns the subtask and waitable-set tables per original instance, event
  delivery, re-entering `[callback]`, backpressure, and may-enter checks.
- Before calling the start adapter, kiln marks the new subtask as current. A
  `[task-return]` during start then gives the caller `RETURNED`; otherwise the
  caller gets `STARTED | handle<<4`. **Both outcomes are legal on the first
  call.**
- **Event order is part of the contract.** Events raised while a task is being
  polled are queued and become visible from the **next** round, on both the
  interpreter and the synth path (this is the same deferral as gale's pending
  mask, §4(a)). Within a waitable set, delivery is FIFO by a single global
  enqueue sequence number. A subtask's own events are delivered in lifecycle
  order (`STARTED` before `RETURNED`). Identical order on both paths is what
  keeps fuel-bounded replay deterministic.
- **Cancel and drop.** The caller's `[subtask-cancel]` and `[subtask-drop]`
  pass through as `$root::[subtask-*]` built-ins and act on the edge's subtask.
  kiln-async delivers a cancel to the callee through `[callback]` as a
  task-cancelled event. The callee then finishes through `[task-return]` or
  `[task-cancel]`. Dropping a subtask that has not returned is a **trap**, not
  a silent leak.
- Cooperative threads (ADR-9, kiln SR-82) use the **same** task table and
  ready queue. There is one arbiter.
- **Callback ABI only.** An `[async-lift]` callee without `[callback]`
  (stackful) needs fibers, which the synth path cannot provide without
  `unsafe`. meld refuses such an edge loudly.

### 4. gale provides wake, time and isolation

- **Placement.** Subtask and waitable state lives in the partition that owns
  the tasks, inside its MPU region.
- **v1: no async edge across partitions or domains.** meld refuses an edge
  whose caller and callee are in different `--domain`s. With `--domain`, the
  Component Model boundary is gale's privilege boundary (gale#408), and handle
  tables are unforgeable only across that boundary (#427). A later version may
  map such an edge onto a supervisor-owned gale IPC object, under a new
  requirement.
- **Wake seam.** It is the existing gust one, with no second readiness
  structure:
  - `wake(h)`, called **only from the main loop**. An ISR must not call it:
    an interrupt in the middle of `poll_round` would set a ready bit inside the
    poll (breaking obligation (a)) and race the loop (a lost wake-up). An ISR
    instead does an atomic OR into the pending mask, which only the main loop
    drains, between rounds. That is what kiln's REQ_ASYNC_EXTWAKE means;
  - `set_deadline(h, tick)`;
  - `next_deadline()`, which bounds how long the outer loop may sleep in
    `WFI`.
- **Proof obligations gale keeps.**
  - (a) Bounded poll. Nothing sets a ready bit synchronously inside
    `poll_round`. Wake-ups from subtask completion and from event delivery are
    deferred into a pending mask, applied after `poll_round` returns.
  - (b) No lost wake-ups. The pending mask is merged with `|=` (atomically
    from an ISR) and never overwritten. It is drained by calling `wake(h)` once
    per set bit, **never** `ready |= pending`: `wake`'s verified contract sets
    the bit only for a Pending slot, which keeps the ready-bit invariant every
    proof rests on.
  - (c) Static capacity, refused loudly when full.
  - (d) No async, closures or trait objects in the verified core. Callback
    re-entry stays behind the unverified `poll_task` call.

- **Seam and trusted base (gale-owned requirement, before step 4).** On gale's
  path the `__p3_*` entry points become undefined symbols in the dissolved
  object. gale's seam gate requires the undefined set to equal the declared
  seam exactly, so gale extends its seam, and kiln-builtins joins gale's
  unverified trusted base. Export names are not a problem: gale builds with
  `--all-exports` and strips nothing.

### 5. Refusals meld adds (all loud, at fuse time)

- An async edge across `--domain`s (gale, v1).
- An `[async-lift]` callee without `[callback]` on an edge (kiln: no fibers).
- `--share-stack` together with stackful async or cooperative threads. A live
  stack across a suspension is silent memory corruption on gale's targets.
  Stackless callback tasks unwind the shadow stack at `WAIT`, so they stay
  allowed.

### 6. Consequences for existing records

- **ADR-1.** Its host-intrinsic ABI (`pulseengine:async`) for streams and
  futures is superseded. Streams and futures pass through as the producer's
  `$root::[stream-*]` / `[future-*]` imports, consistent with ADR-9 for threads
  and with kiln#621's open question.
- **The sync→async trampoline (#555)** is replaced by the same start/return
  adapters, with kiln-async driving the callee. meld then emits no callback
  loop at all.
- **kiln.** This changes kiln's `rfc46-toolchain-architecture.md:107-111`,
  which says the interpreter does no Component Model async. kiln records that
  change as its own design decision.

## Order of work (proposed)

1. **kiln SR-81:** decode `$N` through the import map.
2. **kiln:** change the stub built-ins to refuse loudly until they are real.
3. **meld:** the section format and refusals (§1, §5), plus the start and
   return adapters (§2), Tier-5 with Mythos. This retires the #555 trampoline.
4. **kiln-async:** link it into the engine and kiln-builtins, and add the
   subtask table (§3). gale: pending-mask wake-ups (§4). **Gate: kiln design
   decision accepted.** That decision reverses `rfc46:107-111` and sets kiln's
   v0.8.0 scope; it needs kiln's maintainer's sign-off, which does not exist
   yet. Steps 1 and 2 do not depend on it, and run in parallel. Step 2 is
   expected to make any fused module fail loudly if it only "works" today
   because `[waitable-set-poll]` returns 0; kiln measures that on the corpus
   first.
5. **Together:** run the 19 acceptance pairs fused on kiln and compare against
   wasmtime.
6. **Last:** streams and futures through per-type copy adapters (§1).

## Open questions

- None open. gale reviewed §4 and §5 (2026-11-04); its three corrections are
  folded into §4.

## Resolved

- **Interim behaviour (maintainer, 2026-11-04, recorded in kiln AD-ASYNC-001
  on kiln PR #624).** Until the step-3 adapters land, meld **refuses** an
  `[async-lower]` edge it cannot fuse, loudly and at fuse time. It no longer
  exits 0. kiln already refuses such a module at load (E21A0, measured on the
  fused ping-pong pair), so the refusal moves the same failure earlier and
  names the edge.
- **kiln's design gate (step 4) is met.** kiln AD-ASYNC-001 (approved) has the
  interpreter reuse kiln-async and supersedes `rfc46:107-111`. kiln schedules
  SR-81 and SR-83 (fake built-ins refuse) for v0.8.0, and SR-84 (kiln-async
  wiring plus subtasks against this section) for v0.9.0, after meld step 3.

- **Section encoding:** binary, in Wasm's own style (§1).
- **Edge-index carriage:** in the table, keyed by the producer's exact import
  (§1).
- **The 7 harness-only pairs:** they stay out of the acceptance set. kiln's
  rules forbid simulated host functions outside test code, and a shim in a test
  module would prove nothing about the product path. They are tracked as
  pending real WASI host functions.
