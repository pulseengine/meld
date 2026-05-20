---
id: ADR-3
type: design-question
title: Cross-component stream<T> adapter — fusing paired stream endpoints at merge time
status: open
gating-fixtures:
  - p3_stream::stream_pair_detected_for_connected_producer_consumer
  - p3_stream::no_pair_when_components_not_fusion_connected
  - p3_stream::no_pair_without_producer_consumer_complementarity
  - p3_stream::memory_mode_follows_strategy
design-paths:
  - N — Detection foundation now, runtime-verified emitter follow-up (chosen, this PR)
  - O — Full ring-buffer / copy-chain emitter in a single PR (rejected — cross-component stream codegen cannot be runtime-verified at foundation time)
  - P — Keep host routing, never fuse stream endpoints (rejected — every fused stream pays a host round-trip even when both ends live in the merged module)
---

# ADR-3 — Cross-component `stream<T>` adapter

## Context

ADR-1 fixed the host-intrinsic ABI: every component's `stream<T>` /
`future<T>` operations lower to imports under module
`pulseengine:async`. ADR-2 fixed the error / backpressure conventions
those intrinsics follow.

Both ADRs treat each component in isolation. They leave a gap that
issue #94's audit (deliverable A) and issue #141 call out:

> When two fused components share a `stream<T>` end-to-end — one holds
> the writable end, the other the readable end — meld still lowers both
> sides to *host* imports. Every byte crosses the host boundary twice
> (a `stream_write` on the producer, a `stream_read` on the consumer)
> even though both ends now live in the same merged module.

This is the stream-plane analogue of the synchronous-data problem meld
already solves: when component A calls component B's exported function,
meld emits an in-module adapter rather than routing the call through
the host. The same should hold for a `stream<T>` that A produces and B
consumes.

`stream<T>` is *runtime* data flow — `stream.new` mints the handle pair
at runtime, and which bytes flow when is not statically knowable. But
the **pairing** is static: the resolver already knows that component
A's `stream<T>`-bearing export was resolved to component B's import.
That static pairing is what an in-module stream adapter keys off.

## Decision

**Path N — land the detection foundation now; land the emitter as a
runtime-verified follow-up.**

This PR ships everything that can be proven correct with unit tests and
no wasm runtime:

1. A new `meld-core/src/p3_stream.rs` module (sibling to `p3_async.rs`)
   with the data model and a pure detection function.
2. `StreamPairGraph` — the merge-time inventory of cross-component
   stream pairings, attached to `DependencyGraph` next to the existing
   `resource_graph`.
3. The detection itself: a pure function over
   `(&[ParsedComponent], &resolved_imports, MemoryStrategy)`.

The **emitter** — the wasm codegen for the two adapter shapes below —
is deferred to a follow-up PR. Cross-component stream codegen is data-
plane wasm that is only *correct* if a real P3 component runs through
it on kiln / wasmtime. Landing emitter code that compiles and passes
structural byte-pattern assertions but has never executed would put an
unverified data-plane transform into the merged module — precisely the
H-1 (semantic divergence) / H-3 (misrouted call) hazard class meld's
Mythos and LS-N gates exist to prevent. The repo already shipped P3 in
exactly this staged shape: #124 was the lowering *foundation*, #129 the
full lowering *pass*.

### Why not Path O

A single PR carrying the full emitter would be unreviewable against the
"trust but verify" bar: neither the author nor a reviewer can confirm
the emitted ring buffer or copy chain executes correctly without a
cross-repo runtime loop that does not exist yet. The foundation/emitter
split lets the emitter PR be small, focused, and paired with the
runtime fixture that proves it.

### Why not Path P

Leaving every fused stream on host routing means a `stream<T>` passed
between two components that meld has already merged into one module
still costs a host `stream_write` + host `stream_read` per chunk. That
is the cost fusion exists to remove. Path P is the status quo and the
thing #141 is filed to change.

## The two adapter shapes (emitter follow-up — documented here so the
## foundation records the right data)

The emitter mirrors the existing synchronous multi-memory /
shared-memory split (`generate_direct_adapter` vs
`generate_memory_copy_adapter`):

| Mode | Trigger | Adapter shape |
|---|---|---|
| **Same memory** | `MemoryStrategy::SharedMemory` | Direct ring buffer. Producer and consumer share an in-module queue page; the producer's `stream_write` and the consumer's `stream_read` become ring-buffer cursor operations. Zero-copy. |
| **Cross memory** | `MemoryStrategy::MultiMemory` | `stream_read` from the producer's memory → in-module copy loop → `stream_write` into the consumer's memory. `cabi_realloc`-style allocation on the receiver side. Identical null-guard policy as LS-A-7 (a null realloc result aborts the copy rather than writing through a null pointer). |

Both must preserve the ADR-2 backpressure and EOF contracts end to
end: a `Partial` write on the consumer side propagates back as
backpressure to the producer; an `Eof` from the producer propagates
as a clean stream close to the consumer.

For the foundation to feed the emitter, `StreamPair` records each
endpoint's component index and role (producer / consumer), the shared
parsed element type, and the memory mode.

## What the foundation detects — and its precision boundary

The detection is deliberately conservative. A `StreamPair` is recorded
only when **all** hold:

1. Two distinct components are *fusion-connected* — there is a
   `resolved_imports` entry linking them (in either direction).
2. One component has a **producer** role on a stream — it declares a
   `CanonicalEntry::StreamWrite { ty }` whose `ty` resolves to a
   `stream<T>` component type.
3. The other has a **consumer** role — a `CanonicalEntry::StreamRead`
   on a stream carrying the **same element type** T.

The detection does **not** prove the two endpoints carry the *same
runtime handle* — that is unknowable at build time. It proves the
weaker, sufficient-for-fusion fact: two merged, connected components
where one writes and one reads a stream of the same element type. Each
recorded `StreamPair` is therefore a *candidate* pairing the emitter
follow-up (and #142) refines with signature-level matching.

Pairing on matching element type — rather than any producer with any
consumer — is the line between an honest candidate and a hallucinated
one: a `stream<u8>` and a `stream<s32>` between the same two
components are unambiguously two *different* streams, and recording
that as a pair would be a finding meld's Mythos protocol would reject
("hallucinations are more expensive than silence"). Issue #142's
check (i) (`stream<A>` resolved to `stream<B>`, A ≠ B) operates at the
finer signature granularity #142 itself builds; the foundation does
not manufacture cross-type pairs for it to reject.

Stream element-type indices (`CanonicalEntry::Stream*{ty}`) are
component-local; the foundation matches endpoints by parsed element
type *descriptor*, never by raw index, because component A's type
index 5 and component B's type index 5 are unrelated.

## Out of scope (this PR)

- The ring-buffer and copy-chain **emitter** — follow-up, runtime-verified.
- `future<T>` pair fusion — `future` is the degenerate single-value
  stream; the same graph generalises but the emitter shape differs.
- Static validation of the detected pairs (type compatibility, capacity,
  cycles, lifetime) — that is issue #142, which consumes this graph.

## Rivet artifact

New requirement **SR-33** — "Cross-component `stream<T>` fusion at
merge time". The foundation satisfies the detection half; the emitter
follow-up satisfies the codegen half.

## Test fixtures

The `gating-fixtures` above pin the foundation's contract:

- `stream_pair_detected_for_connected_producer_consumer` — a producer
  component and a consumer component linked by a resolved import yield
  exactly one `StreamPair` with the correct producer/consumer roles
  and shared element type.
- `no_pair_when_components_not_fusion_connected` — a producer and a
  consumer of the same stream element type that are *not* linked by a
  resolved import yield no pair.
- `no_pair_without_producer_consumer_complementarity` — two connected
  components that both only produce (or both only consume) a stream
  yield no pair.
- `memory_mode_follows_strategy` — `SharedMemory` ⇒ `SameMemory`,
  `MultiMemory` ⇒ `CrossMemory`.
