# STPA Comparative Analysis: BA RFC #46 vs Meld

**RFC:** bytecodealliance/rfcs#46 — "Propose tools and APIs for lowering
components to core modules" (dicej, 2026)

**Analysis date:** 2026-03-10
**Status:** Initial analysis — RFC has zero reviewer comments

---

## 1. System Boundary Comparison

### RFC `lower-component` system boundary

```
P2/P3 Component
    │
    ▼
┌─────────────────────────────────────────────────┐
│  lower-component                                │
│  ┌──────────┐  ┌──────────┐  ┌───────────────┐ │
│  │  Parser   │→│ Resolver  │→│   Merger +     │ │
│  │          │  │          │  │   Adapters     │ │
│  └──────────┘  └──────────┘  └───────────────┘ │
│                                                 │
│  ┌──────────────────────────────────────┐       │
│  │  CM Runtime (compiled from Rust)      │       │
│  │  • Resource table mgmt               │       │
│  │  • Stream/future I/O                  │       │
│  │  • Task/thread bookkeeping            │       │
│  └──────────────────────────────────────┘       │
│                                                 │
│  Host intrinsic imports:                        │
│  • fiber create/suspend/resume                  │
│  • fiber-local state                            │
│  • stack traces                                 │
└─────────────────────────────────────────────────┘
    │
    ▼
Core Module (with host intrinsic imports)
    │
    ▼
┌─────────────────────────────────────────────────┐
│  host-wit-bindgen                               │
│  • Host function definitions                    │
│  • Instantiation + invocation wrappers          │
│  • Type checking at boundary                    │
│  • Memory/global access                         │
└─────────────────────────────────────────────────┘
    │
    ▼
Runtime-specific bindings (Rust/C/Go/JS/...)
```

### Meld system boundary (current)

```
P2/P3 Component
    │
    ▼
┌─────────────────────────────────────────────────┐
│  Meld                                           │
│  ┌──────────┐  ┌──────────┐  ┌───────────────┐ │
│  │  Parser   │→│ Resolver  │→│   Merger +     │ │
│  │          │  │          │  │   Adapters     │ │
│  └──────────┘  └──────────┘  └───────────────┘ │
│                                                 │
│  ┌──────────────────────┐                       │
│  │  Component Wrapper    │  (optional P2 wrap)  │
│  │  • Stubs module       │                      │
│  │  • Canon lower/lift   │                      │
│  └──────────────────────┘                       │
│                                                 │
│  ┌──────────────────────┐                       │
│  │  Attestation          │  (optional provenance│
│  │  • wsc-attestation    │   custom section)    │
│  └──────────────────────┘                       │
└─────────────────────────────────────────────────┘
    │
    ▼
Core Module (self-contained, no host intrinsics)
  ─── or ───
P2 Component (re-wrapped for runtime consumption)
    │
    ▼
┌─────────────────────────────────────────────────┐
│  Syn + Kiln  (PulseEngine — separate tools)     │
│  • Host bindings generation                     │
│  • Runtime integration                          │
└─────────────────────────────────────────────────┘
```

### Key structural difference

| Aspect | RFC `lower-component` | Meld |
|--------|----------------------|------|
| Output self-contained? | No — requires host intrinsics | Yes — zero host imports (sync path) |
| Async CM support | Yes (fibers, streams, futures) | P2 stable first; P3 imminent (weeks) |
| Runtime code embedded | Yes (Rust-compiled CM runtime) | No |
| Host bindings | In scope (`host-wit-bindgen`) | Out of scope (syn/kiln) |
| Attestation/provenance | Not mentioned | Yes (wsc-attestation) |
| Formal verification | Not mentioned | Yes (Rocq proofs, 286 Qed) |
| Reproducibility | Not mentioned | Yes (deterministic output) |
| Multiply-instantiated | Open question | Not yet handled |

---

## 2. New Losses Introduced by RFC Scope

The RFC's expanded scope introduces losses that Meld's current STPA does not
cover, because Meld's system boundary excludes them.

### RL-1: Loss of async correctness

The CM runtime embedded in the lowered module manages resource tables, stream/
future I/O, and task bookkeeping. If this runtime has bugs, async component
interactions silently corrupt state or deadlock.

**Why Meld avoids this:** Meld only handles the sync path. No runtime code is
embedded. Async would be a future scope expansion.

### RL-2: Loss of fiber isolation

Host-provided fiber intrinsics (create, suspend, resume) can violate control
flow integrity if the lowered module's generated code misuses them, or if the
host implements them incorrectly.

**Why Meld avoids this:** Meld produces self-contained modules with no fiber
imports.

### RL-3: Loss of host/guest type safety at invocation boundary

If `host-wit-bindgen` generates incorrect bindings, or `lower-component`
embeds wrong type metadata, host→guest and guest→host calls can silently
misinterpret arguments.

**PulseEngine mapping:** This loss lives in **syn/kiln**, not meld. The
P2 component wrapper provides the type boundary — syn/kiln consume it.

### RL-4: Loss of portability

The RFC aims for runtime-agnostic operation. If the Host C API is
underspecified or implementations diverge, the same lowered module behaves
differently across runtimes.

**Why Meld avoids this:** Meld's output is standard core wasm (or P2 component).
No custom host API needed.

### RL-5: Loss of code size efficiency (bloat)

For multiply-instantiated modules, the RFC acknowledges potential "significant
bloat" from duplicating functions. A batteries-included language like Python
could multiply the output size.

**Meld status:** Not yet handled. Same open question applies.

---

## 3. New Hazards from RFC Scope

### RH-1: Embedded CM runtime corrupts resource table state

The Rust-compiled CM runtime manages resource handles, waitables, streams, and
futures in guest-side tables. An off-by-one in table indexing, a use-after-free
of a resource handle, or a race in task bookkeeping corrupts internal state
silently.

**Losses:** RL-1
**Meld equivalent:** None — no runtime embedded.

### RH-2: Fiber intrinsic misuse causes stack corruption

The generated module calls fiber_create/fiber_suspend/fiber_resume in incorrect
order or with wrong parameters. The host runtime corrupts the call stack,
produces dangling fiber references, or leaks fiber memory.

**Losses:** RL-2
**Meld equivalent:** None — no fiber support.

### RH-3: Type metadata in lowered module doesn't match actual signatures

`lower-component` embeds type metadata that `host-wit-bindgen` reads to
generate host bindings. If the metadata is inconsistent with the actual
flattened function signatures, the host passes wrong-sized arguments or
reads wrong return types.

**Losses:** RL-3
**Meld equivalent:** H-8 (component wrapping) covers part of this for the P2
wrapper path. syn/kiln would own the host-bindings side.

### RH-4: Host C API implementation diverges across runtimes

The RFC defines a C API that runtimes must implement. If the API semantics
are ambiguous (e.g., fiber lifetime, memory ownership of buffers, error
signaling), different runtimes implement different behaviors.

**Losses:** RL-4
**Meld equivalent:** None — Meld targets a standard (core wasm / P2 component).

### RH-5: Function duplication for multiply-instantiated modules breaks sharing

When the same module is instantiated N times, duplicating functions changes
the semantics: leaf functions that should share state (globals, memory) are
split into independent copies with independent state.

**Losses:** RL-5, RL-1 (semantic correctness)
**Meld equivalent:** Not yet handled — same open question.

### RH-6: Guest-to-guest stream I/O deadlocks or corrupts data

Two guest components communicating via streams/futures through the embedded CM
runtime can deadlock if the scheduling is non-preemptive, or corrupt data if
buffers are shared across concurrent tasks without synchronization.

**Losses:** RL-1
**Meld equivalent:** None — sync only.

---

## 4. Open Questions — STPA Analysis

### Q1: Multiply-instantiated modules

**RFC options:** reject, duplicate, multi-module output

**STPA assessment:**

| Option | Hazard profile |
|--------|---------------|
| Reject | Safest — clear failure mode. But limits component coverage. |
| Duplicate | H-3 (index remapping) applies: duplication must correctly rebase all indices per instance. H-1 risk: shared state semantics change. Bloat risk (RL-5). |
| Multi-module | New control structure: external linker becomes a controller. Loss scenario: metadata format misspecifies linking order → H-5 (wrong instantiation order). Portability risk: not all runtimes support multi-module linking. |

**Recommendation for Meld:** Start with "reject" (fail-fast, SC-8/SC-9),
add "duplicate" when needed with the existing merger infrastructure (index
remapping is already proven correct for N components; N instances of the same
module is a special case).

### Q2: Type checking responsibility — host-wit-bindgen vs lower-component

**STPA assessment:**

If `lower-component` does type checking:
- Every call goes through validation → performance penalty
- But: validation runs in the **same trust domain** as the lowered module
- UCA: validation logic has a bug → H-4 (wrong adapter behavior) or H-1

If `host-wit-bindgen` does type checking:
- Static type guarantees from target language (Rust, Go) can eliminate runtime checks
- But: trust boundary crossed — host must be trusted
- UCA: host bindings generator has a bug → RL-3 (type safety loss)

**Recommendation for PulseEngine:** Split responsibility:
- **Meld** validates at fusion time (resolver + merger verify type compatibility)
- **syn/kiln** generate statically-typed host bindings that don't need runtime checks
- Runtime validation only for dynamic/untrusted inputs

### Q3: Thread-local state management — module vs host

**STPA assessment:**

Module-side management:
- More code in the TCB of the lowered module
- But: runs sandboxed in wasm, so bugs are contained
- UCA: TLS indexing bug → only affects that module instance

Host-side management:
- Smaller wasm module, but larger host TCB
- Host TLS bugs can affect ALL module instances
- UCA: host TLS corruption → cross-component state leak (RL-2 equivalent)

**Recommendation:** Module-side is safer (sandboxed). Matches Meld's philosophy
of self-contained output. If async is added to Meld, prefer wasm-side state
management with minimal host intrinsics.

---

## 5. Control Structure Delta

New controllers the RFC introduces that Meld doesn't have:

| Controller | RFC role | PulseEngine equivalent |
|-----------|---------|----------------------|
| CM Runtime (embedded) | Resource tables, stream/future I/O, task mgmt | Not needed (sync only) |
| Fiber Manager (host) | Create/suspend/resume fibers | Not needed (sync only) |
| host-wit-bindgen | Generate host-side bindings | **syn/kiln** |
| Host C API impl | Runtime-specific operations | Runtime-dependent; out of scope |

New controlled processes:

| Process | RFC role | PulseEngine equivalent |
|---------|---------|----------------------|
| Resource Table | Handles, waitables | Not needed |
| Fiber Stack | Execution context | Not needed |
| Type Metadata | Embedded type info for host bindings | P2 component type section (CTRL-WRAPPER) |
| Stream/Future Buffers | Async data transfer | Not needed |

---

## 6. Unsafe Control Actions — RFC-specific

### Embedded CM Runtime

| ID | UCA | Type | Hazard |
|----|-----|------|--------|
| UCA-RT-1 | Runtime allocates resource handle but doesn't initialize table entry | not-providing | RH-1 |
| UCA-RT-2 | Runtime drops resource handle while still referenced by stream | too-early | RH-1, RH-6 |
| UCA-RT-3 | Runtime allows concurrent access to non-thread-safe stream buffer | providing-causes-hazard | RH-6 |
| UCA-RT-4 | Runtime task scheduler starves one component indefinitely | too-late | RH-6 |

### Fiber Manager

| ID | UCA | Type | Hazard |
|----|-----|------|--------|
| UCA-FM-1 | Host creates fiber with insufficient stack size | providing-causes-hazard | RH-2 |
| UCA-FM-2 | Host resumes already-completed fiber | providing-causes-hazard | RH-2 |
| UCA-FM-3 | Host doesn't resume suspended fiber (leak) | not-providing | RH-6 |
| UCA-FM-4 | Host reads fiber-local state from wrong fiber | providing-causes-hazard | RH-2 |

### host-wit-bindgen (→ syn/kiln in PulseEngine)

| ID | UCA | Type | Hazard |
|----|-----|------|--------|
| UCA-HB-1 | Generated bindings use wrong memory index for multi-memory module | providing-causes-hazard | RH-3 |
| UCA-HB-2 | Generated bindings don't validate string encoding at boundary | not-providing | RH-3 |
| UCA-HB-3 | Generated bindings read type metadata from wrong custom section offset | providing-causes-hazard | RH-3 |
| UCA-HB-4 | Generated bindings assume single-memory when module uses multi-memory | providing-causes-hazard | RH-3 |

---

## 7. Gap Analysis: What Each System Misses

### RFC gaps (things Meld covers that the RFC doesn't mention)

| Gap | Description | Meld coverage |
|-----|-------------|--------------|
| RG-1 | **Attestation/provenance** — no mention of tracking transformation lineage | wsc-attestation, SR-27 through SR-30 |
| RG-2 | **Build reproducibility** — no mention of deterministic output | L-4, H-7, SR-19 |
| RG-3 | **Formal verification** — no mention of proving correctness | 286 Qed proofs, Rocq pipeline |
| RG-4 | **Certification evidence** — no mention of safety-critical use | L-5, full STPA, traceability matrix |
| RG-5 | **Cycle-tolerant topology** — composed-runner components create cycles | Implemented (cycle-tolerant sort) |
| RG-6 | **CopyLayout static analysis** — element sizing computed at fusion time | CopyLayout enum, recursive fixup |

### Meld gaps (things the RFC covers that Meld doesn't)

| Gap | Description | Priority | Owner |
|-----|-------------|----------|-------|
| MG-1 | **Async CM** — streams, futures, task mgmt | Blocked on P3 ecosystem tools | Meld + gale/kiln |
| MG-2 | **Resource types** — handle tables, drop | Blocked on P3 ecosystem tools | Meld (#10) |
| MG-3 | **Multiply-instantiated modules** | Medium — can occur in P2 | Meld (#24) |
| MG-4 | **Host bindings generation** | N/A — out of scope | syn/kiln |
| MG-5 | **Fiber/stack-switching support** | Blocked on P3 ecosystem tools | Meld + gale/kiln |
| MG-6 | **Host C API definition** | N/A — out of scope | syn/kiln + runtime |

---

## 8. Recommendations

### For Meld

1. **MG-3 is the highest-priority gap.** Create an issue for multiply-
   instantiated module support. Start with "reject" (safe default), then
   add "duplicate" mode.

2. **MG-2 (resources) is next.** Already tracked in #10. The RFC's CM runtime
   approach (embed Rust-compiled resource table manager) is one option; Meld
   could also generate static resource table code at fusion time.

3. **Async (MG-1, MG-5) is blocked on P3 ecosystem availability.** Meld is
   ready to move; the upstream tools (wit-bindgen, runtime support, stack
   switching) aren't. Gale and kiln are already being prepared for this.
   When P3 tools land, the key architectural decision is whether to embed a
   CM runtime (RFC approach) or generate static async adapters at fusion time
   (preserving self-contained output). Prefer wasm-native stack switching
   over host fiber intrinsics to minimize TCB.

4. **Host bindings (MG-4, MG-6) belong in syn/kiln.** The RFC's `host-wit-bindgen`
   maps directly to PulseEngine's syn/kiln tools. Meld's P2 component wrapper
   provides the interface contract that syn/kiln consume.

### For the RFC

5. **Consider attestation.** Safety-critical deployments need transformation
   provenance. A custom section standard for recording input hashes, tool
   version, and configuration would benefit the ecosystem.

6. **Consider reproducibility.** Build systems (Bazel, Nix) require deterministic
   output. The RFC should specify that `lower-component` produces identical
   output for identical input.

7. **Specify the multiply-instantiated module decision.** This is the biggest
   architectural fork. The choice affects the entire downstream tooling.

8. **The TODO sections need filling.** Both C API sections say "(TODO: Sketch
   the proposed API)". The safety analysis of the RFC is incomplete without
   these — they define the trust boundary.

---

## 9. Trust Boundary Comparison

```
RFC approach:
  ┌─ Trusted (host) ─────────────────────┐
  │  Host C API implementation            │
  │  fiber mgmt, memory access, store     │
  │  host-wit-bindgen output              │
  │                                       │
  │  ┌─ Sandboxed (wasm) ──────────────┐  │
  │  │  Lowered module                  │  │
  │  │  + embedded CM runtime           │  │
  │  │  + FACT adapters                 │  │
  │  └────────────────────────────────┘  │
  └───────────────────────────────────────┘

Meld approach:
  ┌─ Trusted (host runtime) ──────────────┐
  │  wasmtime / wamr / browser            │
  │  (standard core wasm execution)       │
  │                                       │
  │  ┌─ Sandboxed (wasm) ──────────────┐  │
  │  │  Fused module                    │  │
  │  │  (self-contained, no intrinsics) │  │
  │  │  + FACT adapters                 │  │
  │  └────────────────────────────────┘  │
  │                                       │
  │  syn/kiln (build-time, not runtime)   │
  └───────────────────────────────────────┘
```

**Key insight:** Meld's trust boundary is smaller. The fused module runs on
any standard wasm runtime without a custom host API. The RFC's approach requires
every runtime to implement the Host C API correctly — each implementation is a
new source of trust boundary violations.

The trade-off is deliberate: Meld builds on P2 first because the P3 toolchain
ecosystem isn't ready yet. The constraint is practical availability of tools
(wit-bindgen P3 support, runtime P3 implementations, stack-switching in
runtimes) — not timeline or ambition. P3 support in Meld is weeks away once
the upstream tooling is available to build and test against.

The PulseEngine toolchain is actively preparing for P3 across multiple tools:
gale and kiln are being designed for threads, async, and the P3 execution model.
Meld's P2 foundation is formally verified and solid — when the P3 ecosystem
tools land, P3 additions build on proven infrastructure rather than refactoring
an everything-at-once implementation that was coupled to in-progress specs.

When Meld adds P3 support, the async hazards (RH-1, RH-2, RH-6) become relevant
and will need to be incorporated into the main STPA. The key architectural
question at that point: embed a CM runtime (as the RFC proposes) or generate
static async adapters at fusion time (keeping the self-contained property).
Gale and kiln will own the runtime-side integration for threads and async I/O.
