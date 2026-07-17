---
id: ADR-7
type: design-question
title: ABI & linking-strategy architecture — canonical mix-and-match vs a symmetric/PIC fast lane
status: resolved
gating-fixtures:
  # The invariant any chosen path MUST preserve: the standard canonical-ABI
  # fusion path stays green (mix-and-match is not sacrificed for the fast lane).
  - rebasing_end_to_end::test_326_reloc_const_rebasing_end_to_end
  - rebasing_end_to_end::test_address_rebasing_end_to_end
  - drop_realloc  # canonical cabi_realloc adapter path
  # Future gate for the optimization path (symmetric/PIC), to be added with the
  # first increment of the chosen path:
  - pic_shared_everything::flatten_disjoint_addresses  # (planned #353)
design-paths:
  - path-G — bolt-on — add symmetric-ABI / PIC handling inline in the current merger + lib.rs alongside the canonical path (rejected — deepens the coupling this ADR exists to fix)
  - path-H — clean strategy-split — ABI-agnostic verified core + pluggable PER-BOUNDARY call-lowering strategy (canonical-FACT default, symmetric-direct opt-in) + pluggable address/memory strategy (multi / shared-rebase / static-base-PIC), canonical as the universal fallback (recommended)
  - path-I — separate tool — a distinct "meld-symmetric" for the safety path, leaving meld canonical-only (rejected — duplicates the proven core, fragments the toolchain)
  - path-J — do nothing — canonical-only fusion + `--emit-relocs`; decline symmetric/PIC entirely (the status-quo baseline)
---

# ADR-7 — ABI & linking-strategy architecture

## Context

### The invariant: RFC-46 conformance and maximum mix-and-match

meld's charter is **BA RFC #46** (bytecodealliance/rfcs#46 — "lower components
to core modules"). RFC #46 *is* the standard, canonical-ABI static-fusion
contract, and it is what lets components be **mixed and matched** across the
ecosystem: any conforming P2/P3 component fuses with any other. This is the
property we must not trade away. "Staying true" = remaining a conforming RFC-46
lowering tool whose output composes in the standard ecosystem; meld's
differentiators *within* RFC-46 are self-contained output (no host intrinsics —
see ADR-6, and the RFC-46 comparative analysis in `safety/stpa/`) and mechanized
verification of the core transforms.

The one RFC-46 item the comparative analysis flags as **not yet handled** is
**multiply-instantiated modules** (Q1: reject / duplicate / multi-module). That
same "several core instances sharing state" question is exactly the topology the
shared-everything spike (#353) must model — so fulfilling RFC-46 and the
optimization direction below share a core of work.

### The opportunity: a shared-address-space fast lane

Two producer-side, opt-in mechanisms dramatically simplify fusion for the
single-address-space / safety-critical target (gale ASIL-D, jess/falcon
Cortex-M):

- **PIC / shared-everything linking** (#353): addresses become
  `__memory_base + offset`; meld assigns a disjoint base per module and folds it
  to a constant. There are no absolute-address relocation sites, so the entire
  `reloc.CODE` rebasing machinery (#326→#340, and the #351 drift class) is
  *structurally unnecessary* on this path. Verified feasible (#353 spike).
- **Symmetric ABI** (cpetig/wit-bindgen; WasmCon24 SDV): "use the import ABI also
  for exports", native representations passed by pointer, no `cabi_realloc`
  phase, handles pointer-sized = `rep`. Cross-component calls become **ordinary
  linking of mangled symbols** — zero-copy, no dynamic allocation (the functional
  -safety property). meld's ~16.4k-line FACT/adapter subsystem
  (`meld-core/src/adapter/`) exists *only* because the canonical ABI assumes
  disjoint memories; for symmetric inputs those calls are direct.

### The tension (why this ADR exists)

The fast lane's power comes precisely from **giving up the universal ABI**:
symmetric composes with symmetric, PIC with PIC; a stock canonical wasip2
component does **not** mix with either. Adopting the fast lane naively would
trade ecosystem mix-and-match for a closed, optimized world — the opposite of
the invariant above.

**Reconciliation:** the fast lane need not be subtractive if ABI/linking is a
**per-boundary strategy** with **canonical as the universal fallback** — direct
wiring only where *both* sides opt into symmetric+PIC, the existing FACT adapter
at every boundary that touches a canonical component. Composability is never
lost; zero-copy is *gained* where both sides opt in.

### The coupling reality (why "split", not "rewrite")

- **Adapter/FACT (16.4k lines) is already separable** — the merger has **zero**
  references to it; it is wired from `lib.rs`. It can become a pluggable
  call-lowering strategy without touching the verified core.
- **Address/rebasing IS interleaved** — the merger has ~26 references to
  `reloc`/`address_rebasing`. This concern must be *extracted* into a pluggable
  address strategy.
- The ABI-agnostic core (parser → resolver → merger index-merge — the
  Rocq-proven part) stays untouched.

So the clean split is a **moderate, incremental refactor**, not a rewrite.

## The design space

- **path-G — bolt-on.** Add symmetric/PIC branches inline in the current merger
  + `lib.rs`. Fastest to a first result, but deepens exactly the coupling that
  makes the current adapter+reloc code hard to verify and evolve. Rejected: a
  bolt-on before the split makes the eventual split harder.
- **path-H — clean strategy-split (recommended).** Layer meld:
  1. **ABI-agnostic core** — parser, resolver, index-space merge (unchanged;
     keeps the proofs).
  2. **Per-boundary call-lowering strategy** — a seam formalizing the choice
     already made implicitly in `lib.rs`: `Canonical` (FACT adapter, default,
     universal) vs `SymmetricDirect` (opt-in, both sides symmetric). Canonical is
     the fallback at any mixed boundary, so mix-and-match is preserved by
     construction.
  3. **Address/memory strategy** — extract from the merger: `MultiMemory`,
     `SharedRebase` (relocatable, ADR-6 path-D), `StaticBasePIC` (#353).
  Multiply-instantiated modules (RFC-46 Q1) is handled once, in the core-instance
  topology layer, and reused by both the canonical and PIC address strategies.
- **path-I — separate tool.** A distinct `meld-symmetric`. Rejected: duplicates
  the verified core and fragments the toolchain; the split of path-H gives the
  same isolation without a fork.
- **path-J — do nothing.** Canonical-only + `--emit-relocs`; decline symmetric/
  PIC. The honest baseline: it keeps mix-and-match and ships #352, but forgoes
  the zero-copy / allocation-free / far-more-verifiable safety path and leaves
  RFC-46 Q1 unresolved.

## Decision (accepted 2026-07-16)

**path-H is adopted.** The two human-owned calls were made deliberately, against
the review's default recommendation, in favour of maximal control + verifiability:

1. **Identity — balanced / dual.** meld is BOTH the generic RFC-46 canonical
   reference fuser (full mix-and-match) AND the sealed-safety product
   (symmetric+PIC, verified, allocation-free, attested). Both are first-class;
   neither is merely "a profile on the other."
2. **Ownership — own the full fusion stack.** meld keeps and formally verifies
   the entire lowering implementation — canonical FACT (~16.4k lines),
   symmetric-direct, and static-base PIC — depending on NO external lowering.
   Rationale that overrides the review's "track upstream": a formally-verified,
   15–30 yr-lifecycle safety tool must own a **frozen, verifiable trusted base**;
   you cannot verify wasmtime's evolving FACT, and self-contained output is
   already a differentiator. Control + verifiability beat escaping the treadmill.

**Distinction that reconciles "own the fork" with "don't fragment":** meld owns
its **implementation**; the **ABIs/conventions stay open standards** — drive the
symmetric ABI to a BA/wit-bindgen spec and the PIC static-base convention to
tool-conventions. Owning a verified impl of an open standard is not privatizing
the standard. Mix-and-match is preserved (path-H canonical fallback); a
third-party canonical component still composes.

**Standing requirements (from the 10-persona review, unchanged and now binding):**
silent-downgrade = hard error; per-boundary strategy declared/attested/observable;
two attested profiles (`open/ecosystem`, `sealed-safety`); and the
**heterogeneous-composition theorem** (any {canonical,symmetric}×{multi,rebase,
PIC} ≡ pure-canonical) — now *mandatory*, since meld owns and verifies the whole
matrix.

**Risks accepted with this decision (named, not hidden):**
1. *Scope / budget* — dual identity + own-everything is the largest surface; the
   review's "splits a small team's budget" and "garrison the commodity" both
   apply. Mitigation: canonical is largely built already; sequence symmetric/PIC
   as the additive safety lane; lean on the agent-driven development model.
2. *Canonical-parity treadmill* — owning FACT means tracking the Component Model
   spec. Mitigation: the RFC-46 conformance suite gates drift; being the
   reference means helping set the pace, not only chasing it.
3. *Proof surface* — owning the full 2×3 matrix multiplies the verification /
   MC-DC obligation; the heterogeneous-composition theorem is the linchpin.

**Next increments (path-H, additive — canonical stays green throughout):**
1. Extract the address strategy out of the merger (multi / shared-rebase /
   static-base-PIC) — "the split, increment 1"; behavior-preserving refactor.
2. Formalize the per-boundary call-lowering seam (canonical-FACT default /
   symmetric-direct opt-in), with the declared/attested/hard-fail contract.
3. Fulfill RFC-46 Q1 (multiply-instantiated modules) — converges with the #353
   shared-everything core-instance topology work.
4. #353 Path-A PIC static-flatten prototype; symmetric-direct lowering behind the
   seam; begin the heterogeneous-composition proof.

## Recommendation (superseded by the Decision above; retained for rationale)

**path-H.** It is the only path that (a) holds the RFC-46 mix-and-match invariant
as a hard constraint (canonical universal fallback), (b) lets the symmetric/PIC
fast lane be *additive*, opt-in, and never subtractive, (c) does the RFC-46
multiply-instantiated-modules work once and shares it, and (d) is a moderate
refactor given the existing seams, not a rewrite. Sequence it **before** bolting
symmetric/PIC on, so the optimization lands as a clean strategy, not more
coupling.

Near-term this does not block #352 (the backstop for the canonical `--emit-relocs`
path) — that ships and serves the mix-and-match path today.

## Strategic review (10-persona) — consensus, refinements, the open choice

A 10-persona review (Standards Steward, Commercial Moat Strategist,
Functional-Safety Engineer, Component-Model Core Architect, Embedded/MCU Lead,
Toolchain Maintenance Realist, Formal-Methods Researcher, Max-Composability
Advocate, DX Lead, Adversarial Competitor) stress-tested this direction against
the crux question: *how much to give away / make generic-for-all vs. keep as
PulseEngine's own.* The following is **decision-independent consensus** and now
refines this ADR regardless of the identity choice below.

### Consensus (unanimous or near) — adopted as requirements

1. **path-H is endorsed by all ten.** No dissent on the per-boundary /
   canonical-fallback architecture.
2. **Give away the ABIs; keep the proofs.** The mechanisms (canonical FACT, the
   symmetric calling convention, PIC `__memory_base` static-base folding) are
   commodity conventions — of no durable value if privatized. The **moat is the
   mechanized-verified core + the soundness/no-alloc proofs + the ASIL-D/DO-178C
   attestation.** Sell the *verification of the fused artifact*, not the fusion.
3. **Silent downgrade is the top safety risk → a hard requirement.** A boundary
   quietly falling back from symmetric/no-alloc to canonical (heap +
   `cabi_realloc` + transcoding) inside a sealed image would smuggle a dynamic
   allocator into an ASIL-D TCB with no signal. **Per-boundary strategy MUST be
   declared, attested, and observable; an unmet symmetric/PIC precondition MUST be
   a hard, loud error — never a silent adapter insertion or rebase.** (Add a
   `--explain` per-edge boundary report.)
4. **Symmetric must not remain a single-vendor fork.** Drive cpetig/Aptiv's
   symmetric ABI into a BA / wit-bindgen named, versioned convention (and the PIC
   static-base convention into tool-conventions) **before** shipping a safety
   product against it; a 15–30 yr safety case cannot cite a hand-tracked fork.
   Until then the symmetric strategy is gated **experimental / non-portable**.
5. **The 16.4k-line adapter subsystem is a cost centre, not a moat** —
   co-maintain / track upstream; do not garrison it.
6. **Concrete shape: one binary, two attested profiles.**
   `open/ecosystem` (canonical fallback, full mix-and-match, meld as reference)
   and `sealed-safety` (symmetric+PIC only, statically rejects any
   adapter/`cabi_realloc` boundary, emits the attestation). Strategy is *inferred
   per edge from both endpoints' capability metadata*, not a user-facing mode
   matrix; keep the strategy seam **internal** (ship exactly the two lowerings),
   not a public plugin ABI.
7. **New key proof obligation:** a **heterogeneous-composition theorem** — any
   assignment of {canonical, symmetric} × {multi-memory, shared-rebase, PIC}
   across boundaries is semantically equivalent to pure-canonical composition.
   "Canonical fallback is safe" is a *claim, not a theorem* until this + the
   symmetric-preserves-semantics refinement are discharged; an unproven fallback
   is a *bigger* TCB, not a safer one.

### The one open decision (for the human — status stays `open`)

Is meld's **identity** "THE generic RFC-46 reference fuser (safety as a profile
on top)" or "the specialized verified safety-critical fuser (canonical as a
compatibility bridge)"? The review's resolution: *be the reference at the
kernel+canonical **layer**, specialized at the strategy+attestation **layer** —
one unforked binary, two profiles.* The **load-bearing sub-choice that forces the
rest**: **do we co-maintain / track the upstream (wasmtime/BA) canonical FACT
reference, or hand-carry our own 16.4k-line adapter fork forever?** Choosing
"track upstream" frees verified-engineering budget for the moat and dissolves the
generic-vs-specialize tension. This sub-choice is the next thing to decide.

### Risks to keep on the board

Silent downgrade (see req. 3); **donating the moat while garrisoning the
commodity** (spending verified-engineering on the canonical adapter treadmill
while giving away the symmetric/PIC lane we pioneered); and combinatorial
verification / fork-drift blow-up across the 2×3 strategy matrix.

## References

- BA RFC #46 (bytecodealliance/rfcs#46); `safety/stpa/rfc46-comparative-analysis.md`.
- ADR-4 (isolation model), ADR-6 (shared-memory address relocation).
- meld#353 (PIC / shared-everything spike), meld#351 / #352 (reloc-drift backstop).
- Symmetric ABI: cpetig/wit-bindgen (`crates/core/src/symmetric.rs`; live tests
  = `crates/cpp/tests/symmetric.rs` `symmetric_integration()`, which runs the
  **standard `tests/runtime*` suite** under `opts.symmetric = true` + `-shared` —
  per @cpetig the `meshless_*` fixtures are outdated); producer contract =
  wit-bindgen `symmetric = true` → `-shared`; design hackmd.io/@cpetig/rJp4l6vKC;
  WasmCon24 "Component Model in Software-Defined Vehicles" (Aptiv).
