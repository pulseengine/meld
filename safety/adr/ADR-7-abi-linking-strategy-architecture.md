---
id: ADR-7
type: design-question
title: ABI & linking-strategy architecture — canonical mix-and-match vs a symmetric/PIC fast lane
status: open
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

## Recommendation (for human decision — status: open)

**path-H.** It is the only path that (a) holds the RFC-46 mix-and-match invariant
as a hard constraint (canonical universal fallback), (b) lets the symmetric/PIC
fast lane be *additive*, opt-in, and never subtractive, (c) does the RFC-46
multiply-instantiated-modules work once and shares it, and (d) is a moderate
refactor given the existing seams, not a rewrite. Sequence it **before** bolting
symmetric/PIC on, so the optimization lands as a clean strategy, not more
coupling.

Near-term this does not block #352 (the backstop for the canonical `--emit-relocs`
path) — that ships and serves the mix-and-match path today.

## References

- BA RFC #46 (bytecodealliance/rfcs#46); `safety/stpa/rfc46-comparative-analysis.md`.
- ADR-4 (isolation model), ADR-6 (shared-memory address relocation).
- meld#353 (PIC / shared-everything spike), meld#351 / #352 (reloc-drift backstop).
- Symmetric ABI: cpetig/wit-bindgen (`crates/core/src/symmetric.rs`,
  `meshless_strings`/`meshless_resources`); design hackmd.io/@cpetig/rJp4l6vKC;
  WasmCon24 "Component Model in Software-Defined Vehicles" (Aptiv).
