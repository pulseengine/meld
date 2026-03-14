# Weighted Gap Analysis: Current P2 and P3 Transition

**Date:** 2026-03-14
**Inputs:** STPA artifacts (SR-1 through SR-30), RFC #46 discussion (cfallin,
alexcrichton, dicej, jellevandenhooff), Christof Petig ecosystem assessment,
codebase test coverage audit

---

## Methodology

Each gap is weighted by three factors:

1. **Ecosystem weight** — How critical is this per the BA RFC #46 discussion
   and the component model ecosystem direction?
2. **Safety weight** — Which STPA losses does this gap expose? (L-1 semantic
   correctness > L-2 memory safety > L-3 supply chain > L-4 reproducibility
   > L-5 certification)
3. **Blast radius** — How many downstream failures does this gap enable?

Scores: CRITICAL / HIGH / MEDIUM / LOW

---

## Part 1: Current P2 Gaps (weighted)

### GAP-P2-1: Multiply-Instantiated Modules — CRITICAL

**Current state:** No detection. No rejection. No test. If a component
instantiates the same core module twice, the merger silently produces
corrupt output.

**Ecosystem weight: CRITICAL**
- cfallin (Cranelift lead): "It's very important to solve this right, and not
  just reject... that's a fundamental capability of the component model that
  core Wasm doesn't have, and we don't want to bifurcate the ecosystem."
- He proposed a "simple component" multi-module output as the best option.
- dicej agreed: "Yeah, I expect this is what it would have to look like."

**Safety weight: CRITICAL**
- Losses: L-1 (semantic correctness), L-2 (memory safety)
- Hazards: H-1, H-2, H-3 (index remapping of duplicated instances)
- No loss scenario exists yet — needs LS-M-5

**Blast radius: HIGH**
- Any component that uses the same adapter module twice (common in
  wit-bindgen output with shared helper modules) could trigger this.
- Silent corruption — no error, no diagnostic.

**Immediate action:** Fail-fast rejection (detect and error). This is a
one-day fix that eliminates the silent corruption risk.

**Strategic action:** Multi-module component output using cfallin's "simple
component" approach. This aligns with OutputFormat::Component and avoids
function duplication bloat.

---

### GAP-P2-2: Resource Handles in P2 Wrapper — HIGH

**Current state:** Core module fusion works for resources. P2 component
wrapping fails on `[resource-new]`, `[resource-rep]`, and `[export]`-prefixed
module namespaces. Resources fixture generates but 2/3 test levels fail.

**Ecosystem weight: HIGH**
- Resources are P2 spec, not P3. This is current-spec functionality we
  don't support.
- Christof Petig's `resource-demo` project and 7 resource-related
  wit-bindgen fixtures signal this is well-exercised territory.
- wit-bindgen upstream has: resources, resource_aggregates, resource_alias,
  resource_alias_redux, resource_borrow, resource_borrow_in_record,
  resource_floats, resource_with_lists (8 fixtures).

**Safety weight: HIGH**
- Losses: L-1 (semantic correctness)
- SR-25 (resource handle pass-through) is draft with zero verification
- Hazards: H-8 (invalid P2 component)
- The wrapper must define resource types, generate `canon resource.drop/new/rep`,
  and create synthetic core instances for `[export]`-prefixed modules.

**Blast radius: MEDIUM**
- Only affects OutputFormat::Component path (not CoreModule).
- Components without resources work fine.
- But: resources are increasingly common in real-world components.

**Action:** Implement resource support in component_wrap.rs. Substantial
but well-scoped: ~4 mechanisms needed (resource type definition, canon
resource ops, synthetic instances, [export]-prefixed module routing).

---

### GAP-P2-3: String Transcoding Verification — HIGH

**Current state:** SR-17 has ZERO test coverage for actual transcoding.
We test that strings have 8-byte ABI element size, and the runtime
wit-bindgen fixtures exercise UTF-8 ↔ UTF-8 (same encoding). But:
- No test for UTF-16 canonical option
- No test for CompactUTF16
- No surrogate pair handling test
- No non-BMP character test

**Ecosystem weight: HIGH**
- XH-4 (string encoding disagreement across tools) is a cross-toolchain
  consistency hazard.
- The strings, strings-alias, and strings-simple fixtures all use UTF-8.
  No fixture exercises cross-encoding transcoding.

**Safety weight: HIGH**
- Losses: L-1 (semantic correctness), L-2 (memory safety — wrong-length
  transcoding can overwrite adjacent memory)
- SR-17 is not-verified

**Blast radius: MEDIUM**
- Only triggers when components use different string encodings.
- Most Rust/C components use UTF-8. But C++ (Petig's bindings) may use UTF-16.

**Action:** Add targeted transcoding tests. Consider a custom fixture with
UTF-16 canonical option.

---

### GAP-P2-4: Fixed-Length Lists Parser — MEDIUM

**Current state:** Parser fails on binary encoding 0x67 (fixed-length-list
component type). Test gracefully degrades.

**Ecosystem weight: MEDIUM**
- Petig personally contributed this to the spec.
- It's an experimental/newer feature — not yet widely used.
- But: Petig is exactly the kind of person who would test meld with it.

**Safety weight: LOW**
- Losses: L-1 (cannot fuse components using this feature)
- Fail-fast: parser returns error (correct behavior for unsupported feature)
- Not a silent corruption — just a capability gap.

**Blast radius: LOW**
- Only affects components using the fixed-length-list type.

**Action:** Add parser support for 0x67 encoding. Likely a small change
to `convert_wp_defined_type()`.

---

### GAP-P2-5: Unverified Safety Requirements — MEDIUM

| SR | Title | Coverage | Risk |
|----|-------|----------|------|
| SR-1 | Complete core module extraction | Partial (structure test, no count) | Medium — nested components may lose modules |
| SR-2 | Complete import/export extraction | Partial (no round-trip count) | Medium |
| SR-4 | Reject malformed components | Good (magic/truncated tested) | Low — malformed sections untested |
| SR-11 | Order matches resolver | Excellent (4 topo sort tests) | Low — well covered |
| SR-17 | String transcoding | **Minimal** | **High — see GAP-P2-3** |
| SR-18 | Adapter instruction ordering | Implicit (runtime tests) | Medium — no binary inspection |

**Action:** SR-17 is the priority (covered by GAP-P2-3). SR-11 can be
upgraded to "partial" based on existing tests. SR-1, SR-2, SR-4 need
targeted tests but are lower risk.

---

### GAP-P2-6: Traceability Matrix Stale — LOW

**Current state:** Doesn't reflect:
- Multi-memory unit tests (SR-21/SR-23 are implemented+tested, not "draft")
- 14 wit-bindgen fixtures (matrix shows 4)
- GAP-3 updated status
- No entry for multiply-instantiated modules

**Ecosystem weight: LOW** (internal bookkeeping)
**Safety weight: MEDIUM** (L-5 — certification evidence requires accurate traceability)

**Action:** Update traceability.yaml and cross-toolchain-consistency.yaml.

---

## Part 2: P3 Transition Risk Projection

When P3 ecosystem tools land (wit-bindgen P3, runtime stack-switching),
the gap landscape shifts dramatically.

### P3-RISK-1: Async Architecture Decision — CRITICAL

**The fork:** Embed a Rust-compiled CM runtime (RFC approach) vs. generate
static async adapters at fusion time (preserve self-contained output).

**alexcrichton's concern:** "Particularly w.r.t. async I don't actually know
how a built-in wasm-based runtime could shave off a large chunk of the
complexity burden from embedders."

**Impact on Meld:**
- RFC losses RL-1 (async correctness), RL-2 (fiber isolation), RL-6 (stream
  deadlock) all become relevant
- New controller: CM Runtime (embedded) with 4 UCAs (UCA-RT-1 through RT-4)
- New controller: Fiber Manager with 4 UCAs (UCA-FM-1 through FM-4)
- Self-contained output property at risk
- TCB grows significantly

**Current preparation:** Zero. No async code, no fiber support, no design.

**Mitigation:** The async decision should be deferred until core wasm stack
switching lands. alexcrichton: "With stack switching in theory a lot more
can be moved to the guest." Meld should prefer wasm-native stack switching
over host fiber intrinsics. Gale/kiln own the runtime side.

**When this becomes urgent:** When wit-bindgen ships P3 guest bindings.

---

### P3-RISK-2: Multi-Module Component Output — HIGH

**cfallin's direction:** "Define a 'just the module linking, please' subset
of component model semantics." dicej agreed.

**Impact on Meld:**
- OutputFormat::Component needs to support emitting multiple core modules
  with a wiring diagram, not just one fused module
- This solves multiply-instantiated modules (GAP-P2-1) properly
- Current stubs module pattern extends naturally to multi-module
- But: the "simple component" format doesn't exist yet in any spec

**Current preparation:** OutputFormat::Component wrapping works for single
fused module. Multi-module output is a new code path.

**Mitigation:** Solve GAP-P2-1 with fail-fast rejection first. Design
multi-module output when the "simple component" format is specified.

---

### P3-RISK-3: Performance / Memory Pressure — HIGH

**alexcrichton's concern:** "All components likely to have at least 2 linear
memories... which balloons 8G of virtual memory to 16G per component."

**Impact on Meld:**
- Our multi-memory approach (one memory per component) directly creates
  this pressure
- P3 async contexts may add more memories (runtime state, fiber stacks)
- Embedded targets (Synth/automotive) have hard memory constraints

**Current preparation:** SharedMemory mode exists as fallback but has its
own issues (memory.grow corruption).

**Mitigation:** Consider memory coalescing optimization (prove memories
don't alias, merge when safe). This would be a LOOM-level optimization
applied after meld fusion.

---

### P3-RISK-4: Cross-Toolchain Consistency Becomes Real — HIGH

**Current state:** Fixture matrix empty for kiln and synth. When P3 lands:
- Kiln runtime integration becomes real (XH-1 through XH-5 activate)
- Synth AOT compilation needs ABI agreement
- String encoding disagreement (XH-4) more likely with UTF-16 components

**Impact:** Silent data corruption at tool boundaries. No formal guarantee
tools agree on canonical ABI layout.

**Mitigation:** Shared Rocq specs in proofs/spec/ and shared fixture runs
across all three tool paths. Priority increases linearly with integration.

---

### P3-RISK-5: Resource Lifecycle Complexity — HIGH

**P2 resources:** Create, pass handle (i32), drop. Relatively simple.
**P3 resources:** Async drop, resource tables with concurrent access,
stream-attached resources, borrow scoping across async boundaries.

**Impact:** SR-25 gap grows from "implement 4 wrapper mechanisms" to
"implement full resource table management with async lifecycle."

**Current preparation:** Core module fusion handles resource handles as
i32 pass-through (correct for P2). P2 wrapper blocked on basic resource
support (GAP-P2-2). P3 resource complexity compounds the gap.

**Mitigation:** Solve GAP-P2-2 (P2 resources) first. P3 resource table
management is a separate, larger effort that depends on the async
architecture decision (P3-RISK-1).

---

## Part 3: Priority Matrix

```
                    P2 (now)                    P3 (transition)
              ┌─────────────────────┐    ┌─────────────────────────┐
   CRITICAL   │ GAP-P2-1: Multiply  │    │ P3-RISK-1: Async arch   │
              │   instantiated      │    │ P3-RISK-2: Multi-module  │
              │   modules           │    │   component output       │
              ├─────────────────────┤    ├─────────────────────────┤
   HIGH       │ GAP-P2-2: Resources │    │ P3-RISK-3: Memory       │
              │ GAP-P2-3: String    │    │   pressure               │
              │   transcoding       │    │ P3-RISK-4: Cross-tool    │
              │                     │    │   consistency             │
              │                     │    │ P3-RISK-5: Resource       │
              │                     │    │   lifecycle               │
              ├─────────────────────┤    ├─────────────────────────┤
   MEDIUM     │ GAP-P2-4: Fixed-len │    │                         │
              │   lists parser      │    │                         │
              │ GAP-P2-5: Unverif.  │    │                         │
              │   SRs               │    │                         │
              ├─────────────────────┤    ├─────────────────────────┤
   LOW        │ GAP-P2-6: Stale     │    │                         │
              │   traceability      │    │                         │
              └─────────────────────┘    └─────────────────────────┘
```

## Part 4: Recommended Execution Order

### Phase A: Immediate (eliminate silent corruption)
1. **Multiply-instantiated module fail-fast** — detect and reject (1 day)
2. **Update traceability matrix** — reflect current state (bookkeeping)

### Phase B: P2 completeness (close HIGH gaps)
3. **Resource handles in wrapper** — SR-25, 4 mechanisms (3-5 days)
4. **String transcoding tests** — SR-17 verification (1 day)
5. **Fixed-length-lists parser** — 0x67 encoding support (1 day)

### Phase C: P3 preparation (design, not implementation)
6. **Multi-module component output design** — extends OutputFormat::Component
7. **Async architecture decision document** — embed runtime vs. static adapters
8. **Cross-toolchain fixture integration** — run shared fixtures through kiln

### Phase D: Formal verification (when code stabilizes)
9. **Rocq proofs for adapter** (GAP-3, Issue #11)
10. **Rocq proofs for attestation** (GAP-1)
11. **Shared Rocq specs** for cross-toolchain consistency (XH-1 through XH-5)

---

## Part 5: New STPA Artifacts Needed

### New Loss Scenario
- **LS-M-5:** Multiply-instantiated module — merger processes same module
  index twice, creating duplicate function/memory/table entries with
  conflicting index offsets. Functions from the second instance reference
  the first instance's memory. (Hazards: H-1, H-2, H-3)

### New Safety Requirement
- **SR-31:** Multiply-instantiated module detection — the merger shall detect
  when the same core module is instantiated more than once and return an
  error. (Derives from: SC-8, SC-9. Verification: test)

### Updated Hazard
- **H-8** (component wrapping): Add sub-hazard H-8.1 for resource type
  definition failure, H-8.2 for missing canon resource.new/rep operations.

### New Cross-Toolchain Entry
- **XH-6:** Multi-module component format disagreement — if Meld outputs
  a "simple component" (per cfallin's proposal) and runtimes interpret the
  format differently, module linking order or import wiring may diverge.

### Updated Loss Coverage
- L-1 requirements: add SR-31 (multiply-instantiated modules)
- L-5: Consider modeling proof pipeline as controlled process (GAP-2)
