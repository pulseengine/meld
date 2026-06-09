# Meld release roadmap (v0.22 → v0.31)

> Drafted 2026-06-09. Living document — update each release.
> Supersedes the v0.8→v0.11 roadmap (all four shipped; v0.12–v0.21
> shipped issue-driven without a standing roadmap — this document
> restores the practice).

Released so far through 2026-06-09: **v0.21.0**. See `CHANGELOG.md`.

This roadmap walks the residual DWARF umbrella (#130: #143 closeout,
#144, #208), the last multi-component fusion gap (#212.1), the P3-async
closeout (#94/#141), and the first formal-soundness increment (#218)
to completion across ten minor releases.

## Cadence

- Target **~one minor release per feature boundary**, 1–3 thematically
  related items each; cut at a feature boundary, not on a clock.
- Pre-release Mythos pass (per `scripts/mythos/discover.md`) is the
  cutting gate. Releases without a Mythos delta-pass on changed Tier-5
  files are blocked. The PR-level `Mythos delta-pass gate` (clean-room
  pass + findings comment + `mythos-pass-done` label) applies to every
  Tier-5 PR along the way.
- No admin-merge. The user merges; CI (`Test`, `Clippy`, `Coverage`,
  `LS-N verification gate`, `Mythos delta-pass gate`) is authoritative.
  `Fuzz smoke` failures are triangulated against the known #168
  musl/sccache infra flake before any action.

## Release plan

### v0.22.0 — Sound memory default + composed-export correctness

| Item | Issue | Rivet | State |
|---|---|---|---|
| `--memory auto` default (probe `memory.grow` → shared+rebase iff sound) | #172 | SR-37, LS-M-7, UCA-M-11 | PR #220 green |
| Name-based lift resolution for composed multi-component exports | #212 (items 2+3) | LS-CP-5 | PR #216 green |
| Chore: SR-34 status sync (`planned` → `implemented`; #142 chain shipped v0.12–v0.21) | #142 | SR-34 | this roadmap PR |

**Why first.** Both PRs are merged-blocked only. Auto-memory is the
headline: out-of-the-box `meld fuse` output flows through
`wasm-opt → synth` with no flags whenever soundness permits.
**Mythos surface.** Done — clean-room passes completed on both PRs
(#216: component_wrap.rs; #220: resolver.rs, 2 findings fixed in-PR).
**Done when** both PRs merged, SR-37 `verified` (gates green on main),
#172 closed, tag pushed, release assets verified per #185 standard.

### v0.23.0 — Adapter DWARF attribution end-to-end (#144 inc 1–3)

| Item | Issue | Rivet | State |
|---|---|---|---|
| Adapter-span enumeration seam | #144 | SR-36 | PR #217 green |
| Synthetic `<meld-adapter>` DWARF builder (write→read oracle) | #144 | SR-36 | PR #219 green (stacked) |
| inc 3: emit the synthetic unit in the `DwarfHandling::Remap` pipeline | #144 | SR-36 → implemented | not started |

**Design constraint (recorded on #144).** The synthetic unit must be
added into the SAME `gimli::write::Dwarf` that `rewrite_debug_sections`
builds — one `dwarf.write()`, one offset space. Concatenating
independently-written `.debug_*` bytes produces conflicting offsets.
**Acceptance.** Fuse a multi-component that generates adapters under
Remap; re-parse fused `.debug_line`; adapter ranges resolve to
`<meld-adapter>:1` while original code still resolves to its real
source. Decide + pin the "emit even when no source DWARF" contract
(proposed: yes, fresh CU).
**Mythos surface.** dwarf.rs is not Tier-5; no gate cycle expected.

### v0.24.0 — Per-class adapter lines (#144 inc 4, closes #144)

| Item | Issue | Rivet |
|---|---|---|
| Merger tags each synthetic function's adapter class at generation; `<meld-adapter>:N` per class (transcode / cabi_realloc / lift / lower per #130) | #144 | SR-36 → verified |

**Mythos surface.** merger.rs (Tier-5) — class tagging on
`MergedFunction`. Full clean-room pass.
**Done when** witness-facing classes are distinguishable by line; LS-N
approved for "adapter branches accounted in MC/DC line map"; #144
closed.

### v0.25.0 — DWARF Phase 2 closeout (#143): witness-verified Remap → default

| Item | Issue | Rivet |
|---|---|---|
| Cross-repo witness MC/DC attribution check on a real fused wit-bindgen fixture under `--dwarf remap` | #143 | SR-35 → verified |
| Flip `DwarfHandling` default `Strip` → `Remap` once the witness check passes | #143 | SR-35 |

**Why gated.** The issue scoped the default flip on "verified against
witness on real-world fused modules" — that cross-repo run is the
oracle, not meld-side tests. If attribution coverage is poor, the flip
does NOT ship and the gap goes back into #143/#208.
**Done when** #143 closed with the witness evidence quoted.

### v0.26.0 — Multi-source DWARF merge, increment 1 (#208)

| Item | Issue | Rivet |
|---|---|---|
| Lift the "exactly one source module carries DWARF" restriction: two-input CU concatenation with offset relocation through one `gimli::write::Dwarf` | #208 | new SR-38 |

**Scope discipline.** Same single-write architecture as #144 inc 3 —
they share plumbing; land #144 first.
**Mythos surface.** dwarf.rs (not Tier-5); rewriter touchpoints if the
per-module offset maps need extension (Tier-5 if so).

### v0.27.0 — Multi-source DWARF merge, completion (#208 close)

| Item | Issue | Rivet |
|---|---|---|
| `.debug_str` pool dedup across inputs; `.debug_abbrev` byte-equal merge / per-CU fallback; cross-module ranges | #208 | SR-38 → verified |

**Done when** #208 closed; #130 epic reviewed for closure (Phases 1.5,
2, 3 + multi-source all shipped → close with disposition).

### v0.28.0 — Separate-input cross-component linking (#212.1, closes #212)

| Item | Issue | Rivet |
|---|---|---|
| `meld fuse consumer.wasm provider.wasm --component` resolves consumer's instance import against provider's matching export and internalises the call | #212 | new SR-39 + LS-N |

**Oracle exists today.** `golden_e2e.rs::tier_b_separate_inputs_internalise_link`
is `#[ignore]`d with the exact acceptance assertion (runner standalone,
`compute()==42`). Un-ignoring it is the gate.
**Mythos surface.** resolver.rs + component_wrap.rs (both Tier-5).
This is meld's headline capability — full clean-room pass, adversarial
fixtures for type mismatch and partial matches.

### v0.29.0 — P3 async closeout (#141 / #94 residuals)

| Item | Issue | Rivet |
|---|---|---|
| Audit #141 deliverables vs shipped (same-memory ring-buffer path, backpressure propagation tests, EOF passthrough) and close the gaps | #141 | SR-33 → verified |
| #94 umbrella disposition: enumerate sub-items, close or re-scope what remains | #94 | — |

**Honesty note.** SR-33 is `implemented`, but resolver carries a
"detection foundation only" comment — the audit decides whether the
in-module emitter chain is actually complete before anything is called
verified.

### v0.30.0 — Formal soundness, increment 1 (#218)

| Item | Issue | Rivet |
|---|---|---|
| Proof artifacts for Canonical ABI lift/lower invariants: flat-size / alignment lemmas (Kani harnesses; Rocq where the lemma is closed-form), adapter copy-length soundness | #218 | new SR-40 |

**Scope discipline.** #218 is a research lead — this increment ships
only proofs for invariants the code already claims (SR-17 transcoding
chain, LS-A-7 guard policy), not new theory. Output: checked-in
harnesses run in CI.

### v0.31.0 — Traceability closeout + hardening

| Item | Issue | Rivet |
|---|---|---|
| rivet full-V audit: every `implemented` SR either gains real verification linkage (→ `verified`) or is downgraded honestly | — | all SRs |
| #139 meld-side disposition (smithy reliability tracker) | #139 | — |
| Fuzz corpus expansion: seed corpora from golden-e2e + compose fixtures | — | — |

**Done when** `rivet coverage` (compliance report) shows the V closed
for everything shipped v0.22–v0.30, and the release notes carry a
falsification statement for the audit itself.

## Cross-cutting tracks

- **Smithy reliability** (#139, #168). The musl/sccache fuzz-smoke
  flake is triangulated (cc-rs C++ failure pre-fuzzing + sibling target
  green + `Test` green ⇒ infra), never rerun-hammered.
- **Mythos delta passes.** Every Tier-5 PR: clean-room pass + findings
  comment + `mythos-pass-done` label. Recent precedent: PR #220's pass
  found 2 real findings (stale Auto resolution; Merger split-brain),
  both fixed pre-merge — the gate earns its cost.
- **RFC #46 alignment.** Unchanged from the prior roadmap: track
  [bytecodealliance/rfcs#46](https://github.com/bytecodealliance/rfcs/pull/46);
  ADR-1 documents the "no injected linear memories" conformance;
  `OutputFormat::MultiModule` stays a design exploration.

## SDLC tracking

Each numbered deliverable above has:

| Artefact | Where |
|---|---|
| Issue with milestone | GitHub `pulseengine/meld` |
| Rivet requirement | `safety/requirements/safety-requirements.yaml` (SR-N) |
| Verification linkage | `safety/requirements/traceability.yaml` |
| ADR (where design-level) | `safety/adr/ADR-N-<topic>.md` |
| LS-N (where a loss scenario applies) | `safety/stpa/loss-scenarios.yaml` (status `approved` only after the fix lands) |
| CHANGELOG entry | `CHANGELOG.md` `[Unreleased]` → renamed at release PR |
| Pre-release Mythos pass note | release PR body + CHANGELOG |

A release is "done" when:

1. All milestone issues are closed.
2. Their rivet requirements show `status: implemented` (and `verified`
   where the release is the verification vehicle).
3. Their entries in `traceability.yaml::verification-status` point at
   real test files / proof paths, not TBD.
4. CHANGELOG entry under `[Unreleased]` is renamed to `[vX.Y.Z] — <date>`.
5. Pre-release Mythos scan completed on Tier-5 + Tier-4 files changed
   since the previous release; findings either fixed in the same
   release PR or filed as a follow-up.
6. Tag `vX.Y.Z` pushed; release.yml produced all binaries + the #185
   artifact standard set (SHA256SUMS + cosign + SBOM + SLSA), spot-
   verified with the consumer one-liner.

## Out of scope for this roadmap

- Variable-level DWARF (`.debug_loc`, `.debug_loclists`) — explicit
  non-goal per #130.
- `OutputFormat::MultiModule` — design exploration first; not yet a
  scheduled deliverable.
- Performance regression detection on fused output — WarpL evaluation
  (`docs/arxiv-2604.13693-warpl-evaluation.md`) recommended deferring.
- Hardware smoke testing — user-owned, separate from this roadmap.
