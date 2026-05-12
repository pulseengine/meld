# Meld release roadmap (v0.8 → v0.11)

> Drafted 2026-05-12. Living document — update each release.

Released so far through 2026-05-11: **v0.7.0**. See `CHANGELOG.md`.

This roadmap walks the residual P3-async (#94) and DWARF (#130) umbrellas
to completion across four minor releases, batching related work and
respecting the "no `--admin` bypass" gate from #139 (smithy reliability).

## Cadence

- Five releases in two weeks (v0.3 → v0.7, 2026-04-28 → 2026-05-11) was
  faster than downstream consumers (witness, gale, kiln) can absorb.
- Going forward: target **~one minor release per 3–4 weeks**. Batch 1–3
  thematically related issues per release; cut at a feature boundary,
  not on a clock.
- Pre-release Mythos pass (per `scripts/mythos/discover.md`) is the
  cutting gate. Releases without a Mythos delta-pass on changed Tier-5
  files are blocked.
- Smithy CI must be "stable enough" per #139's acceptance bar before a
  release ships without `--admin`. If smithy is not yet there, the
  release is documented as admin-merged in the PR body and the
  precedent is reset to zero on #139.

## Release plan

### v0.8.0 — Stackful P3 lifting

| Item | Issue | Rivet |
|---|---|---|
| Stackful lifting trampoline (`task.wait`/`task.yield` + `thread_new`/`thread_switch_to`) | #140 | SR-32 |

**Why first.** Smallest touch among the three #94 sub-items. Parallels
the callback trampoline from #128 — limited merger-side change. Also
the first release after the v0.7 smithy incidents; small scope means
the release validates that CI stability has improved before we throw a
larger PR at it.

**Pre-release Mythos surface.** Tier-5 file changed: `adapter/fact.rs`
(new stackful trampoline emitter). Standard Tier-5 scan.

### v0.9.0 — Cross-component stream + (stretch) validation

| Item | Issue | Rivet |
|---|---|---|
| Cross-component stream adapter (same-mem zero-copy + cross-mem chain) | #141 | SR-33 |
| Stream-graph static validation (type / capacity / cycle / lifetime) | #142 | SR-34 |

**Why this bundle.** #142 *uses* the artefact #141 produces — type
compatibility, cycle detection, and resource-lifetime tracking all
operate on the stream-pair graph that the adapter pass builds. Landing
them together avoids a "we shipped the adapter but it's not validated"
gap.

**Stretch.** If #142 isn't ready by the v0.9 cut, slip to v0.10 — do
not delay the adapter for the checker.

**Mythos surface.** New emitter (Tier-5), new resolver pass (Tier-4).
Two scans.

### v0.10.0 — DWARF Phase 2 (address remap)

| Item | Issue | Rivet |
|---|---|---|
| `.debug_line` / `.debug_info` / `.debug_ranges` address remap into merged code section | #143 | SR-35 |
| `DwarfHandling::Remap` variant — opt-in this release, default in a future release after witness validates | #143 | (SR-35) |

**Why solo.** Real DWARF surgery (gimli read + write or a thin
standalone writer helper). Cross-repo verification loop with witness
needs to be set up. Bundling this with anything else dilutes the
release-note story and the testing focus.

**Mythos surface.** New module, new dependency (`gimli`). Tier-5 by
default for the new module; cross-component invariants check that
non-DWARF behaviour is unchanged when `DwarfHandling::Strip` (the v0.7
default) remains selected.

### v0.11.0 — DWARF Phase 3 (adapter DIEs)

| Item | Issue | Rivet |
|---|---|---|
| Synthesised DIEs for meld-generated adapter functions | #144 | SR-36 |

**Why last.** Blocked on #143. Closes out the witness MC/DC story for
fused output: every `br_if` in the fused module gets a source
attribution, including the ones meld synthesised.

After v0.11 ships and witness confirms attribution coverage, consider
flipping `DwarfHandling::Remap` to the default in a v0.11.1 or v0.12.

## Cross-cutting tracks

These don't ride a single release — they're ongoing.

- **Smithy reliability** (#139). Acceptance bar is the gate for
  lifting `--admin`-merge precedent. Closed when three consecutive
  meld releases ship without admin-bypass.
- **Mythos delta passes.** Run on every release per the existing
  pattern (LS-P-4 v0.3, LS-A-8 v0.3, LS-P-5 v0.5, LS-A-9 v0.6,
  LS-CP-4 v0.7).
- **RFC #46 alignment.** Track
  [bytecodealliance/rfcs#46](https://github.com/bytecodealliance/rfcs/pull/46).
  Two upcoming meld touchpoints are anticipated from
  alexcrichton's 2026-04-08 comment:
  - Document that `pulseengine:async` already satisfies the "no
    injected linear memories — all CM intrinsics are host imports"
    constraint (update ADR-1).
  - Investigate adding a sibling output mode `OutputFormat::MultiModule`
    so meld can be adopted inside wasmtime under the "emit N modules +
    metadata" strategy rather than the current single-module fusion.

## SDLC tracking

Each numbered deliverable above has:

| Artefact | Where |
|---|---|
| Issue with milestone | GitHub `pulseengine/meld` |
| Rivet requirement | `safety/requirements/safety-requirements.yaml` (SR-N) or `safety/requirements/p3-async.yaml` (feature subset) |
| Verification linkage | `safety/requirements/traceability.yaml` |
| ADR (where design-level) | `safety/adr/ADR-N-<topic>.md` |
| LS-N (where a loss scenario applies) | `safety/stpa/loss-scenarios.yaml` (status `approved` only after the fix lands) |
| CHANGELOG entry | `CHANGELOG.md` `[Unreleased]` → renamed at release PR |
| Pre-release Mythos pass note | release PR body + CHANGELOG |

A release is "done" when:

1. All milestone issues are closed.
2. Their rivet requirements show `status: implemented` in
   `safety-requirements.yaml`.
3. Their entries in `traceability.yaml::verification-status` point at
   real test files / proof paths, not TBD.
4. CHANGELOG entry under `[Unreleased]` is renamed to `[vX.Y.Z] — <date>`.
5. Pre-release Mythos scan completed on Tier-5 + Tier-4 files changed
   since the previous release; findings either fixed in the same
   release PR or filed as a follow-up.
6. Tag `vX.Y.Z` pushed; release.yml produced all 4 binaries.

## Out of scope for this roadmap

- Variable-level DWARF (`.debug_loc`, `.debug_loclists`) — explicit
  non-goal per #130.
- `OutputFormat::MultiModule` — design exploration first; not yet a
  scheduled deliverable.
- Performance regression detection on fused output — WarpL evaluation
  (`docs/arxiv-2604.13693-warpl-evaluation.md`) recommended deferring;
  if this becomes a real need, it'll get its own issue + roadmap entry.
