# Mythos delta-pass gate — reviewer / author guide

This document is what to do when the `mythos-gate` CI check fails on
your PR. The gate is defined in `.github/workflows/mythos-gate.yml`.

## When the gate fires

A PR modifies one or more **Tier-5** source files per the rubric in
[`scripts/mythos/rank.md`](rank.md). The current Tier-5 path list lives
in `mythos-gate.yml`; it tracks the rubric but is concrete repo paths,
not glob patterns.

When the gate fires, the PR gets a sticky comment from `mythos-gate`
listing the touched files, and the check fails until the
`mythos-pass-done` label is applied.

## What to do

For each Tier-5 file touched by this PR:

1. **Spawn a fresh agent session** (Claude Code, claude.ai, or
   equivalent) pointed at the repo.
2. **Hand it [`scripts/mythos/discover.md`](discover.md)** with the
   target file substituted. One file per agent session — don't ask a
   single agent to scan multiple files.
3. **Wait for the structured report.** The agent must produce, for any
   reported finding:
   - A `#[kani::proof]` harness that fails today and passes after fix.
   - A failing `#[test]` (or `proptest!`) reproducing the bug with
     concrete inputs.

   "If you cannot produce both, do not report" is load-bearing in the
   protocol — the agent should return **NO FINDINGS** rather than
   speculate.

4. **Validate any findings** by spawning a *second* fresh agent
   session and handing it [`validate.md`](validate.md). The validator
   must independently re-run the oracle pair against the current code
   and confirm both halves fail. Hypotheses that don't survive the
   fresh-validator round are discarded.

5. **Attach the result to the PR** as a comment:
   - For each touched Tier-5 file: a section with either the validated
     findings (per `discover.md`'s output schema) or **NO FINDINGS**.
   - Multiple files → multiple sections in one comment.

6. **Add the `mythos-pass-done` label** to the PR. The gate check
   re-runs on label change and passes.

## What to do with a confirmed finding

- File the finding as a draft loss-scenario entry in
  [`safety/stpa/loss-scenarios.yaml`](../../safety/stpa/loss-scenarios.yaml)
  via [`emit.md`](emit.md). Promote to `approved` status once the fix
  PR is ready.
- The fix may land in the same PR (if scope-aligned) or in a separate
  PR that blocks merge of this one.

## Why this gate exists

LS-A-10 (CABI alignment padding in async-lift retptr writeback) was
found by the v0.8.0 pre-release Mythos pass on `adapter/fact.rs`. It
had silently lived in the callback emitter since #128, affecting six
releases. A PR-time gate catches LS-A-10-class defects at review time
instead of release time.

The gate does **not** automate the LLM invocation — it gates on a
human-verified label. Automating the discover/validate pipeline in CI
requires API keys, cost budgeting, and a way to surface findings as
checks; that's tracked separately. The gate ships the value of the
process (no Tier-5 PR merges without a recorded pass) without the
infra cost of the LLM-in-CI step.

## Adjusting the Tier-5 path list

If you add a file that the Tier-5 rubric in `rank.md` would classify as
fusion-critical (parser, fuser, type-checker, writer, canonical-ABI
emitter), add its path to the `patterns` array in
`.github/workflows/mythos-gate.yml`. The workflow's audit comment in
that file documents this requirement.

If you intentionally bypass the gate for a Tier-5 file change (e.g.,
pure rename, comment-only edit, whitespace cleanup with no semantic
change), record the bypass reason in the PR description before
applying the label.
