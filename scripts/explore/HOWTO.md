# Explore — Mythos-style design exploration pipeline

Sibling pattern to `scripts/mythos/` (bug hunting). Where mythos forces
divergent bug hypotheses through a convergent oracle (failing test +
Kani harness), explore forces divergent **design alternatives** through
a convergent oracle (working prototype that flips a `fuse_only_test!`
to `runtime_test!` PASSING).

The pattern is: let agents reason about designs freely, but require a
machine-checkable oracle for every recommended design so we don't ship
hand-waved architecture.

## When to use

- A failing fixture or class of failures has more than one plausible
  fix — typically because the right fix straddles meld, wit-bindgen,
  the component-model spec, or wasm-tools. Examples: the re-exporter
  resource chains in epic #69, future RFC #46 lowering, etc.
- Decisions where "implementation as argumentation" matters. If you'll
  defend a design choice in a discussion with someone outside meld
  (Christof Petig, BA, kiln team), having a working branch beats prose.
- Multiple agents can usefully work in parallel on independent paths.
  If the design space is one-dimensional, just pick the obvious thing.

## The four prompts

| Prompt | Purpose | Output | Sigil analog |
|---|---|---|---|
| `rank.md` | Score design paths by **viability × locus-of-fix** | JSON list, sorted descending | `mythos/rank.md` |
| `prototype.md` | Build smallest viable slice + memo for ONE path | Branch + structured report | `mythos/discover.md` |
| `validate.md` | Fresh validator confirms prototype + assesses generalization | Verdict + reason | `mythos/validate.md` |
| `emit.md` | Convert confirmed prototype to a draft ADR | YAML matching `safety/adr/schema.yaml` | `mythos/emit.md` |

## The two-axis rank

This is the key difference from mythos. Each design path gets two ratings:

1. **Viability (1–5)**: how likely the prototype actually fixes the
   gating fixture, given current knowledge.
2. **Locus-of-fix (meld | wit-bindgen | spec | wasm-tools | hybrid)**:
   where the change properly belongs.

A path with viability 5 and locus = `wit-bindgen` is a strong signal
to invest upstream rather than build a downstream workaround. A path
with viability 5 and locus = `meld` is "do it now."

## Pipeline run

From a Claude Code session in the meld repo:

1. `Read scripts/explore/rank.md` and substitute the parent question
   from `safety/adr/ADR-N.md`. Produces ranked design paths.
2. For each path with viability ≥ 3: new session (parallel), paste
   `prototype.md` with `{{adr-id}}`, `{{path-name}}`, `{{gating-oracle}}`,
   `{{hypothesis-priors}}`, `{{locus-of-fix}}`. Output = structured
   prototype report.
3. For each prototype: fresh session with `validate.md`. Both oracle
   halves must hold (prototype actually flips the test, validator
   confirms generalization claims). Reject anything that doesn't
   confirm.
4. For each confirmed: `emit.md` produces a draft `safety/adr/ADR-N.md`
   entry under the parent ADR. Human promotes to `accepted` /
   `rejected` / `superseded`.

One agent per path, in parallel — the same trick mythos uses.

## Per-project customization

- **`rank.md`** rubric is meld-specific (the locus options, the
  viability-criteria for fusion correctness)
- **`prototype.md`** carries hypothesis priors per path — discovered
  by the human running the pipeline. Examples: "look at wit-component's
  re-exporter handling," "check if wasm-tools has prior art for X."
- **`emit.md`** generates a YAML matching `safety/adr/schema.yaml`
- **`validate.md`** rejects on top of the standard "prototype works"
  oracle: maintenance cost too high, generalization too narrow,
  upstream-only fix, etc.

## Gotchas

- **Approaches you haven't built a 100-line prototype for default to
  viability rank 3.** Do not let abstract speculation inflate ranks.
  Mirror of sigil's "Files you haven't seen default to rank 2."
- **Validators must be fresh sessions.** Reusing prototype context lets
  the agent defend its own design.
- **One agent per path, not per epic.** Parallel agents on different
  paths produce diverse approaches; a single agent converges on its
  first plausible idea.
- **Locus-of-fix is part of the verdict.** Honest "this isn't ours to
  fix; here's the upstream issue we should file" is a valid output.
  Hallucinating a downstream workaround is more expensive than that
  silence.
