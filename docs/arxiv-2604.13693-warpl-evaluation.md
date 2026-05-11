# Can WarpL (arXiv 2604.13693) be wired into meld CI?

> Evaluation memo — drafted 2026-05-11 by avrabe + Claude Opus 4.7
>
> Reference: Zeng, Jiang, Zhao, Zhou. *Debugging Performance Issues in
> WebAssembly Runtimes via Mutation-based Inference*. ICSE '26.
> [arXiv:2604.13693](https://arxiv.org/abs/2604.13693).
> Tool repo: <https://github.com/BZTesting/WarpL>.

## TL;DR

The brief that motivated this evaluation asked for "mutation-inference
baseline signatures captured on five representative meld fixtures, used
as a perf-regression CI signal on fused output." That mismatches what
the paper actually proposes. **WarpL is a post-hoc root-cause
localiser, not a regression detector.** It assumes a slow program is
already in hand and pinpoints which JIT-emitted machine instructions
caused the slowdown. It needs a second runtime as a differential
oracle, costs ~14 hours per case, and has no notion of a "perf
signature."

Recommendation: **defer** wiring into PR CI. Keep on a watch-list for a
specific class of incident (a meld-fused module that runs slower than
expected on a downstream runtime), where it is the right tool.

## What the brief described vs. what the paper does

| Aspect | Brief's framing | What WarpL actually does |
|---|---|---|
| Output of capture | "Baseline perf signature per fixture" | No baseline signature; mutates a *known-slow* module and ranks mutants by perf-diff + functional-similarity scores |
| Use case | Detect that meld emitted a Wasm whose perf characteristics drifted | Diagnose *why* a chosen Wasm runtime is slow on a chosen module |
| Trigger | Run on every PR as an advisory CI step | Run once, manually, after a slow case is reported |
| Required oracle | The fixture's own prior run | A *second* Wasm runtime (e.g. WasmEdge while debugging Wasmtime) |
| Inputs vs. output | "Optimised / fused output of meld" as input | Stock guest modules in the paper's eval; never demonstrated on fused / Component-Model output |
| Cost | "Advisory" CI signal implies seconds-to-minutes | ~3 h mutation+selection+isolation per case, plus ~11 h `wasm-reduce` upstream |

## Pipeline (paper, Fig. 3)

1. **Reduce** the slow program with `wasm-reduce` (Binaryen). Reported
   average: 11 h/case.
2. **Mutate**: single-instruction, type-aware mutation per mutant
   (operand substitution, operator substitution within the same
   operator class, operator deletion). Control-flow excluded.
   Hundreds of mutants per case.
3. **Select** mutants using a differential oracle — a second runtime
   that lowers the same Wasm code without the buggy slow path.
   Each mutant gets a score
   `α · perfDiffScore + β · funcSimScore` (Eq. 1/2 in §3.3).
4. **Localise** by diffing the buggy runtime's JIT-emitted x86-64 for
   the original vs. the top-ranked mutant, using LCS on opcodes.
   Output is a side-by-side bytecode + machine-code diff (Figs. 1, 4–8).

`#MI(I)` in Table 2 ranges 1–35 machine instructions per case — the
"answer" is in the JIT output, **not in the source Wasm**.

## Why this doesn't fit meld CI

1. **Wrong problem.** PR CI needs a *detector* ("this PR made the fused
   output slower than the baseline"). WarpL needs you to bring the
   slow case yourself. Plugging it into CI without a detector in front
   would never fire.
2. **Wrong cost class.** meld's PR CI budget is ~15 min total. A 14 h
   per-case localisation pass is three orders of magnitude over budget
   even as a "nightly advisory" job.
3. **Wrong scope.** The 12 cases the paper evaluates are Wasmtime /
   Wasmer / WasmEdge issue-tracker bugs against stock guest modules.
   Component-Model fusion, canonical-ABI adapters, multi-memory
   adapter trampolines, and re-encoded merged code sections were
   neither in the corpus nor discussed. The localisation diff is in
   x86-64, attributing blame to the *runtime*, not to *what meld
   emitted*.
4. **Oracle runtime requirement.** Selecting mutants depends on a
   second runtime that does *not* exhibit the slowdown. meld emits one
   Wasm; we have no signal about which runtime is "the oracle" for a
   given fusion artefact.

## What a meld-flavoured regression detector would actually look like

If the underlying ask is "tell me when meld's optimised output gets
slower across releases", the cheaper, native fits are:

- The existing **criterion fusion benches** (`meld-core/benches/`,
  shipped in #103 / #123): compile-time perf of the *fuser pipeline
  itself*, not of the emitted Wasm. Already in place.
- **Runtime-execution time** of fused output under `wasmtime run` on a
  small fixture set (e.g. `numbers.wasm`, `lists.wasm`, `flavorful.wasm`,
  `calculator.wasm`, `yolo_inference_release.wasm`), tracked across
  commits. Single scalar per fixture; cheap; advisory in nightly.
- **`wasm-opt -O3` size + instruction-count deltas** of the emitted
  module across PRs. Free, fast, catches "fusion accidentally
  re-introduced X" without running anything.

These would replace the perf-signature concept the brief assumed. None
of them are WarpL.

## When WarpL would be the right tool

Bookmark for a narrow incident class:

- A user reports that a specific meld-fused module is unexpectedly
  slow on Wasmtime/Wasmer/WasmEdge, and the *same* module run before
  fusion is fast.
- We need to know whether to file the bug against meld (we emitted
  pathological code) or upstream against the JIT (it lowered fine code
  pathologically).

In that scenario WarpL — with `wasm-reduce` first, then a second
runtime as the oracle — is exactly the right tool, and 14 h is
acceptable. It is **not** an everyday-CI tool.

## Recommendation

- **Do not** wire WarpL into meld CI now.
- **Do not** capture "five baseline perf signatures" — there is no
  signature representation to capture.
- **Track** [BZTesting/WarpL on GitHub](https://github.com/BZTesting/WarpL)
  in case the authors extend to component-model output or publish a
  faster detection-mode follow-up.
- **Open the door** to the cheaper detector ideas above if a real
  regression-detection ask exists. Those should be filed as their own
  issue with concrete fixtures, budgets, and signal definitions.

## Five fixtures the brief asked for (for the record)

If a future, *actual* perf-regression detector lands, the five most
useful meld-corpus fixtures for capturing per-commit perf-delta on
fused output are (per parallel inventory):

| # | Fixture | Size | Profile |
|---|---|---|---|
| 1 | `tests/wit_bindgen/fixtures/numbers.wasm` | 7.5 MB | numeric throughput baseline |
| 2 | `tests/wit_bindgen/fixtures/lists.wasm` | 8 MB | malloc-heavy list packing |
| 3 | `tests/wit_bindgen/fixtures/flavorful.wasm` | 7.9 MB | combined lists + strings + records + variants |
| 4 | `tests/wit_bindgen/fixtures/release-0.2.0/calculator.wasm` | 2.3 MB | control-flow heavy CLI app |
| 5 | `tests/wit_bindgen/fixtures/release-0.2.0/yolo_inference_release.wasm` | 4.2 MB | float / memory-intensive ML |

The brief's named fixtures (`httparse`, `nom_numbers`, `state_machine`,
`json_lite`, kiln) do not exist in `pulseengine/meld`; they would need
to be imported or re-built before any such detector could use them.

---

*Cross-repo note:* the parallel `pulseengine/loom` half of the
original brief was descoped per user instruction. This memo covers
meld only.
