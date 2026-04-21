# Mythos-Style Bug Hunt — Portable Pipeline

A four-prompt pipeline modeled on Anthropic's Claude Mythos (red.anthropic.com,
April 2026) plus Vidoc's open-model reproduction. The architecture is: let
the agent reason about code freely, but require a machine-checkable oracle
for every reported bug so hallucinations don't ship.

## Prerequisites

- Claude Code or any agent harness that can read files and drive test runs
- A truth oracle for your language/domain (see §5)
- A bug-tracking format (STPA-Sec, STPA, in-house, whatever)
- Optional: parallel sessions (rank → N parallel discoveries → validate → emit)

## 1. Four prompt templates in `scripts/mythos/`

- **`rank.md`** — agent ranks every source file 1–5 by bug likelihood. The
  rubric is the one non-portable part — write it per repo (§2).
- **`discover.md`** — Mythos-verbatim discovery prompt plus repo-specific
  context plus the oracle requirement (§3).
- **`validate.md`** — fresh-agent validator that enforces the oracle and
  filters uninteresting findings.
- **`emit.md`** — converts a confirmed finding into a draft entry in your
  bug-tracking format.

## 2. Ranking rubric (non-portable)

5 tiers, named by concrete path patterns not abstract categories. Skeleton:

```
5 (crown jewels): secrets, parse-before-trust, canonicalization
4 (direct security boundary): verification, signing, argv+env
3 (one hop from untrusted input): token parsers, network clients, format parsers
2 (supporting, no direct security role): HTTP plumbing, policy eval, logging
1 (config / constants / proof artifacts): error types, wiring, proofs
```

Straddle rule: if a file sits between two tiers, pick the higher. Run the
rank pass once, then **patch the rubric** to eliminate files that required
overrides. A good rubric produces zero overrides on re-run.

## 3. Oracle choice (drives `discover.md`)

The oracle separates "agent thinks there's a bug" from "there is a bug."

| Hunting… | Oracle candidates |
|---|---|
| Memory corruption in C/C++/unsafe Rust | AddressSanitizer, MemorySanitizer, UBSan |
| Logic bugs in safe Rust | Kani + property tests (proptest/quickcheck) |
| Compiler correctness | Rocq + Z3 SMT + differential testing |
| Kernel primitives | Verus + Kani + Rocq; proof-skip analysis |
| Python/TypeScript | Hypothesis, fast-check, concrete PoC |
| Go | fuzz, property tests |
| Crypto protocols | Proverif, Tamarin, CryptoVerif counterexample |

`discover.md` MUST require BOTH (1) a failing machine-checkable proof AND
(2) a failing concrete PoC. "If you cannot produce both, do not report.
Hallucinations are more expensive than silence." — load-bearing sentence.

## 4. Run the pipeline

From a Claude Code session in the repo:

1. `Read scripts/mythos/rank.md` → JSON ranking
2. For each rank-≥4 file: new session (parallel), paste `discover.md` with
   `{{file}}` substituted. Output = structured finding report.
3. For each finding: fresh session with `validate.md`. Both oracle halves
   must fail on unfixed code. Reject anything that doesn't confirm.
4. For each confirmed: `emit.md` produces a `draft` tracking entry. Human
   promotes to `approved`.

One agent per file in step 2 is Mythos's parallelism trick. Don't run one
agent across the whole codebase.

## 5. Per-project customization

- **`rank.md`**: your threat model in 5 tiers
- **`discover.md`**: repo context paragraph + oracle requirement + optional
  hypothesis priors (e.g., wasmtime 2026-04-09 CVE wave for any WASM tool)
- **`validate.md`**: reject against your known-mitigations / system
  constraints / existing scenarios. Swap threat-agent checks for
  hazard-only checks if the repo is safety not security.
- **`emit.md`**: match the exact YAML/JSON shape of your artifact store.

## 6. Gotchas

- **Failing tests directly in source break CI.** Use `#[ignore]` / `@skip`
  and put the rerun command in the ignore reason.
- **The rubric is wrong the first time.** Expect to patch after pass 1.
  Sign you need to patch: "straddle rule → promoted X" lines in output.
- **Validators must be fresh sessions.** Reusing discovery context lets
  the agent defend its own hypothesis.
- **One agent per file, not per codebase.** Parallel agents on different
  files find diverse bugs; a single agent converges on surface issues.
- **Keep the discovery prompt minimal.** Mythos's "Please find a security
  vulnerability" outperforms elaborate CWE checklists because the agent
  has tools (oracle, debugger, runtime) and the environment filters truth.

## 7. Worked example — sigil `signature/sig_sections.rs`

First tier-5 file produced a finding:

```rust
let certificate_chain = if let Ok(cert_count) = varint::get32(&mut reader) {
    // ... read chain
} else {
    None  // ← silently swallows ALL parse errors, not just EOF
};
```

Intent: backward-compat (missing cert_count → None). Bug: any error —
including malformed bytes — gets converted to "no chain," downgrading a
cert-based signature to a bare-key signature.

- **PoC test**: append 5 MSB-set bytes after a valid prefix; expect `Err`;
  current code returns `Ok { certificate_chain: None }`. **Confirmed failing.**
- **Kani harness**: symbolic 5-byte cert_count with MSB-set constraint;
  `assert!(result.is_err())`.

Maps to STPA-Sec UCA-6. Emitted as `draft AS-N` under UCA-6.
