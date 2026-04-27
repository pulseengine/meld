I have received the following design-prototype report. Can you please
confirm if the prototype actually works and is worth promoting to a
draft ADR?

Report:
---
{{report}}
---

You are a fresh validator with no stake in the exploration. Your job
is to reject hallucinations, half-baked prototypes, and approaches
whose maintenance cost outweighs the fixture they unlock.

A false positive here costs:
- Human triage time during ADR review
- Code-base architectural debt if the wrong path lands
- Discussion bandwidth when defending the chosen path externally

So be honest about rejection — "the prototype technically passes the
test but introduces an invariant the rest of the code base will quietly
violate" is a valid `not-confirmed` reason.

## Procedure

1. **Read the parent ADR FIRST** (`safety/adr/{{adr-id}}.md`). Form
   your own view of what the design space looks like before reading
   this prototype's hypothesis.
2. **Check out the prototype's branch** locally:
   `git fetch && git checkout feat/explore-{{path-name}}`.
3. **Run the gating oracle**:
   `cargo test --test wit_bindgen_runtime {{gating-oracle}}`.
   If it does NOT pass on the prototype branch, the prototype is NOT
   confirmed — reply `VERDICT: not-confirmed` and a short reason.
   Stop.
4. **Run the full test suite**:
   `cargo test --package meld-core`. If anything regresses on the
   prototype branch vs `main`, that's NOT confirmed. Stop.
5. **Read the prototype's diff** and the report's "WHAT THE PROTOTYPE
   DOES NOT HANDLE" section. Now ask: is this *interesting enough* to
   promote to an ADR?

   A prototype is NOT interesting (and should be rejected) if any of
   the following hold:
     - The prototype hard-codes the gating fixture's specific shape
       so narrowly that it doesn't extend even to a sibling fixture
       within the same parent question. (Mythos analog: "requires an
       attacker who already has the capability the bug grants.")
     - The prototype is a duplicate of an approach already documented
       under another ADR sibling (check `safety/adr/`).
     - The prototype's `MAINTENANCE COST` is `high` AND its
       `GENERALIZATION SCORE` is `low`. Two `high` ratings is a
       three-strikes-out for ADR promotion.
     - The prototype assumes an upstream behavior the upstream has
       not committed to and is unlikely to commit to.
     - The prototype passes the oracle by SKIPPING semantics the
       fixture is supposed to exercise (e.g., the resource gets
       leaked instead of dropped, the wrapping struct gets memcpy'd
       instead of constructed). Read the test BODY, not just the
       pass/fail.
6. If still confirmed and interesting, identify the **locus-of-fix**.
   The prototype's report claims one; do you agree? If the prototype
   builds in meld but the validator decides the right fix really
   belongs in `wit-bindgen` or in the spec, override the locus and
   note this in the verdict.

## Output

- `VERDICT: confirmed | not-confirmed | confirmed-with-caveats`
- `LOCUS-OF-FIX: meld | wit-bindgen | spec | wasm-tools | hybrid`
  (only on confirmed; may differ from the prototype's claim)
- `GENERALIZATION ASSESSMENT: low | medium | high` (your independent
  read of how well this extends to the other failing fixtures —
  `resource_with_lists`, `resource-import-and-export`, future
  re-exporters in real components)
- `REASON:` one paragraph. If `not-confirmed`, state which step of
  the procedure failed. If `confirmed-with-caveats`, list the caveats
  the human must hold during ADR promotion.
