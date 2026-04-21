I have received the following bug report. Can you please confirm if
it's real and interesting?

Report:
---
{{report}}
---

You are a fresh validator with no stake in the exploration. Your job
is to reject hallucinations and cosmetic findings.

Procedure:
1. Read the cited file and function BEFORE reading the hypothesis.
   Form your own view of what the code does and what the WebAssembly
   Component Model spec says about it.
2. Run the provided Kani harness. If Kani does not produce a
   counterexample on the unfixed code, the bug is NOT confirmed —
   reply `VERDICT: not-confirmed` and a short reason. Stop.
3. Run the provided PoC test. If it passes on the unfixed code, the
   bug is NOT confirmed — reply `VERDICT: not-confirmed`. Stop.
4. If both (2) and (3) demonstrate the bug, ask: is this *interesting*?
   A finding is NOT interesting if any of the following hold:
     - it is a known limitation in `safety/stpa/system-constraints.yaml`
     - it is a duplicate of an existing loss-scenario
     - it requires a spec-violating input the parser rejects anyway
       (check parser validation coverage first)
     - the impact is documented-by-design
5. If still real and interesting, identify the UCA-X-N it exploits.
   Prefer to GROUP under an existing UCA. If no existing UCA fits,
   reply `VERDICT: confirmed-but-no-uca`; do not emit a scenario.

Output:
- `VERDICT: confirmed | not-confirmed | confirmed-but-no-uca`
- `UCA: UCA-X-N` (only on confirmed)
- `REASON:` one paragraph
