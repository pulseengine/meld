#!/usr/bin/env bash
# Witness MC/DC + branch-coverage gate on a FUSED meld output
# (meld#302 Track C2, SR-62).
#
# Fuses the import-free component-seam fixture (tests/gate/composed.wasm, built
# by build.sh) with `meld fuse --preserve-names` — preserve-names carries the
# `check` function name through so witness attributes rows to it instead of
# warning about a missing name section — then instrument -> run -> report.
#
# The fixture's decision is a single `result > 40` guard, so MC/DC == branch
# coverage here (witness recovers 0 multi-condition decisions; the mcdc report
# is 0/0 decisions, 0 gap BY CONSTRUCTION). Rich multi-condition MC/DC needs a
# rustc-built fixture — short-circuit && hand-written in WAT is not fully
# coverable under witness's condition-to-branch model (the masked condition is
# recorded absent, not F) — and is tracked as the SR-62 follow-up.
#
# This gate is therefore a PIPELINE + BRANCH-COVERAGE no-regression guard with
# real teeth:
#   (1) meld fuse must produce a VALID, import-free core module (else witness
#       cannot run it);
#   (2) witness must still find the seam's branches (branch_count >= 1) — guards
#       against a future meld/witness change that dead-strips them, which would
#       otherwise make the gap check vacuous;
#   (3) invoking check() above and below the threshold must reach BOTH branch
#       edges (100% branch coverage) — regresses to RED if a branch edge becomes
#       UNREACHABLE, if the decision outcome stops flipping between the two
#       vectors, or if the export is renamed/dropped so `witness run` invokes
#       nothing (0/2). NOTE: this checks reachability, not value-correctness — a
#       broken fusion that made add() return the wrong value would still flip the
#       x=100 vs x=1 outcome and stay green;
#   (4) the MC/DC report must be well-formed and show 0 gap rows.
#
# Usage:  WITNESS=/path/to/witness [MELD=/path/to/meld] tests/gate/run-witness.sh
set -euo pipefail

MELD="${MELD:-target/release/meld}"
WITNESS="${WITNESS:?set WITNESS to the witness binary}"
cd "$(dirname "$0")/../.."   # repo root

FIXTURE=tests/gate/composed.wasm
EXPORT='gate:seam/runner@0.1.0#check'

WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT

# (1) Fuse the seam into a single import-free core module (and validate it).
"$MELD" fuse "$FIXTURE" --preserve-names --validate -o "$WORK/fused.wasm"

# (2) Instrument, and assert witness still finds the seam's branches.
"$WITNESS" instrument "$WORK/fused.wasm" -o "$WORK/i.wasm"
BRANCHES="$(python3 -c "import json; print(len(json.load(open('$WORK/i.wasm.witness.json'))['branches']))")"
if [ "$BRANCHES" -lt 1 ]; then
    echo "::error::witness instrumented 0 branches on the fused seam — meld may have dead-stripped them; the gate would be vacuous"
    exit 1
fi
echo "instrumented $BRANCHES branch edge(s) on the fused seam"

# (3) Exercise both edges of the decision: x=100 (>40, true) and x=1 (<40, false).
"$WITNESS" run "$WORK/i.wasm" \
    --invoke-with-args "$EXPORT=100" \
    --invoke-with-args "$EXPORT=1" \
    -o "$WORK/r.json"

TEXT="$("$WITNESS" report --input "$WORK/r.json" --format text)"
echo "$TEXT"
# Line shape: "branches reached: N/M (P%) ...". Require full branch coverage.
COV="$(printf '%s\n' "$TEXT" | grep -oE 'branches reached: [0-9]+/[0-9]+' | head -1 || true)"
if [ -z "$COV" ]; then
    echo "::error::witness text report format changed — 'branches reached: N/M' not found"
    exit 1
fi
REACHED="$(printf '%s' "$COV" | grep -oE '[0-9]+/[0-9]+' | cut -d/ -f1)"
TOTAL="$(printf '%s' "$COV" | grep -oE '[0-9]+/[0-9]+' | cut -d/ -f2)"
if [ "$TOTAL" -lt 1 ] || [ "$REACHED" -ne "$TOTAL" ]; then
    echo "::error::branch coverage regressed: $REACHED/$TOTAL edges reached on the fused seam (expected full)"
    exit 1
fi
echo "PASS(cov): $REACHED/$TOTAL branch edges reached on the fused seam"

# (4) MC/DC report: assert the format is present (do NOT default a missing field
#     to pass), then gate on 0 gap rows.
REPORT="$("$WITNESS" report --input "$WORK/r.json" --format mcdc)"
echo "$REPORT"
if ! printf '%s\n' "$REPORT" | grep -qE '[0-9]+ gap'; then
    echo "::error::witness mcdc report format changed — '<N> gap' not found; refusing to pass vacuously"
    exit 1
fi
GAP="$(printf '%s\n' "$REPORT" | grep -oE '[0-9]+ gap' | grep -oE '[0-9]+' | head -1)"
if [ "$GAP" -ne 0 ]; then
    echo "::error::witness reports $GAP unresolved MC/DC gap row(s) on the fused seam"
    exit 1
fi
echo "PASS: 0 MC/DC gap rows on the fused seam (single-condition decision — MC/DC == branch coverage)"
