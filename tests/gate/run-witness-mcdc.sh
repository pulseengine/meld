#!/usr/bin/env bash
# Witness RICH MULTI-CONDITION MC/DC gate on a FUSED meld output
# (meld#302 Track C2, SR-62 follow-up to run-witness.sh).
#
# Where run-witness.sh gates a single-condition seam (hand-written WAT,
# `result > 40`, where MC/DC collapses to branch coverage — 0 recoverable
# multi-condition decisions BY CONSTRUCTION), THIS gate uses a rustc-built
# fixture (tests/gate/leap_mcdc/) whose leap-year predicate
#     (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
# lowers to a short-circuit br_if chain WITH DWARF. rustc fuses the third
# condition, so witness reconstructs ONE decision with TWO independent
# conditions and proves each under masking / unique-cause MC/DC.
#
# The fixture ships as a checked-in Component (tests/gate/leap_component.wasm,
# built by leap_mcdc/build.sh — CI does NOT rebuild from rustc). `meld fuse`
# internalises the component seam into a single import-free core module; this
# gate proves the multi-condition decision AND its DWARF source attribution
# SURVIVE that fusion, then that witness recovers full MC/DC with 0 gap.
#
# Teeth (each parse is preceded by a format-present check that refuses to
# pass vacuously if witness's output shape changes):
#   (1) meld fuse must emit a VALID, import-free core module;
#   (2) witness must instrument >= 2 branch edges on the fused seam — this is
#       what makes it a MULTI-condition gate, not another branch-coverage one;
#       red if a future meld/witness change dead-strips or collapses the chain;
#   (3) the MC/DC report must reconstruct >= 1 decision, ALL proved (proved ==
#       total), with >= 2 conditions proved, 0 gap, and 0 dead — red if fusion
#       drops DWARF, mangles the branch chain, or the decision stops being
#       fully coverable by the five year vectors;
#   (4) the decision must carry a source-line attribution (`lib.rs:`) — red if
#       DWARF line info does not survive fusion (witness would fall back to a
#       synthetic location and rich MC/DC would silently degrade).
#
# Usage:  WITNESS=/path/to/witness [MELD=/path/to/meld] tests/gate/run-witness-mcdc.sh
set -euo pipefail

MELD="${MELD:-target/release/meld}"
WITNESS="${WITNESS:?set WITNESS to the witness binary}"
cd "$(dirname "$0")/../.."   # repo root

FIXTURE=tests/gate/leap_component.wasm
EXPORT='gate:leap/rule@0.1.0#is-leap'

WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT

# (1) Fuse the component seam into a single import-free core module (validated).
#     Pin `--memory multi` (what `auto` resolves to here) so a future change to
#     meld's memory-strategy heuristic can't silently alter the fused shape this
#     gate reconstructs against — and to satisfy ADR-4 (explicit, not auto).
"$MELD" fuse "$FIXTURE" --memory multi --preserve-names --validate -o "$WORK/fused.wasm"

# (2) Instrument; assert witness finds the multi-condition chain (>= 2 edges).
"$WITNESS" instrument "$WORK/fused.wasm" -o "$WORK/i.wasm"
BRANCHES="$(python3 -c "import json,sys; print(len(json.load(open('$WORK/i.wasm.witness.json'))['branches']))")"
if [ "$BRANCHES" -lt 2 ]; then
    echo "::error::witness instrumented $BRANCHES branch edge(s) on the fused leap seam (expected >= 2) — the multi-condition chain was dead-stripped or collapsed; the MC/DC gate would be vacuous"
    exit 1
fi
echo "instrumented $BRANCHES branch edge(s) on the fused leap seam"

# (3) Drive the five year vectors that cover the truth table:
#   2001 -> c0=F                  -> F        (first condition false)
#   2004 -> c0=T, c1=T            -> T        (a&&b carries)
#   2100 -> c0=T, c1=F            -> F
#   2000 -> c0=T, c1=F, %400      -> T        (% 400 fused into the chain)
#   1900 -> c0=T, c1=F            -> F
"$WITNESS" run "$WORK/i.wasm" \
    --invoke-with-args "$EXPORT=2001" \
    --invoke-with-args "$EXPORT=2004" \
    --invoke-with-args "$EXPORT=2100" \
    --invoke-with-args "$EXPORT=2000" \
    --invoke-with-args "$EXPORT=1900" \
    -o "$WORK/r.json"

REPORT="$("$WITNESS" report --input "$WORK/r.json" --format mcdc)"
echo "----- witness report --format mcdc -----"
echo "$REPORT"
echo "----------------------------------------"

# Header line shape (format-present check first — refuse to pass vacuously):
#   "decisions: A/B full MC/DC; conditions: N proved, G gap, D dead"
HDR="$(printf '%s\n' "$REPORT" | grep -E 'decisions: [0-9]+/[0-9]+.*conditions: [0-9]+ proved' | head -1 || true)"
if [ -z "$HDR" ]; then
    echo "::error::witness mcdc report format changed — 'decisions: A/B ... conditions: N proved' header not found; refusing to pass vacuously"
    exit 1
fi

PROVED_DEC="$(printf '%s' "$HDR" | grep -oE 'decisions: [0-9]+/[0-9]+' | grep -oE '[0-9]+/[0-9]+' | cut -d/ -f1)"
TOTAL_DEC="$(printf '%s' "$HDR" | grep -oE 'decisions: [0-9]+/[0-9]+' | grep -oE '[0-9]+/[0-9]+' | cut -d/ -f2)"
COND_PROVED="$(printf '%s' "$HDR" | grep -oE 'conditions: [0-9]+ proved' | grep -oE '[0-9]+')"
GAP="$(printf '%s' "$HDR" | grep -oE '[0-9]+ gap' | grep -oE '[0-9]+')"
DEAD="$(printf '%s' "$HDR" | grep -oE '[0-9]+ dead' | grep -oE '[0-9]+')"

if [ -z "$GAP" ] || [ -z "$DEAD" ]; then
    echo "::error::witness mcdc report format changed — 'N gap' / 'N dead' not found; refusing to pass vacuously"
    exit 1
fi

# Decisions: at least one, and every one fully proved.
if [ "$TOTAL_DEC" -lt 1 ] || [ "$PROVED_DEC" -ne "$TOTAL_DEC" ]; then
    echo "::error::MC/DC regressed on the fused leap seam: $PROVED_DEC/$TOTAL_DEC decisions proved (expected all, >= 1)"
    exit 1
fi
# The point of THIS gate: a genuine MULTI-condition decision (>= 2 conditions).
if [ "$COND_PROVED" -lt 2 ]; then
    echo "::error::only $COND_PROVED condition(s) proved on the fused leap seam (expected >= 2) — the decision collapsed to single-condition; this is no longer a multi-condition MC/DC gate"
    exit 1
fi
# No unresolved / infeasible rows.
if [ "$GAP" -ne 0 ]; then
    echo "::error::witness reports $GAP unresolved MC/DC gap row(s) on the fused leap seam"
    exit 1
fi
if [ "$DEAD" -ne 0 ]; then
    echo "::error::witness reports $DEAD dead MC/DC row(s) on the fused leap seam"
    exit 1
fi

# (4) DWARF source attribution must survive fusion (do not assert a specific
#     line number — it moves when the fixture is edited).
if ! printf '%s\n' "$REPORT" | grep -qE 'decision #[0-9]+ [^ ]*lib\.rs:[0-9]+'; then
    echo "::error::no 'lib.rs:<line>' source attribution on the fused decision — DWARF line info did not survive fusion; rich MC/DC degraded to a synthetic location"
    exit 1
fi

echo "PASS: fused leap seam — $PROVED_DEC/$TOTAL_DEC decision(s) full MC/DC, $COND_PROVED conditions proved, 0 gap, 0 dead, DWARF source attribution intact"
