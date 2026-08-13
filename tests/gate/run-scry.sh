#!/usr/bin/env bash
# Scry sound-abstract-interpretation robustness gate on a FUSED meld output
# (meld#302 Track C3, SR-61) — the DO-333 leg of the verification chain.
#
# Fuses the checked-in real wit_bindgen fixture (`strings-simple.wasm`) with
# meld, then runs `scry-viz check` — sound over-approximating abstract
# interpretation over the fused CORE module — asserting the analysis result is
# structurally well-formed (functions / program points / call edges resolve).
# Red on any malformed result or analyzer crash; scry over-approximates, so a
# well-formed result on a real fused module is a genuine robustness oracle.
#
# Scry does NOT execute the module, so the ~38 residual wasi:* imports the real
# fixture carries are harmless here (contrast run-witness.sh, which executes and
# therefore needs an import-free fixture).
#
# Usage:  SCRY=/path/to/scry-viz [MELD=/path/to/meld] tests/gate/run-scry.sh
set -euo pipefail

MELD="${MELD:-target/release/meld}"
SCRY="${SCRY:?set SCRY to the scry-viz binary}"
cd "$(dirname "$0")/../.."   # repo root

WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT

"$MELD" fuse tests/wit_bindgen/fixtures/strings-simple.wasm --validate -o "$WORK/fused.wasm"

# `scry-viz check` runs the sound analysis and exits non-zero on a malformed
# result (a scry-detected structural violation) or a crash. It writes its
# summary line to stderr, so capture both streams; inspect the exit code
# explicitly (don't let `set -e` abort before we can print diagnostics).
set +e
OUT="$("$SCRY" check "$WORK/fused.wasm" 2>&1)"
RC=$?
set -e
echo "$OUT"
if [ "$RC" -ne 0 ]; then
    echo "::error::scry-viz check exited $RC (malformed result or analyzer crash)"
    exit 1
fi

# Non-vacuity guard: exit 0 alone is not enough — a future scry that analysed 0
# functions and still exited 0 would pass silently. Require the "<N> functions"
# field to be present and N > 0.
FUNCS="$(printf '%s\n' "$OUT" | grep -oE '[0-9]+ functions' | grep -oE '[0-9]+' | head -1 || true)"
if [ -z "$FUNCS" ]; then
    echo "::error::scry-viz check output format changed — '<N> functions' not found; refusing to pass vacuously"
    exit 1
fi
if [ "$FUNCS" -lt 1 ]; then
    echo "::error::scry-viz analysed 0 functions on the fused module — vacuous result"
    exit 1
fi
echo "PASS: scry sound-AI analysis of the fused strings-simple module is well-formed ($FUNCS functions)"
