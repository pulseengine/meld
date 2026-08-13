#!/usr/bin/env bash
# Rebuilds the import-free wasm-verification gate fixture, fully offline with
# wasm-tools + wac (meld#302 Track C, SR-61/SR-62).
#
# A `consumer` whose `runner.check(x)` calls a `provider`'s `add(x, 0)` across a
# scalar component seam, then decides `result > 40`. Host-linked via `wac plug`
# into `composed.wasm`. When meld fuses composed.wasm the seam is internalised,
# so the fused CORE module has ZERO imports — which is what lets `witness run`
# execute it under wasmtime (a core module cannot stub component imports;
# `--stub-imports` is component-backend only). The single `if` gives the witness
# gate a real branch to cover in both directions (invoke check with x>40 and
# x<40 -> 2/2 branch coverage); it is one condition, so MC/DC == branch coverage
# here (0 recoverable multi-condition decisions — rich MC/DC needs a rustc-built
# fixture, tracked as the SR-62 follow-up).
#
# Re-run after changing any .wat/.wit. Requires: wasm-tools, wac.
set -euo pipefail
cd "$(dirname "$0")"

wasm-tools parse provider_core.wat -o provider_core.wasm
wasm-tools component embed provider.wit --world provider provider_core.wasm -o provider_embed.wasm
wasm-tools component new provider_embed.wasm -o provider.wasm

wasm-tools parse consumer_core.wat -o consumer_core.wasm
wasm-tools component embed consumer_wit --world consumer consumer_core.wasm -o consumer_embed.wasm
wasm-tools component new consumer_embed.wasm -o consumer.wasm

wac plug consumer.wasm --plug provider.wasm -o composed.wasm
wasm-tools validate composed.wasm
echo "built composed.wasm (consumer.runner.check(x) -> add(x,0), decide >40)"
