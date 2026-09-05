#!/usr/bin/env bash
# Builds the #390 record-carrying multi-component fixture, fully offline with
# wasm-tools + wac.
#
# The point of this fixture is the CALLING CONVENTION, not the arithmetic: a
# 4xf32 record exceeds MAX_FLAT_RESULTS, so the canonical ABI puts the two
# sides on different core signatures —
#
#   consumer (lowered import): (f32, f32, retptr: i32) -> ()
#   provider (lifted export):  (f32, f32)              -> i32   ; return-area ptr
#
# which is exactly the shape meld's same-memory `Direct` path used to assume
# away (#390). `run()` must return 26 (3 + 4 + 7 + 12).
#
# Neither core module declares a data segment, so the SR-56 overlap gate and
# the path-F relocation gate stay quiet and the boundary itself is what the
# test exercises.
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
wac plug consumer.wasm --plug provider.wasm -o composed_record_use.wasm
wasm-tools validate composed_record_use.wasm
echo "built composed_record_use.wasm (consumer.runner.run -> 91)"
