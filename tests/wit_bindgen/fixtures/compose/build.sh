#!/usr/bin/env bash
# Builds the Tier B multi-component fixture for golden_e2e.rs, fully
# offline with wasm-tools + wac. A `consumer` whose `runner.compute()`
# calls a `provider`'s `add(20,22)`, host-linked via `wac plug` into
# `composed.wasm`. meld fusing composed.wasm must preserve compute()==42.
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
echo "built composed.wasm (consumer.runner.compute -> provider.add(20,22)=42)"
