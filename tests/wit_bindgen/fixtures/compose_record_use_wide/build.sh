#!/usr/bin/env bash
# Builds the #423 / #400 wide-`use`d-params fixture, fully offline with
# wasm-tools + wac. No cargo-component, no network.
#
# The point of this fixture is the FLAT PARAMETER COUNT. `tick` takes a 14-f32
# record plus a 4-f32 record, both reached through `use`:
#
#   18 flattened params  >  MAX_FLAT_PARAMS (16)
#
# so the canonical ABI passes them through a pointer into an argument area that
# the CALLEE's allocator provides — `wasm-tools component new` refuses the
# provider without an exported `cabi_realloc`, which is the tooling stating the
# same requirement. meld counted a `use`d record as ONE flat value (2 instead of
# 18), took the flat branch, and the fused module validated, ran, and returned 0
# instead of 120 (#423).
#
# The existing `compose_record_use` fixture cannot reach this: its records are
# four fields wide, so the wrong count (1) and the right one (4) are both under
# the limit — which is why #393's size fix was sufficient there.
#
# `provider2` is a second wide provider under a different package. Both need the
# callee's allocator, and in shared memory every component names its allocator
# `cabi_realloc`, so only one can hold that name: the other export ends up with
# no reachable allocator, which is what SR-81 / #400 fixes. Its arithmetic
# differs (o3 = state.f2, not state.f1) so the two cannot be confused.
#
# `run()` must return 120: o1 = sum(1..14) = 105, o2 = sum(1..4) = 10,
# o3 = state.f1 = 1, o4 = setpoint.r4 = 4.
#
# Re-run after changing any .wat/.wit. Requires: wasm-tools, wac.
set -euo pipefail
cd "$(dirname "$0")"

wasm-tools parse provider_core.wat -o provider_core.wasm
wasm-tools component embed provider.wit --world provider provider_core.wasm -o provider_embed.wasm
wasm-tools component new provider_embed.wasm -o provider.wasm

wasm-tools parse provider2_core.wat -o provider2_core.wasm
wasm-tools component embed provider2.wit --world provider provider2_core.wasm -o provider2_embed.wasm
wasm-tools component new provider2_embed.wasm -o provider2.wasm

wasm-tools parse consumer_core.wat -o consumer_core.wasm
wasm-tools component embed consumer_wit --world consumer consumer_core.wasm -o consumer_embed.wasm
wasm-tools component new consumer_embed.wasm -o consumer.wasm

wac plug consumer.wasm --plug provider.wasm -o composed_wide_use.wasm
wasm-tools validate composed_wide_use.wasm
echo "built composed_wide_use.wasm (golden:wideapp/runner#run -> 120) and provider2.wasm"
