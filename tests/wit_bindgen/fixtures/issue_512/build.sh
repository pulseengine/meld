#!/bin/bash
# Rebuild the #512 fixtures: cx/composed.wasm and shapes/composed.wasm.
#
# Needs the exact tools recorded in README.md, located by environment:
#   WASI_SDK      wasi-sdk 34.0 root (contains bin/clang)
#   WIT_BINDGEN   wit-bindgen-cli 0.63.0 binary
#   WASM_TOOLS    wasm-tools 1.262.0 binary
#
# Usage: build.sh [cx|shapes]...   (default: both)
# Generated bindings and intermediates go to a temporary directory; only
# composed.wasm is written back next to the sources.
set -euo pipefail
: "${WASI_SDK:?set WASI_SDK to a wasi-sdk 34.0 root}"
: "${WIT_BINDGEN:?set WIT_BINDGEN to a wit-bindgen 0.63.0 binary}"
: "${WASM_TOOLS:?set WASM_TOOLS to a wasm-tools 1.262.0 binary}"
HERE="$(cd "$(dirname "$0")" && pwd)"
CC="$WASI_SDK/bin/clang"

[ $# -gt 0 ] || set -- cx shapes
for fx in "$@"; do
  src="$HERE/$fx"
  work="$(mktemp -d)"
  cp -R "$src/wit" "$src/provider_impl.c" "$src/guest_impl.c" "$work/"
  (
    cd "$work"
    # The issue's commands, verbatim.
    "$WIT_BINDGEN" c wit --world provider --out-dir gp
    "$WIT_BINDGEN" c wit --world guest --out-dir gg
    "$CC" --target=wasm32-wasip2 -O1 -mexec-model=reactor -o provider.wasm \
      provider_impl.c gp/provider.c gp/provider_component_type.o
    "$CC" --target=wasm32-wasip2 -O1 -mexec-model=reactor -o guest.wasm \
      guest_impl.c gg/guest.c gg/guest_component_type.o
    "$WASM_TOOLS" compose guest.wasm -d provider.wasm -o composed.wasm
  )
  cp "$work/composed.wasm" "$src/composed.wasm"
  rm -rf "$work"
  shasum -a 256 "$src/composed.wasm"
done
