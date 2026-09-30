#!/usr/bin/env bash
# domains_427 (SR-86, meld#427) — rebuilds the three components.
#
# provider/ and consumer/ are gale's, from gale#412
# (benches/gust/fixtures/meld-domains/). consumer2/ is consumer with its
# package, world and export renamed, so two tenants call one provider and the
# only difference between the call sites is which domain they land in.
#
# --emit-relocs on the final link is required: without relocation metadata meld
# REFUSES the shared path rather than rebasing unsafely.
set -euo pipefail
cd "$(dirname "$0")"
for d in provider consumer consumer2; do
  ( cd "$d" && RUSTFLAGS="-C link-arg=--emit-relocs" CARGO_TARGET_DIR="$PWD/target" \
      cargo build --release --target wasm32-unknown-unknown >/dev/null )
  wasm-tools component new \
    "$d/target/wasm32-unknown-unknown/release/capfix_${d}.wasm" -o "$d.comp.wasm"
  echo "  $d.comp.wasm  $(wc -c < "$d.comp.wasm") bytes"
done
