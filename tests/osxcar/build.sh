#!/usr/bin/env bash
# Build composed P2 components from osxcar core modules
# Requires: wasm-tools (https://github.com/bytecodealliance/wasm-tools)
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FIXTURES="$SCRIPT_DIR/fixtures"
WIT="$SCRIPT_DIR/wit"
OUT="$SCRIPT_DIR/composed"

mkdir -p "$OUT"

echo "Wrapping core modules into P2 components..."
for pair in \
    "anti_pinch_v2:anti-pinch-v2-component" \
    "motor_driver_v2:motor-driver-v2-component" \
    "soft_start_stop:soft-start-stop-component"; do

    name="${pair%%:*}"
    world="${pair##*:}"
    echo "  ${name}: embedding WIT (world=${world})..."

    # Step 1: Embed WIT metadata into the core module
    wasm-tools component embed \
        "$WIT" \
        "$FIXTURES/${name}.wasm" \
        --world "$world" \
        -o "$OUT/${name}.embedded.wasm"

    # Step 2: Create P2 component from embedded module
    wasm-tools component new \
        "$OUT/${name}.embedded.wasm" \
        -o "$OUT/${name}.component.wasm"

    # Clean up intermediate file
    rm -f "$OUT/${name}.embedded.wasm"

    size=$(wc -c < "$OUT/${name}.component.wasm")
    echo "  ${name}.component.wasm: ${size} bytes"
done

echo ""
echo "Validating components..."
for f in "$OUT"/*.component.wasm; do
    if wasm-tools validate "$f" 2>/dev/null; then
        echo "  $(basename "$f"): OK"
    else
        echo "  $(basename "$f"): INVALID"
    fi
done

echo ""
echo "Components ready in $OUT/"
echo "To fuse with meld:  meld fuse $OUT/*.component.wasm -o osxcar_fused.wasm"
