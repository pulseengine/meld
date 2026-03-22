#!/bin/bash
# Build composed P2 components from osxcar core modules
# Requires: wasm-tools (https://github.com/bytecodealliance/wasm-tools)
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FIXTURES="$SCRIPT_DIR/fixtures"
WIT="$SCRIPT_DIR/wit"
OUT="$SCRIPT_DIR/composed"

mkdir -p "$OUT"

echo "Wrapping core modules into P2 components..."
for name in anti_pinch_v2 motor_driver_v2 soft_start_stop; do
    wasm-tools component new \
        "$FIXTURES/${name}.wasm" \
        --wit "$WIT" \
        -o "$OUT/${name}.component.wasm" \
        2>&1 || echo "WARN: ${name} wrapping failed (may need WIT adjustments)"
    echo "  ${name}: $(wc -c < "$OUT/${name}.component.wasm" 2>/dev/null || echo 'failed') bytes"
done

echo ""
echo "Components ready in $OUT/"
echo "To fuse with meld:  meld fuse $OUT/*.component.wasm -o osxcar_fused.wasm"
