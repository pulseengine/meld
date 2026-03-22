#!/bin/bash
# Download and extract osxcar anti-pinch WASM core modules
# from https://osxcar.de/insights/demonstration/
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FIXTURES="$SCRIPT_DIR/fixtures"
BASE_URL="https://osxcar.de/js/anti-pinch/components/html"

mkdir -p "$FIXTURES"

for name in anti_pinch_v2 motor_driver_v2 soft_start_stop; do
    echo "Downloading ${name}..."
    js=$(curl -sL "${BASE_URL}/${name}_component.js")
    b64=$(echo "$js" | grep -oE "base64Compile\('[^']+'\)" | head -1 | sed "s/base64Compile('//;s/')$//")
    pad=$((4 - ${#b64} % 4))
    [ $pad -eq 1 ] && b64="${b64}="
    [ $pad -eq 2 ] && b64="${b64}=="
    [ $pad -eq 3 ] && b64="${b64}==="
    echo -n "$b64" | base64 -d > "$FIXTURES/${name}.wasm"
    size=$(wc -c < "$FIXTURES/${name}.wasm")
    echo "  ${name}.wasm: ${size} bytes"
done

echo ""
echo "Validating..."
for f in "$FIXTURES"/*.wasm; do
    if wasm-tools validate "$f" 2>/dev/null; then
        echo "  $(basename "$f"): OK"
    else
        echo "  $(basename "$f"): INVALID"
    fi
done
