#!/usr/bin/env bash
# Rebuild the rustc-built multi-condition MC/DC gate fixture
# (meld#302 Track C2, SR-62 follow-up).
#
# Produces tests/gate/leap_component.wasm — a Component wrapping a rustc
# core module whose leap-year predicate lowers to a short-circuit br_if
# chain WITH DWARF. `meld fuse` internalises the component seam into a
# single import-free core module that KEEPS the predicate's branches and
# DWARF, so `witness` reconstructs a real 2-condition MC/DC decision from
# the fused output (see ../run-witness-mcdc.sh).
#
# The built .wasm is force-added to git (tests/gate/ has a `*.wasm`
# gitignore, same as composed.wasm), so CI does NOT rebuild from rustc —
# it fuses the checked-in component. Re-run this LOCALLY after editing
# src/lib.rs or wit/leap.wit, then `git add -f ../leap_component.wasm`.
#
# Requires: a wasm32-unknown-unknown rust target + cargo, and wasm-tools.
# Pin note: rustc lowering can shift the exact br_if shape across versions.
# If witness stops recovering the 2-condition decision after a toolchain
# bump, regenerate here and re-verify with ../run-witness-mcdc.sh.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

TARGET="${TARGET:-wasm32-unknown-unknown}"

if ! rustup target list --installed | grep -q "^${TARGET}$"; then
    echo "error: rustup target '${TARGET}' is not installed." >&2
    echo "  hint: rustup target add ${TARGET}" >&2
    exit 1
fi

# Build to a scratch target dir so a local regen leaves no untracked
# tests/gate/leap_mcdc/target/ noise. Remap the crate path so the
# checked-in .wasm's DWARF comp-dir does not leak an absolute build path.
BUILD_TARGET_DIR="${CARGO_TARGET_DIR:-$(mktemp -d)}"
RUSTFLAGS="${RUSTFLAGS:-} --remap-path-prefix=${SCRIPT_DIR}=leap_mcdc" \
    CARGO_TARGET_DIR="$BUILD_TARGET_DIR" \
    cargo build --release --target "$TARGET"

CORE="$BUILD_TARGET_DIR/${TARGET}/release/leap_mcdc.wasm"
[ -f "$CORE" ] || { echo "build did not produce $CORE" >&2; exit 1; }

# Wrap the core module into a Component so `meld fuse` accepts it (fuse
# takes component inputs, not bare core modules).
wasm-tools component embed wit --world leap "$CORE" -o leap_embed.wasm
wasm-tools component new leap_embed.wasm -o ../leap_component.wasm
wasm-tools validate ../leap_component.wasm
rm -f leap_embed.wasm

echo "built ../leap_component.wasm ($(wc -c < ../leap_component.wasm) bytes)"
echo "  export: gate:leap/rule@0.1.0#is-leap  decision: (y%4==0 && y%100!=0) || y%400==0"
echo "  next:   git add -f ../leap_component.wasm  &&  ../run-witness-mcdc.sh"
