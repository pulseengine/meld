# #461 — adapter re-rewrite discarded shared-memory rebasing

Three components that reproduce #461: under `--memory shared --address-rebase`
the third one's data segments were rebased while its code was not, so it read
a neighbour's statics and spun forever in a panic handler.

## Provenance

Built and attached to pulseengine/meld#461 by @cpetig, from
`wasm/cm/cascade-{estimator,control,split}` in pulseengine/relay. Verified by
sha256 against the values published in that issue:

    falcon_cascade_estimator_cm.wasm   3fc79423…2dc975b9
    falcon_cascade_control_cm.wasm     77b77d72…6daf232d
    falcon_cascade_split_cm.wasm       7313422b…80ebbe6b

Built with:

    RUSTFLAGS="-C link-arg=--emit-relocs -C link-arg=-zstack-size=8192 \
      -C link-arg=--export=__heap_base -C link-arg=--export=__data_end" \
    cargo component build --release --target wasm32-unknown-unknown \
      --no-default-features

cargo-component 0.21.1, wasm-tools 1.259.0, wac-cli 0.10.1.

## Why these and not a synthetic pair

`split` is the component that matters, and what makes it matter is structural:
because its imports pass records by pointer, wit-component gives it **three**
core modules —

    module 0   16109 B   linking, reloc.CODE, reloc.DATA   (defines the memory)
    module 1     281 B   no relocs                          (lowered-import shim)
    module 2     133 B   no relocs                          (fixup)

— and its import is redirected to an adapter, which is the precise condition
that put it through the re-rewrite loop that discarded the rebasing.

A synthetic fixture would have to reproduce that whole shape to trigger
anything, and a fixture that quietly fails to is worse than none: it reads as
a passing regression test while testing nothing.

## The oracle

`split` is placed at base 131072. Before the fix the fused module contained
**no** load or store offset at or above 128K, while split's data segments had
moved to 139264/139296 — data rebased, code not. After it, split's 95
absolute offsets appear shifted by exactly +131072, and its code and data
agree again.
