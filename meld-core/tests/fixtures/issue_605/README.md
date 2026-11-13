# #605: exported interfaces that define their own types

falcon-cascade v0.13.0, the three components of relay's split cascade plus
their `wac plug` composition. The `pilot` interface the split exports defines
its own `record supervisor-config`, `record sensor-calibration` and
`enum pilot-command`. The other interfaces only `use` types from the imported
`types` interface.

## Provenance

Deployment builds (no_std, 8 KiB stack, relocations) from pulseengine/relay
main 4836198, made by the relay session for the meld differential:

    cascade-split.wasm       9df1a114…c37893c
    cascade-estimator.wasm   034e55e8…e56428
    cascade-control.wasm     96bf9219…bd5b3c
    composed.wasm            0def6a0d…b7b1e8   (wac 0.6.0, `wac plug` of the three, as in relay's scripts/split-differential.sh)

## Used by

`tests/component_wrap_605.rs`: `meld fuse --component` of the three inputs
must return what `composed.wasm` returns for every exported function, and
`pilot`'s own types must come out named, with the enum as an `enum`.
