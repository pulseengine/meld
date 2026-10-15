# #463 — export surface of a composed input

Compositions of cpetig's three falcon-cascade components (the `issue_461`
fixtures), used to test `meld fuse --exports world`.

The outer world of both is a composition of `estimator` + `flight-control`
(internal) behind `split`, which exports `controller` and `observer`. Fused
without `--exports world`, the core module also exports the internal
`estimator@…#…` and `flight-control@…#…` functions, two `cabi_realloc*`
allocators, and `__data_end` / `__heap_base` (#475).

## Files

    composed.wasm            sha256 b6601eba0660379fa23329de8f2be5b5ed9d16501d90ae2615d928585c8cecf2
    composed_reexport.wasm   sha256 f0fce6e364718815e71354b5dfed18311d5717a32b27dd520bd777c4078d42c8
    composed_reexport.wac    the source of composed_reexport.wasm

`composed.wasm` is:

    wac plug --plug falcon_cascade_control_cm.wasm \
             --plug falcon_cascade_estimator_cm.wasm \
             falcon_cascade_split_cm.wasm -o composed.wasm

It exports `controller@0.11.0` and `observer@0.11.0` only.

`composed_reexport.wasm` is the same composition, additionally re-exporting
the INNER estimator interface (`export est[...]` in the `.wac`) so the outer
world legitimately contains an interface that was internal in the other file.
It is the negative control for "an outer world that re-exports an inner
interface keeps it":

    wac compose composed_reexport.wac \
        -d pulseengine:estimator=falcon_cascade_estimator_cm.wasm \
        -d pulseengine:control=falcon_cascade_control_cm.wasm \
        -d pulseengine:split=falcon_cascade_split_cm.wasm \
        -o composed_reexport.wasm

## Provenance

Built with **wac-cli 0.6.0**. The issue reports a composed input built with
wac-cli 0.10.1 (sha256 `b2ba69ca…f06f`); these bytes are therefore NOT that
file, only the same composition of the same three inputs. The inputs are the
`issue_461` fixtures, whose own provenance is recorded there.

The test does not shell out to `wac`: it is not available on every CI runner,
and a test that skipped without it would read as passing while testing
nothing (SR-85).

`composed_renamed.wasm` (sha256 322ef1daf0d16c529e2d863957ae612572203c88ed6617fd45a164b2c474c6be,
source `composed_renamed.wac`, same `wac compose` command) exports the estimator
as `test:renamed/est@0.1.0`. The fused module keeps the lifted export's own
name, so that world export has no fused counterpart: it is the refusal case.
