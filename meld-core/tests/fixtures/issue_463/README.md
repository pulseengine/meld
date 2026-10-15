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
name. The world is found through the lifts, so the rename is no obstacle: the
functions are exported under `test:renamed/est@0.1.0#…`.

## Review fixtures (hand-written components)

Built from `src/*.wat` with `wasm-tools parse`; `middleware.wasm` is
`wac plug --plug svc.wasm mid.wasm`. sha256:

    import_needs.wasm  479fabc929b4d5c897503e6ded96ee25e71400091cf9fc8b388d264bdeee24e1
    drop_g.wasm        bb638e96321fec324e7ca46b689270edaa9f0f7aefdd0107ed42ee797fa268c5
    svc.wasm           159c9991d8c93dd5bab86502592be402ca12f850395cc0715a947e4f4c35d309
    mid.wasm           5a702634629dd5669cb80146f453e733c428a489276cabb1aa93c31424cf1661
    middleware.wasm    5af35d85de1ea3066e279226eca9f55ebb539584db0efcf4f80ab5da26d232bb

- `import_needs`: the kept `run` calls two lowered imports whose `canon lower`
  names a memory and an allocator.
- `drop_g`: interface `test:x/i` with `f` (core `test:x/i#f`) and `g` (core
  `impl_g`).
- `middleware`: the outer world is `mid`'s `test:x/i`; `svc` is internal; both
  have the core export `test:x/i#f`.
