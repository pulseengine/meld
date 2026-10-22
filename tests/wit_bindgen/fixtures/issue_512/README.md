# #512 fixtures — `list<string>` behind a discriminant, across memories

Regression fixtures for [meld#512](https://github.com/pulseengine/meld/issues/512),
read by `meld-core/tests/nested_list_string_result_512.rs` and by the
wasmtime-environ oracle (`meld-core/tests/oracle_wasmtime_environ.rs`).

Both are C wit-bindgen provider/guest pairs composed with `wasm-tools compose`.
The guest exports `run-all: func() -> string`. The tests run the composition
directly under wasmtime, as the oracle, and compare it with
`meld fuse --component` (multi-memory).

| directory | what it is |
|-----------|------------|
| `cx/`     | The reporter's component. `wit/cx.wit`, `provider_impl.c` and `guest_impl.c` are copied byte-for-byte from the issue. |
| `shapes/` | The narrowing matrix: one call per shape. The table in the test file maps each label to its WIT shape and the adapter path it exercises. |

## Tools

| tool | version |
|------|---------|
| wasi-sdk | 34.0 (`wasi-sdk-34.0-arm64-macos`, clang 23.1.0-wasi-sdk) |
| wit-bindgen-cli | 0.63.0 |
| wasm-tools | 1.262.0 |

These are the reporter's versions. The reporter ran Linux x86-64; these
fixtures were built on macOS arm64.

## Build

```sh
WASI_SDK=/path/to/wasi-sdk-34.0 WIT_BINDGEN=/path/to/wit-bindgen \
WASM_TOOLS=/path/to/wasm-tools ./build.sh
```

`build.sh` runs the issue's commands verbatim. A second build from these
sources produced byte-identical output.

## sha256

```
e31d954f9dabd7fbbf7004e6d47037b3caa9ec4bdb20b84899746786ce797888  cx/composed.wasm
ab3df2910c45bb05b77b0c1beb62ad697e656c34242004d47a49f9664e7b700e  shapes/composed.wasm
```

## Expected `run-all` output

These are the composition's own values under wasmtime 50.

`cx/`:

```
put=ok:0;put0=err:qty must be > 0;get=apple,3,[red,big];get9=none;area=48,42,0;level=0,1,2;perms=3;sum=4000000006;counter=15,counter=15,peek=100
```

Before the fix, meld 0.64.0 returned `get=apple,3,[,]`.

`shapes/`:

```
a=2[red,big];b=2[rec,ord];c=2[opt,lst];d=apple,3,2[itm,tag];e=solo;f=2[res,ok];g=2[owr,apx];h=2[los,two];p=arg|in|;q=933777361;r=40033474
```

Before the fix, meld 0.64.0 got shapes c, d, f, g, p, q and r wrong. The call
order in `guest_impl.c` matters: with both q and r present, the unfixed adapter
traps out of bounds rather than returning a wrong value.
