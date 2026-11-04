# #545 fixture: P3 component whose fusion produced an invalid module at exit 0

`empty-wait.wasm` is the first component of `test/async/empty-wait.wast` in the
WebAssembly component-model specification repository
(https://github.com/WebAssembly/component-model, commit 38db7ee), extracted with
wasm-tools 1.263. sha256 `bb30bc2f79447e64cdb0c3a195b55f0ee0212d9847776c2e0b981cd30471d5df`.

meld 0.66.0 fused it with `--memory multi` at exit 0 into a core module that
fails validation inside `<meld-adapter>`. It was one of 11 such components in a
504-component P3 corpus (#545). The test in
`meld-cli/tests/validate_default_545.rs` checks the invariant that holds before and
after the underlying adapter defect is fixed: if `meld fuse` exits 0, its output
validates.
