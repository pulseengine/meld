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

## reentrance-m6.wasm (current fixture, since #558)

From #558 on, meld refuses `empty-wait.wasm` before validation runs: it wires a
`future.read` that meld cannot name yet. A refusal still satisfies the
invariant, but the potency check (`--no-validate` writes an invalid module)
would no longer bite. So the tests now use `reentrance-m6.wasm`, module 6 of
`test/async/reentrance.wast` from the same specification commit (38db7ee),
extracted with wasm-tools 1.263, sha256
`be6e806bfb32c17a1ba827dcce660f5ee75ab9abd8077296f2a079d16e6c2f87`. It is
another of the 11 #545 components. It uses no stream or future read/write, and
with `--no-validate` it still fuses into a module that fails validation
("func 13 failed to validate"). `empty-wait.wasm` stays for provenance.
