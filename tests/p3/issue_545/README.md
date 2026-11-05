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

## Fixture history: empty-wait.wasm is current again

- **First cut of #558 (PR #559, 00ecdaa).** meld refused `empty-wait.wasm`
  before validation ran: its `future.read` was caught by the then over-broad
  #558 refusal. A refusal still satisfies the invariant, but the potency check
  (`--no-validate` writes an invalid module) no longer bit, so the tests moved
  to `reentrance-m6.wasm`: module 6 of `test/async/reentrance.wast` from the
  same specification commit (38db7ee), extracted with wasm-tools 1.263, sha256
  `be6e806bfb32c17a1ba827dcce660f5ee75ab9abd8077296f2a079d16e6c2f87`.
- **#558 narrowed (6cb3e63).** The refusal was limited to the shim's internal
  name, and `empty-wait.wasm` again fuses with `--no-validate` into a module
  that fails validation inside `<meld-adapter>`.
- **#548 by the async option (#560).** `reentrance-m6.wasm` calls a sibling
  component with an async lowering, so from #560 on it is refused as a #548 edge
  before validation runs. The tests are back on `empty-wait.wasm`.
  `reentrance-m6.wasm` stays for provenance.
