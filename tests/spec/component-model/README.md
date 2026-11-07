# Vendored Component Model reference tests (#562)

`test/` is `WebAssembly/component-model`'s `test/` directory, copied byte for
byte at the commit in `COMMIT`. `LICENSE` and `LICENSE-APACHE` are upstream's
(Apache-2.0). `MODULE.bazel` pins the same commit for `component_model_spec`.
`meld-core/tests/cm_wast_ratchet.rs` checks both pins and every file against
`SHA256SUMS`.

That test fuses every component the WASTs define and compares meld's outcome
with `../component-model-fuse-baseline.tsv`. With `MELD_CM_WAST_OUT=<dir>` it
also writes each input and fused module plus `manifest.json`, which kiln's
runner (kiln SR-93) uses to execute the WAST assertions on fused output.

## Updating

1. Download the new commit's `test/` directory into `test/`, replacing it.
2. Write the commit to `COMMIT` and to `MODULE.bazel`.
3. `cd tests/spec/component-model && find test -type f | LC_ALL=C sort | xargs shasum -a 256 > SHA256SUMS`
4. `MELD_BLESS=1 cargo test -p meld-core --test cm_wast_ratchet`, then review
   the baseline diff line by line: every newly refused or newly invalid
   component is a finding, not a formality.
5. Update the WAST count in `vendored_suite_matches_its_checksums`.
