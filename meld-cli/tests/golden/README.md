# Golden files

`import_map_stream_write_662.json` is the `--emit-import-map` output for
`meld-core/tests/fixtures/issue_662/stream_write_via_shim_wt1263.wat`. synth and
kiln read its key spellings, so `import_map_schema_692.rs` compares it byte for
byte (#692).

It still lists two `pulseengine:async` imports with `unknown` options. They are
dead (#693), and the file changes when #693 removes them.

Regenerate it only for an intended change:

    wasm-tools parse meld-core/tests/fixtures/issue_662/stream_write_via_shim_wt1263.wat -o in.wasm
    meld fuse in.wasm --memory multi --no-attestation --reproducible \
        --emit-import-map meld-cli/tests/golden/import_map_stream_write_662.json -o out.wasm

If a consumer would read the new map differently, bump the map's `version`
and say so in the release notes.
