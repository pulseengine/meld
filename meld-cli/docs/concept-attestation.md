# Attestation — a signed record of how the artifact was fused

By default meld embeds an attestation in the fused module: a record of the
fusion event — which components went in and how they were combined — carried in
the output so a downstream consumer can tell where the artifact came from. It
is on by default; `fuse --no-attestation` omits it.

For supply-chain reproducibility, `fuse --reproducible` (issue #325) makes the
artifact byte-for-byte deterministic: the attestation id is derived from the
output content instead of a random UUID, and the timestamp is taken from
`SOURCE_DATE_EPOCH` (default epoch 0) instead of the wall clock. Identical
inputs and flags then yield an identical sha256, so a rebuild can be checked
against a published digest.

The record is written in the schema of `wsc-attestation` 0.13, the attestation types of
sigil's `wsc`, with `transformation_type: "fusion"` (from v0.73.0, #709; earlier releases
wrote meld's own schema). `tool.parameters` holds every fusion parameter (`profile`,
`memory_strategy`, `reproducible`, `share_stack`, `domains`, ...); `metadata` holds the
fusion statistics, the per-boundary and per-placement records, and `metadata.inputs`, one
entry per input in input order with its `module_count`. wsc reads the record with its own
types, and `wsc verify-chain` checks `output.hash` against the module.

The parameters and metadata are maps, and meld writes their keys in sorted order, so
`--reproducible` stays byte-stable. A build of meld-core without its default `attestation`
cargo feature writes meld's own schema with the same fields; its digests are not
comparable with those of the default build.

Under a varve shim, the `tool` object also names the toolchain layer meld ran from:
`toolchain` (from `VARVE_LAYER`) and `toolchain_manifest_digest` (from
`VARVE_LAYER_MANIFEST_DIGEST`). With them, the toolchain that produced the artifact can be
identified from the artifact alone. `--reproducible` leaves both out, so the reproducible
bytes do not depend on the environment.

Attestation integrity is a governed property of meld (system requirement
SYS-10): the record must faithfully describe the fusion, and the reproducible
mode must actually reproduce. See also the `provenance` topic for the
per-function mapping back to originating components.
