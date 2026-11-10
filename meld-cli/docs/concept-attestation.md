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

This holds for the default build, which is what releases ship, and for builds with the
optional `attestation` cargo feature. That path records the fusion parameters through
`wsc-attestation`, whose parameter map is a `HashMap`. Before meld 0.68 its order
changed from run to run, so two such builds of the same inputs had different digests.
meld now writes those keys in sorted order.

The two builds write different records, so their digests are not comparable with each
other. A digest you produce with `--all-features` will not match one this project
published, and that does not mean the artifact was tampered with. Compare like with like.

Under a varve shim, the `tool` object also names the toolchain layer meld ran from:
`toolchain` (from `VARVE_LAYER`) and `toolchain_manifest_digest` (from
`VARVE_LAYER_MANIFEST_DIGEST`). With them, the toolchain that produced the artifact can be
identified from the artifact alone. `--reproducible` leaves both out, so the reproducible
bytes do not depend on the environment.

Attestation integrity is a governed property of meld (system requirement
SYS-10): the record must faithfully describe the fusion, and the reproducible
mode must actually reproduce. See also the `provenance` topic for the
per-function mapping back to originating components.
