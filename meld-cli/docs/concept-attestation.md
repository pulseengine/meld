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

Attestation integrity is a governed property of meld (system requirement
SYS-10): the record must faithfully describe the fusion, and the reproducible
mode must actually reproduce. See also the `provenance` topic for the
per-function mapping back to originating components.
