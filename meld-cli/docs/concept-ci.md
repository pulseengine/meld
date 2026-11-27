# Calling meld in CI — pinned, reproducible, then run

Fusion in CI is a separate step from the build that produces the components
and the runtime that runs the result. It should give the same bytes on every
runner, come from a meld whose identity you can name, and leave an artifact
you can check later. Three things get you there: pin meld, fuse with
`--reproducible`, and check that two fusions agree.

## 1. Pin meld through varve

Take meld from a varve layer rather than from whatever is on `PATH`. A layer
is a signed, dated set of tool versions; the project pins one in `varve.toml`,
and changing it is a reviewed edit:

```toml
# varve.toml
manifest-version = 1

[toolchain]
realm   = "covalent"      # or "pulseengine"; the realm names the trust root
channel = "rolling"
layer   = "2026.11.16"
```

Pick a layer that carries the meld and kiln versions you need; `varve
inspect` lists every tool in the pinned layer with its version, and `varve
outdated` lists newer layers. Commit `varve-realms.toml` next to it (it ships as an asset of every varve
release), then in the job:

```sh
varve install          # fetch the layer and verify it against the realm's root
varve shim install     # put the layer's tools on PATH
varve which meld       # the binary that runs, and the layer + manifest digest
meld --version
```

Record the `varve which meld` line with the job's output: the layer name and
manifest digest answer "which meld produced this?" later. On a self-hosted
runner, give each job its own `VARVE_ROOT` (e.g. under `$RUNNER_TEMP`);
a shared `~/.varve` carries another repository's anti-rollback mark into your
job.

Without varve, download a release archive and verify it as the README's
"Verifying a Release" section shows (cosign-signed `SHA256SUMS.txt`, SLSA
provenance), and record the tag.

## 2. Fuse with `--reproducible`

```sh
meld fuse --reproducible --memory multi -o fused.wasm app.wasm
```

`--reproducible` derives the attestation id from the output's content and
takes the timestamp from `SOURCE_DATE_EPOCH` (epoch 0 when unset) instead of a
random UUID and the wall clock. It also replaces each attested input name with
`component-0`, `component-1`, ..., since input paths differ between checkouts;
the inputs stay pinned by their sha256. Without the flag, two runs differ in
the attestation only.

Name the memory strategy in the job. The default, `--memory auto`, always
resolves to multi-memory; writing `--memory multi` states that in the job's
own text. A single-address-space build is a separate, explicit choice. See
`meld docs memory-strategies`.

## 3. Check that two fusions agree

```sh
meld fuse --reproducible --memory multi -o a.wasm app.wasm
meld fuse --reproducible --memory multi -o b.wasm app.wasm
cmp a.wasm b.wasm
```

`cmp` exits non-zero on any byte difference. meld's own CI holds this across
processes and across 32- and 64-bit hosts (native meld and `meld.wasm`
produce identical bytes).

## Checking the artifact later

The output carries a `wsc.transformation.attestation` section: meld's
version, the inputs and their sha256, the parameters, and `output.hash`.
From releases after 0.71.0, `output.hash` covers every byte except that
section, so a wsc that checks the binding (sigil#395) accepts the artifact
with `wsc verify-chain -i fused.wasm` and refuses it if any other byte,
`component-provenance` included, changed after fusion. See
`meld docs attestation`.

## meld as a component

Releases after 0.71.0 also attach `meld-<tag>-wasm32-wasip2.wasm`, listed in
the signed `SHA256SUMS.txt`. A runner with a WASI 0.2 host and no native meld
can run it; it produces the same bytes as native meld:

```sh
wasmtime run -S cli-exit-with-code=y --dir .::/w meld.wasm \
  fuse --reproducible --memory multi -o /w/fused.wasm /w/app.wasm
```

Exit codes are the same as native meld: 0 on success, 2 for a usage error,
1 for a failed fusion.

## Then run it on kiln

kiln 0.9.0 and later runs a meld-fused wasm32-wasip2 command component built
by Rust 1.100; older kiln refuses it at the `wasi:cli/exit@0.2.12` import
(kiln v0.9.0 release notes). Take kiln from the same varve layer, and check
that the layer carries 0.9.0 or later: `varve inspect` lists each tool's
version (layer 2026.11.16 carries kiln 0.7.3).

```sh
varve which kiln
kiln --version
kiln --wasi --component --dir . fused.wasm [guest args...]
```

kiln's options go before the module and everything after it is the guest's
argv, as with `wasmtime run`. For a `--memory multi` module whose host
imports pass pointers, `meld fuse --emit-import-map imports.json` writes the
memory and allocator of each import, and `kiln --import-map imports.json`
reads it.

A differential is the cheapest check that the fused artifact behaves like the
original: run the same invocations on the native build, or on the unfused
component under wasmtime, and on the fused module under kiln, and compare
stdout and exit status.
