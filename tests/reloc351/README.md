# meld#351 regression fixtures

`a.wasm` / `b.wasm` are the exact reproducing components from avrabe on
pulseengine/meld#351 (producers: Homebrew clang 22.1.4 + wit-component 0.245.1).
Each embeds a core module whose `reloc.CODE` offsets are **stale** relative to
the emitted minimal-LEB code (drift +2 per preceding memory-address reloc — the
LEB-relaxation signature; upstream pulseengine/wasm-tools#3).

Fusing them `--memory shared --address-rebase` used to leave `ptr-b`'s
`i32.const` data pointer un-rebased (returns 65536 instead of 196608): silent
cross-component aliasing. meld now hard-fails with `MisalignedReloc` (backstop)
rather than emit a wrong module.

`b.wasm` sha256: 481c36137ebe6b75b1699b757065cca4fb9cd8ae2b4f18ee00732f625b19d3a3
