# Memory strategies — auto, multi, shared

Each input component brings its own linear memory. When meld fuses them it must
decide how those memories coexist in the output. `fuse --memory` selects the
strategy (issue #172):

- `auto` (default) — meld picks the sound single-memory form when it can:
  shared memory with address rebasing whenever no input module contains
  `memory.grow` and there are two or more memories to merge. The resulting
  single-memory module flows straight through `wasm-opt` → `synth` with no
  extra flags. When an input can grow memory, `auto` falls back to `multi`.

- `multi` — keep one linear memory per input component. The fused module is a
  multi-memory module; `wasm-opt` needs `--enable-multimemory` to consume it,
  and there is no single-address-space (MCU) lowering for it.

- `shared` — force one merged memory. Pair it with `--address-rebase` so each
  component's data lands at a distinct, non-overlapping offset. This is
  unsound if any input grows memory, because a grow would move data another
  component is still addressing at a fixed offset.

The single-memory (shared + rebase) form is the one that unlocks the MCU
single-address-space story; see the `address-rebasing` and `pack-rebase`
topics.
