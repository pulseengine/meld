# Memory strategies — auto, multi, shared

Each input component brings its own linear memory. When meld fuses them it must
decide how those memories coexist in the output. `fuse --memory` selects the
strategy (issue #172):

- `auto` (default) — always selects `multi`, the strategy that is sound for
  every input. It never selects shared memory or address rebasing on its own.
  (Until #326 it chose shared + rebase for inputs without `memory.grow`; that
  was unsound for inputs whose pointers it could not relocate, and was
  removed.)

- `multi` — keep one linear memory per input component. The fused module is a
  multi-memory module; `wasm-opt` needs `--enable-multimemory` to consume it,
  and there is no single-address-space (MCU) lowering for it.

- `shared` — force one merged memory. Pair it with `--address-rebase` so each
  component's data lands at a distinct, non-overlapping offset. This is
  unsound if any input grows memory, because a grow would move data another
  component is still addressing at a fixed offset.

The single-memory (shared + rebase) form is the one that unlocks the MCU
single-address-space story. It is reached only by choosing it explicitly —
`--memory shared` with `--address-rebase` or `--pack-rebase` — never through
`auto`. See the `address-rebasing` and `pack-rebase` topics.
