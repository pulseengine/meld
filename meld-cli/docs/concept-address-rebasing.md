# Address rebasing — one memory, no collisions

When `--memory shared` merges several components into a single linear memory,
their data segments would otherwise all start at their original offsets and
overlap. Address rebasing (`--address-rebase`) relocates each component's data
to a distinct base within the merged memory and rewrites the component's
memory-referencing instructions — data-segment offsets, element-segment
offsets, and the pointer constants folded into `i32.const` / extended-const
initialisers — so every access lands at the component's new base.

This is the MCU single-address-space story: instead of one memory per
component, everything shares a flat address space, which is what a
microcontroller runtime and a native linker expect.

Rebasing is sound only when memory does not grow: a `memory.grow` would move a
component's region out from under fixed offsets another component is still
using. `--memory auto` never chooses shared + rebase; rebasing happens only
when you select `--memory shared` explicitly. Rebasing places each component at
its declared page extent; the compact used-extent variant is `--pack-rebase`
(see that topic).
