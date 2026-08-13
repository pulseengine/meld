# Pack-rebase — the compact used-extent envelope

`--pack-rebase` is a compact variant of address rebasing for single-address-
space (MCU) targets. Plain `--address-rebase` reserves each component's full
declared page count (a multiple of 64 KiB). `--pack-rebase` instead places each
component at its actual used data extent — the end of its last data segment,
rounded up to a 16-byte alignment — and sizes the merged memory to the packed
total. Three thin drivers that would each claim a 64 KiB page fit in a few KiB.

It implies `--address-rebase` and requires `--memory shared`. It is OPT-IN
because it is sound only under a strict precondition: the component must
reference no address above its last data segment. That means no separately-
addressed `.bss`, no heap, and no computed pointers reaching past the packed
extent. A component that has any of those must use `--address-rebase` (full
page extent) instead — packing it would place another component's data inside
the region it silently addresses beyond its segments.

The safe envelope is the "used extent": everything the component actually
touches lies at or below its last data segment. Pack within that envelope and
the layout is dense and sound; exceed it and it is neither.
