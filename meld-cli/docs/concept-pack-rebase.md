# Pack-rebase — the compact used-extent envelope

`--pack-rebase` is a compact variant of address rebasing for single-address-
space (MCU) targets. Plain `--address-rebase` reserves each component's full
declared page count (a multiple of 64 KiB). `--pack-rebase` instead places each
component at its actual used data extent — the end of its last data segment,
plus a 7-byte unwritten guard (#479), rounded up to a 16-byte alignment — and
sizes the merged memory to the packed total. The guard keeps an access of up to
8 bytes that starts inside one component's data from reaching its neighbour, so
width-over-approximating validators (synth VCR-VER-003) stay sound on the packed
layout; it costs 7 to 22 bytes per component. Three thin drivers that would each claim a 64 KiB page fit in a few KiB.

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

## Declaring the packed size in bytes — `--memory-page-size 1`

By default the packed total is rounded up to whole 64 KiB pages when the memory
is declared, so 7.4 KiB of packed data is declared as 64 KiB or 128 KiB.
`--memory-page-size 1` declares each packed memory (one per `--domain`, or the
single shared memory) with the custom-page-sizes proposal's `(pagesize 1)` and
`minimum == maximum ==` the packed total in bytes: the same value the placements
report, including the 7-byte guard and the 16-byte alignment. The default,
`65536`, leaves the output unchanged.

It is OPT-IN because a module that declares `(pagesize 1)` does not load in a
runtime that has not enabled custom-page-sizes (wasmtime: `wasm_custom_page_sizes`).
Any other value is a usage error (exit 2), as is using the flag without
`--pack-rebase` (or `--share-stack`) or with `--component`, whose wrapper
re-declares the memory in pages. An imported shared memory is refused: the page
size of an import must match what the importer provides.

`memory.size` and `memory.grow` count pages, so on a byte-sized memory they would
silently change meaning. Fusion fails, naming the function, if the emitted module
contains either on a byte-sized memory. It also fails if an active data segment
of such a memory has a non-constant offset or ends past the declared extent. The
page size is recorded in the attestation whenever it is not the default, and
`--explain` lists each memory with its unit.
