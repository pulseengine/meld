# Share-stack — one shadow stack for all providers

`--share-stack` closes the last MCU-fit gap after `--pack-rebase`. Even packed,
each fused provider still carries its own shadow stack — the `[0, __stack_pointer)`
region at the bottom of its extent — reserved but used by only one provider at a
time. Three drivers reserve three stacks; on an 8 KiB part that duplication is
the difference between fitting and not.

`--share-stack` reserves a single shadow-stack region sized to the largest
provider's stack (`max` of the per-provider `__stack_pointer` inits) at the
bottom of the fused memory, then packs each provider's data directly above it and
coalesces every `__stack_pointer` onto one shared global. The `(N-1)` duplicated
stacks are reclaimed.

It builds on `--pack-rebase` (and so implies `--address-rebase` and requires
`--memory shared`). meld refuses — loudly, never silently — unless every provider:

- exposes a `__stack_pointer` marker (a mutable `i32` global with a constant
  init, named in the export table or the `name` section),
- exposes a `__heap_base` marker (the `--pack-rebase` precondition),
- is **stack-first**: every data segment sits at or above its stack pointer, so
  removing the `[0, sp)` stack region never cuts into data.

The default `wasm-ld` layout puts the shadow stack *between* the data and
`__heap_base`, which the stack-first gate rejects; build the inputs with
`-Wl,--stack-first` alongside `--emit-relocs`. `--emit-relocs` also exports
`__heap_base` as an immutable global (verified in the rustc/wasm-ld toolchain by
the falcon suppliers), so a separate `-Wl,--export=__heap_base` is normally
unnecessary — add it only if your toolchain does not export the marker.

## The envelope meld cannot check

One shared region sized to the *largest* stack is sound only when at most one
provider's stack is live at a time. That holds when the providers are
non-reentrant, single-threaded, mutually-non-calling, and one-live-at-a-time — a
cross-provider call chain would need the *sum* of the participants' stack use,
not the max. No provider may hold a baked-in constant address into the `[0, sp)`
region, and no interrupt or signal handler may re-enter a provider. meld enforces
the structural preconditions; this behavioural envelope is the caller's to
guarantee. Within it, the single coalesced stack keeps even nested calls coherent
— the residual risk is overflow of the shared region, not corruption of a
neighbour's frames.
