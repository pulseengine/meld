---
id: ADR-6
type: design-question
title: Address relocation for the shared-memory fusion mode
status: resolved
gating-fixtures:
  - rebasing_end_to_end::reloc_326_static_addr_rebased_shared
  - rebasing_end_to_end::reloc_326_data_pointer_rebased_shared
design-paths:
  - path-D — relocatable inputs; meld consumes `linking` + `reloc.CODE`/`reloc.DATA` and rebases every `R_WASM_MEMORY_ADDR_*` site by the module's shared-memory base (chosen)
  - path-E — PIC / dylink inputs; meld assigns each module a window and supplies `__memory_base` (rejected — `wasm-tools component new` refuses a core that imports memory/base globals)
  - path-F — refuse; keep `--memory shared` a hard error on non-relocatable inputs, force multi-memory (retained as the fallback when path-D's metadata is absent)
---

# ADR-6 — Address relocation for the shared-memory fusion mode

## Context

ADR-4 chose **multi-memory** as the committed isolation model and retained
**single shared memory** (`meld fuse --memory shared`) as a *secondary* mode
for the single-address-space MCU lowering (gale Pixhawk / gust:os, meld#298,
meld#299). meld#326 proved that secondary mode is **unsound**: when meld places
component *k*'s linear memory at base `Bₖ` in the shared space, component *k*'s
code still computes addresses as if its memory started at 0. The rewriter today
rebases only the *static* memarg offset and bulk-memory operands — never the
*dynamic* address operand of ordinary loads/stores, nor absolute `i32.const`
address literals. So any component that writes through a computed pointer
silently collides with a neighbour.

gale supplied two runtime datapoints (meld#326, qemu-cortex-m3):

1. **`list<u8>` buffer content** — `log.line(b"gust:os up\n")` delivers 11 bytes
   but the first 7 read as 0; the canonical-ABI `cabi_realloc` `memcpy` source
   address is not rebased.
2. **`static mut` persistence** — `DONE[0] = true` is written but the next
   `poll` reads it back `false`; a store to a `static mut` at an absolute
   `i32.const` address lands in the wrong window. This proves the defect is not
   buffer-specific — it corrupts *any* provider that writes into fused shared
   memory. Only stateless-read providers (gust:os/time) escape.

This is the LS-M-11 hazard. The gate shipped in v0.38.0 (Auto → multi-memory)
mitigates it by *avoiding* shared mode; ADR-6 decides how to make shared mode
*correct* when a caller genuinely needs the single address space.

## The design space and the spike

A finished non-PIC, reloc-stripped module cannot be relocated: the information
saying "*this* `i32.const` is an address" was destroyed by `wasm-ld` at final
link, and no heuristic recovers it soundly (an address is indistinguishable
from an integer). This matches the whole ecosystem — every tool that shares one
linear memory requires **either** PIC inputs (Emscripten MAIN/SIDE_MODULE,
`wasm-tools component link`, `dylink.0`) **or** relocation metadata (`wasm-ld`
on object files). So the real question is an *input contract*, and it forks D/E/F.

A spike (`/tmp/spike326`, a gale-shaped `#![no_std]` cdylib reproducing both
datapoints) settled it empirically:

- **path-E (PIC) is architecturally excluded.** `wasm-tools component new`
  refuses a PIC/dylink core: *"failed to resolve import `env::__memory_base` …
  module is only allowed to import functions."* A Component-Model core may
  import only functions; a dylink library imports `memory`/`__memory_base`/
  `__table_base` as globals. A PIC core therefore can never become a component.
- **path-D (relocatable) survives.** A relocatable core (`--emit=obj` →
  `wasm-ld -r`, carrying `linking` v2 + `reloc.CODE`) passes `component new`
  **byte-for-byte** — the reloc entries (`MemoryAddrSleb`/`MemoryAddrLeb`, and
  `_I32` in `reloc.DATA` for initialised data) reach meld intact.
- **meld already preserves this metadata.** meld 0.39.0 copies both inputs'
  `linking` + `reloc.CODE` verbatim through fusion; it simply does not *consume*
  them, so the offsets go stale against the merged code section. The fix is
  *consume + apply*, not *acquire*.

## Decision — path-D (relocatable), with path-F as the fallback

meld's sound `--memory shared` input contract is **relocatable inputs**. meld
consumes `linking` + `reloc.CODE`/`reloc.DATA`, translates each relocation site
through the rewriter's existing `offset_map` (the same `AddressRemap` seam the
#331 DWARF `.debug_line` fix uses to locate code offsets in the rewritten
body), adds the module's `memory_base` to every `R_WASM_MEMORY_ADDR_SLEB`/
`_LEB`/`_I32` operand, and strips the consumed relocs. When an input lacks the
metadata, `--memory shared` stays a hard error (path-F) rather than silently
corrupting — never a plausible-but-wrong output (LS-D-1 discipline).

path-E is **rejected** (component pipeline cannot carry PIC). The producer cost
of path-D is a single build flag: **`cargo rustc … -- -C link-arg=--emit-relocs`**
keeps `reloc.CODE`/`reloc.DATA` in the *final linked* module — a valid,
self-contained core (table + memory defined, no dangling imports) that also
carries `linking` v2 + `reloc.*`. This is strictly better than the `--emit=obj`
→ `wasm-ld -r` route the spike used: a relocatable *object* is under-linked and
`wasm-tools component new` rejects it (dangling `env::__indirect_function_table`),
whereas `--emit-relocs` yields a linked module `component new` accepts, importing
neither `__memory_base` nor `memory` as globals (so it stays inside the no-PIC
contract). Verified gale-side across all six gust:os cores and through
`wac plug` — the composite carries one `reloc.CODE` + `linking` per inner core,
so every core's metadata reaches meld unstripped (gale#168, RESOLVED gale-side).

Locus of fix: **hybrid** — meld consumes; the producer must emit relocatable
cores. Oracle: the gating fixtures above, derived from the spike, reproducing
both gale datapoints under a fused shared memory.

## References

- meld#326 (corruption + the two gale datapoints + spike result)
- meld#334 (companion: unify `__stack_pointer` globals + DCE the dead trampoline)
- meld#298 / meld#299 (the MCU-lowering cluster shared mode serves)
- gale#168 (producer-side relocatable build helper)
- WebAssembly/tool-conventions `Linking.md` (`linking` v2, `reloc.*`, R_WASM_MEMORY_ADDR_*)
- WebAssembly/tool-conventions `DynamicLinking.md` (PIC ABI — why path-E can't be a component)
- ADR-4 (parent isolation model; shared is its retained secondary mode)
- LS-M-11 (the hazard this makes correct); SR-37 (the v0.38.0 gate mitigation)
