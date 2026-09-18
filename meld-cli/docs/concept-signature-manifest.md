# Signature manifest — invoking a fused export

Fusing a component to a core module drops the WIT type information. A runtime
that knows the component's shape at build time does not care: it generates
bindings from the WIT world. A runtime that does **not** — a generic invoker
given a `.wasm` and an export name — is left with a core signature, and a core
signature does not say enough.

`meld fuse --emit-manifest` adds a `meld.signature-manifest` custom section: a
JSON description, per exported lifted function, of what it takes and what a host
must call to invoke it.

## Why a core signature is not enough

These two exports have the **same** core type:

```wit
f: func(x: u32) -> u32                       // (i32) -> (i32)
tick: func(s: state, sp: setpoint) -> out    // (i32) -> (i32)
```

In the first, the `i32` is the value. In the second — 18 floats flattened, over
the canonical ABI's limit of 16 — it is a pointer to an argument area the
*callee's* allocator must provide. Nothing in the core type distinguishes them,
and the Canonical ABI passes garbage rather than erroring: a host that guesses
wrong gets a clean-looking run and a wrong answer.

## What each entry says

| field | meaning |
|---|---|
| `export` | the name the module exports, exactly as emitted |
| `wit` | the WIT signature, rendered structurally |
| `core` | the core signature, **read back from the emitted bytes** |
| `flat_param_count` | flattened parameter count; above 16 the arguments travel through a pointer |
| `needs` | `memory` and `realloc`, per component-model#378's `Needs` |
| `memory`, `realloc`, `post_return` | the exports a host must use, resolved through fusion |
| `return_area` | size, alignment and top-level `(offset, field, size)` layout |

`wit` and `core` come from different places on purpose: `wit` from the
component's types, `core` from the bytes meld emitted. A consumer can therefore
cross-check its own lowering against `core` instead of trusting meld. Derived
from one source they would agree by construction and the field would be
decoration.

## What it refuses to do

**It never guesses.** An export whose types do not fully resolve is listed under
`omitted` with a reason instead of being described with fallback sizes. A
fallback is how a `use`d record was once silently sized at four bytes.

**It never names a plausible substitute.** `realloc` is resolved through fusion
to the allocator that export's own lift names — never matched by a likely
name. Components keep their own allocators through fusion, and in shared memory
they all want the name `cabi_realloc`, so meld exports the ones an export needs
under a distinct name (`meld:realloc/<n>`) and the manifest states it.

If an allocator still cannot be resolved, the entry says `"realloc": null`
while `needs.realloc` stays `true`. That pair is a contradiction on purpose:
the export cannot be invoked as the ABI requires, and a host should refuse
rather than call some other exported allocator that happens to look right.

## Reading it

```bash
meld fuse a.wasm b.wasm --emit-manifest -o fused.wasm
wasm-tools objdump fused.wasm | grep signature-manifest
```

The section is opt-in because it adds bytes, which matters for
microcontroller-sized artifacts.

Status: the format is version `1` and settling with its consumers (#400). A
reader that does not recognise the major version should refuse the manifest
rather than parse it partially.

## Keeping allocators alive

An export whose arguments exceed 16 flattened values, or whose parameters carry
a string or list, is staged through the callee's allocator. meld therefore keeps
that allocator exported, which means it — and its `memory.grow` — stay reachable
for a downstream DCE pass. A build that wants the smallest possible artifact and
does not need to invoke such exports gets the allocator dropped as before.
