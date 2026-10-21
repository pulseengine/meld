# meld fuse — fuse components into one core module

`meld fuse <inputs...> -o <output>` statically links two or more WebAssembly
components into a single core module (or, with `--component`, a P2 component).
Cross-component imports are resolved at build time; see the `fusion` topic.

Key flags:

- `-o, --output <PATH>` — output path (default `fused.wasm`).
- `--memory <auto|multi|shared>` — how the input memories coexist (default
  `auto`). See the `memory-strategies` topic.
- `--address-rebase` — relocate each component's data within one shared memory
  and rewrite its pointers. Valid only with `--memory shared`; not accepted
  with `auto`, which always selects `multi`. See `address-rebasing`.
- `--emit-manifest` — add the `meld.signature-manifest` section describing, per
  export, the WIT and core signatures, the flattened parameter count, and the
  memory / allocator / post-return a host must use. See `signature-manifest`.
- `--pack-rebase` — compact used-extent variant of `--address-rebase` for MCU
  targets; implies `--address-rebase`, requires `--memory shared`, and is sound
  only for components that address nothing above their last data segment. See
  `pack-rebase`.
- `--exports <all|world>` — which exports the fused core module keeps (default
  `all`: every export of every inner module). `world` keeps only the functions
  that implement the outer world of the input(s). Each world function is traced
  through its `canon lift` to a fused function (membership is never decided by
  a name or prefix) and exported under its **world name**,
  `<interface>#<function>`: when the merger named it `iface#f$1` because an
  internal function took `iface#f`, the world name is rebound to the world
  function and the internal one is dropped. Also kept: the memory and realloc
  of the kept lifts **and of every `canon lower` behind an import the module
  still has** (a realloc nothing exports is exported as
  `meld:realloc/<component>`, with or without `--emit-manifest`), `cabi_post_*`,
  the `[dtor]` exports of resources whose `new`/`rep`/`drop` are still
  imported, and the start function. `__data_end`, `__heap_base` and every other
  global or table export are dropped. Only the export list changes; function
  bodies stay, so a downstream tool can drop what becomes unreachable. A world
  function that cannot be traced to a fused function that some export carries
  is an error naming it, never silently dropped. With `--emit-manifest` the
  manifest lists only the world's functions. Not valid with `--component`,
  which already exports exactly the outer world. Recorded in the attestation
  when set.
- `--component` — emit a P2 component instead of a core module.
- `--dwarf <remap|strip|passthrough>` — debug-info handling (default `remap`).
- `--opaque-rep <iface.resource>` — treat a resource's representation as a
  `u32` per component rather than the shared-by-name boxed default; repeatable.
- `--no-attestation` / `--reproducible` — see the `attestation` topic.
- `--no-component-provenance` — drop the per-function origin map (`provenance`).
- `--stats`, `--validate`, `--preserve-names`, `--emit-import-map <PATH>` —
  fusion statistics, wasmparser validation, name preservation, and a JSON
  import map for synth/kiln integration.
