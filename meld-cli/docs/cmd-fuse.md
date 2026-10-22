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
- `--stats`, `--validate`, `--preserve-names` — fusion statistics, wasmparser
  validation, name preservation.
- `--emit-import-map <PATH>` — a JSON import map of the fused module's function
  imports, for hosts that implement them (synth/kiln, a native WASI host for
  wasm2c output). The file is `{"version": 2, "imports": [...]}`; version 2
  (#513) only adds fields, and `index`, `kind`, `module` and `name` are as
  before. Per import:
  - `component` — the flattened component that owns it (the `N` of a `$N`
    name suffix). Under `--memory shared` identical lowers of several
    components merge into one import; the others are listed in
    `also_components`.
  - `memory` — `{"index": <fused memory>, "export": <its export name or null>}`:
    the memory the import's pointer arguments index.
  - `realloc` — `{"func": <fused function>, "export": <name or null>}`: the
    `cabi_realloc` to allocate list/string results with.
  - `encoding` — `utf8`, `utf16` or `latin1+utf16`, for string arguments.
  - `resource` — only on `[resource-new]` / `[resource-rep]` /
    `[resource-drop]` imports: `operation`, `resource` (type name),
    `interface`, `definer` (the importer defines the type), `dtor_export` (the
    `<interface>#[dtor]<resource>` export, or `null`; when it is `null`
    because several exports could match they are in `dtor_candidates`).

  All of this is resolved from the import's OWN source `canon lower`, not from
  a per-component default, so two components lowering the same WASI function
  (`write`, `write$1`) each name their own memory and allocator. Read each
  value three ways: `null` means the lower has no such option (the import
  cannot touch a memory / allocate; resource intrinsics are always `null`);
  an object with `index`/`func` is the answer; `{"unknown": "<reason>"}` means
  meld could not trace the lower, and a host must not treat it as `null` or
  guess. With `--component`, entries are joined to the output by their unique
  `(module, name)`.
