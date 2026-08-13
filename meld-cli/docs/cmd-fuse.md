# meld fuse — fuse components into one core module

`meld fuse <inputs...> -o <output>` statically links two or more WebAssembly
components into a single core module (or, with `--component`, a P2 component).
Cross-component imports are resolved at build time; see the `fusion` topic.

Key flags:

- `-o, --output <PATH>` — output path (default `fused.wasm`).
- `--memory <auto|multi|shared>` — how the input memories coexist (default
  `auto`). See the `memory-strategies` topic.
- `--address-rebase` — relocate each component's data within one shared memory
  and rewrite its pointers. Valid only with `--memory shared`; `auto` decides
  it itself. See `address-rebasing`.
- `--pack-rebase` — compact used-extent variant of `--address-rebase` for MCU
  targets; implies `--address-rebase`, requires `--memory shared`, and is sound
  only for components that address nothing above their last data segment. See
  `pack-rebase`.
- `--component` — emit a P2 component instead of a core module.
- `--dwarf <remap|strip|passthrough>` — debug-info handling (default `remap`).
- `--opaque-rep <iface.resource>` — treat a resource's representation as a
  `u32` per component rather than the shared-by-name boxed default; repeatable.
- `--no-attestation` / `--reproducible` — see the `attestation` topic.
- `--no-component-provenance` — drop the per-function origin map (`provenance`).
- `--stats`, `--validate`, `--preserve-names`, `--emit-import-map <PATH>` —
  fusion statistics, wasmparser validation, name preservation, and a JSON
  import map for synth/kiln integration.
