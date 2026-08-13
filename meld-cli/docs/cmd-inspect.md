# meld inspect — examine a WebAssembly component

`meld inspect <input>` reads a `.wasm` file and reports what it is. It checks
the magic number and version to distinguish a WebAssembly Component (P2) from a
plain core module, and prints the file size. For a component it parses the
structure and reports the number of core modules, imports, and exports.

Flags:

- `--interfaces` — list the component's imports and exports by name (exports
  also show their kind). Useful for seeing the seams meld would have to resolve
  before fusing.
- `--types` — show per-core-module detail: counts of types, functions,
  imports, exports, memories, tables, and globals.

If the input is a core module rather than a component, `inspect` says so and
notes that `wasm-tools component new` can convert it. `inspect` is read-only;
it never modifies the input and is the quick way to sanity-check an artifact
before or after a `fuse`.
