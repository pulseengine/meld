# Static fusion — what meld does

Meld fuses several WebAssembly components into a single core module ahead of
time, so there is no runtime component linking. Where a host would normally
instantiate each component and wire imports to exports at load time, meld
resolves those cross-component edges statically: it merges the index spaces
(types, functions, tables, globals, memories), internalises the imports that
one input satisfies for another, and synthesises Canonical-ABI adapters where
two components meet across an interface boundary.

The result is one `.wasm` that a runtime can instantiate directly, with the
cross-component calls already turned into ordinary in-module calls. This is
what makes meld suitable for constrained targets (MCUs) and for cold-start-
sensitive deployments: the linking cost is paid once, at build time, and the
fused module carries an attestation describing how it was produced.

Fusion is deterministic and fail-fast: identical inputs and flags yield the
same output, and an unresolvable seam is an error, never a silent stub.
