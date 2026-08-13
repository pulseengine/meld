# Adapters — Canonical-ABI cross-component seams

Two components that talk across an interface do not share a calling convention
for free: the Component Model's Canonical ABI defines how high-level values
(strings, lists, records, resources) are lowered into and lifted out of linear
memory at each boundary. When component A imports what component B exports,
meld synthesises an adapter — a small generated core function — that lifts the
caller's arguments and lowers them into the callee's ABI, and does the inverse
for results.

Adapters are where meld does the real cross-component work: string transcoding
between encodings, list and record marshalling, and resource-handle
translation through per-resource handle tables. When both sides share the
merged memory (a rebased single-memory fusion), same-memory transcoding can
avoid a copy; when encodings differ the adapter still transcodes.

Adapters are counted separately in `fuse --stats` (adapter functions), and in
DWARF `remap` mode the code meld generates is attributed to synthetic
`<meld-adapter>` source lines so a debugger does not mis-map it onto an input
component's source.
