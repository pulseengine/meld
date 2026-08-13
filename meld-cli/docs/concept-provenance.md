# Provenance — mapping fused functions back to their component

Fusion collapses many components into one core module, which flattens every
component's function index space into a single one. The `component-provenance`
custom section (issue #192) records the inverse map: for each function index in
the fused module, which component it came from and its function index there.

Downstream consumers use it to project Component-Model invariants back onto
fused-module locations. `pulseengine/scry`, for example, reads it to attribute
a property or a finding in the fused binary to the original component and
function, rather than to an opaque merged index.

It is emitted by default; `fuse --no-component-provenance` disables it. The
overhead is roughly 120 bytes per fused function, so disabling it is a size
lever for artifacts that will never be analysed downstream. Provenance is
distinct from the attestation (which records the fusion event as a whole) and
from DWARF (which maps to source lines); it is the function-index-to-component
map specifically.
