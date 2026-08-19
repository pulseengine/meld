# Build profiles — ecosystem and safety

meld has two identities, and both are first-class: the generic Component-Model
fuser anyone can use, and a tool you can put in a functional-safety toolchain.
`--profile` says which one this build is.

The profiles do **not** fuse differently. A build that succeeds under
`--profile safety` produces byte-identical output to the same explicit invocation
under `--profile ecosystem`. What changes is **how much meld is allowed to decide
for you**.

## `--profile ecosystem` (default)

Convenience defaults apply. Where a property is unset, meld picks a sensible,
sound value and tells you what it picked. `--memory auto` selects a memory
strategy for you; advisory checks warn.

## `--profile safety`

Every safety-relevant property must be **stated**, not inferred. Inferring one is
a hard error instead of a warning.

Enforced today:

- **The memory strategy must be explicit.** `--memory auto` is refused. The
  memory strategy selects the inter-component isolation model — one shared
  address space, or one memory per component — which decides whether a fault in
  one component can reach another component's state. That is not a decision a
  build should inherit silently. Pass `--memory multi` (isolation preserved) or
  `--memory shared` (single address space; add `--address-rebase`, and build
  every input with `--emit-relocs`).

The reasoning is the same one behind meld's other loud failures: for a property
that changes what the artifact *guarantees*, a wrong-but-plausible default is
worse than a stopped build. You can always state the value you want — the profile
only insists that you state it.

## Why a profile rather than "strict when attested"

Attestation is on by default, and so is `--memory auto`. Enforcing on
"attested build" would therefore fail the ordinary `meld fuse a.wasm b.wasm`
invocation, which would break the ecosystem identity to serve the safety one.
The profile is the explicit signal that separates them, so neither identity is
compromised.
