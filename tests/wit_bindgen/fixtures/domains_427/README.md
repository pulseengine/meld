# domains_427 — two tenants and a supervisor, so grouping is observable

Extends gale's handle-carrying fixture (`gale#412`,
`benches/gust/fixtures/meld-domains/`) with a **second tenant on the same
interface**. That is the whole point: with two callers of one provider, the
only difference between the two call sites is **which domain they land in**, so
the lowering of an identical call becomes a function of the grouping alone.

`provider` and `consumer` are gale's, unmodified. `consumer2` is `consumer`
with its package, world and export renamed — same imports, same calls.

## What the boundary carries

`gale:capfix/caps` has `resource task` (constructor, `tick` on an owned handle,
`peek` as a borrow) plus a scalar `now`, so each tenant→provider boundary
carries `own<>`, `borrow<>` and a scalar together. Four boundaries per tenant,
eight in total.

## The gap this fixture makes visible (measured, meld 0.58.3)

| invocation | boundaries | memories | |
|---|---|---|---|
| `--memory multi` | 8 memory-copy | 3 | isolated, but **unfittable** |
| `--memory shared --address-rebase` | 8 direct, 8 wired with nothing interposed | 1 | fits, but **unisolated** |
| **with domains (SR-86)** | **4 direct + 4 memory-copy** | **2** | the shape an MCU privilege boundary needs |

Today `fuse` takes one global `--memory`, so only the first two rows are
reachable: every component shares one memory, or every component keeps its own.
A node with a tenant and a supervisor is therefore either unfittable or
unisolated — which is `meld#427`.

The third row is the requirement. Grouping `consumer` with `provider` and
leaving `consumer2` outside must leave `consumer`'s four boundaries `direct`
and make `consumer2`'s four `memory-copy`, from the same interface and the same
generated call sites.

## Why a second tenant rather than a second provider

Handle tables are keyed per component and `HandleTableInfo` carries
`memory_idx` + `table_base_addr` — a handle table is a region in linear memory
reached through `memory_index_map`. Two components sharing a domain therefore
have mutually addressable handle tables **by construction**. That makes
unforgeability a property of the domain boundary rather than of the handle, and
it is only observable when two components share a domain while a third does
not. One provider and one consumer cannot show it.

## Building

`./build.sh` — needs `cargo` with the `wasm32-unknown-unknown` target and
`wasm-tools`. `-C link-arg=--emit-relocs` on the final link is required: without
relocation metadata meld refuses the shared path outright rather than rebasing
unsafely, which is itself part of what gale's original fixture demonstrates.

The `.comp.wasm` outputs are **committed** (SR-85, #405): a fixture a test reads
but nobody commits makes the test pass without running.
