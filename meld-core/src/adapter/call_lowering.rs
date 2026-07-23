//! Per-boundary call-lowering seam (ADR-7 path-H, increment 2).
//!
//! When one fused component calls another, meld synthesizes a trampoline whose
//! shape depends on what the boundary crosses. This module is the single home
//! for that **decision** — *which* [`AdapterClass`] lowers the call — separated
//! from the body generators that emit each class's instructions.
//!
//! The boundary classes:
//!
//! - **[`AdapterClass::Direct`]** — same memory, same string encoding: a thin
//!   call shim. When it carries no resource conversions and no post-return it is
//!   a *pure identity trampoline* eligible for #304 inlining.
//! - **[`AdapterClass::MemoryCopy`]** — cross-memory, same encoding: a
//!   lower → `cabi_realloc` → `memory.copy` → lift chain.
//! - **[`AdapterClass::Transcode`]** — cross-memory *and* an encoding mismatch:
//!   the memory-copy chain with a UTF-8/UTF-16/Latin-1 transcode loop fused in.
//!
//! ([`AdapterClass::Async`] boundaries are dispatched *before* this seam is
//! reached — see the async branch in `FactStyleGenerator::generate` — so they
//! never flow through here.)
//!
//! ## Why the class *and* the inline decision live together
//!
//! `#304` inline-eligibility is *not* an independent flag: an adapter may be
//! inlined only when its class is `Direct` **and** it carries no resource
//! rep/new conversions **and** no post-return. That guard has to stay a superset
//! of `generate_direct_adapter`'s pure-trampoline branch (the "#304 INVARIANT"
//! note there) — the two are coupled and must move together. Computing both the
//! class and the inline decision in one place ([`resolve_call_lowering_plan`])
//! makes that coupling explicit and keeps the merger/adapter call site a lookup
//! rather than a re-derivation.
//!
//! ## Extraction is behavior-preserving (plus one silent-corruption backstop)
//!
//! Increment 2 lifts the exact three-way dispatch (`site.crosses_memory` /
//! `options.needs_transcoding()`) and the #304 inline guard out of
//! `FactStyleGenerator::generate_adapter` unchanged. Future per-boundary ABI
//! strategies (symmetric ABI, static-base PIC — ADR-7 / #353) become new inputs
//! to [`resolve_call_lowering_plan`] instead of new branches threaded through
//! the generator's hot path.
//!
//! The one deliberate behavior change: a boundary that needs transcoding but
//! does **not** cross memory now **hard-fails** instead of silently emitting a
//! non-transcoding `Direct` shim (#361). The pre-extraction dispatch mapped that
//! case to `Direct` and mis-transcoded silently; the async path already failed
//! loud on the identical case (#272), so this closes the sync gap consistently.

use super::AdapterClass;
use crate::Result;

/// The facts about one call boundary that determine how it is lowered. All are
/// cheap booleans read from the resolved [`AdapterSite`](crate::resolver::AdapterSite)
/// and its analyzed [`AdapterOptions`](super::fact::AdapterOptions) — no
/// side effects, no ordering dependence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoundaryFacts {
    /// Caller and callee live in different linear memories (multi-memory, or
    /// `auto` where both components own a memory). Set once at resolve time.
    pub crosses_memory: bool,
    /// Caller and callee disagree on string encoding (UTF-8 vs UTF-16 vs
    /// Latin-1) — a transcode loop is required on top of the copy.
    pub needs_transcoding: bool,
    /// `--inline-adapters` is enabled (the #304 identity-trampoline bypass).
    pub inline_adapters: bool,
    /// The call carries `resource.rep` conversions (handle → representation).
    pub has_resource_rep_calls: bool,
    /// The call carries `resource.new` conversions (representation → handle).
    pub has_resource_new_calls: bool,
    /// The callee declares a `post-return` that must run after lifting.
    pub has_post_return: bool,
}

/// The resolved lowering decision for one boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallLoweringPlan {
    /// Which adapter body synthesizes the call.
    pub class: AdapterClass,
    /// Whether the adapter is a pure identity trampoline the caller may be wired
    /// straight to (#304). Only ever `true` for a `Direct` class; see the module
    /// doc for why this rides with the class decision.
    pub inline_eligible: bool,
}

/// Resolve how a single cross-component call boundary is lowered.
///
/// Class selection:
/// - encoding mismatch (needs transcoding) → `Transcode`, whether or not the
///   boundary crosses memory (#361 — the transcode adapter is
///   memory-index-parameterised, so it transcodes correctly within one shared
///   memory as well as across two)
/// - cross-memory, same encoding → `MemoryCopy`
/// - same memory, same encoding → `Direct`
///
/// and `inline_eligible` iff inlining is on, the class is `Direct`, and the call
/// carries no resource conversions and no post-return.
pub fn resolve_call_lowering_plan(facts: BoundaryFacts) -> Result<CallLoweringPlan> {
    // #361: transcoding is required whenever the encodings differ, regardless of
    // whether memory is crossed. Route to `Transcode`; the adapter reads from
    // `caller_memory` and writes the transcoded bytes to `callee_memory` (both
    // the one shared memory under `--memory shared`), so a same-memory boundary
    // transcodes correctly rather than falling through to a verbatim `Direct`
    // copy. (This lifts the #360 hard-fail, which was the loud-not-silent
    // placeholder until this support landed.)
    let class = if facts.needs_transcoding {
        AdapterClass::Transcode
    } else if facts.crosses_memory {
        AdapterClass::MemoryCopy
    } else {
        AdapterClass::Direct
    };

    // #304: a Direct adapter is a *pure identity trampoline* — and thus safe to
    // bypass — only when it carries no resource conversions AND no post-return
    // (the Direct generator still emits `call post_return` when
    // `has_post_return && result_count == 0`, so post-return must be excluded
    // entirely). This guard MUST stay a superset of `generate_direct_adapter`'s
    // complex-branch trigger; the two are coupled. Any doubt → not eligible.
    let inline_eligible = facts.inline_adapters
        && matches!(class, AdapterClass::Direct)
        && !facts.has_resource_rep_calls
        && !facts.has_resource_new_calls
        && !facts.has_post_return;

    Ok(CallLoweringPlan {
        class,
        inline_eligible,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A `Direct` boundary with nothing extra: same memory, same encoding.
    fn direct() -> BoundaryFacts {
        BoundaryFacts {
            crosses_memory: false,
            needs_transcoding: false,
            inline_adapters: true,
            has_resource_rep_calls: false,
            has_resource_new_calls: false,
            has_post_return: false,
        }
    }

    #[test]
    fn same_memory_is_direct_and_inlinable() {
        let plan = resolve_call_lowering_plan(direct()).unwrap();
        assert_eq!(plan.class, AdapterClass::Direct);
        assert!(plan.inline_eligible);
    }

    #[test]
    fn cross_memory_same_encoding_is_memory_copy() {
        let plan = resolve_call_lowering_plan(BoundaryFacts {
            crosses_memory: true,
            ..direct()
        })
        .unwrap();
        assert_eq!(plan.class, AdapterClass::MemoryCopy);
        assert!(!plan.inline_eligible, "only Direct is ever inlinable");
    }

    #[test]
    fn cross_memory_encoding_mismatch_is_transcode() {
        let plan = resolve_call_lowering_plan(BoundaryFacts {
            crosses_memory: true,
            needs_transcoding: true,
            ..direct()
        })
        .unwrap();
        assert_eq!(plan.class, AdapterClass::Transcode);
        assert!(!plan.inline_eligible);
    }

    #[test]
    fn same_memory_transcoding_routes_to_transcode() {
        // #361: a boundary that needs transcoding but does NOT cross memory now
        // routes to `Transcode` (the transcode adapter is memory-index-
        // parameterised and transcodes within one shared memory), rather than
        // hard-failing or falling through to a verbatim `Direct` copy.
        let plan = resolve_call_lowering_plan(BoundaryFacts {
            needs_transcoding: true,
            ..direct()
        })
        .unwrap();
        assert_eq!(plan.class, AdapterClass::Transcode);
        assert!(!plan.inline_eligible, "Transcode is never inlinable");
    }

    #[test]
    fn inlining_disabled_never_eligible() {
        let plan = resolve_call_lowering_plan(BoundaryFacts {
            inline_adapters: false,
            ..direct()
        })
        .unwrap();
        assert_eq!(plan.class, AdapterClass::Direct);
        assert!(!plan.inline_eligible);
    }

    #[test]
    fn direct_with_resource_rep_not_eligible() {
        let plan = resolve_call_lowering_plan(BoundaryFacts {
            has_resource_rep_calls: true,
            ..direct()
        })
        .unwrap();
        assert_eq!(plan.class, AdapterClass::Direct);
        assert!(!plan.inline_eligible);
    }

    #[test]
    fn direct_with_resource_new_not_eligible() {
        let plan = resolve_call_lowering_plan(BoundaryFacts {
            has_resource_new_calls: true,
            ..direct()
        })
        .unwrap();
        assert!(!plan.inline_eligible);
    }

    #[test]
    fn direct_with_post_return_not_eligible() {
        // The Direct generator still emits `call post_return` for a 0-result
        // callee, so bypassing the thunk would skip cleanup — must not inline.
        let plan = resolve_call_lowering_plan(BoundaryFacts {
            has_post_return: true,
            ..direct()
        })
        .unwrap();
        assert!(!plan.inline_eligible);
    }
}
