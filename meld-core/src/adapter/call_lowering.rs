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
use crate::{Error, Result};

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
/// Class selection (unchanged from the pre-extraction `generate_adapter`):
/// - cross-memory + encoding mismatch → `Transcode`
/// - cross-memory, same encoding → `MemoryCopy`
/// - same memory → `Direct`
///
/// and `inline_eligible` iff inlining is on, the class is `Direct`, and the call
/// carries no resource conversions and no post-return.
///
/// # Errors
///
/// Hard-fails ([`Error::AdapterGeneration`](crate::Error::AdapterGeneration))
/// when the boundary needs transcoding but does **not** cross memory
/// (`needs_transcoding && !crosses_memory`). A same-memory boundary is lowered
/// as a `Direct` shim that does not transcode, so emitting one for a
/// mixed-encoding call would deliver string bytes verbatim in the wrong encoding
/// — a silent miscompile. This is the sync twin of `guard_async_cross_encoding_strings`
/// (the async path already fails loud here, #272). Supporting same-memory
/// transcoding is tracked in #361; until then we refuse rather than corrupt.
pub fn resolve_call_lowering_plan(facts: BoundaryFacts) -> Result<CallLoweringPlan> {
    // #361: a boundary that needs transcoding but does not cross memory has no
    // lowering that transcodes — `Direct` (the same-memory class) is a thin
    // shim. Fail loud instead of silently mis-transcoding (mirrors the async
    // guard, #272).
    if facts.needs_transcoding && !facts.crosses_memory {
        return Err(Error::AdapterGeneration(
            "same-memory string transcoding is not supported: this call requires \
             transcoding (caller and callee use different string encodings) but \
             does not cross a memory boundary, so it would be lowered as a Direct \
             shim that copies the bytes verbatim — silently mis-transcoding. The \
             async path already fails loud here (#272); see #361 to support it"
                .to_string(),
        ));
    }

    let class = if facts.crosses_memory && facts.needs_transcoding {
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
    fn same_memory_transcoding_hard_fails() {
        // #361: a boundary that needs transcoding but does not cross memory has
        // no lowering that transcodes (Direct is a thin shim). Emitting one
        // would silently mis-transcode, so the seam refuses — the sync twin of
        // the async cross-encoding guard (#272).
        let err = resolve_call_lowering_plan(BoundaryFacts {
            needs_transcoding: true,
            ..direct()
        })
        .unwrap_err();
        assert!(
            matches!(err, Error::AdapterGeneration(_)),
            "expected AdapterGeneration hard-fail, got {err:?}"
        );
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
