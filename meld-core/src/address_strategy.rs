//! Address / memory strategy seam (ADR-7 path-H, increment 1).
//!
//! meld places each fused module's linear memory somewhere in the output's
//! address space, and how a module's *absolute addresses* are handled depends
//! on the memory strategy in force:
//!
//! - **multi-memory** — each component keeps its own memory; nothing to rebase.
//! - **shared-rebase** (ADR-6 path-D) — the module is placed at a shared-memory
//!   base and its `reloc.CODE`/`reloc.DATA` memory-address sites are shifted by
//!   that base (the #326→#340 reloc consumer, with the #351 stale-reloc backstop).
//! - **static-base PIC** (ADR-7 / #353, future) — PIC inputs compute addresses
//!   from `__memory_base`; meld folds a disjoint constant base per module. No
//!   absolute-address relocation sites exist, so this strategy will short-circuit
//!   the reloc machinery entirely.
//!
//! This module is the single home for that decision. Increment 1 extracts the
//! existing shared-rebase resolution here **behavior-preservingly** — same
//! validation (`MissingRelocMetadata`, memory64 reject, `MisalignedReloc`), same
//! short-circuits — so the pluggable variants above can be added later without
//! touching the merger's hot path. The canonical/multi path is unchanged (it
//! resolves to an empty plan).

use crate::{Error, Result};

/// What the address strategy resolved for one module: which relocation sites the
/// rewriter must rebase. An empty plan (`code_addr_relocs: None`, no data
/// entries) means "no address rebasing for this module" (multi-memory, or shared
/// memory with a zero base / no reloc metadata).
#[derive(Debug, Default)]
pub struct AddressPlan {
    /// Code-section byte offsets of `R_WASM_MEMORY_ADDR_*` sites to rebase
    /// ([`crate::reloc::RelocInfo::code_memory_addr_offsets`]). `None` = the
    /// legacy blanket path (a no-op when the base is 0); `Some` = reloc-driven.
    pub code_addr_relocs: Option<std::collections::HashSet<u32>>,
    /// `reloc.DATA` `R_WASM_MEMORY_ADDR_I32` inline pointers to rebase in the
    /// data segments' payloads.
    pub data_addr_relocs: Vec<crate::reloc::RelocEntry>,
}

/// Resolve the address plan for one module placed at `memory_base_offset`.
///
/// `has_direct_memory_access` is evaluated **lazily** (only when a non-zero base
/// carries no reloc metadata) so a component that never needs the check pays
/// nothing and cannot fail on it — preserving the merger's original
/// short-circuit exactly.
///
/// Behaviour (shared-rebase strategy; unchanged from the pre-extraction merger):
/// - `address_rebasing == false` → empty plan.
/// - non-zero base, no reloc metadata, direct memory access → `MissingRelocMetadata`
///   (ADR-6 path-F: cannot rebase baked-in absolute addresses → don't silently
///   corrupt).
/// - reloc metadata with non-32-bit inline data pointers (memory64) →
///   `UnsupportedFeature` (#326 Finding B).
/// - reloc metadata whose `reloc.CODE` sites no longer land on rebasable
///   immediates → `MisalignedReloc` (#351 backstop; stale/relaxed relocs).
/// - reloc metadata otherwise → the code/data reloc sites to rebase.
/// - no reloc metadata (and base 0 or bulk-only access) → empty plan.
#[allow(clippy::too_many_arguments)]
pub fn resolve_address_plan(
    custom_sections: &[(String, Vec<u8>)],
    code_section_range: Option<(usize, usize)>,
    module_bytes: &[u8],
    memory_base_offset: u64,
    address_rebasing: bool,
    component_name: &str,
    module_idx: usize,
    has_direct_memory_access: impl FnOnce() -> Result<bool>,
) -> Result<AddressPlan> {
    if !address_rebasing {
        return Ok(AddressPlan::default());
    }

    let has_reloc = crate::reloc::has_reloc_metadata(custom_sections);

    // Path-F (ADR-6): a non-zero-base module with no reloc metadata that does
    // *direct* (non-bulk) memory access has absolute addresses we cannot find —
    // emitting it unchanged would collide it with a prior module. Hard-fail.
    if memory_base_offset != 0 && !has_reloc && has_direct_memory_access()? {
        return Err(Error::MissingRelocMetadata {
            component: component_name.to_string(),
            module: module_idx.to_string(),
        });
    }

    if !has_reloc {
        return Ok(AddressPlan::default());
    }

    let info = crate::reloc::parse_reloc_info(custom_sections)?;

    // #326 Finding B: memory64 emits 8-byte inline data pointers we cannot
    // rebase; the segment moves while the pointers stay stale. Reject.
    if info.has_unhandled_data_addr_relocs() {
        return Err(Error::UnsupportedFeature(format!(
            "component '{component_name}' module {module_idx}: shared-memory \
             rebasing of non-32-bit inline data pointers (memory64 reloc.DATA) \
             is not supported (#326)",
        )));
    }

    let data_addr_relocs = info.data_memory_addr_entries();
    let code_offsets = info.code_memory_addr_offsets();

    // #351 backstop: every reloc.CODE memory-address site must still land on a
    // rebasable immediate; a producer that relaxed LEB immediates without
    // rewriting reloc offsets (pulseengine/wasm-tools#3) leaves them drifted.
    if let Some((start, end)) = code_section_range {
        let code_content = &module_bytes[start..end];
        if let Some(offset) =
            crate::reloc::first_misaligned_code_reloc(code_content, &code_offsets)?
        {
            return Err(Error::MisalignedReloc {
                component: component_name.to_string(),
                module: module_idx.to_string(),
                offset,
            });
        }
    }

    Ok(AddressPlan {
        code_addr_relocs: Some(code_offsets),
        data_addr_relocs,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    // A module with no reloc custom sections.
    fn no_reloc() -> Vec<(String, Vec<u8>)> {
        vec![("name".to_string(), vec![0])]
    }

    #[test]
    fn rebasing_off_is_empty_plan_and_never_probes_memory_access() {
        let probed = Cell::new(false);
        let plan = resolve_address_plan(
            &no_reloc(),
            None,
            &[],
            0x1_0000,
            false, // address_rebasing off
            "c",
            0,
            || {
                probed.set(true);
                Ok(true)
            },
        )
        .unwrap();
        assert!(plan.code_addr_relocs.is_none());
        assert!(plan.data_addr_relocs.is_empty());
        assert!(
            !probed.get(),
            "must not probe memory access when rebasing is off"
        );
    }

    #[test]
    fn base_zero_no_reloc_is_empty_plan_without_probe() {
        // At base 0 there is nothing to collide with, so the path-F check (and
        // its memory-access probe) must be skipped even without reloc metadata.
        let probed = Cell::new(false);
        let plan = resolve_address_plan(
            &no_reloc(),
            None,
            &[],
            0, // base 0
            true,
            "c",
            0,
            || {
                probed.set(true);
                Ok(true)
            },
        )
        .unwrap();
        assert!(plan.code_addr_relocs.is_none());
        assert!(
            !probed.get(),
            "base 0 must not trigger the direct-access probe"
        );
    }

    #[test]
    fn nonzero_base_no_reloc_direct_access_hard_fails() {
        let err = resolve_address_plan(&no_reloc(), None, &[], 0x1_0000, true, "comp", 3, || {
            Ok(true)
        })
        .unwrap_err();
        assert!(
            matches!(err, Error::MissingRelocMetadata { .. }),
            "expected MissingRelocMetadata, got {err:?}"
        );
    }

    #[test]
    fn nonzero_base_no_reloc_bulk_only_is_empty_plan() {
        // No reloc but only bulk-memory access (probe returns false): safe — the
        // rewriter rebases bulk ops' runtime operands, so no baked address hides.
        let plan =
            resolve_address_plan(&no_reloc(), None, &[], 0x1_0000, true, "c", 0, || Ok(false))
                .unwrap();
        assert!(plan.code_addr_relocs.is_none());
        assert!(plan.data_addr_relocs.is_empty());
    }
}
