//! MCU-dissolve fixups for the `--memory shared` path (#334, SR-49).
//!
//! `meld fuse --memory shared` flattens a wac-composed multi-provider
//! Component-Model node into one shared-memory core module. Two artifacts
//! survive that flattening and block the downstream
//! `synth --native-pointer-abi --shadow-stack-size` MCU dissolve. gale
//! hand-patches both via WAT surgery today; this pass emits them fused so
//! the dissolve proceeds without manual intervention.
//!
//! ## Part 1 — coalesce the per-provider `__stack_pointer` globals
//!
//! `--memory shared` merges the N linear memories into one but leaves one
//! mutable-`i32` `__stack_pointer` global PER fused provider, all descending
//! from the same shared shadow-stack top (`sp_init`). A shared memory has ONE
//! shadow stack; keeping N of them is UNSOUND (two providers on a
//! cross-component call clobber each other's frames) and blocks synth's
//! shadow-stack rebasing ("could not uniquely identify the shadow-stack
//! global", synth#707). We keep one survivor and remap every reference to the
//! coalesced duplicates onto it, then drop the extras from the global section.
//!
//! ## Part 2 — DCE the dead lowered-import shim trampoline
//!
//! The pre-meld wac composite carries a lowered-import shim: an `$imports`
//! table plus a `call_indirect` trampoline populated at instantiation. After
//! meld flattens cross-component calls to DIRECT calls, a vestigial
//! trampoline survives — unreachable, mis-typed, kept alive only by its
//! numeric-named export. synth's closed-world check (synth#642/#676) declines
//! it. Dropping the keep-alive export makes the function DCE-eligible, which
//! is the minimal correct fix (#334); synth then DCEs the body.
//!
//! Both fixups are `--memory shared`-only. The non-shared / multi-memory
//! paths never call into this module, so their output is byte-for-byte
//! unchanged.

use std::collections::{HashMap, HashSet};

use wasm_encoder::{ExportKind as EncoderExportKind, Function, ValType};
use wasmparser::{BinaryReader, CodeSectionReader, Operator};

use crate::merger::MergedModule;
use crate::parser::{ImportKind, ParsedComponent};
use crate::rewriter::{IndexMaps, rewrite_function_body};
use crate::segments::{ElementSegmentMode, ReindexedElementItems};
use crate::{Error, Result};

/// Outcome of an MCU-dissolve pass, for logging and test assertions.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DissolveStats {
    /// Number of duplicate `__stack_pointer`-class globals coalesced away
    /// (i.e. dropped from the global section; the survivor is not counted).
    pub stack_pointers_coalesced: usize,
    /// Number of dead lowered-import trampoline keep-alive exports dropped.
    pub trampoline_exports_dropped: usize,
}

/// Apply both MCU-dissolve fixups in place. Caller gates this on
/// `MemoryStrategy::SharedMemory`.
pub fn dissolve_fixups(
    merged: &mut MergedModule,
    components: &[ParsedComponent],
) -> Result<DissolveStats> {
    let stack_pointers_coalesced = coalesce_stack_pointers(merged, components)?;
    let trampoline_exports_dropped = drop_dead_import_trampolines(merged)?;
    let stats = DissolveStats {
        stack_pointers_coalesced,
        trampoline_exports_dropped,
    };
    if stats != DissolveStats::default() {
        log::info!(
            "#334 MCU-dissolve: coalesced {} duplicate __stack_pointer global(s), \
             dropped {} dead lowered-import trampoline export(s)",
            stats.stack_pointers_coalesced,
            stats.trampoline_exports_dropped,
        );
    }
    Ok(stats)
}

// ---------------------------------------------------------------------------
// Part 1 — __stack_pointer coalescing
// ---------------------------------------------------------------------------

/// A `__stack_pointer`-class defined global, resolved into the fused module's
/// absolute global-index space.
struct SpCandidate {
    /// Absolute global index in the fused module.
    merged_idx: u32,
    /// The `i32.const` shadow-stack top the global initialises to.
    init: i32,
    /// Whether the `name` section's global-name subsection named this global
    /// exactly `__stack_pointer` (the authoritative signal).
    named: bool,
}

/// Coalesce the per-provider `__stack_pointer` globals into one survivor.
/// Returns the number of duplicates dropped.
fn coalesce_stack_pointers(
    merged: &mut MergedModule,
    components: &[ParsedComponent],
) -> Result<usize> {
    let import_base = merged.import_counts.global;

    // Gather candidates from the ORIGINAL parsed globals — the merged
    // `ConstExpr` init is opaque, but the source `init_expr_bytes` is
    // readable and the `global_index_map` translates its index into the
    // fused space. `__stack_pointer` is always a DEFINED (not imported)
    // global, and cross-module SP sharing via a global import is already
    // unified by the merger, so iterating defined globals visits each
    // genuinely-separate SP exactly once.
    let mut candidates: Vec<SpCandidate> = Vec::new();
    let mut seen: HashSet<u32> = HashSet::new();
    for (comp_idx, comp) in components.iter().enumerate() {
        for (mod_idx, module) in comp.core_modules.iter().enumerate() {
            let import_global_count = module
                .imports
                .iter()
                .filter(|i| matches!(i.kind, ImportKind::Global(_)))
                .count() as u32;
            let names = parse_global_names(module);
            for (old_idx, g) in module.globals.iter().enumerate() {
                // Only mutable i32 globals with a single `i32.const` initialiser
                // can be a shadow-stack pointer.
                if !g.mutable || g.content_type != ValType::I32 {
                    continue;
                }
                let Some(init) = read_i32_const(&g.init_expr_bytes) else {
                    continue;
                };
                let abs_old = import_global_count + old_idx as u32;
                let Some(&merged_idx) = merged.global_index_map.get(&(comp_idx, mod_idx, abs_old))
                else {
                    continue;
                };
                // Guard: only consider globals that still live in the fused
                // global section (a defined slot), and dedup by fused index.
                if merged_idx < import_base || !seen.insert(merged_idx) {
                    continue;
                }
                let named = names
                    .get(&abs_old)
                    .map(|n| n == "__stack_pointer")
                    .unwrap_or(false);
                candidates.push(SpCandidate {
                    merged_idx,
                    init,
                    named,
                });
            }
        }
    }

    // Decide which sets to coalesce. Correctness over cleanup: only fuse
    // globals we are confident share one shadow stack.
    let groups = choose_coalesce_groups(&candidates);
    if groups.is_empty() {
        return Ok(0);
    }

    // Build the redirect (dropped -> survivor) and the drop set.
    let mut redirect: HashMap<u32, u32> = HashMap::new();
    let mut drop_set: Vec<u32> = Vec::new();
    for group in &groups {
        let survivor = *group.iter().min().expect("group is non-empty");
        for &idx in group {
            if idx != survivor {
                redirect.insert(idx, survivor);
                drop_set.push(idx);
            }
        }
    }
    drop_set.sort_unstable();
    drop_set.dedup();
    let coalesced = drop_set.len();

    // New absolute index after removing everything in `drop_set` below it.
    let shift = |old: u32| -> u32 {
        let removed_below = drop_set.iter().filter(|&&d| d < old).count() as u32;
        old - removed_below
    };

    // Full old -> new global-index remap: a coalesced duplicate routes to the
    // survivor's post-shift index; every surviving global slides down past the
    // holes left by the drops.
    let total = import_base + merged.globals.len() as u32;
    let mut gmap: HashMap<u32, u32> = HashMap::new();
    for old in 0..total {
        let new = match redirect.get(&old) {
            Some(&survivor) => shift(survivor),
            None => shift(old),
        };
        if new != old || redirect.contains_key(&old) {
            gmap.insert(old, new);
        }
    }

    // Rewrite every `global.get`/`global.set` in the fused code section
    // through the same remap the merger uses for its own renumbering.
    let maps = IndexMaps {
        globals: gmap.clone(),
        ..IndexMaps::new()
    };
    for f in merged.functions.iter_mut() {
        f.body = reparse_and_rewrite_body(&f.body, &maps)?;
    }

    // Remap global exports (the survivor may be re-exported).
    for e in merged.exports.iter_mut() {
        if matches!(e.kind, EncoderExportKind::Global)
            && let Some(&new) = gmap.get(&e.index)
        {
            e.index = new;
        }
    }

    // Drop the coalesced duplicates from the global section. (Defined globals
    // occupy `merged.globals[merged_idx - import_base]`.) Init expressions can
    // only reference IMPORTED globals, which we never drop, so surviving
    // initialisers need no rewrite.
    let drop_positions: HashSet<usize> = drop_set
        .iter()
        .map(|&d| (d - import_base) as usize)
        .collect();
    let kept: Vec<_> = std::mem::take(&mut merged.globals)
        .into_iter()
        .enumerate()
        .filter_map(|(j, g)| (!drop_positions.contains(&j)).then_some(g))
        .collect();
    merged.globals = kept;

    Ok(coalesced)
}

/// Group SP candidates into coalescible sets (each set shares one shadow
/// stack). Returns groups of fused global indices, each with ≥2 members.
///
/// ONLY the authoritative signal is used: a global the `name` section named
/// exactly `__stack_pointer`. An init-value heuristic was rejected (Mythos
/// #334 review): two unrelated mutable-i32 globals in different components that
/// merely share an init value (an errno/TLS/counter global at the same `K`)
/// would be fused, redirecting one component's `global.set` onto the other's
/// storage — silent cross-component corruption. A mis-coalesce is worse than a
/// no-op, so absent the name we do NOT guess (the fused module keeps its
/// several SP globals; synth surfaces the multi-SP condition rather than meld
/// corrupting it). The robust name-free signal, if ever needed, is the
/// `linking` symbol table — not the init value.
fn choose_coalesce_groups(candidates: &[SpCandidate]) -> Vec<Vec<u32>> {
    // Group `__stack_pointer`-named candidates by init value (a shared memory's
    // SP top is the common `sp_init`); coalesce equal-init groups only —
    // differing inits would signal a pre-partitioned layout we must not merge.
    let mut by_init: HashMap<i32, Vec<u32>> = HashMap::new();
    for c in candidates.iter().filter(|c| c.named) {
        by_init.entry(c.init).or_default().push(c.merged_idx);
    }
    finalize_groups(by_init)
}

/// Keep only multi-member groups; sort each for deterministic survivor choice.
fn finalize_groups(by_init: HashMap<i32, Vec<u32>>) -> Vec<Vec<u32>> {
    let mut groups: Vec<Vec<u32>> = by_init
        .into_values()
        .filter(|g| g.len() >= 2)
        .map(|mut g| {
            g.sort_unstable();
            g.dedup();
            g
        })
        .filter(|g| g.len() >= 2)
        .collect();
    groups.sort();
    groups
}

/// Parse a module's `name` section global-name subsection into
/// `absolute-global-index -> name`. Returns empty on absence or malformation
/// (never guess).
fn parse_global_names(module: &crate::parser::CoreModule) -> HashMap<u32, String> {
    let mut out = HashMap::new();
    let Some((_, data)) = module.custom_sections.iter().find(|(n, _)| n == "name") else {
        return out;
    };
    let reader = wasmparser::NameSectionReader::new(BinaryReader::new(data, 0));
    for subsection in reader {
        let Ok(subsection) = subsection else {
            return HashMap::new();
        };
        if let wasmparser::Name::Global(namemap) = subsection {
            for naming in namemap {
                let Ok(naming) = naming else { continue };
                out.insert(naming.index, naming.name.to_string());
            }
        }
    }
    out
}

/// Read a lone `i32.const K` constant-expression body (init-expr bytes, with
/// the trailing `end` already stripped by the parser). Returns `None` for any
/// other shape — we only coalesce globals whose initialiser is exactly a
/// shadow-stack-top constant.
fn read_i32_const(bytes: &[u8]) -> Option<i32> {
    // 0x41 = i32.const, followed by a signed LEB128 immediate.
    if bytes.first() != Some(&0x41) {
        return None;
    }
    let (val, consumed) = read_sleb128(&bytes[1..])?;
    if 1 + consumed != bytes.len() {
        return None;
    }
    i32::try_from(val).ok()
}

/// Minimal signed-LEB128 decoder. Returns `(value, bytes_consumed)`.
fn read_sleb128(bytes: &[u8]) -> Option<(i64, usize)> {
    let mut result: i64 = 0;
    let mut shift: u32 = 0;
    let mut i = 0;
    loop {
        let byte = *bytes.get(i)?;
        i += 1;
        result |= ((byte & 0x7f) as i64) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            if shift < 64 && (byte & 0x40) != 0 {
                result |= -1i64 << shift;
            }
            return Some((result, i));
        }
        if shift >= 64 {
            return None;
        }
    }
}

// ---------------------------------------------------------------------------
// Part 2 — dead lowered-import trampoline export drop
// ---------------------------------------------------------------------------

/// Drop the keep-alive export of any vestigial lowered-import trampoline so
/// synth can DCE the body. Returns the number of exports dropped.
fn drop_dead_import_trampolines(merged: &mut MergedModule) -> Result<usize> {
    let func_base = merged.import_counts.func;

    // Every function reachable by a real call (direct, tail, or ref.func) plus
    // the start function. A trampoline reached by any of these is live —
    // leave it alone.
    let mut reachable: HashSet<u32> = HashSet::new();
    if let Some(s) = merged.start_function {
        reachable.insert(s);
    }
    for f in &merged.functions {
        collect_reachable(&f.body, &mut reachable)?;
    }

    // Tables that hold at least one DEFINED function via a static element
    // segment are ordinary indirect-call tables, NOT the host-populated
    // lowered-import table. The `$imports` table holds only imported
    // functions (or is filled at instantiation with no static segment).
    let mut table_has_defined_fn: HashSet<u32> = HashSet::new();
    for seg in &merged.elements {
        if let ElementSegmentMode::Active { table_index, .. } = seg.mode
            && let ReindexedElementItems::Functions(fs) = &seg.items
            && fs.iter().any(|&fi| fi >= func_base)
        {
            table_has_defined_fn.insert(table_index);
        }
    }

    // Collect the exports to drop: numeric-named function exports whose body
    // is a bare `local.get*; i32.const K; call_indirect` over an import table
    // and which nothing calls.
    let mut to_drop: Vec<(String, u32)> = Vec::new();
    for e in &merged.exports {
        if !matches!(e.kind, EncoderExportKind::Func) {
            continue;
        }
        // Keep-alive exports of the wac shim are numeric ("0", "1", …). A real
        // WIT export never uses a pure-integer core name — a strong,
        // conservative discriminator.
        if e.name.is_empty() || !e.name.bytes().all(|b| b.is_ascii_digit()) {
            continue;
        }
        let fidx = e.index;
        if fidx < func_base || reachable.contains(&fidx) {
            continue;
        }
        let Some(mf) = merged.defined_func(fidx) else {
            continue;
        };
        let Some(table) = match_import_trampoline(&mf.body)? else {
            continue;
        };
        // The dispatch table must be an import table, not a normal vtable.
        if table_has_defined_fn.contains(&table) {
            continue;
        }
        to_drop.push((e.name.clone(), fidx));
    }

    if to_drop.is_empty() {
        return Ok(0);
    }
    let before = merged.exports.len();
    merged.exports.retain(|e| {
        !(matches!(e.kind, EncoderExportKind::Func)
            && to_drop.iter().any(|(n, i)| *n == e.name && *i == e.index))
    });
    Ok(before - merged.exports.len())
}

/// Structural match for a lowered-import trampoline body:
/// `(local.get …)* i32.const K  call_indirect <table> (type T)  end`.
/// Returns the dispatch table index on a match, `None` otherwise.
fn match_import_trampoline(body: &Function) -> Result<Option<u32>> {
    let section = one_func_code_section(body);
    let reader = CodeSectionReader::new(BinaryReader::new(&section, 0))?;
    if let Some(b) = reader.into_iter().next() {
        let b = b?;
        let mut table = None;
        let mut seen_call_indirect = false;
        let mut seen_const = false;
        let mut ok = true;
        for op in b.get_operators_reader()? {
            match op? {
                Operator::LocalGet { .. } => {
                    if seen_call_indirect {
                        ok = false;
                    }
                }
                Operator::I32Const { .. } => {
                    if seen_call_indirect {
                        ok = false;
                    }
                    seen_const = true;
                }
                Operator::CallIndirect { table_index, .. } => {
                    if seen_call_indirect {
                        ok = false; // more than one call_indirect — not a bare trampoline
                    }
                    table = Some(table_index);
                    seen_call_indirect = true;
                }
                Operator::End => {}
                _ => ok = false,
            }
        }
        return Ok((ok && seen_call_indirect && seen_const)
            .then_some(table)
            .flatten());
    }
    Ok(None)
}

/// Collect direct/tail-call and `ref.func` targets from a function body.
fn collect_reachable(body: &Function, out: &mut HashSet<u32>) -> Result<()> {
    let section = one_func_code_section(body);
    let reader = CodeSectionReader::new(BinaryReader::new(&section, 0))?;
    for b in reader {
        let b = b?;
        for op in b.get_operators_reader()? {
            match op? {
                Operator::Call { function_index }
                | Operator::ReturnCall { function_index }
                | Operator::RefFunc { function_index } => {
                    out.insert(function_index);
                }
                _ => {}
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Shared body-reparse helper
// ---------------------------------------------------------------------------

/// Wrap one already-encoded function body as a single-entry code section so
/// `wasmparser` can re-read it. `into_raw_body` yields the body bytes
/// (`locals + code`) WITHOUT a size prefix, so a valid single-entry code
/// section is `[count=1][body-size][body]`.
fn one_func_code_section(body: &Function) -> Vec<u8> {
    let raw = body.clone().into_raw_body();
    let mut section = vec![0x01u8]; // one function entry
    write_uleb128(raw.len() as u64, &mut section);
    section.extend_from_slice(&raw);
    section
}

/// Append a u32/u64 as unsigned LEB128.
fn write_uleb128(mut v: u64, out: &mut Vec<u8>) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(byte);
            break;
        }
        out.push(byte | 0x80);
    }
}

/// Re-parse an encoded body and rewrite its index references through `maps`
/// (only `globals` is populated by this module; everything else is identity).
fn reparse_and_rewrite_body(body: &Function, maps: &IndexMaps) -> Result<Function> {
    let section = one_func_code_section(body);
    let reader = CodeSectionReader::new(BinaryReader::new(&section, 0))?;
    if let Some(b) = reader.into_iter().next() {
        let b = b?;
        // `param_count` only matters under address rebasing (off here), so 0.
        return rewrite_function_body(&b, 0, maps);
    }
    Err(Error::EncodingError(
        "mcu_dissolve: empty single-function code section".to_string(),
    ))
}
