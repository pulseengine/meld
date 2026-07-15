//! Memory-usage probing for automatic memory-strategy selection (#172).
//!
//! `MemoryStrategy::SharedMemory` is sound only when no input module can
//! grow its linear memory at runtime: under address rebasing every module's
//! static layout is frozen at fuse time, so a `memory.grow` executed by one
//! module hands it pages whose ownership the other modules know nothing
//! about — allocator state diverges and address spaces silently collide
//! (merger Bug #7). `memory.grow` is an opcode, so its *absence* is a
//! static, decidable property of the input. This module provides that
//! probe; `Fuser::fuse_with_stats` uses it to resolve
//! `MemoryStrategy::Auto` to shared-memory fusion exactly when the probe
//! proves growth cannot occur.
//!
//! The probe is deliberately conservative in the right direction: any parse
//! failure counts as "uses memory.grow", so malformed input can never trick
//! auto-resolution into the shared path.

use wasmparser::{Operator, Parser, Payload};

/// Returns `true` if the core module's code section contains at least one
/// `memory.grow` instruction (for any memory index), or if the module
/// cannot be parsed (conservative: unparseable input must not select
/// shared-memory fusion).
pub fn module_uses_memory_grow(module_bytes: &[u8]) -> bool {
    for payload in Parser::new(0).parse_all(module_bytes) {
        let Ok(payload) = payload else {
            return true;
        };
        if let Payload::CodeSectionEntry(body) = payload {
            let Ok(ops) = body.get_operators_reader() else {
                return true;
            };
            for op in ops {
                match op {
                    Ok(Operator::MemoryGrow { .. }) => return true,
                    Ok(_) => {}
                    Err(_) => return true,
                }
            }
        }
    }
    false
}

/// #298 — is `name` an export the vestigial-`cabi_realloc` drop may remove?
///
/// The merger emits the allocator export under exactly two shapes: the bare
/// `cabi_realloc`, and the per-memory-index suffixed `cabi_realloc$<digits>`
/// form. Match those two ONLY — a legitimately-authored export such as
/// `cabi_realloc$foo` (non-digit suffix) is NOT one of ours and must never be
/// dropped. So the suffix, when present, must be non-empty and all ASCII
/// digits.
pub fn is_vestigial_realloc_export_name(name: &str) -> bool {
    if name == "cabi_realloc" {
        return true;
    }
    match name.strip_prefix("cabi_realloc$") {
        Some(suffix) => !suffix.is_empty() && suffix.bytes().all(|b| b.is_ascii_digit()),
        None => false,
    }
}

/// #298 (FINDING 1) — is a `memory.grow` reachable from any LIVE root once the
/// vestigial `cabi_realloc*` exports are dropped?
///
/// The vestigial-`cabi_realloc` verdict ([`crate::Fuser::
/// cabi_realloc_drop_provably_safe`]) proves only that the *interface boundary*
/// needs no realloc (scalar lifts, core output, no adapters). It does NOT prove
/// the allocator is dead: a scalar-interface component can still allocate
/// internally (`Vec`/`String`/`Box` → `dlmalloc`/`sbrk` → `memory.grow`)
/// reachable from a live export. Deferring EVERY `memory.grow` to `unreachable`
/// there would fuse-`Ok` then trap at runtime — a compile error silently
/// downgraded to a trap.
///
/// This probe closes that gap: it builds the module call graph and asks whether
/// any `memory.grow` survives once the dropped `cabi_realloc*` exports are no
/// longer roots. If it returns `true`, the allocator is LIVE and the drop/defer
/// must NOT fire (keep `cabi_realloc`, keep the hard error). It returns `true`
/// (fail-safe: assume live) on any parse failure.
///
/// **Roots** (a function is reachable if reached from any of these):
///   * every exported function EXCEPT the dropped `cabi_realloc*` exports
///     (see [`is_vestigial_realloc_export_name`]);
///   * the `start` function;
///   * every function named by a `ref.func` (in a body, a global initializer,
///     or an element-segment expression) or listed in any element segment —
///     these may be reached via `call_indirect`/`call_ref`, whose targets are
///     not statically known, so they are treated as roots conservatively.
///
/// **Edges**: a function → its direct callees via `call` / `return_call`
/// (`call_indirect`/`call_ref` are covered by the ref.func/elem roots above).
pub fn module_has_reachable_memory_grow(module_bytes: &[u8]) -> bool {
    let mut num_imported_funcs: u32 = 0;
    let mut func_exports: Vec<(String, u32)> = Vec::new();
    let mut start: Option<u32> = None;
    // Functions reachable indirectly (ref.func / element segments) — roots.
    let mut ref_roots: Vec<u32> = Vec::new();
    // Per defined function: (direct callees, contains memory.grow).
    // Indexed by absolute function index (>= num_imported_funcs).
    let mut bodies: std::collections::HashMap<u32, (Vec<u32>, bool)> =
        std::collections::HashMap::new();
    let mut next_defined_idx: u32 = 0;

    for payload in Parser::new(0).parse_all(module_bytes) {
        let Ok(payload) = payload else {
            return true; // fail-safe: unparseable ⇒ assume a live grow
        };
        match payload {
            Payload::ImportSection(reader) => {
                for imp in reader.into_imports() {
                    let Ok(imp) = imp else { return true };
                    if matches!(
                        imp.ty,
                        wasmparser::TypeRef::Func(_) | wasmparser::TypeRef::FuncExact(_)
                    ) {
                        num_imported_funcs += 1;
                    }
                }
            }
            Payload::ExportSection(reader) => {
                for exp in reader {
                    let Ok(exp) = exp else { return true };
                    if matches!(
                        exp.kind,
                        wasmparser::ExternalKind::Func | wasmparser::ExternalKind::FuncExact
                    ) {
                        func_exports.push((exp.name.to_string(), exp.index));
                    }
                }
            }
            Payload::StartSection { func, .. } => start = Some(func),
            Payload::GlobalSection(reader) => {
                for g in reader {
                    let Ok(g) = g else { return true };
                    let Ok(ops) = g
                        .init_expr
                        .get_operators_reader()
                        .into_iter()
                        .collect::<Result<Vec<_>, _>>()
                    else {
                        return true;
                    };
                    for op in ops {
                        if let Operator::RefFunc { function_index } = op {
                            ref_roots.push(function_index);
                        }
                    }
                }
            }
            Payload::ElementSection(reader) => {
                for elem in reader {
                    let Ok(elem) = elem else { return true };
                    match elem.items {
                        wasmparser::ElementItems::Functions(fr) => {
                            for f in fr {
                                let Ok(f) = f else { return true };
                                ref_roots.push(f);
                            }
                        }
                        wasmparser::ElementItems::Expressions(_, er) => {
                            for expr in er {
                                let Ok(expr) = expr else { return true };
                                let Ok(ops) = expr
                                    .get_operators_reader()
                                    .into_iter()
                                    .collect::<Result<Vec<_>, _>>()
                                else {
                                    return true;
                                };
                                for op in ops {
                                    if let Operator::RefFunc { function_index } = op {
                                        ref_roots.push(function_index);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                let func_idx = num_imported_funcs + next_defined_idx;
                next_defined_idx += 1;
                let Ok(ops) = body.get_operators_reader() else {
                    return true;
                };
                let mut callees: Vec<u32> = Vec::new();
                let mut has_grow = false;
                for op in ops {
                    match op {
                        Ok(Operator::MemoryGrow { .. }) => has_grow = true,
                        Ok(Operator::Call { function_index })
                        | Ok(Operator::ReturnCall { function_index }) => {
                            callees.push(function_index)
                        }
                        Ok(Operator::RefFunc { function_index }) => ref_roots.push(function_index),
                        Ok(_) => {}
                        Err(_) => return true,
                    }
                }
                bodies.insert(func_idx, (callees, has_grow));
            }
            _ => {}
        }
    }

    // Assemble roots: live func exports (drop the vestigial realloc ones) +
    // start + all indirectly-referenced functions.
    let mut worklist: Vec<u32> = Vec::new();
    for (name, idx) in &func_exports {
        if !is_vestigial_realloc_export_name(name) {
            worklist.push(*idx);
        }
    }
    if let Some(s) = start {
        worklist.push(s);
    }
    worklist.extend(ref_roots);

    // BFS over call edges; any reachable body with a grow ⇒ live grow.
    let mut visited: std::collections::HashSet<u32> = std::collections::HashSet::new();
    while let Some(idx) = worklist.pop() {
        if !visited.insert(idx) {
            continue;
        }
        if let Some((callees, has_grow)) = bodies.get(&idx) {
            if *has_grow {
                return true;
            }
            worklist.extend(callees.iter().copied());
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    fn module(wat: &str) -> Vec<u8> {
        wat::parse_str(wat).expect("test wat must assemble")
    }

    #[test]
    fn detects_memory_grow() {
        let bytes = module(
            r#"(module
                (memory 1)
                (func (export "grow") (result i32)
                    i32.const 1
                    memory.grow))"#,
        );
        assert!(module_uses_memory_grow(&bytes));
    }

    #[test]
    fn no_grow_in_plain_module() {
        let bytes = module(
            r#"(module
                (memory 1)
                (func (export "load") (result i32)
                    i32.const 0
                    i32.load))"#,
        );
        assert!(!module_uses_memory_grow(&bytes));
    }

    /// `memory.size` reads the page count without growing — it must not
    /// trip the probe, otherwise auto-resolution is needlessly pessimistic.
    #[test]
    fn memory_size_does_not_count_as_grow() {
        let bytes = module(
            r#"(module
                (memory 1)
                (func (export "size") (result i32)
                    memory.size))"#,
        );
        assert!(!module_uses_memory_grow(&bytes));
    }

    /// Growth buried in a later function among several non-growing ones is
    /// still found — the probe scans every body, not just the first.
    #[test]
    fn detects_grow_in_later_function() {
        let bytes = module(
            r#"(module
                (memory 1)
                (func (export "a") (result i32) i32.const 1)
                (func (export "b") (result i32) i32.const 2)
                (func (export "c") (result i32)
                    i32.const 1
                    memory.grow))"#,
        );
        assert!(module_uses_memory_grow(&bytes));
    }

    /// Unparseable bytes are treated as growing (conservative direction:
    /// never let malformed input select the shared-memory path).
    /// (`ls_m_7_` prefix: regression test for the approved LS-M-7
    /// scenario, run by the LS-N verification gate.)
    #[test]
    fn ls_m_7_malformed_input_counts_as_grow() {
        assert!(module_uses_memory_grow(&[0x00, 0x61, 0x73, 0x6d, 0xff]));
    }

    /// A module with no memory at all trivially cannot grow one.
    #[test]
    fn memoryless_module_does_not_grow() {
        let bytes = module(r#"(module (func (export "f") (result i32) i32.const 7))"#);
        assert!(!module_uses_memory_grow(&bytes));
    }

    // --- #298 FINDING 2: droppable-name predicate -----------------------

    #[test]
    fn vestigial_realloc_name_match_is_tight() {
        assert!(is_vestigial_realloc_export_name("cabi_realloc"));
        assert!(is_vestigial_realloc_export_name("cabi_realloc$0"));
        assert!(is_vestigial_realloc_export_name("cabi_realloc$42"));
        // Non-digit / mixed / empty suffixes are NOT ours — keep them.
        assert!(!is_vestigial_realloc_export_name("cabi_realloc$"));
        assert!(!is_vestigial_realloc_export_name("cabi_realloc$foo"));
        assert!(!is_vestigial_realloc_export_name("cabi_realloc$1a"));
        assert!(!is_vestigial_realloc_export_name("cabi_realloc$notdigits"));
        assert!(!is_vestigial_realloc_export_name("cabi_realloc_extra"));
        assert!(!is_vestigial_realloc_export_name("my_cabi_realloc"));
    }

    // --- #298 FINDING 1: memory.grow reachability -----------------------

    /// A grow reachable ONLY via the (to-be-dropped) `cabi_realloc` export is
    /// dead: no live root reaches it.
    #[test]
    fn grow_only_under_vestigial_realloc_is_dead() {
        let bytes = module(
            r#"(module
                (memory 1)
                (func $realloc (export "cabi_realloc")
                    (param i32 i32 i32 i32) (result i32)
                    i32.const 1 memory.grow drop i32.const 0)
                (func (export "compute") (result i32) i32.const 7))"#,
        );
        assert!(!module_has_reachable_memory_grow(&bytes));
    }

    /// A grow in a LIVE export's own body is reachable ⇒ allocator is live.
    #[test]
    fn grow_in_live_export_is_reachable() {
        let bytes = module(
            r#"(module
                (memory 1)
                (func $realloc (export "cabi_realloc")
                    (param i32 i32 i32 i32) (result i32) i32.const 0)
                (func (export "compute") (result i32)
                    i32.const 1 memory.grow drop i32.const 7))"#,
        );
        assert!(module_has_reachable_memory_grow(&bytes));
    }

    /// A grow buried in a helper CALLED (transitively) by a live export is
    /// reachable — the naive "grow not in the export body" check would miss it.
    #[test]
    fn grow_transitively_reachable_from_live_export() {
        let bytes = module(
            r#"(module
                (memory 1)
                (func $sbrk (result i32) i32.const 1 memory.grow)
                (func $dlmalloc (result i32) call $sbrk)
                (func (export "compute") (result i32) call $dlmalloc))"#,
        );
        assert!(module_has_reachable_memory_grow(&bytes));
    }

    /// A grow inside a helper called ONLY by `cabi_realloc` (the dlmalloc/sbrk
    /// shape) is dead once that export is dropped.
    #[test]
    fn grow_transitively_under_only_realloc_is_dead() {
        let bytes = module(
            r#"(module
                (memory 1)
                (func $sbrk (result i32) i32.const 1 memory.grow)
                (func $dlmalloc (result i32) call $sbrk)
                (func $realloc (export "cabi_realloc")
                    (param i32 i32 i32 i32) (result i32) call $dlmalloc)
                (func (export "compute") (result i32) i32.const 7))"#,
        );
        assert!(!module_has_reachable_memory_grow(&bytes));
    }

    /// A grow in a function reachable only via `call_indirect` (an element
    /// segment) is treated as live — the elem entry is a conservative root.
    #[test]
    fn grow_via_elem_segment_is_reachable() {
        let bytes = module(
            r#"(module
                (memory 1)
                (table 1 funcref)
                (elem (i32.const 0) $grower)
                (func $grower (result i32) i32.const 1 memory.grow)
                (func (export "compute") (result i32) i32.const 7))"#,
        );
        assert!(module_has_reachable_memory_grow(&bytes));
    }

    /// The `start` function is a root: a grow reachable from it is live.
    #[test]
    fn grow_reachable_from_start_is_reachable() {
        let bytes = module(
            r#"(module
                (memory 1)
                (start $init)
                (func $init i32.const 1 memory.grow drop)
                (func (export "compute") (result i32) i32.const 7))"#,
        );
        assert!(module_has_reachable_memory_grow(&bytes));
    }

    /// A grow reachable only via the `cabi_realloc$<digits>` suffixed export is
    /// still dead (that name is dropped too).
    #[test]
    fn grow_under_suffixed_realloc_is_dead() {
        let bytes = module(
            r#"(module
                (memory 1)
                (func $realloc (export "cabi_realloc$0")
                    (param i32 i32 i32 i32) (result i32)
                    i32.const 1 memory.grow drop i32.const 0)
                (func (export "compute") (result i32) i32.const 7))"#,
        );
        assert!(!module_has_reachable_memory_grow(&bytes));
    }

    /// But a grow under a LOOK-ALIKE `cabi_realloc$notdigits` export (which is
    /// NOT dropped, so stays a live root) is reachable.
    #[test]
    fn grow_under_lookalike_realloc_is_reachable() {
        let bytes = module(
            r#"(module
                (memory 1)
                (func $realloc (export "cabi_realloc$notdigits")
                    (param i32 i32 i32 i32) (result i32)
                    i32.const 1 memory.grow drop i32.const 0)
                (func (export "compute") (result i32) i32.const 7))"#,
        );
        assert!(module_has_reachable_memory_grow(&bytes));
    }

    /// Fail-safe: unparseable bytes count as having a live grow.
    #[test]
    fn malformed_input_counts_as_reachable_grow() {
        assert!(module_has_reachable_memory_grow(&[
            0x00, 0x61, 0x73, 0x6d, 0xff
        ]));
    }
}
