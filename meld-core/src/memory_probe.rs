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
}
