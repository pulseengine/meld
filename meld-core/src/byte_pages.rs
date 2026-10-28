//! SR-107 / #530: output-side soundness guard for byte-paged memories.
//!
//! `--memory-page-size 1` declares each packed memory with the
//! custom-page-sizes proposal's `(pagesize 1)`. Two things would then silently
//! change meaning, and this module refuses both on the *emitted bytes* rather
//! than relying on the merger having avoided them:
//!
//! * `memory.size` / `memory.grow` return and take a count of PAGES. On a
//!   `(pagesize 1)` memory that count is bytes, so an allocator that does
//!   `memory.grow 1` to get 64 KiB would get one byte.
//! * An active data segment that does not fit `[0, minimum)` of a memory whose
//!   `minimum == maximum` is a fixed size: it would fail at instantiation, or
//!   (with a non-constant offset) cannot be proven to fit at all.

use crate::{Error, Result};
use std::collections::HashMap;
use wasmparser::{DataKind, KnownCustom, Name, Operator, Parser, Payload};

/// Check a fused core module's byte-paged memories (those declared with
/// `page_size_log2 == Some(0)`).
///
/// Fails when:
///   * any function contains `memory.size` or `memory.grow` targeting a
///     byte-paged memory (the error names the function);
///   * an active data segment targets a byte-paged memory with a
///     non-constant offset, or ends past the memory's `minimum` bytes;
///   * a byte-paged memory is not fixed-size (`minimum != maximum`).
///
/// A module with no byte-paged memory passes trivially.
pub fn check_byte_paged_memories(module_bytes: &[u8]) -> Result<()> {
    // Memory index space: imported memories first, then defined ones.
    // Value: `Some((minimum, maximum))` when byte-paged.
    let mut memories: Vec<Option<(u64, Option<u64>)>> = Vec::new();
    let mut imported_funcs = 0u32;
    let mut func_export_names: HashMap<u32, String> = HashMap::new();
    let mut func_debug_names: HashMap<u32, String> = HashMap::new();
    // (memory index, function index, op) for each offending instruction.
    let mut offenders: Vec<(u32, u32, &'static str)> = Vec::new();
    let mut data: Vec<(u32, Option<u64>, u64)> = Vec::new();
    let mut next_body = 0u32;

    let byte_paged = |m: &wasmparser::MemoryType| {
        (m.page_size_log2 == Some(0)).then_some((m.initial, m.maximum))
    };

    for payload in Parser::new(0).parse_all(module_bytes) {
        match payload? {
            Payload::ImportSection(reader) => {
                for import in reader.into_imports() {
                    match import?.ty {
                        wasmparser::TypeRef::Func(_) | wasmparser::TypeRef::FuncExact(_) => {
                            imported_funcs += 1
                        }
                        wasmparser::TypeRef::Memory(m) => memories.push(byte_paged(&m)),
                        _ => {}
                    }
                }
            }
            Payload::MemorySection(reader) => {
                for m in reader {
                    memories.push(byte_paged(&m?));
                }
            }
            Payload::ExportSection(reader) => {
                for e in reader {
                    let e = e?;
                    if e.kind == wasmparser::ExternalKind::Func {
                        func_export_names
                            .entry(e.index)
                            .or_insert_with(|| e.name.to_string());
                    }
                }
            }
            Payload::DataSection(reader) => {
                for d in reader {
                    let d = d?;
                    if let DataKind::Active {
                        memory_index,
                        offset_expr,
                    } = d.kind
                    {
                        let start = match crate::segments::parse_const_expr_with_value(&offset_expr)
                        {
                            Ok((_, Some(crate::segments::ConstExprValue::I32(v)))) => {
                                Some(v as u32 as u64)
                            }
                            Ok((_, Some(crate::segments::ConstExprValue::I64(v)))) => {
                                Some(v as u64)
                            }
                            _ => None,
                        };
                        data.push((memory_index, start, d.data.len() as u64));
                    }
                }
            }
            Payload::CustomSection(c) => {
                if let KnownCustom::Name(names) = c.as_known() {
                    for n in names.into_iter().flatten() {
                        if let Name::Function(map) = n {
                            for naming in map.into_iter().flatten() {
                                func_debug_names.insert(naming.index, naming.name.to_string());
                            }
                        }
                    }
                }
            }
            Payload::CodeSectionEntry(body) => {
                let func_index = imported_funcs + next_body;
                next_body += 1;
                let mut reader = body.get_operators_reader()?;
                while !reader.eof() {
                    match reader.read()? {
                        Operator::MemorySize { mem }
                            if memories.get(mem as usize).is_some_and(Option::is_some) =>
                        {
                            offenders.push((mem, func_index, "memory.size"));
                        }
                        Operator::MemoryGrow { mem }
                            if memories.get(mem as usize).is_some_and(Option::is_some) =>
                        {
                            offenders.push((mem, func_index, "memory.grow"));
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    let describe = |func: u32| -> String {
        let name = func_debug_names
            .get(&func)
            .or_else(|| func_export_names.get(&func));
        match name {
            Some(n) => format!("function {func} (`{n}`)"),
            None => format!("function {func}"),
        }
    };

    if let Some(&(mem, func, op)) = offenders.first() {
        return Err(Error::MemoryStrategyUnsupported(format!(
            "--memory-page-size 1: {} contains `{op}` on memory {mem}, which is declared \
             `(pagesize 1)`; its operand/result would silently change from 64 KiB pages to \
             bytes ({} such instruction(s) in total). Fuse without --memory-page-size 1, or \
             remove the allocator that grows memory.",
            describe(func),
            offenders.len()
        )));
    }

    for (idx, mem) in memories.iter().enumerate() {
        let Some((min, max)) = mem else { continue };
        if *max != Some(*min) {
            return Err(Error::MemoryStrategyUnsupported(format!(
                "--memory-page-size 1: memory {idx} is byte-paged but not fixed-size \
                 (minimum {min}, maximum {max:?})"
            )));
        }
    }

    for &(mem, start, len) in &data {
        let Some(Some((min, _))) = memories.get(mem as usize) else {
            continue;
        };
        let Some(start) = start else {
            return Err(Error::MemoryStrategyUnsupported(format!(
                "--memory-page-size 1: an active data segment of memory {mem} has a \
                 non-constant offset, so it cannot be proven to fit the {min}-byte memory"
            )));
        };
        let end = start.saturating_add(len);
        if end > *min {
            return Err(Error::MemoryStrategyUnsupported(format!(
                "--memory-page-size 1: an active data segment of memory {mem} ends at byte \
                 {end}, past the memory's {min}-byte extent"
            )));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_encoder::{
        CodeSection, DataSection, ExportKind, ExportSection, Function, FunctionSection,
        Instruction, MemorySection, MemoryType, Module, TypeSection,
    };

    fn module(
        page_size_log2: Option<u32>,
        min: u64,
        max: Option<u64>,
        body: &[Instruction<'static>],
        data: Option<(i32, usize)>,
    ) -> Vec<u8> {
        let mut m = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([], [wasm_encoder::ValType::I32]);
        m.section(&types);
        let mut funcs = FunctionSection::new();
        funcs.function(0);
        m.section(&funcs);
        let mut mems = MemorySection::new();
        mems.memory(MemoryType {
            minimum: min,
            maximum: max,
            memory64: false,
            shared: false,
            page_size_log2,
        });
        m.section(&mems);
        let mut exports = ExportSection::new();
        exports.export("probe", ExportKind::Func, 0);
        m.section(&exports);
        let mut code = CodeSection::new();
        let mut f = Function::new([]);
        for i in body {
            f.instruction(i);
        }
        f.instruction(&Instruction::End);
        code.function(&f);
        m.section(&code);
        if let Some((off, len)) = data {
            let mut d = DataSection::new();
            d.active(0, &wasm_encoder::ConstExpr::i32_const(off), vec![0u8; len]);
            m.section(&d);
        }
        m.finish()
    }

    // rivet: verifies SWV-119
    #[test]
    fn guard_fires_on_memory_size_and_grow_of_a_byte_paged_memory() {
        for (instr, op) in [
            (Instruction::MemorySize(0), "memory.size"),
            (Instruction::MemoryGrow(0), "memory.grow"),
        ] {
            let body: Vec<Instruction<'static>> = if op == "memory.grow" {
                vec![Instruction::I32Const(1), instr]
            } else {
                vec![instr]
            };
            let bytes = module(Some(0), 64, Some(64), &body, None);
            let err = check_byte_paged_memories(&bytes).unwrap_err().to_string();
            assert!(err.contains(op), "{err}");
            assert!(err.contains("`probe`"), "names the function: {err}");
            assert!(err.contains("function 0"), "{err}");
        }
    }

    // rivet: verifies SWV-119
    #[test]
    fn guard_is_silent_for_page_sized_memories_and_for_memories_without_the_ops() {
        // Same instructions, default page size: passes (negative control for
        // the guard's *targeting*, so it cannot fire on everything).
        let bytes = module(None, 1, Some(2), &[Instruction::MemorySize(0)], None);
        check_byte_paged_memories(&bytes).unwrap();
        // Byte-paged but no size/grow: passes.
        let bytes = module(Some(0), 64, Some(64), &[Instruction::I32Const(0)], None);
        check_byte_paged_memories(&bytes).unwrap();
    }

    // rivet: verifies SWV-119
    #[test]
    fn guard_checks_data_fits_and_fixed_size() {
        let body = [Instruction::I32Const(0)];
        let ok = module(Some(0), 64, Some(64), &body, Some((60, 4)));
        check_byte_paged_memories(&ok).unwrap();
        let past = module(Some(0), 64, Some(64), &body, Some((61, 4)));
        let err = check_byte_paged_memories(&past).unwrap_err().to_string();
        assert!(err.contains("past the memory's 64-byte extent"), "{err}");
        let growable = module(Some(0), 64, Some(128), &body, None);
        let err = check_byte_paged_memories(&growable)
            .unwrap_err()
            .to_string();
        assert!(err.contains("not fixed-size"), "{err}");
    }
}
