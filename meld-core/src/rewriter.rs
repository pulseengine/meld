//! Function body rewriting for index remapping
//!
//! This module handles extracting function bodies from WebAssembly modules
//! and rewriting all index references (functions, globals, tables, memories, types)
//! to use the new indices in the merged module.

use crate::{Error, Result};
use std::collections::HashMap;
use wasm_encoder::{BlockType, Function, Instruction, MemArg};
use wasmparser::{
    BlockType as WpBlockType, FunctionBody, MemArg as WpMemArg, Operator, OperatorsReader,
};

/// Index mappings for rewriting
#[derive(Debug, Clone, Default)]
pub struct IndexMaps {
    /// Function index remapping: old -> new
    pub functions: HashMap<u32, u32>,
    /// Type index remapping: old -> new
    pub types: HashMap<u32, u32>,
    /// Global index remapping: old -> new
    pub globals: HashMap<u32, u32>,
    /// Table index remapping: old -> new
    pub tables: HashMap<u32, u32>,
    /// Memory index remapping: old -> new
    pub memories: HashMap<u32, u32>,
    /// Memory base offset in bytes (for shared-memory rebasing)
    pub memory_base_offset: u64,
    /// Whether address rebasing is enabled
    pub address_rebasing: bool,
    /// Whether the memory uses 64-bit addressing
    pub memory64: bool,
    /// Initial memory size in pages for the module (used for rebased memory.size)
    pub memory_initial_pages: Option<u64>,
    /// Scratch locals used for address rebasing
    pub rebase_locals: Option<RebaseLocals>,
}

#[derive(Debug, Clone, Copy)]
pub struct RebaseLocals {
    pub addr0: u32,
    pub addr1: u32,
    pub addr2: u32,
    pub value: u32,
}

impl IndexMaps {
    /// Create new empty index maps
    pub fn new() -> Self {
        Self::default()
    }

    /// Remap a function index
    pub fn remap_func(&self, idx: u32) -> u32 {
        *self.functions.get(&idx).unwrap_or(&idx)
    }

    /// Remap a type index
    pub fn remap_type(&self, idx: u32) -> u32 {
        *self.types.get(&idx).unwrap_or(&idx)
    }

    /// Remap a global index
    pub fn remap_global(&self, idx: u32) -> u32 {
        *self.globals.get(&idx).unwrap_or(&idx)
    }

    /// Remap a table index
    pub fn remap_table(&self, idx: u32) -> u32 {
        *self.tables.get(&idx).unwrap_or(&idx)
    }

    /// Remap a memory index
    pub fn remap_memory(&self, idx: u32) -> u32 {
        *self.memories.get(&idx).unwrap_or(&idx)
    }
}

/// Rewrite a function body with new index mappings
pub fn rewrite_function_body(
    body: &FunctionBody<'_>,
    param_count: u32,
    maps: &IndexMaps,
) -> Result<Function> {
    let locals_reader = body.get_locals_reader()?;

    // Collect locals
    let mut locals: Vec<(u32, wasm_encoder::ValType)> = Vec::new();
    let mut local_count: u32 = 0;
    for local in locals_reader {
        let (count, ty) = local?;
        locals.push((count, convert_val_type(ty)));
        local_count = local_count.saturating_add(count);
    }

    let needs_rebase_locals = if maps.address_rebasing {
        let mut needs = false;
        let ops_reader = body.get_operators_reader()?;
        for op in ops_reader {
            match op? {
                Operator::MemoryCopy { .. }
                | Operator::MemoryFill { .. }
                | Operator::MemoryInit { .. } => {
                    needs = true;
                    break;
                }
                _ => {}
            }
        }
        needs
    } else {
        false
    };

    let mut maps = maps.clone();
    if needs_rebase_locals {
        let address_type = if maps.memory64 {
            wasm_encoder::ValType::I64
        } else {
            wasm_encoder::ValType::I32
        };
        locals.push((1, address_type));
        locals.push((1, address_type));
        locals.push((1, address_type));
        locals.push((1, wasm_encoder::ValType::I32));

        let base_index = param_count + local_count;
        maps.rebase_locals = Some(RebaseLocals {
            addr0: base_index,
            addr1: base_index + 1,
            addr2: base_index + 2,
            value: base_index + 3,
        });
    }

    let mut func = Function::new(locals);

    // Get operators and rewrite them
    let ops_reader = body.get_operators_reader()?;
    rewrite_operators(ops_reader, &maps, &mut func)?;

    Ok(func)
}

/// Rewrite operators in a function body
fn rewrite_operators(
    reader: OperatorsReader<'_>,
    maps: &IndexMaps,
    func: &mut Function,
) -> Result<()> {
    for op in reader {
        let op = op?;
        let instrs = rewrite_operator(op, maps)?;
        for instr in instrs {
            func.instruction(&instr);
        }
    }
    Ok(())
}

/// Convert a wasmparser operator to wasm-encoder instruction with index remapping
fn rewrite_operator(op: Operator<'_>, maps: &IndexMaps) -> Result<Vec<Instruction<'static>>> {
    use Operator::*;

    let instr = match op {
        // Control flow
        Unreachable => Instruction::Unreachable,
        Nop => Instruction::Nop,
        Block { blockty } => Instruction::Block(convert_block_type(blockty, maps)),
        Loop { blockty } => Instruction::Loop(convert_block_type(blockty, maps)),
        If { blockty } => Instruction::If(convert_block_type(blockty, maps)),
        Else => Instruction::Else,
        End => Instruction::End,
        Br { relative_depth } => Instruction::Br(relative_depth),
        BrIf { relative_depth } => Instruction::BrIf(relative_depth),
        BrTable { targets } => {
            let table: Vec<u32> = targets.targets().map(|t| t.unwrap()).collect();
            let default = targets.default();
            Instruction::BrTable(table.into(), default)
        }
        Return => Instruction::Return,

        // Calls - these need index remapping
        Call { function_index } => Instruction::Call(maps.remap_func(function_index)),
        CallIndirect {
            type_index,
            table_index,
            ..
        } => Instruction::CallIndirect {
            type_index: maps.remap_type(type_index),
            table_index: maps.remap_table(table_index),
        },

        // Reference types
        RefNull { hty } => Instruction::RefNull(convert_heap_type(hty)),
        RefIsNull => Instruction::RefIsNull,
        RefFunc { function_index } => Instruction::RefFunc(maps.remap_func(function_index)),

        // Parametric
        Drop => Instruction::Drop,
        Select => Instruction::Select,

        // Variable access
        LocalGet { local_index } => Instruction::LocalGet(local_index),
        LocalSet { local_index } => Instruction::LocalSet(local_index),
        LocalTee { local_index } => Instruction::LocalTee(local_index),
        GlobalGet { global_index } => Instruction::GlobalGet(maps.remap_global(global_index)),
        GlobalSet { global_index } => Instruction::GlobalSet(maps.remap_global(global_index)),

        // Table operations - need table index remapping
        TableGet { table } => Instruction::TableGet(maps.remap_table(table)),
        TableSet { table } => Instruction::TableSet(maps.remap_table(table)),
        TableGrow { table } => Instruction::TableGrow(maps.remap_table(table)),
        TableSize { table } => Instruction::TableSize(maps.remap_table(table)),
        TableFill { table } => Instruction::TableFill(maps.remap_table(table)),
        TableCopy {
            dst_table,
            src_table,
        } => Instruction::TableCopy {
            src_table: maps.remap_table(src_table),
            dst_table: maps.remap_table(dst_table),
        },
        TableInit { elem_index, table } => Instruction::TableInit {
            elem_index,
            table: maps.remap_table(table),
        },
        ElemDrop { elem_index } => Instruction::ElemDrop(elem_index),

        // Memory operations - need memory index remapping
        I32Load { memarg } => Instruction::I32Load(convert_memarg(memarg, maps)?),
        I64Load { memarg } => Instruction::I64Load(convert_memarg(memarg, maps)?),
        F32Load { memarg } => Instruction::F32Load(convert_memarg(memarg, maps)?),
        F64Load { memarg } => Instruction::F64Load(convert_memarg(memarg, maps)?),
        I32Load8S { memarg } => Instruction::I32Load8S(convert_memarg(memarg, maps)?),
        I32Load8U { memarg } => Instruction::I32Load8U(convert_memarg(memarg, maps)?),
        I32Load16S { memarg } => Instruction::I32Load16S(convert_memarg(memarg, maps)?),
        I32Load16U { memarg } => Instruction::I32Load16U(convert_memarg(memarg, maps)?),
        I64Load8S { memarg } => Instruction::I64Load8S(convert_memarg(memarg, maps)?),
        I64Load8U { memarg } => Instruction::I64Load8U(convert_memarg(memarg, maps)?),
        I64Load16S { memarg } => Instruction::I64Load16S(convert_memarg(memarg, maps)?),
        I64Load16U { memarg } => Instruction::I64Load16U(convert_memarg(memarg, maps)?),
        I64Load32S { memarg } => Instruction::I64Load32S(convert_memarg(memarg, maps)?),
        I64Load32U { memarg } => Instruction::I64Load32U(convert_memarg(memarg, maps)?),
        I32Store { memarg } => Instruction::I32Store(convert_memarg(memarg, maps)?),
        I64Store { memarg } => Instruction::I64Store(convert_memarg(memarg, maps)?),
        F32Store { memarg } => Instruction::F32Store(convert_memarg(memarg, maps)?),
        F64Store { memarg } => Instruction::F64Store(convert_memarg(memarg, maps)?),
        I32Store8 { memarg } => Instruction::I32Store8(convert_memarg(memarg, maps)?),
        I32Store16 { memarg } => Instruction::I32Store16(convert_memarg(memarg, maps)?),
        I64Store8 { memarg } => Instruction::I64Store8(convert_memarg(memarg, maps)?),
        I64Store16 { memarg } => Instruction::I64Store16(convert_memarg(memarg, maps)?),
        I64Store32 { memarg } => Instruction::I64Store32(convert_memarg(memarg, maps)?),
        MemorySize { mem, .. } => {
            if maps.address_rebasing {
                let pages = maps.memory_initial_pages.ok_or_else(|| {
                    Error::UnsupportedFeature(
                        "memory.size requires a module memory in rebasing mode".to_string(),
                    )
                })?;
                if maps.memory64 {
                    let pages_i64 = i64::try_from(pages).map_err(|_| {
                        Error::UnsupportedFeature(
                            "memory.size page count exceeds i64 range".to_string(),
                        )
                    })?;
                    return Ok(vec![Instruction::I64Const(pages_i64)]);
                }
                let pages_u32 = u32::try_from(pages).map_err(|_| {
                    Error::UnsupportedFeature(
                        "memory.size page count exceeds i32 range".to_string(),
                    )
                })?;
                return Ok(vec![Instruction::I32Const(pages_u32 as i32)]);
            }
            Instruction::MemorySize(maps.remap_memory(mem))
        }
        MemoryGrow { mem, .. } => {
            if maps.address_rebasing {
                return Err(Error::UnsupportedFeature(
                    "memory.grow not supported with address rebasing".to_string(),
                ));
            }
            Instruction::MemoryGrow(maps.remap_memory(mem))
        }
        MemoryInit { data_index, mem } => {
            return rewrite_memory_init(data_index, mem, maps);
        }
        DataDrop { data_index } => Instruction::DataDrop(data_index),
        MemoryCopy { dst_mem, src_mem } => {
            return rewrite_memory_copy(src_mem, dst_mem, maps);
        }
        MemoryFill { mem } => {
            return rewrite_memory_fill(mem, maps);
        }

        // Constants
        I32Const { value } => Instruction::I32Const(value),
        I64Const { value } => Instruction::I64Const(value),
        F32Const { value } => Instruction::F32Const(f32::from_bits(value.bits())),
        F64Const { value } => Instruction::F64Const(f64::from_bits(value.bits())),

        // Comparison operators
        I32Eqz => Instruction::I32Eqz,
        I32Eq => Instruction::I32Eq,
        I32Ne => Instruction::I32Ne,
        I32LtS => Instruction::I32LtS,
        I32LtU => Instruction::I32LtU,
        I32GtS => Instruction::I32GtS,
        I32GtU => Instruction::I32GtU,
        I32LeS => Instruction::I32LeS,
        I32LeU => Instruction::I32LeU,
        I32GeS => Instruction::I32GeS,
        I32GeU => Instruction::I32GeU,
        I64Eqz => Instruction::I64Eqz,
        I64Eq => Instruction::I64Eq,
        I64Ne => Instruction::I64Ne,
        I64LtS => Instruction::I64LtS,
        I64LtU => Instruction::I64LtU,
        I64GtS => Instruction::I64GtS,
        I64GtU => Instruction::I64GtU,
        I64LeS => Instruction::I64LeS,
        I64LeU => Instruction::I64LeU,
        I64GeS => Instruction::I64GeS,
        I64GeU => Instruction::I64GeU,
        F32Eq => Instruction::F32Eq,
        F32Ne => Instruction::F32Ne,
        F32Lt => Instruction::F32Lt,
        F32Gt => Instruction::F32Gt,
        F32Le => Instruction::F32Le,
        F32Ge => Instruction::F32Ge,
        F64Eq => Instruction::F64Eq,
        F64Ne => Instruction::F64Ne,
        F64Lt => Instruction::F64Lt,
        F64Gt => Instruction::F64Gt,
        F64Le => Instruction::F64Le,
        F64Ge => Instruction::F64Ge,

        // Numeric operators
        I32Clz => Instruction::I32Clz,
        I32Ctz => Instruction::I32Ctz,
        I32Popcnt => Instruction::I32Popcnt,
        I32Add => Instruction::I32Add,
        I32Sub => Instruction::I32Sub,
        I32Mul => Instruction::I32Mul,
        I32DivS => Instruction::I32DivS,
        I32DivU => Instruction::I32DivU,
        I32RemS => Instruction::I32RemS,
        I32RemU => Instruction::I32RemU,
        I32And => Instruction::I32And,
        I32Or => Instruction::I32Or,
        I32Xor => Instruction::I32Xor,
        I32Shl => Instruction::I32Shl,
        I32ShrS => Instruction::I32ShrS,
        I32ShrU => Instruction::I32ShrU,
        I32Rotl => Instruction::I32Rotl,
        I32Rotr => Instruction::I32Rotr,
        I64Clz => Instruction::I64Clz,
        I64Ctz => Instruction::I64Ctz,
        I64Popcnt => Instruction::I64Popcnt,
        I64Add => Instruction::I64Add,
        I64Sub => Instruction::I64Sub,
        I64Mul => Instruction::I64Mul,
        I64DivS => Instruction::I64DivS,
        I64DivU => Instruction::I64DivU,
        I64RemS => Instruction::I64RemS,
        I64RemU => Instruction::I64RemU,
        I64And => Instruction::I64And,
        I64Or => Instruction::I64Or,
        I64Xor => Instruction::I64Xor,
        I64Shl => Instruction::I64Shl,
        I64ShrS => Instruction::I64ShrS,
        I64ShrU => Instruction::I64ShrU,
        I64Rotl => Instruction::I64Rotl,
        I64Rotr => Instruction::I64Rotr,
        F32Abs => Instruction::F32Abs,
        F32Neg => Instruction::F32Neg,
        F32Ceil => Instruction::F32Ceil,
        F32Floor => Instruction::F32Floor,
        F32Trunc => Instruction::F32Trunc,
        F32Nearest => Instruction::F32Nearest,
        F32Sqrt => Instruction::F32Sqrt,
        F32Add => Instruction::F32Add,
        F32Sub => Instruction::F32Sub,
        F32Mul => Instruction::F32Mul,
        F32Div => Instruction::F32Div,
        F32Min => Instruction::F32Min,
        F32Max => Instruction::F32Max,
        F32Copysign => Instruction::F32Copysign,
        F64Abs => Instruction::F64Abs,
        F64Neg => Instruction::F64Neg,
        F64Ceil => Instruction::F64Ceil,
        F64Floor => Instruction::F64Floor,
        F64Trunc => Instruction::F64Trunc,
        F64Nearest => Instruction::F64Nearest,
        F64Sqrt => Instruction::F64Sqrt,
        F64Add => Instruction::F64Add,
        F64Sub => Instruction::F64Sub,
        F64Mul => Instruction::F64Mul,
        F64Div => Instruction::F64Div,
        F64Min => Instruction::F64Min,
        F64Max => Instruction::F64Max,
        F64Copysign => Instruction::F64Copysign,

        // Conversions
        I32WrapI64 => Instruction::I32WrapI64,
        I32TruncF32S => Instruction::I32TruncF32S,
        I32TruncF32U => Instruction::I32TruncF32U,
        I32TruncF64S => Instruction::I32TruncF64S,
        I32TruncF64U => Instruction::I32TruncF64U,
        I64ExtendI32S => Instruction::I64ExtendI32S,
        I64ExtendI32U => Instruction::I64ExtendI32U,
        I64TruncF32S => Instruction::I64TruncF32S,
        I64TruncF32U => Instruction::I64TruncF32U,
        I64TruncF64S => Instruction::I64TruncF64S,
        I64TruncF64U => Instruction::I64TruncF64U,
        F32ConvertI32S => Instruction::F32ConvertI32S,
        F32ConvertI32U => Instruction::F32ConvertI32U,
        F32ConvertI64S => Instruction::F32ConvertI64S,
        F32ConvertI64U => Instruction::F32ConvertI64U,
        F32DemoteF64 => Instruction::F32DemoteF64,
        F64ConvertI32S => Instruction::F64ConvertI32S,
        F64ConvertI32U => Instruction::F64ConvertI32U,
        F64ConvertI64S => Instruction::F64ConvertI64S,
        F64ConvertI64U => Instruction::F64ConvertI64U,
        F64PromoteF32 => Instruction::F64PromoteF32,
        I32ReinterpretF32 => Instruction::I32ReinterpretF32,
        I64ReinterpretF64 => Instruction::I64ReinterpretF64,
        F32ReinterpretI32 => Instruction::F32ReinterpretI32,
        F64ReinterpretI64 => Instruction::F64ReinterpretI64,

        // Sign extension
        I32Extend8S => Instruction::I32Extend8S,
        I32Extend16S => Instruction::I32Extend16S,
        I64Extend8S => Instruction::I64Extend8S,
        I64Extend16S => Instruction::I64Extend16S,
        I64Extend32S => Instruction::I64Extend32S,

        // Saturating truncation
        I32TruncSatF32S => Instruction::I32TruncSatF32S,
        I32TruncSatF32U => Instruction::I32TruncSatF32U,
        I32TruncSatF64S => Instruction::I32TruncSatF64S,
        I32TruncSatF64U => Instruction::I32TruncSatF64U,
        I64TruncSatF32S => Instruction::I64TruncSatF32S,
        I64TruncSatF32U => Instruction::I64TruncSatF32U,
        I64TruncSatF64S => Instruction::I64TruncSatF64S,
        I64TruncSatF64U => Instruction::I64TruncSatF64U,

        // Catch-all for unsupported operators
        _ => {
            return Err(Error::UnsupportedFeature(format!(
                "unsupported instruction: {:?}",
                op
            )));
        }
    };

    Ok(vec![instr])
}

fn rewrite_memory_copy(
    src_mem: u32,
    dst_mem: u32,
    maps: &IndexMaps,
) -> Result<Vec<Instruction<'static>>> {
    if !maps.address_rebasing {
        return Ok(vec![Instruction::MemoryCopy {
            src_mem: maps.remap_memory(src_mem),
            dst_mem: maps.remap_memory(dst_mem),
        }]);
    }

    let locals = maps.rebase_locals.ok_or_else(|| {
        Error::UnsupportedFeature("address rebasing requires scratch locals".to_string())
    })?;

    let mut instrs = Vec::new();
    instrs.push(Instruction::LocalSet(locals.addr2)); // len
    instrs.push(Instruction::LocalSet(locals.addr1)); // src
    instrs.push(Instruction::LocalSet(locals.addr0)); // dst
    append_rebased_address(&mut instrs, maps, locals.addr0)?;
    append_rebased_address(&mut instrs, maps, locals.addr1)?;
    instrs.push(Instruction::LocalGet(locals.addr2));
    instrs.push(Instruction::MemoryCopy {
        src_mem: maps.remap_memory(src_mem),
        dst_mem: maps.remap_memory(dst_mem),
    });

    Ok(instrs)
}

fn rewrite_memory_fill(mem: u32, maps: &IndexMaps) -> Result<Vec<Instruction<'static>>> {
    if !maps.address_rebasing {
        return Ok(vec![Instruction::MemoryFill(maps.remap_memory(mem))]);
    }

    let locals = maps.rebase_locals.ok_or_else(|| {
        Error::UnsupportedFeature("address rebasing requires scratch locals".to_string())
    })?;

    let mut instrs = Vec::new();
    instrs.push(Instruction::LocalSet(locals.addr2)); // len
    instrs.push(Instruction::LocalSet(locals.value)); // value (i32)
    instrs.push(Instruction::LocalSet(locals.addr0)); // dst
    append_rebased_address(&mut instrs, maps, locals.addr0)?;
    instrs.push(Instruction::LocalGet(locals.value));
    instrs.push(Instruction::LocalGet(locals.addr2));
    instrs.push(Instruction::MemoryFill(maps.remap_memory(mem)));

    Ok(instrs)
}

fn rewrite_memory_init(
    data_index: u32,
    mem: u32,
    maps: &IndexMaps,
) -> Result<Vec<Instruction<'static>>> {
    if !maps.address_rebasing {
        return Ok(vec![Instruction::MemoryInit {
            mem: maps.remap_memory(mem),
            data_index,
        }]);
    }

    let locals = maps.rebase_locals.ok_or_else(|| {
        Error::UnsupportedFeature("address rebasing requires scratch locals".to_string())
    })?;

    let mut instrs = Vec::new();
    instrs.push(Instruction::LocalSet(locals.addr2)); // len
    instrs.push(Instruction::LocalSet(locals.addr1)); // src
    instrs.push(Instruction::LocalSet(locals.addr0)); // dst
    append_rebased_address(&mut instrs, maps, locals.addr0)?;
    instrs.push(Instruction::LocalGet(locals.addr1));
    instrs.push(Instruction::LocalGet(locals.addr2));
    instrs.push(Instruction::MemoryInit {
        mem: maps.remap_memory(mem),
        data_index,
    });

    Ok(instrs)
}

fn append_rebased_address(
    instrs: &mut Vec<Instruction<'static>>,
    maps: &IndexMaps,
    local_index: u32,
) -> Result<()> {
    instrs.push(Instruction::LocalGet(local_index));
    if maps.memory_base_offset != 0 {
        instrs.push(base_const_instruction(maps)?);
        instrs.push(base_add_instruction(maps));
    }
    Ok(())
}

fn base_const_instruction(maps: &IndexMaps) -> Result<Instruction<'static>> {
    if maps.memory64 {
        Ok(Instruction::I64Const(maps.memory_base_offset as i64))
    } else {
        let base = u32::try_from(maps.memory_base_offset).map_err(|_| {
            Error::UnsupportedFeature("address rebasing base offset overflow".to_string())
        })?;
        Ok(Instruction::I32Const(base as i32))
    }
}

fn base_add_instruction(maps: &IndexMaps) -> Instruction<'static> {
    if maps.memory64 {
        Instruction::I64Add
    } else {
        Instruction::I32Add
    }
}

/// Convert wasmparser BlockType to wasm-encoder BlockType
fn convert_block_type(bt: WpBlockType, maps: &IndexMaps) -> BlockType {
    match bt {
        WpBlockType::Empty => BlockType::Empty,
        WpBlockType::Type(ty) => BlockType::Result(convert_val_type(ty)),
        WpBlockType::FuncType(idx) => BlockType::FunctionType(maps.remap_type(idx)),
    }
}

/// Convert wasmparser MemArg to wasm-encoder MemArg
fn convert_memarg(ma: WpMemArg, maps: &IndexMaps) -> Result<MemArg> {
    let offset =
        ma.offset
            .checked_add(maps.memory_base_offset)
            .ok_or(Error::UnsupportedFeature(
                "memory offset overflow during rebasing".to_string(),
            ))?;
    Ok(MemArg {
        offset,
        align: ma.align as u32,
        memory_index: maps.remap_memory(ma.memory),
    })
}

/// Convert wasmparser ValType to wasm-encoder ValType
fn convert_val_type(ty: wasmparser::ValType) -> wasm_encoder::ValType {
    match ty {
        wasmparser::ValType::I32 => wasm_encoder::ValType::I32,
        wasmparser::ValType::I64 => wasm_encoder::ValType::I64,
        wasmparser::ValType::F32 => wasm_encoder::ValType::F32,
        wasmparser::ValType::F64 => wasm_encoder::ValType::F64,
        wasmparser::ValType::V128 => wasm_encoder::ValType::V128,
        wasmparser::ValType::Ref(rt) => wasm_encoder::ValType::Ref(convert_ref_type(rt)),
    }
}

/// Convert wasmparser RefType to wasm-encoder RefType
fn convert_ref_type(rt: wasmparser::RefType) -> wasm_encoder::RefType {
    if rt.is_func_ref() {
        wasm_encoder::RefType::FUNCREF
    } else if rt.is_extern_ref() {
        wasm_encoder::RefType::EXTERNREF
    } else {
        // Default to funcref for other reference types
        wasm_encoder::RefType::FUNCREF
    }
}

/// Convert wasmparser HeapType to wasm-encoder HeapType
fn convert_heap_type(ht: wasmparser::HeapType) -> wasm_encoder::HeapType {
    match ht {
        wasmparser::HeapType::Concrete(_) => wasm_encoder::HeapType::Concrete(0),
        wasmparser::HeapType::Abstract { shared: _, ty } => match ty {
            wasmparser::AbstractHeapType::Func => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::Func,
            },
            wasmparser::AbstractHeapType::Extern => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::Extern,
            },
            _ => wasm_encoder::HeapType::Abstract {
                shared: false,
                ty: wasm_encoder::AbstractHeapType::Func,
            },
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasmparser::Operator;

    #[test]
    fn test_index_maps_remap() {
        let mut maps = IndexMaps::new();
        maps.functions.insert(0, 5);
        maps.functions.insert(1, 6);
        maps.globals.insert(0, 10);

        assert_eq!(maps.remap_func(0), 5);
        assert_eq!(maps.remap_func(1), 6);
        assert_eq!(maps.remap_func(2), 2); // Not mapped, returns original
        assert_eq!(maps.remap_global(0), 10);
    }

    #[test]
    fn test_convert_block_type() {
        let maps = IndexMaps::new();

        let empty = convert_block_type(WpBlockType::Empty, &maps);
        assert!(matches!(empty, BlockType::Empty));

        let result = convert_block_type(WpBlockType::Type(wasmparser::ValType::I32), &maps);
        assert!(matches!(
            result,
            BlockType::Result(wasm_encoder::ValType::I32)
        ));
    }

    #[test]
    fn test_rewrite_memory_copy_rebased() {
        let mut maps = IndexMaps::new();
        maps.address_rebasing = true;
        maps.memory_base_offset = 16;
        maps.memory64 = false;
        maps.rebase_locals = Some(RebaseLocals {
            addr0: 0,
            addr1: 1,
            addr2: 2,
            value: 3,
        });

        let instrs = rewrite_operator(
            Operator::MemoryCopy {
                src_mem: 0,
                dst_mem: 0,
            },
            &maps,
        )
        .unwrap();

        assert!(
            instrs
                .iter()
                .any(|instr| matches!(instr, Instruction::I32Const(16)))
        );
        assert!(matches!(
            instrs.last(),
            Some(Instruction::MemoryCopy { .. })
        ));
    }

    #[test]
    fn test_rewrite_memory_fill_rebased() {
        let mut maps = IndexMaps::new();
        maps.address_rebasing = true;
        maps.memory_base_offset = 8;
        maps.memory64 = false;
        maps.rebase_locals = Some(RebaseLocals {
            addr0: 0,
            addr1: 1,
            addr2: 2,
            value: 3,
        });

        let instrs = rewrite_operator(Operator::MemoryFill { mem: 0 }, &maps).unwrap();

        assert!(
            instrs
                .iter()
                .any(|instr| matches!(instr, Instruction::I32Const(8)))
        );
        assert!(matches!(instrs.last(), Some(Instruction::MemoryFill(_))));
    }

    #[test]
    fn test_rewrite_memory_init_rebased() {
        let mut maps = IndexMaps::new();
        maps.address_rebasing = true;
        maps.memory_base_offset = 4;
        maps.memory64 = false;
        maps.rebase_locals = Some(RebaseLocals {
            addr0: 0,
            addr1: 1,
            addr2: 2,
            value: 3,
        });

        let instrs = rewrite_operator(
            Operator::MemoryInit {
                data_index: 0,
                mem: 0,
            },
            &maps,
        )
        .unwrap();

        assert!(
            instrs
                .iter()
                .any(|instr| matches!(instr, Instruction::I32Const(4)))
        );
        assert!(matches!(
            instrs.last(),
            Some(Instruction::MemoryInit { .. })
        ));
    }

    #[test]
    fn test_rewrite_memory_size_rebased_const() {
        let mut maps = IndexMaps::new();
        maps.address_rebasing = true;
        maps.memory64 = false;
        maps.memory_initial_pages = Some(3);

        let instrs = rewrite_operator(Operator::MemorySize { mem: 0 }, &maps).unwrap();
        assert!(matches!(instrs.as_slice(), [Instruction::I32Const(3)]));
    }

    #[test]
    fn test_rewrite_memory_grow_rebased_fails() {
        let mut maps = IndexMaps::new();
        maps.address_rebasing = true;

        assert!(rewrite_operator(Operator::MemoryGrow { mem: 0 }, &maps).is_err());
    }
}
