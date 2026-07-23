//! Element and data segment handling for module merging
//!
//! This module handles extracting, reindexing, and encoding element and data
//! segments from core modules during fusion.
//!
//! ## Element Segments
//!
//! Element segments populate tables with function references. They need:
//! - Table index remapping
//! - Function index remapping for all function refs
//! - Offset expression rewriting (if it references globals)
//!
//! ## Data Segments
//!
//! Data segments initialize linear memory. They need:
//! - Memory index remapping
//! - Offset expression rewriting (if it references globals)

use crate::parser::CoreModule;
use crate::rewriter::{IndexMaps, convert_abstract_heap_type};
use crate::{Error, Result};
use wasm_encoder::{
    ConstExpr, DataSegment, DataSegmentMode, ElementMode, ElementSection, ElementSegment, Elements,
    RefType,
};
use wasmparser::{DataSectionReader, ElementItems, ElementKind, ElementSectionReader, Operator};

/// A single operator inside a preserved wasm-2.0 extended-const expression
/// whose value is runtime-dependent because it begins with `global.get`
/// (the position-independent `__memory_base + N` / `__table_base + N` shape,
/// #338). Such an expression CANNOT be folded to a constant, so its operators
/// are kept verbatim and re-emitted, with `GlobalGet` indices remapped.
#[derive(Debug, Clone, PartialEq)]
pub enum ExtConstOp {
    GlobalGet(u32),
    I32Const(i32),
    I64Const(i64),
    I32Add,
    I32Sub,
    I32Mul,
    I64Add,
    I64Sub,
    I64Mul,
}

impl ExtConstOp {
    /// Remap any `GlobalGet` index in this operator using `f`.
    pub(crate) fn remap_global(&self, f: impl Fn(u32) -> u32) -> ExtConstOp {
        match self {
            ExtConstOp::GlobalGet(idx) => ExtConstOp::GlobalGet(f(*idx)),
            other => other.clone(),
        }
    }

    /// Append this operator to a `wasm_encoder::ConstExpr` builder.
    fn append_to(&self, ce: ConstExpr) -> ConstExpr {
        match self {
            ExtConstOp::GlobalGet(i) => ce.with_global_get(*i),
            ExtConstOp::I32Const(v) => ce.with_i32_const(*v),
            ExtConstOp::I64Const(v) => ce.with_i64_const(*v),
            ExtConstOp::I32Add => ce.with_i32_add(),
            ExtConstOp::I32Sub => ce.with_i32_sub(),
            ExtConstOp::I32Mul => ce.with_i32_mul(),
            ExtConstOp::I64Add => ce.with_i64_add(),
            ExtConstOp::I64Sub => ce.with_i64_sub(),
            ExtConstOp::I64Mul => ce.with_i64_mul(),
        }
    }
}

/// Build a `wasm_encoder::ConstExpr` from a full preserved extended-const
/// operator sequence (leading `global.get` + trailing arithmetic). The
/// `End` opcode is appended by `ConstExpr`'s own encoder.
pub(crate) fn ext_const_to_expr(ops: &[ExtConstOp]) -> ConstExpr {
    let mut ce = ConstExpr::empty();
    for op in ops {
        ce = op.append_to(ce);
    }
    ce
}

/// Evaluate a `global.get`-first extended-const i32 sequence (`base ± N …`) as a
/// concrete constant, substituting `base` for the leading `global.get`. Returns
/// `None` if the sequence isn't a pure i32 expression over a *single* (leading)
/// `global.get` — a non-leading `global.get`, an i64 op, or an unbalanced stack
/// all decline the fold. Used by [`ParsedConstExpr::reindex`] to fold a data /
/// element offset `global.get $__memory_base + N` once the base is a defined
/// constant (#353).
fn eval_ext_const_i32_with_base(ops: &[ExtConstOp], base: i32) -> Option<i32> {
    let mut stack: Vec<i32> = Vec::new();
    for (i, op) in ops.iter().enumerate() {
        match op {
            ExtConstOp::GlobalGet(_) if i == 0 => stack.push(base),
            // Only the leading global.get is the folded base; any other one means
            // the value depends on a second global we can't fold here.
            ExtConstOp::GlobalGet(_) => return None,
            ExtConstOp::I32Const(v) => stack.push(*v),
            ExtConstOp::I32Add => {
                let b = stack.pop()?;
                let a = stack.pop()?;
                stack.push(a.wrapping_add(b));
            }
            ExtConstOp::I32Sub => {
                let b = stack.pop()?;
                let a = stack.pop()?;
                stack.push(a.wrapping_sub(b));
            }
            ExtConstOp::I32Mul => {
                let b = stack.pop()?;
                let a = stack.pop()?;
                stack.push(a.wrapping_mul(b));
            }
            // i64 ops don't apply to a 32-bit memory offset.
            ExtConstOp::I64Const(_)
            | ExtConstOp::I64Add
            | ExtConstOp::I64Sub
            | ExtConstOp::I64Mul => return None,
        }
    }
    (stack.len() == 1).then(|| stack[0])
}

/// The outcome of reading a `const`-first extended-const expression: either a
/// pure-constant fold (no `global.get` anywhere) that collapses to a single
/// value, or a runtime-dependent sequence that embeds a `global.get` partway
/// through (the operand-swapped `N + __memory_base` shape) and therefore must
/// be preserved verbatim so its global index can be remapped later (#338).
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum ExtConstFold<T> {
    /// No `global.get` — the expression folded to this constant.
    Value(T),
    /// An embedded `global.get` was found; the COMPLETE operator sequence
    /// (in input order) is preserved for later index remapping. The value is
    /// runtime-dependent and stays `None` at the parse layer.
    Extended(Vec<ExtConstOp>),
}

/// Read wasm-2.0 extended-const operators until `End`, appending each to `seq`
/// (which already holds the operators consumed so far, in INPUT ORDER). Used
/// by both the `global.get`-first path and the const-first path once an
/// embedded `global.get` has forced the preserve-and-remap route.
///
/// Rejects any operator outside the extended-const set with a clear error
/// (mirrors `fold_extended_const_*`) so audit and CI surface the path instead
/// of silently dropping operators (#338 / LS-A-11). Operand order is preserved
/// verbatim — non-commutative `sub`/`mul` must not be reordered.
fn read_remaining_ext_const(
    ops: &mut wasmparser::OperatorsReader<'_>,
    mut seq: Vec<ExtConstOp>,
) -> Result<Vec<ExtConstOp>> {
    loop {
        let op = ops.read()?;
        match op {
            Operator::End => break,
            Operator::GlobalGet { global_index } => seq.push(ExtConstOp::GlobalGet(global_index)),
            Operator::I32Const { value } => seq.push(ExtConstOp::I32Const(value)),
            Operator::I64Const { value } => seq.push(ExtConstOp::I64Const(value)),
            Operator::I32Add => seq.push(ExtConstOp::I32Add),
            Operator::I32Sub => seq.push(ExtConstOp::I32Sub),
            Operator::I32Mul => seq.push(ExtConstOp::I32Mul),
            Operator::I64Add => seq.push(ExtConstOp::I64Add),
            Operator::I64Sub => seq.push(ExtConstOp::I64Sub),
            Operator::I64Mul => seq.push(ExtConstOp::I64Mul),
            other => {
                return Err(Error::UnsupportedFeature(format!(
                    "unsupported extended-const operator after global.get: {other:?}"
                )));
            }
        }
    }
    Ok(seq)
}

/// Read the remainder of a wasm-2.0 extended-const expression that begins
/// with `global.get`, after the leading `GlobalGet(first_index)` has already
/// been consumed by the caller. Returns the FULL operator sequence (leading
/// `global.get` + trailing arithmetic) up to but not including `End`.
///
/// If the only remaining operator is `End` (a bare `global.get`), returns
/// `Ok(None)` so callers preserve the existing single-`GlobalGet` behaviour
/// verbatim. Otherwise returns `Ok(Some(ops))` with the complete sequence.
pub(crate) fn read_extended_const_global_get(
    ops: &mut wasmparser::OperatorsReader<'_>,
    first_index: u32,
) -> Result<Option<Vec<ExtConstOp>>> {
    let seq = read_remaining_ext_const(ops, vec![ExtConstOp::GlobalGet(first_index)])?;
    if seq.len() == 1 {
        Ok(None)
    } else {
        Ok(Some(seq))
    }
}

/// A structured constant expression that preserves the operator and operands,
/// allowing index remapping before final encoding to `wasm_encoder::ConstExpr`.
#[derive(Debug, Clone)]
pub enum ParsedConstExpr {
    I32Const(i32),
    I64Const(i64),
    F32Const(f32),
    F64Const(f64),
    V128Const(i128),
    RefNull(wasm_encoder::HeapType),
    RefFunc(u32),
    GlobalGet(u32),
    /// A wasm-2.0 extended-const expression that begins with `global.get`
    /// and continues with arithmetic (the position-independent
    /// `__memory_base + N` shape). Its value is runtime-dependent, so the
    /// complete operator sequence is preserved and re-emitted rather than
    /// folded to a constant (#338). The `Vec` always holds the leading
    /// `GlobalGet` plus at least one trailing operator; a bare `global.get`
    /// with no trailing arithmetic stays a plain [`ParsedConstExpr::GlobalGet`].
    ExtendedGlobalGet(Vec<ExtConstOp>),
}

/// If a global's init const-expr bytes (WITHOUT the trailing `End`) fold to a
/// constant `i32` — a bare `i32.const N`, or the wasm-2.0 extended-const
/// `i32.const N (± M)*` with no embedded `global.get` — return that value.
/// Anything with a `global.get` (runtime-dependent) or a non-i32 type → `None`.
///
/// Used by the merger to record which merged **defined** globals are constant
/// i32s, so a data/element offset that `global.get`s one (a post-fusion
/// `__memory_base`) can be folded to `i32.const` (#353).
pub(crate) fn const_i32_init_value(init_bytes: &[u8]) -> Option<i32> {
    let mut full = init_bytes.to_vec();
    full.push(0x0B); // append End so wasmparser sees a complete const-expr
    let reader = wasmparser::BinaryReader::new(&full, 0);
    let expr = wasmparser::ConstExpr::new(reader);
    let mut ops = expr.get_operators_reader();
    match ops.read().ok()? {
        Operator::I32Const { value } => match fold_extended_const_i32(&mut ops, value).ok()? {
            ExtConstFold::Value(v) => Some(v),
            // Embeds a `global.get` (`base + N`) → not a pure constant here.
            ExtConstFold::Extended(_) => None,
        },
        _ => None,
    }
}

impl ParsedConstExpr {
    /// Convert this parsed const expression into a `wasm_encoder::ConstExpr`
    pub fn to_const_expr(&self) -> ConstExpr {
        match self {
            ParsedConstExpr::I32Const(v) => ConstExpr::i32_const(*v),
            ParsedConstExpr::I64Const(v) => ConstExpr::i64_const(*v),
            ParsedConstExpr::F32Const(v) => ConstExpr::f32_const((*v).into()),
            ParsedConstExpr::F64Const(v) => ConstExpr::f64_const((*v).into()),
            ParsedConstExpr::V128Const(v) => ConstExpr::v128_const(*v),
            ParsedConstExpr::RefNull(ht) => ConstExpr::ref_null(*ht),
            ParsedConstExpr::RefFunc(idx) => ConstExpr::ref_func(*idx),
            ParsedConstExpr::GlobalGet(idx) => ConstExpr::global_get(*idx),
            ParsedConstExpr::ExtendedGlobalGet(ops) => ext_const_to_expr(ops),
        }
    }

    /// Remap indices in this const expression using the provided index maps
    pub fn reindex(&self, maps: &IndexMaps) -> ParsedConstExpr {
        match self {
            ParsedConstExpr::RefFunc(idx) => ParsedConstExpr::RefFunc(maps.remap_func(*idx)),
            ParsedConstExpr::GlobalGet(idx) => {
                // #353 (static PIC): a data/element offset may `global.get` only
                // an IMPORTED global. After fusion a `__memory_base`-style base
                // (imported by a dylib, defined by `$main`) becomes DEFINED, so a
                // `global.get` of it here would be rejected by wasmtime. Fold it
                // to the concrete `i32.const` base. Imported globals are absent
                // from the map and stay a verbatim `global.get` (#338).
                let new = maps.remap_global(*idx);
                match maps.defined_global_i32_consts.get(&new) {
                    Some(&value) => ParsedConstExpr::I32Const(value),
                    None => ParsedConstExpr::GlobalGet(new),
                }
            }
            ParsedConstExpr::ExtendedGlobalGet(ops) => {
                let remapped: Vec<ExtConstOp> = ops
                    .iter()
                    .map(|o| o.remap_global(|i| maps.remap_global(i)))
                    .collect();
                // #353 (static PIC): `wasm-tools component link` emits base-relative
                // data at the position-independent offset
                // `(i32.add (global.get $__memory_base) (i32.const N))` for every
                // N > 0 (only N == 0 is a bare `global.get`). After fusion the base
                // becomes a DEFINED global, so this whole extended-const would be
                // `global.get <defined>; i32.const N; i32.add` — rejected by
                // wasmtime in a const-expr. If the leading global is a defined
                // constant-i32, FOLD the entire `base ± N` expression to a single
                // `i32.const`. (Imported bases are absent from the map → left
                // verbatim, preserving #338's runtime-dependent extended-const.)
                if let Some(ExtConstOp::GlobalGet(g)) = remapped.first()
                    && let Some(&base) = maps.defined_global_i32_consts.get(g)
                    && let Some(folded) = eval_ext_const_i32_with_base(&remapped, base)
                {
                    ParsedConstExpr::I32Const(folded)
                } else {
                    ParsedConstExpr::ExtendedGlobalGet(remapped)
                }
            }
            ParsedConstExpr::RefNull(ht) => {
                let remapped_ht = match ht {
                    wasm_encoder::HeapType::Concrete(idx) => {
                        wasm_encoder::HeapType::Concrete(maps.remap_type(*idx))
                    }
                    // Abstract heap types have no indices to remap
                    other => *other,
                };
                ParsedConstExpr::RefNull(remapped_ht)
            }
            // All other variants have no indices to remap
            other => other.clone(),
        }
    }
}

/// Parsed element segment ready for reindexing
#[derive(Debug, Clone)]
pub struct ParsedElementSegment {
    /// Element kind (active, passive, declared)
    pub mode: ParsedElementSegmentMode,
    /// Element type (funcref, externref, etc.)
    pub element_type: RefType,
    /// Function indices or expressions in this segment
    pub items: ElementItems_,
}

/// Element segment mode (parsed, with structured offset)
#[derive(Debug, Clone)]
pub enum ParsedElementSegmentMode {
    /// Active segment: initialized at instantiation
    Active {
        table_index: u32,
        offset: ParsedConstExpr,
    },
    /// Passive segment: initialized via elem.init
    Passive,
    /// Declared segment: only validates refs
    Declared,
}

/// Element segment mode (reindexed, with encoded offset)
#[derive(Debug, Clone)]
pub enum ElementSegmentMode {
    /// Active segment: initialized at instantiation
    Active { table_index: u32, offset: ConstExpr },
    /// Passive segment: initialized via elem.init
    Passive,
    /// Declared segment: only validates refs
    Declared,
}

/// Element items (function refs or expressions)
#[derive(Debug, Clone)]
pub enum ElementItems_ {
    /// Simple function indices
    Functions(Vec<u32>),
    /// Expressions (for typed function references)
    Expressions(Vec<ParsedConstExpr>),
}

/// Parsed data segment ready for reindexing
#[derive(Debug, Clone)]
pub struct ParsedDataSegment {
    /// Data segment mode
    pub mode: DataSegmentMode_,
    /// Raw data bytes
    pub data: Vec<u8>,
    /// Byte offset of this segment's payload (`data`) bytes within the data
    /// section's *content* — the coordinate space `reloc.DATA` entry offsets
    /// use (#326 Part C). Lets the fuser locate which absolute pointers inside
    /// `data` a `reloc.DATA` site names, to rebase them for shared memory.
    pub content_offset: u32,
}

/// Data segment mode
#[derive(Debug, Clone)]
pub enum DataSegmentMode_ {
    /// Active segment: initialized at instantiation
    Active {
        memory_index: u32,
        offset: ParsedConstExpr,
        offset_value: Option<ConstExprValue>,
    },
    /// Passive segment: initialized via memory.init
    Passive,
}

/// Parsed constant expression value (when available)
#[derive(Debug, Clone, Copy)]
pub enum ConstExprValue {
    I32(i32),
    I64(i64),
}

/// Reindexed element segment ready for encoding
#[derive(Debug, Clone)]
pub struct ReindexedElementSegment {
    /// Element kind (active, passive, declared)
    pub mode: ElementSegmentMode,
    /// Element type (funcref, externref, etc.)
    pub element_type: RefType,
    /// Function indices (reindexed)
    pub items: ReindexedElementItems,
}

/// Reindexed element items
#[derive(Debug, Clone)]
pub enum ReindexedElementItems {
    /// Simple function indices (reindexed)
    Functions(Vec<u32>),
    /// Expressions (reindexed). Held in STRUCTURED `ParsedConstExpr` form —
    /// already remapped by the merger via [`reindex_element_segment`] — rather
    /// than opaque encoded `ConstExpr` bytes, so that a later pass (notably the
    /// P3-async function-index shift, see `p3_async::shift_function_indices`)
    /// can still read and bump the `ref.func` index inside the expression.
    /// Encoded to `ConstExpr` only at final emit (see [`encode_element_segment`]).
    Expressions(Vec<ParsedConstExpr>),
}

/// Reindexed data segment ready for encoding
#[derive(Debug, Clone)]
pub struct ReindexedDataSegment {
    /// Data segment mode (reindexed)
    pub mode: ReindexedDataMode,
    /// Raw data bytes
    pub data: Vec<u8>,
}

/// Reindexed data segment mode
#[derive(Debug, Clone)]
pub enum ReindexedDataMode {
    /// Active segment with reindexed memory index
    Active {
        memory_index: u32,
        offset: ConstExpr,
    },
    /// Passive segment
    Passive,
}

/// Parse element segments from a module
pub fn parse_element_segments(module: &CoreModule) -> Result<Vec<ParsedElementSegment>> {
    let Some((start, end)) = module.element_section_range else {
        return Ok(Vec::new());
    };

    let bytes = &module.bytes[start..end];
    let binary_reader = wasmparser::BinaryReader::new(bytes, 0);
    let reader = ElementSectionReader::new(binary_reader)?;

    let mut segments = Vec::new();
    for elem in reader {
        let elem = elem?;

        // Determine element type from items
        let (element_type, items) = match elem.items {
            ElementItems::Functions(func_reader) => {
                let funcs: Vec<u32> = func_reader.into_iter().map(|f| f.unwrap()).collect();
                (RefType::FUNCREF, ElementItems_::Functions(funcs))
            }
            ElementItems::Expressions(ref_type, expr_reader) => {
                // Carry the FULL ref type faithfully — bucketing every
                // non-funcref to externref (the prior behaviour) dropped
                // concrete typed function references `(ref $t)` and GC
                // abstract heap types (struct/array/eq/any/i31/none), and
                // lost the concrete type index entirely, producing a fused
                // module that fails wasm validation ("type mismatch:
                // expected externref, found (ref $type)"). The concrete
                // index is remapped during reindexing (see remap_ref_type).
                let element_type = convert_ref_type(ref_type);
                let mut exprs = Vec::new();
                for expr in expr_reader {
                    let expr = expr?;
                    exprs.push(parse_const_expr(&expr)?);
                }
                (element_type, ElementItems_::Expressions(exprs))
            }
        };

        let mode = match elem.kind {
            ElementKind::Active {
                table_index,
                offset_expr,
            } => {
                let offset = parse_const_expr(&offset_expr)?;
                ParsedElementSegmentMode::Active {
                    table_index: table_index.unwrap_or(0),
                    offset,
                }
            }
            ElementKind::Passive => ParsedElementSegmentMode::Passive,
            ElementKind::Declared => ParsedElementSegmentMode::Declared,
        };

        segments.push(ParsedElementSegment {
            mode,
            element_type,
            items,
        });
    }

    Ok(segments)
}

/// Parse data segments from a module
pub fn parse_data_segments(module: &CoreModule) -> Result<Vec<ParsedDataSegment>> {
    let Some((start, end)) = module.data_section_range else {
        return Ok(Vec::new());
    };

    let bytes = &module.bytes[start..end];
    let binary_reader = wasmparser::BinaryReader::new(bytes, 0);
    let reader = DataSectionReader::new(binary_reader)?;

    let mut segments = Vec::new();
    for data in reader {
        let data = data?;

        let mode = match data.kind {
            wasmparser::DataKind::Active {
                memory_index,
                offset_expr,
            } => {
                let (offset, offset_value) = parse_const_expr_with_value(&offset_expr)?;
                DataSegmentMode_::Active {
                    memory_index,
                    offset,
                    offset_value,
                }
            }
            wasmparser::DataKind::Passive => DataSegmentMode_::Passive,
        };

        // `data.range` covers this whole segment entry within the section
        // content (base-0 reader); the payload bytes are its final `len` bytes,
        // so their start is `range.end - len` — the data-section-content offset
        // that `reloc.DATA` sites are relative to.
        let content_offset = (data.range.end - data.data.len()) as u32;
        segments.push(ParsedDataSegment {
            mode,
            data: data.data.to_vec(),
            content_offset,
        });
    }

    Ok(segments)
}

/// Count a module's element segments without fully parsing each entry.
///
/// Used to size the per-module element-segment index map: the local indices
/// `0..count` must each be remapped to `base + local`. Returns 0 when the
/// module has no element section or the section header cannot be read (the
/// rewriter then falls back to identity remapping, which is the pre-fix
/// behaviour for an unmappable index).
pub fn count_element_segments(module: &CoreModule) -> u32 {
    let Some((start, end)) = module.element_section_range else {
        return 0;
    };
    let binary_reader = wasmparser::BinaryReader::new(&module.bytes[start..end], 0);
    match ElementSectionReader::new(binary_reader) {
        Ok(reader) => reader.count(),
        Err(_) => 0,
    }
}

/// Count a module's data segments without fully parsing each entry.
///
/// See [`count_element_segments`] for the sizing rationale.
pub fn count_data_segments(module: &CoreModule) -> u32 {
    let Some((start, end)) = module.data_section_range else {
        return 0;
    };
    let binary_reader = wasmparser::BinaryReader::new(&module.bytes[start..end], 0);
    match DataSectionReader::new(binary_reader) {
        Ok(reader) => reader.count(),
        Err(_) => 0,
    }
}

/// Reindex an element segment with new index mappings
/// Faithfully convert a `wasmparser::RefType` to a `wasm_encoder::RefType`,
/// preserving nullability, abstract heap types, and concrete type indices.
/// (Concrete indices are module-level here; they are remapped later by
/// [`remap_ref_type`].) Replaces the lossy funcref/externref bucketing that
/// previously corrupted typed-ref and GC element segments.
fn convert_ref_type(rt: wasmparser::RefType) -> RefType {
    let heap_type = match rt.heap_type() {
        wasmparser::HeapType::Abstract { shared, ty } => wasm_encoder::HeapType::Abstract {
            shared,
            ty: convert_abstract_heap_type(ty),
        },
        wasmparser::HeapType::Concrete(idx) | wasmparser::HeapType::Exact(idx) => {
            wasm_encoder::HeapType::Concrete(idx.as_module_index().unwrap_or(0))
        }
    };
    RefType {
        nullable: rt.is_nullable(),
        heap_type,
    }
}

/// Remap a ref type's concrete heap-type index through the merge index maps;
/// abstract heap types carry no index. Mirrors the `RefNull` heap-type
/// handling in [`ParsedConstExpr::reindex`].
fn remap_ref_type(rt: RefType, maps: &IndexMaps) -> RefType {
    let heap_type = match rt.heap_type {
        wasm_encoder::HeapType::Concrete(idx) => {
            wasm_encoder::HeapType::Concrete(maps.remap_type(idx))
        }
        other => other,
    };
    RefType { heap_type, ..rt }
}

pub fn reindex_element_segment(
    segment: &ParsedElementSegment,
    maps: &IndexMaps,
) -> ReindexedElementSegment {
    let mode = match &segment.mode {
        ParsedElementSegmentMode::Active {
            table_index,
            offset,
        } => ElementSegmentMode::Active {
            table_index: maps.remap_table(*table_index),
            offset: offset.reindex(maps).to_const_expr(),
        },
        ParsedElementSegmentMode::Passive => ElementSegmentMode::Passive,
        ParsedElementSegmentMode::Declared => ElementSegmentMode::Declared,
    };

    let items = match &segment.items {
        ElementItems_::Functions(funcs) => {
            let remapped: Vec<u32> = funcs.iter().map(|&f| maps.remap_func(f)).collect();
            ReindexedElementItems::Functions(remapped)
        }
        ElementItems_::Expressions(exprs) => {
            // Keep the STRUCTURED, merger-reindexed form so a later
            // function-index shift (P3-async) can still bump `ref.func`.
            // Encoding is deferred to `encode_element_segment`.
            let remapped: Vec<ParsedConstExpr> = exprs.iter().map(|e| e.reindex(maps)).collect();
            ReindexedElementItems::Expressions(remapped)
        }
    };

    ReindexedElementSegment {
        mode,
        element_type: remap_ref_type(segment.element_type, maps),
        items,
    }
}

/// Reindex a data segment with new index mappings
pub fn reindex_data_segment(
    segment: &ParsedDataSegment,
    maps: &IndexMaps,
) -> Result<ReindexedDataSegment> {
    let mode = match &segment.mode {
        DataSegmentMode_::Active {
            memory_index,
            offset,
            offset_value,
        } => {
            let rebased_offset = if maps.address_rebasing {
                let Some(value) = offset_value else {
                    return Err(Error::UnsupportedFeature(
                        "data segment offset must be a constant for address rebasing".to_string(),
                    ));
                };
                rebase_const_expr_value(*value, maps.memory_base_offset)?
            } else {
                offset.reindex(maps).to_const_expr()
            };

            ReindexedDataMode::Active {
                memory_index: maps.remap_memory(*memory_index),
                offset: rebased_offset,
            }
        }
        DataSegmentMode_::Passive => ReindexedDataMode::Passive,
    };

    Ok(ReindexedDataSegment {
        mode,
        data: segment.data.clone(),
    })
}

/// Parse a constant expression from wasmparser into a structured representation
fn parse_const_expr(expr: &wasmparser::ConstExpr<'_>) -> Result<ParsedConstExpr> {
    parse_const_expr_with_value(expr).map(|(expr, _)| expr)
}

/// Fold a wasm 2.0 extended-const i32 expression that has already had its
/// first `i32.const <initial>` consumed by the caller. Continues reading
/// operators from `ops` until `End`, applying `i32.add` / `i32.sub` /
/// `i32.mul` / further `i32.const` to a small evaluation stack with
/// wrapping semantics per the wasm execution model.
///
/// If an embedded `global.get` is encountered partway through (the
/// operand-swapped `N + __memory_base` position-independent shape), the value
/// is runtime-dependent and CANNOT be folded: this captures the COMPLETE
/// operator sequence in input order (leading `i32.const` + ops already read +
/// the `global.get` + the remainder) and returns [`ExtConstFold::Extended`],
/// so the global index is remapped later instead of the un-remapped raw bytes
/// being emitted (#338). Pure-constant input still returns
/// [`ExtConstFold::Value`] — behaviourally identical to before.
///
/// Rejects unsupported operators (any non-extended-const op) with a clear
/// error so audit and CI surface the path instead of silently dropping
/// operators (LS-A-11).
pub(crate) fn fold_extended_const_i32(
    ops: &mut wasmparser::OperatorsReader<'_>,
    initial: i32,
) -> Result<ExtConstFold<i32>> {
    let mut stack: Vec<i32> = vec![initial];
    // Operator sequence captured in INPUT ORDER, kept in lockstep with the
    // fold so that if an embedded `global.get` appears we can hand back the
    // exact operators verbatim (no fold, no reorder) for later remapping.
    let mut seq: Vec<ExtConstOp> = vec![ExtConstOp::I32Const(initial)];
    loop {
        let op = ops.read()?;
        match op {
            Operator::End => break,
            Operator::I32Const { value } => {
                stack.push(value);
                seq.push(ExtConstOp::I32Const(value));
            }
            Operator::I32Add => {
                fold_i32_binop(&mut stack, i32::wrapping_add)?;
                seq.push(ExtConstOp::I32Add);
            }
            Operator::I32Sub => {
                fold_i32_binop(&mut stack, i32::wrapping_sub)?;
                seq.push(ExtConstOp::I32Sub);
            }
            Operator::I32Mul => {
                fold_i32_binop(&mut stack, i32::wrapping_mul)?;
                seq.push(ExtConstOp::I32Mul);
            }
            Operator::GlobalGet { global_index } => {
                // Runtime-dependent: abandon folding, preserve the full
                // sequence (already-read ops + this global.get + remainder).
                seq.push(ExtConstOp::GlobalGet(global_index));
                return read_remaining_ext_const(ops, seq).map(ExtConstFold::Extended);
            }
            other => {
                return Err(Error::UnsupportedFeature(format!(
                    "unsupported i32 extended-const operator: {other:?}"
                )));
            }
        }
    }
    if stack.len() != 1 {
        return Err(Error::UnsupportedFeature(format!(
            "extended-const i32 expression left {} values on the stack \
             (expected 1)",
            stack.len()
        )));
    }
    Ok(ExtConstFold::Value(stack[0]))
}

fn fold_i32_binop(stack: &mut Vec<i32>, op: fn(i32, i32) -> i32) -> Result<()> {
    let b = stack.pop().ok_or_else(|| {
        Error::UnsupportedFeature("i32 extended-const binop with empty stack".to_string())
    })?;
    let a = stack.pop().ok_or_else(|| {
        Error::UnsupportedFeature("i32 extended-const binop with single operand".to_string())
    })?;
    stack.push(op(a, b));
    Ok(())
}

/// i64 counterpart to `fold_extended_const_i32`. An embedded `global.get`
/// likewise switches to the preserve-and-remap [`ExtConstFold::Extended`]
/// path instead of folding (#338).
pub(crate) fn fold_extended_const_i64(
    ops: &mut wasmparser::OperatorsReader<'_>,
    initial: i64,
) -> Result<ExtConstFold<i64>> {
    let mut stack: Vec<i64> = vec![initial];
    let mut seq: Vec<ExtConstOp> = vec![ExtConstOp::I64Const(initial)];
    loop {
        let op = ops.read()?;
        match op {
            Operator::End => break,
            Operator::I64Const { value } => {
                stack.push(value);
                seq.push(ExtConstOp::I64Const(value));
            }
            Operator::I64Add => {
                fold_i64_binop(&mut stack, i64::wrapping_add)?;
                seq.push(ExtConstOp::I64Add);
            }
            Operator::I64Sub => {
                fold_i64_binop(&mut stack, i64::wrapping_sub)?;
                seq.push(ExtConstOp::I64Sub);
            }
            Operator::I64Mul => {
                fold_i64_binop(&mut stack, i64::wrapping_mul)?;
                seq.push(ExtConstOp::I64Mul);
            }
            Operator::GlobalGet { global_index } => {
                seq.push(ExtConstOp::GlobalGet(global_index));
                return read_remaining_ext_const(ops, seq).map(ExtConstFold::Extended);
            }
            other => {
                return Err(Error::UnsupportedFeature(format!(
                    "unsupported i64 extended-const operator: {other:?}"
                )));
            }
        }
    }
    if stack.len() != 1 {
        return Err(Error::UnsupportedFeature(format!(
            "extended-const i64 expression left {} values on the stack \
             (expected 1)",
            stack.len()
        )));
    }
    Ok(ExtConstFold::Value(stack[0]))
}

fn fold_i64_binop(stack: &mut Vec<i64>, op: fn(i64, i64) -> i64) -> Result<()> {
    let b = stack.pop().ok_or_else(|| {
        Error::UnsupportedFeature("i64 extended-const binop with empty stack".to_string())
    })?;
    let a = stack.pop().ok_or_else(|| {
        Error::UnsupportedFeature("i64 extended-const binop with single operand".to_string())
    })?;
    stack.push(op(a, b));
    Ok(())
}

fn parse_const_expr_with_value(
    expr: &wasmparser::ConstExpr<'_>,
) -> Result<(ParsedConstExpr, Option<ConstExprValue>)> {
    let mut ops = expr.get_operators_reader();

    // Read the first operator. For an i32 / i64 const, the expression may
    // continue with extended-const ops (i32.add / i32.sub / i32.mul and
    // their i64 counterparts) per the WebAssembly 2.0 extended-const
    // proposal. Fold those into a single value via `fold_extended_const_*`
    // so downstream consumers see the semantically correct initializer.
    //
    // LS-A-11 — silent extended-const truncation: prior versions returned
    // only the first const and dropped the remaining operators, producing
    // a global / data / element offset that differed from the source.
    let op = ops.read()?;

    let (const_expr, value) = match op {
        Operator::I32Const { value } => match fold_extended_const_i32(&mut ops, value)? {
            ExtConstFold::Value(folded) => (
                ParsedConstExpr::I32Const(folded),
                Some(ConstExprValue::I32(folded)),
            ),
            // A const-first expr with an embedded `global.get` (`N + base`) is
            // runtime-dependent: preserve the full sequence so the global index
            // is remapped, and expose no constant value (#338).
            ExtConstFold::Extended(seq) => (ParsedConstExpr::ExtendedGlobalGet(seq), None),
        },
        Operator::I64Const { value } => match fold_extended_const_i64(&mut ops, value)? {
            ExtConstFold::Value(folded) => (
                ParsedConstExpr::I64Const(folded),
                Some(ConstExprValue::I64(folded)),
            ),
            ExtConstFold::Extended(seq) => (ParsedConstExpr::ExtendedGlobalGet(seq), None),
        },
        Operator::F32Const { value } => (
            ParsedConstExpr::F32Const(f32::from_bits(value.bits())),
            None,
        ),
        Operator::F64Const { value } => (
            ParsedConstExpr::F64Const(f64::from_bits(value.bits())),
            None,
        ),
        Operator::V128Const { value } => (
            ParsedConstExpr::V128Const(i128::from_le_bytes(*value.bytes())),
            None,
        ),
        Operator::RefNull { hty } => {
            let heap_type = match hty {
                wasmparser::HeapType::Abstract { shared, ty } => wasm_encoder::HeapType::Abstract {
                    shared,
                    ty: convert_abstract_heap_type(ty),
                },
                wasmparser::HeapType::Concrete(idx) | wasmparser::HeapType::Exact(idx) => {
                    // Preserve the concrete type index. It will be remapped
                    // later during reindexing if needed. For initial parsing,
                    // extract the module-level index.
                    let type_idx = idx.as_module_index().unwrap_or(0);
                    wasm_encoder::HeapType::Concrete(type_idx)
                }
            };
            (ParsedConstExpr::RefNull(heap_type), None)
        }
        Operator::RefFunc { function_index } => (ParsedConstExpr::RefFunc(function_index), None),
        Operator::GlobalGet { global_index } => {
            // A `global.get`-first expression may continue with extended-const
            // arithmetic (the position-independent `__memory_base + N` shape).
            // Its value is runtime-dependent, so it CANNOT be folded — the
            // complete operator sequence is preserved and re-emitted with the
            // global index remapped later during reindexing. Prior versions
            // read only the leading `global.get` and silently dropped the
            // trailing arithmetic, corrupting the offset/initializer (#338).
            match read_extended_const_global_get(&mut ops, global_index)? {
                Some(seq) => (ParsedConstExpr::ExtendedGlobalGet(seq), None),
                None => (ParsedConstExpr::GlobalGet(global_index), None),
            }
        }
        _ => {
            return Err(Error::UnsupportedFeature(format!(
                "unsupported const expr operator: {:?}",
                op
            )));
        }
    };

    Ok((const_expr, value))
}

fn rebase_const_expr_value(value: ConstExprValue, base: u64) -> Result<ConstExpr> {
    if base == 0 {
        return Ok(match value {
            ConstExprValue::I32(v) => ConstExpr::i32_const(v),
            ConstExprValue::I64(v) => ConstExpr::i64_const(v),
        });
    }

    match value {
        ConstExprValue::I32(v) => {
            let base_i64 = i64::try_from(base).map_err(|_| {
                Error::UnsupportedFeature("address rebasing offset overflow".to_string())
            })?;
            let new_value = (v as i64).checked_add(base_i64).ok_or_else(|| {
                Error::UnsupportedFeature("address rebasing offset overflow".to_string())
            })?;
            if new_value > i64::from(i32::MAX) {
                return Err(Error::UnsupportedFeature(
                    "address rebasing offset exceeds i32 range".to_string(),
                ));
            }
            Ok(ConstExpr::i32_const(new_value as i32))
        }
        ConstExprValue::I64(v) => {
            let base_i64 = i64::try_from(base).map_err(|_| {
                Error::UnsupportedFeature("address rebasing offset overflow".to_string())
            })?;
            let new_value = v.checked_add(base_i64).ok_or_else(|| {
                Error::UnsupportedFeature("address rebasing offset overflow".to_string())
            })?;
            Ok(ConstExpr::i64_const(new_value))
        }
    }
}

/// Convert a reindexed element segment to wasm_encoder format for encoding
/// Encode a reindexed element segment into the given element section.
///
/// Takes a `&mut ElementSection` rather than returning an `ElementSegment`
/// because the `Expressions` arm now holds structured [`ParsedConstExpr`]
/// values that must be encoded into a temporary `Vec<ConstExpr>` here; that
/// temporary would not outlive a returned borrowing `ElementSegment`, so the
/// segment is pushed directly while the temporary is still live.
pub fn encode_element_segment(section: &mut ElementSection, segment: &ReindexedElementSegment) {
    let mode = match &segment.mode {
        ElementSegmentMode::Active {
            table_index,
            offset,
        } => ElementMode::Active {
            table: Some(*table_index),
            offset,
        },
        ElementSegmentMode::Passive => ElementMode::Passive,
        ElementSegmentMode::Declared => ElementMode::Declared,
    };

    match &segment.items {
        ReindexedElementItems::Functions(funcs) => {
            section.segment(ElementSegment {
                mode,
                elements: Elements::Functions(funcs.as_slice().into()),
            });
        }
        ReindexedElementItems::Expressions(exprs) => {
            // Encode the structured form at the last possible moment.
            let encoded: Vec<ConstExpr> = exprs.iter().map(|e| e.to_const_expr()).collect();
            section.segment(ElementSegment {
                mode,
                elements: Elements::Expressions(segment.element_type, encoded.as_slice().into()),
            });
        }
    }
}

/// Convert a reindexed data segment to wasm_encoder format for encoding
pub fn encode_data_segment(segment: &ReindexedDataSegment) -> DataSegment<'_, Vec<u8>> {
    let mode = match &segment.mode {
        ReindexedDataMode::Active {
            memory_index,
            offset,
        } => DataSegmentMode::Active {
            memory_index: *memory_index,
            offset,
        },
        ReindexedDataMode::Passive => DataSegmentMode::Passive,
    };

    DataSegment {
        mode,
        data: segment.data.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_encoder::Encode;

    #[test]
    fn eval_ext_const_i32_with_base_folds_and_declines() {
        use ExtConstOp::*;
        // base + N  (the PIC `__memory_base + offset` shape)
        assert_eq!(
            eval_ext_const_i32_with_base(&[GlobalGet(0), I32Const(16), I32Add], 0x10_0000),
            Some(0x10_0010)
        );
        // base - N and base * N
        assert_eq!(
            eval_ext_const_i32_with_base(&[GlobalGet(0), I32Const(4), I32Sub], 100),
            Some(96)
        );
        assert_eq!(
            eval_ext_const_i32_with_base(&[GlobalGet(0), I32Const(2), I32Mul], 21),
            Some(42)
        );
        // bare base folds to base
        assert_eq!(eval_ext_const_i32_with_base(&[GlobalGet(0)], 7), Some(7));
        // DECLINE: a non-leading global.get (value depends on a 2nd global)
        assert_eq!(
            eval_ext_const_i32_with_base(&[GlobalGet(0), GlobalGet(1), I32Add], 5),
            None
        );
        // DECLINE: an i64 op is not an i32 memory offset
        assert_eq!(
            eval_ext_const_i32_with_base(&[GlobalGet(0), I64Const(1), I64Add], 5),
            None
        );
        // DECLINE: unbalanced (missing operand)
        assert_eq!(
            eval_ext_const_i32_with_base(&[GlobalGet(0), I32Add], 5),
            None
        );
    }

    #[test]
    fn test_element_segment_mode() {
        let mode = ElementSegmentMode::Active {
            table_index: 0,
            offset: ConstExpr::i32_const(0),
        };
        assert!(matches!(mode, ElementSegmentMode::Active { .. }));

        let mode = ElementSegmentMode::Passive;
        assert!(matches!(mode, ElementSegmentMode::Passive));
    }

    #[test]
    fn test_data_segment_mode() {
        let mode = DataSegmentMode_::Active {
            memory_index: 0,
            offset: ParsedConstExpr::I32Const(0),
            offset_value: None,
        };
        assert!(matches!(mode, DataSegmentMode_::Active { .. }));

        let mode = DataSegmentMode_::Passive;
        assert!(matches!(mode, DataSegmentMode_::Passive));
    }

    #[test]
    fn test_element_items() {
        let items = ElementItems_::Functions(vec![0, 1, 2]);
        assert!(matches!(items, ElementItems_::Functions(_)));
    }

    #[test]
    fn test_reindex_data_segment_rebases_offset() {
        let segment = ParsedDataSegment {
            mode: DataSegmentMode_::Active {
                memory_index: 0,
                offset: ParsedConstExpr::I32Const(10),
                offset_value: Some(ConstExprValue::I32(10)),
            },
            data: vec![1, 2, 3],
            content_offset: 0,
        };

        let mut maps = IndexMaps::new();
        maps.address_rebasing = true;
        maps.memory_base_offset = 5;

        let reindexed = reindex_data_segment(&segment, &maps).unwrap();
        let ReindexedDataMode::Active { offset, .. } = reindexed.mode else {
            panic!("expected active data segment");
        };

        let mut actual = Vec::new();
        offset.encode(&mut actual);

        let mut expected = Vec::new();
        ConstExpr::i32_const(15).encode(&mut expected);

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_reindex_data_segment_rebases_requires_constant() {
        let segment = ParsedDataSegment {
            mode: DataSegmentMode_::Active {
                memory_index: 0,
                offset: ParsedConstExpr::GlobalGet(0),
                offset_value: None,
            },
            data: vec![1],
            content_offset: 0,
        };

        let mut maps = IndexMaps::new();
        maps.address_rebasing = true;

        assert!(reindex_data_segment(&segment, &maps).is_err());
    }

    #[test]
    fn test_reindex_const_expr_ref_func() {
        let expr = ParsedConstExpr::RefFunc(3);
        let mut maps = IndexMaps::new();
        maps.functions.insert(3, 10);

        let reindexed = expr.reindex(&maps);
        match reindexed {
            ParsedConstExpr::RefFunc(idx) => assert_eq!(idx, 10),
            _ => panic!("expected RefFunc"),
        }
    }

    #[test]
    fn test_reindex_const_expr_global_get() {
        let expr = ParsedConstExpr::GlobalGet(2);
        let mut maps = IndexMaps::new();
        maps.globals.insert(2, 7);

        let reindexed = expr.reindex(&maps);
        match reindexed {
            ParsedConstExpr::GlobalGet(idx) => assert_eq!(idx, 7),
            _ => panic!("expected GlobalGet"),
        }
    }

    #[test]
    fn test_reindex_const_expr_passthrough() {
        let expr = ParsedConstExpr::I32Const(42);
        let maps = IndexMaps::new();

        let reindexed = expr.reindex(&maps);
        match reindexed {
            ParsedConstExpr::I32Const(v) => assert_eq!(v, 42),
            _ => panic!("expected I32Const"),
        }
    }

    /// SR-10: Active element segment table index is remapped correctly.
    #[test]
    fn test_reindex_element_segment_active_remaps_table() {
        let segment = ParsedElementSegment {
            mode: ParsedElementSegmentMode::Active {
                table_index: 0,
                offset: ParsedConstExpr::I32Const(0),
            },
            element_type: RefType::FUNCREF,
            items: ElementItems_::Functions(vec![0]),
        };

        let mut maps = IndexMaps::new();
        maps.tables.insert(0, 3);

        let reindexed = reindex_element_segment(&segment, &maps);
        match &reindexed.mode {
            ElementSegmentMode::Active { table_index, .. } => {
                assert_eq!(
                    *table_index, 3,
                    "table index should be remapped from 0 to 3"
                );
            }
            _ => panic!("expected active element segment mode"),
        }
    }

    /// SR-10: Function references inside element segments are remapped.
    #[test]
    fn test_reindex_element_segment_remaps_function_refs() {
        let segment = ParsedElementSegment {
            mode: ParsedElementSegmentMode::Passive,
            element_type: RefType::FUNCREF,
            items: ElementItems_::Functions(vec![0, 1, 2]),
        };

        let mut maps = IndexMaps::new();
        maps.functions.insert(0, 10);
        maps.functions.insert(1, 11);
        maps.functions.insert(2, 12);

        let reindexed = reindex_element_segment(&segment, &maps);
        match &reindexed.items {
            ReindexedElementItems::Functions(funcs) => {
                assert_eq!(funcs, &[10, 11, 12], "function indices should be remapped");
            }
            _ => panic!("expected Functions variant in reindexed items"),
        }
    }

    /// SR-10: Active data segment memory index is remapped correctly.
    #[test]
    fn test_reindex_data_segment_remaps_memory_index() {
        let segment = ParsedDataSegment {
            mode: DataSegmentMode_::Active {
                memory_index: 0,
                offset: ParsedConstExpr::I32Const(0),
                offset_value: Some(ConstExprValue::I32(0)),
            },
            data: vec![0xAA, 0xBB],
            content_offset: 0,
        };

        let mut maps = IndexMaps::new();
        maps.memories.insert(0, 2);

        let reindexed = reindex_data_segment(&segment, &maps).unwrap();
        match &reindexed.mode {
            ReindexedDataMode::Active { memory_index, .. } => {
                assert_eq!(
                    *memory_index, 2,
                    "memory index should be remapped from 0 to 2"
                );
            }
            _ => panic!("expected active data segment mode"),
        }
    }

    /// SR-10 / UCA-M-6: Global index in data segment offset expression is
    /// remapped. Without this, a `global.get 0` offset could reference the
    /// wrong global after merging, corrupting the data segment placement.
    #[test]
    fn test_reindex_data_segment_global_get_remaps_global() {
        let segment = ParsedDataSegment {
            mode: DataSegmentMode_::Active {
                memory_index: 0,
                offset: ParsedConstExpr::GlobalGet(0),
                offset_value: None,
            },
            data: vec![0xFF],
            content_offset: 0,
        };

        let mut maps = IndexMaps::new();
        maps.globals.insert(0, 5);

        let reindexed = reindex_data_segment(&segment, &maps).unwrap();
        let ReindexedDataMode::Active { offset, .. } = &reindexed.mode else {
            panic!("expected active data segment mode");
        };

        // Encode both the actual and expected ConstExpr to compare bytes,
        // since ConstExpr does not implement PartialEq.
        let mut actual = Vec::new();
        offset.encode(&mut actual);

        let mut expected = Vec::new();
        ConstExpr::global_get(5).encode(&mut expected);

        assert_eq!(
            actual, expected,
            "global index in offset should be remapped from 0 to 5"
        );
    }

    /// SR-10: Concrete type index inside RefNull expressions in element
    /// segments is remapped through the type index map.
    #[test]
    fn test_reindex_element_segment_expression_remaps_ref_null_type() {
        let segment = ParsedElementSegment {
            mode: ParsedElementSegmentMode::Passive,
            element_type: RefType::FUNCREF,
            items: ElementItems_::Expressions(vec![ParsedConstExpr::RefNull(
                wasm_encoder::HeapType::Concrete(0),
            )]),
        };

        let mut maps = IndexMaps::new();
        maps.types.insert(0, 4);

        let reindexed = reindex_element_segment(&segment, &maps);
        let ReindexedElementItems::Expressions(exprs) = &reindexed.items else {
            panic!("expected Expressions variant in reindexed items");
        };
        assert_eq!(exprs.len(), 1, "should have exactly one expression");

        // Encode both the actual and expected ConstExpr to compare bytes.
        // `Expressions` now holds structured `ParsedConstExpr`; encode it the
        // same way `encode_element_segment` does (deferred `to_const_expr`).
        let mut actual = Vec::new();
        exprs[0].to_const_expr().encode(&mut actual);

        let mut expected = Vec::new();
        ConstExpr::ref_null(wasm_encoder::HeapType::Concrete(4)).encode(&mut expected);

        assert_eq!(
            actual, expected,
            "concrete type index should be remapped from 0 to 4"
        );
    }

    /// Regression for the element-segment ref-type collapse: reindexing a
    /// segment whose element type is a CONCRETE typed reference `(ref null
    /// $t)` must preserve the concrete heap type and remap its index — not
    /// collapse it to externref (the prior bug dropped the type entirely).
    #[test]
    fn test_reindex_element_segment_preserves_and_remaps_concrete_element_type() {
        let segment = ParsedElementSegment {
            mode: ParsedElementSegmentMode::Passive,
            element_type: RefType {
                nullable: true,
                heap_type: wasm_encoder::HeapType::Concrete(0),
            },
            items: ElementItems_::Expressions(vec![ParsedConstExpr::RefFunc(0)]),
        };
        let mut maps = IndexMaps::new();
        maps.types.insert(0, 4);

        let reindexed = reindex_element_segment(&segment, &maps);
        assert_eq!(
            reindexed.element_type,
            RefType {
                nullable: true,
                heap_type: wasm_encoder::HeapType::Concrete(4),
            },
            "concrete element type must be preserved and its index remapped 0->4, \
             not collapsed to externref"
        );
    }

    /// End-to-end regression (the discovery-pass PoC): a core module with a
    /// concrete typed-ref element segment `(elem (ref null 0) (ref.func 0))`
    /// must survive parse -> reindex -> encode and still VALIDATE. Before the
    /// fix the segment was re-typed externref while its items stayed funcref,
    /// so the re-emitted module was rejected ("type mismatch: expected
    /// externref, found (ref $type)").
    #[test]
    fn ls_a_21_test_typed_ref_element_segment_roundtrips_and_validates() {
        let src = r#"(module (type (func)) (func) (elem (ref null 0) (ref.func 0)))"#;
        let module_bytes = wat::parse_str(src).expect("wat compiles");

        // Locate the element section payload range.
        let mut elem_range = None;
        for payload in wasmparser::Parser::new(0).parse_all(&module_bytes) {
            if let wasmparser::Payload::ElementSection(reader) = payload.expect("payload") {
                elem_range = Some((reader.range().start, reader.range().end));
            }
        }
        let elem_range = elem_range.expect("module has an element section");

        let module = crate::parser::CoreModule {
            index: 0,
            bytes: module_bytes.clone(),
            types: Vec::new(),
            imports: Vec::new(),
            exports: Vec::new(),
            functions: Vec::new(),
            memories: Vec::new(),
            tables: Vec::new(),
            globals: Vec::new(),
            start: None,
            data_count: None,
            element_count: 1,
            custom_sections: Vec::new(),
            code_section_range: None,
            global_section_range: None,
            element_section_range: Some(elem_range),
            data_section_range: None,
        };

        let parsed = parse_element_segments(&module).expect("parse element segments");
        assert_eq!(parsed.len(), 1);
        assert!(
            matches!(
                parsed[0].element_type.heap_type,
                wasm_encoder::HeapType::Concrete(_)
            ),
            "parsed element type must stay a concrete typed ref, got {:?}",
            parsed[0].element_type
        );

        // Reindex with identity maps (single module), re-encode the segment
        // into a fresh module, and validate it.
        let maps = IndexMaps::new();
        let reindexed = reindex_element_segment(&parsed[0], &maps);

        let mut types = wasm_encoder::TypeSection::new();
        types.ty().function([], []);
        let mut funcs = wasm_encoder::FunctionSection::new();
        funcs.function(0);
        let mut elems = wasm_encoder::ElementSection::new();
        encode_element_segment(&mut elems, &reindexed);
        let mut code = wasm_encoder::CodeSection::new();
        let mut f = wasm_encoder::Function::new([]);
        f.instruction(&wasm_encoder::Instruction::End);
        code.function(&f);

        let mut out = wasm_encoder::Module::new();
        out.section(&types);
        out.section(&funcs);
        out.section(&elems);
        out.section(&code);
        let out_bytes = out.finish();

        wasmparser::Validator::new()
            .validate_all(&out_bytes)
            .expect("re-encoded module with a typed-ref element segment must validate");
    }

    // ---------------------------------------------------------------
    // LS-A-11 — extended-const truncation
    //
    // Prior to this fix, `parse_const_expr_with_value` read only the
    // first operator and silently dropped the rest. Any wasm 2.0
    // extended-const expression — e.g. `(i32.const 5)(i32.const 10)
    // i32.add` — parsed as `i32.const 5` (value 5), producing data /
    // element segment offsets at the wrong addresses.
    // ---------------------------------------------------------------

    /// Build a minimal active-data section with one segment whose offset
    /// is an extended-const expression `(i32.const a)(i32.const b)(op)`,
    /// then run parse_const_expr_with_value on it and return the
    /// computed offset value.
    fn parse_i32_extended_offset(a: i32, b: i32, opcode: u8) -> i32 {
        let body: Vec<u8> = vec![
            0x01, // segment count = 1
            0x00, // flags = active mem 0
            0x41, a as u8, // i32.const a
            0x41, b as u8, // i32.const b
            opcode,  // i32.add / sub / mul
            0x0B,    // end
            0x00,    // data count = 0
        ];

        let br = wasmparser::BinaryReader::new(&body, 0);
        let reader = wasmparser::DataSectionReader::new(br).unwrap();
        let mut value: Option<i32> = None;
        for d in reader {
            let d = d.unwrap();
            if let wasmparser::DataKind::Active { offset_expr, .. } = d.kind {
                let (_pce, v) = parse_const_expr_with_value(&offset_expr).unwrap();
                if let Some(ConstExprValue::I32(n)) = v {
                    value = Some(n);
                }
            }
        }
        value.expect("offset value present")
    }

    #[test]
    fn ls_a_11_extended_const_i32_add_is_folded() {
        // (i32.const 5)(i32.const 10) i32.add  →  15
        assert_eq!(parse_i32_extended_offset(5, 10, 0x6A), 15);
    }

    #[test]
    fn ls_a_11_extended_const_i32_sub_is_folded() {
        // (i32.const 20)(i32.const 7) i32.sub  →  13
        assert_eq!(parse_i32_extended_offset(20, 7, 0x6B), 13);
    }

    #[test]
    fn ls_a_11_extended_const_i32_mul_is_folded() {
        // (i32.const 6)(i32.const 7) i32.mul  →  42
        assert_eq!(parse_i32_extended_offset(6, 7, 0x6C), 42);
    }

    #[test]
    fn ls_a_11_single_const_still_works() {
        // Plain `(i32.const 42) end` — no extended-const ops, must still
        // round-trip as before. (42 fits in single-byte sleb128; 99 would
        // need a 2-byte encoding due to sign-bit at position 6.)
        let body: Vec<u8> = vec![
            0x01, // segment count = 1
            0x00, // flags = active mem 0
            0x41, 42,   // i32.const 42
            0x0B, // end
            0x00, // data count = 0
        ];
        let br = wasmparser::BinaryReader::new(&body, 0);
        let reader = wasmparser::DataSectionReader::new(br).unwrap();
        for d in reader {
            let d = d.unwrap();
            if let wasmparser::DataKind::Active { offset_expr, .. } = d.kind {
                let (_pce, v) = parse_const_expr_with_value(&offset_expr).unwrap();
                assert!(
                    matches!(v, Some(ConstExprValue::I32(42))),
                    "expected Some(I32(42)), got {v:?}",
                );
            }
        }
    }
}
