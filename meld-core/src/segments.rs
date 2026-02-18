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
    ConstExpr, DataSegment, DataSegmentMode, ElementMode, ElementSegment, Elements, RefType,
};
use wasmparser::{DataSectionReader, ElementItems, ElementKind, ElementSectionReader, Operator};

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
}

impl ParsedConstExpr {
    /// Convert this parsed const expression into a `wasm_encoder::ConstExpr`
    pub fn to_const_expr(&self) -> ConstExpr {
        match self {
            ParsedConstExpr::I32Const(v) => ConstExpr::i32_const(*v),
            ParsedConstExpr::I64Const(v) => ConstExpr::i64_const(*v),
            ParsedConstExpr::F32Const(v) => ConstExpr::f32_const(*v),
            ParsedConstExpr::F64Const(v) => ConstExpr::f64_const(*v),
            ParsedConstExpr::V128Const(v) => ConstExpr::v128_const(*v),
            ParsedConstExpr::RefNull(ht) => ConstExpr::ref_null(*ht),
            ParsedConstExpr::RefFunc(idx) => ConstExpr::ref_func(*idx),
            ParsedConstExpr::GlobalGet(idx) => ConstExpr::global_get(*idx),
        }
    }

    /// Remap indices in this const expression using the provided index maps
    pub fn reindex(&self, maps: &IndexMaps) -> ParsedConstExpr {
        match self {
            ParsedConstExpr::RefFunc(idx) => ParsedConstExpr::RefFunc(maps.remap_func(*idx)),
            ParsedConstExpr::GlobalGet(idx) => ParsedConstExpr::GlobalGet(maps.remap_global(*idx)),
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
    /// Expressions (reindexed)
    Expressions(Vec<ConstExpr>),
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
                let element_type = if ref_type.is_func_ref() {
                    RefType::FUNCREF
                } else {
                    RefType::EXTERNREF
                };
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

        segments.push(ParsedDataSegment {
            mode,
            data: data.data.to_vec(),
        });
    }

    Ok(segments)
}

/// Reindex an element segment with new index mappings
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
            let remapped: Vec<ConstExpr> = exprs
                .iter()
                .map(|e| e.reindex(maps).to_const_expr())
                .collect();
            ReindexedElementItems::Expressions(remapped)
        }
    };

    ReindexedElementSegment {
        mode,
        element_type: segment.element_type,
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

fn parse_const_expr_with_value(
    expr: &wasmparser::ConstExpr<'_>,
) -> Result<(ParsedConstExpr, Option<ConstExprValue>)> {
    let mut ops = expr.get_operators_reader();

    // Read the first (and usually only) operator
    let op = ops.read()?;

    let (const_expr, value) = match op {
        Operator::I32Const { value } => (
            ParsedConstExpr::I32Const(value),
            Some(ConstExprValue::I32(value)),
        ),
        Operator::I64Const { value } => (
            ParsedConstExpr::I64Const(value),
            Some(ConstExprValue::I64(value)),
        ),
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
                wasmparser::HeapType::Concrete(idx) => {
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
        Operator::GlobalGet { global_index } => (ParsedConstExpr::GlobalGet(global_index), None),
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
pub fn encode_element_segment(segment: &ReindexedElementSegment) -> ElementSegment<'_> {
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

    let elements = match &segment.items {
        ReindexedElementItems::Functions(funcs) => Elements::Functions(funcs.as_slice().into()),
        ReindexedElementItems::Expressions(exprs) => {
            Elements::Expressions(segment.element_type, exprs.as_slice().into())
        }
    };

    ElementSegment { mode, elements }
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
}
