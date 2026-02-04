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
use crate::rewriter::IndexMaps;
use crate::{Error, Result};
use wasm_encoder::{
    ConstExpr, DataSegment, DataSegmentMode, ElementMode, ElementSegment, Elements, RefType,
};
use wasmparser::{DataSectionReader, ElementItems, ElementKind, ElementSectionReader, Operator};

/// Parsed element segment ready for reindexing
#[derive(Debug, Clone)]
pub struct ParsedElementSegment {
    /// Element kind (active, passive, declared)
    pub mode: ElementSegmentMode,
    /// Element type (funcref, externref, etc.)
    pub element_type: RefType,
    /// Function indices or expressions in this segment
    pub items: ElementItems_,
}

/// Element segment mode
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
    Expressions(Vec<ConstExpr>),
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
        offset: ConstExpr,
    },
    /// Passive segment: initialized via memory.init
    Passive,
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
                ElementSegmentMode::Active {
                    table_index: table_index.unwrap_or(0),
                    offset,
                }
            }
            ElementKind::Passive => ElementSegmentMode::Passive,
            ElementKind::Declared => ElementSegmentMode::Declared,
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
                let offset = parse_const_expr(&offset_expr)?;
                DataSegmentMode_::Active {
                    memory_index,
                    offset,
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
        ElementSegmentMode::Active {
            table_index,
            offset,
        } => ElementSegmentMode::Active {
            table_index: maps.remap_table(*table_index),
            offset: reindex_const_expr(offset, maps),
        },
        ElementSegmentMode::Passive => ElementSegmentMode::Passive,
        ElementSegmentMode::Declared => ElementSegmentMode::Declared,
    };

    let items = match &segment.items {
        ElementItems_::Functions(funcs) => {
            let remapped: Vec<u32> = funcs.iter().map(|&f| maps.remap_func(f)).collect();
            ReindexedElementItems::Functions(remapped)
        }
        ElementItems_::Expressions(exprs) => {
            let remapped: Vec<ConstExpr> =
                exprs.iter().map(|e| reindex_const_expr(e, maps)).collect();
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
pub fn reindex_data_segment(segment: &ParsedDataSegment, maps: &IndexMaps) -> ReindexedDataSegment {
    let mode = match &segment.mode {
        DataSegmentMode_::Active {
            memory_index,
            offset,
        } => ReindexedDataMode::Active {
            memory_index: maps.remap_memory(*memory_index),
            offset: reindex_const_expr(offset, maps),
        },
        DataSegmentMode_::Passive => ReindexedDataMode::Passive,
    };

    ReindexedDataSegment {
        mode,
        data: segment.data.clone(),
    }
}

/// Parse a constant expression from wasmparser
fn parse_const_expr(expr: &wasmparser::ConstExpr<'_>) -> Result<ConstExpr> {
    let mut ops = expr.get_operators_reader();

    // Read the first (and usually only) operator
    let op = ops.read()?;

    let const_expr = match op {
        Operator::I32Const { value } => ConstExpr::i32_const(value),
        Operator::I64Const { value } => ConstExpr::i64_const(value),
        Operator::F32Const { value } => ConstExpr::f32_const(f32::from_bits(value.bits())),
        Operator::F64Const { value } => ConstExpr::f64_const(f64::from_bits(value.bits())),
        Operator::V128Const { value } => ConstExpr::v128_const(i128::from_le_bytes(*value.bytes())),
        Operator::RefNull { hty } => {
            let heap_type = match hty {
                wasmparser::HeapType::Abstract { ty, .. } => match ty {
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
                wasmparser::HeapType::Concrete(_) => wasm_encoder::HeapType::Concrete(0),
            };
            ConstExpr::ref_null(heap_type)
        }
        Operator::RefFunc { function_index } => ConstExpr::ref_func(function_index),
        Operator::GlobalGet { global_index } => ConstExpr::global_get(global_index),
        _ => {
            return Err(Error::UnsupportedFeature(format!(
                "unsupported const expr operator: {:?}",
                op
            )));
        }
    };

    Ok(const_expr)
}

/// Reindex a constant expression (for global.get and ref.func)
fn reindex_const_expr(expr: &ConstExpr, _maps: &IndexMaps) -> ConstExpr {
    // ConstExpr doesn't expose its internals easily, so we need to
    // rebuild it. For now, return as-is - full implementation would
    // parse and rewrite the expression bytes.
    expr.clone()
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
            offset: ConstExpr::i32_const(0),
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
}
