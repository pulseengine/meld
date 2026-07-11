//! # Relocation-metadata reader (`linking` + `reloc.*` custom sections)
//!
//! meld fuses WebAssembly components into a shared linear memory but does not
//! yet rebase a component's absolute addresses (issue #326). The fix consumes
//! each input's `linking` + `reloc.*` metadata to find and rewrite the byte
//! sites that encode memory addresses / relocatable indices.
//!
//! `wasmparser` 0.246 no longer exposes reloc/linking readers (they were
//! dropped from modern versions), so meld hand-parses the raw custom-section
//! bytes. meld already retains custom sections as `Vec<(String, Vec<u8>)>`
//! (see [`crate::parser::ParsedComponent::custom_sections`]), so this reader
//! takes those bytes directly.
//!
//! ## Wire format (verified empirically against `wasm-tools`-produced bytes)
//!
//! This module was reverse-engineered from a real relocatable core produced by
//! the LLVM/`wasm-tools` toolchain. The exact `reloc.CODE` body observed was:
//!
//! ```text
//! 03 04  04 3e 03 20  04 58 03 00  03 84 01 04 00  03 90 01 04 00
//! ^^ ^^  \_________/  \_________/  \____________/  \____________/
//! |  |    entry 0      entry 1        entry 2          entry 3
//! |  count = 4
//! target-section index = 3  (the CODE section)
//! ```
//!
//! Findings that matter for the parser:
//!
//! * **A target-section-index prefix IS present.** The body is
//!   `target_section: varuint32`, then `count: varuint32`, then `count`
//!   entries. This is the LLVM/`wasm-tools` layout (the "historical variant"
//!   the tool-conventions doc mentions); it is NOT the bare `count`-first
//!   layout. Confirmed because the first byte `0x03` equals the index of the
//!   code section and `wasm-tools objdump` labels it `section 3`.
//! * **Each entry is** `type: u8`, `offset: varuint32`, `index: varuint32`,
//!   and — only for the memory-address / offset relocation types — an
//!   `addend: varint32` (signed LEB128).
//! * **The addend is always emitted for memory-address types, even when 0.**
//!   The two `MemoryAddrLeb` entries above carry an explicit `00` addend byte;
//!   it is an *encoded* zero, not an absent field. Both the LEB and the SLEB
//!   memory-address forms carry the addend identically — presence is keyed on
//!   the relocation *type*, not on LEB-vs-SLEB encoding.
//!
//! ## Scope (issue #326, increment 1)
//!
//! This is a pure, side-effect-free reader. It does not touch the
//! fusion/rewriter/merger path — consuming these entries to actually rebase
//! addresses is increment 2.

use crate::{Error, Result};

/// A relocation type code, as defined by the WebAssembly tool-conventions
/// `Linking.md`. The memory-address / offset variants (the ones meld must
/// rebase) are modelled precisely; every other code is preserved verbatim as
/// [`RelocType::Other`] so that unknown or newer types never panic the parser.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelocType {
    /// `R_WASM_FUNCTION_INDEX_LEB` = 0
    FunctionIndexLeb,
    /// `R_WASM_TABLE_INDEX_SLEB` = 1
    TableIndexSleb,
    /// `R_WASM_TABLE_INDEX_I32` = 2
    TableIndexI32,
    /// `R_WASM_MEMORY_ADDR_LEB` = 3
    MemoryAddrLeb,
    /// `R_WASM_MEMORY_ADDR_SLEB` = 4
    MemoryAddrSleb,
    /// `R_WASM_MEMORY_ADDR_I32` = 5
    MemoryAddrI32,
    /// `R_WASM_TYPE_INDEX_LEB` = 6
    TypeIndexLeb,
    /// `R_WASM_GLOBAL_INDEX_LEB` = 7
    GlobalIndexLeb,
    /// `R_WASM_FUNCTION_OFFSET_I32` = 8
    FunctionOffsetI32,
    /// `R_WASM_SECTION_OFFSET_I32` = 9
    SectionOffsetI32,
    /// `R_WASM_TAG_INDEX_LEB` = 10
    TagIndexLeb,
    /// `R_WASM_MEMORY_ADDR_REL_SLEB` = 11
    MemoryAddrRelSleb,
    /// `R_WASM_TABLE_INDEX_REL_SLEB` = 12
    TableIndexRelSleb,
    /// Any relocation type code this reader does not model explicitly. The raw
    /// byte is preserved. Addend presence for these is inferred from the
    /// tool-conventions code ranges (see [`RelocType::has_addend`]).
    Other(u8),
}

impl RelocType {
    /// Decode a raw relocation-type byte.
    pub fn from_code(code: u8) -> Self {
        match code {
            0 => RelocType::FunctionIndexLeb,
            1 => RelocType::TableIndexSleb,
            2 => RelocType::TableIndexI32,
            3 => RelocType::MemoryAddrLeb,
            4 => RelocType::MemoryAddrSleb,
            5 => RelocType::MemoryAddrI32,
            6 => RelocType::TypeIndexLeb,
            7 => RelocType::GlobalIndexLeb,
            8 => RelocType::FunctionOffsetI32,
            9 => RelocType::SectionOffsetI32,
            10 => RelocType::TagIndexLeb,
            11 => RelocType::MemoryAddrRelSleb,
            12 => RelocType::TableIndexRelSleb,
            other => RelocType::Other(other),
        }
    }

    /// The raw relocation-type byte.
    pub fn code(self) -> u8 {
        match self {
            RelocType::FunctionIndexLeb => 0,
            RelocType::TableIndexSleb => 1,
            RelocType::TableIndexI32 => 2,
            RelocType::MemoryAddrLeb => 3,
            RelocType::MemoryAddrSleb => 4,
            RelocType::MemoryAddrI32 => 5,
            RelocType::TypeIndexLeb => 6,
            RelocType::GlobalIndexLeb => 7,
            RelocType::FunctionOffsetI32 => 8,
            RelocType::SectionOffsetI32 => 9,
            RelocType::TagIndexLeb => 10,
            RelocType::MemoryAddrRelSleb => 11,
            RelocType::TableIndexRelSleb => 12,
            RelocType::Other(code) => code,
        }
    }

    /// Whether this relocation targets an absolute linear-memory address — the
    /// class meld must rebase when collapsing inputs into a shared memory.
    pub fn is_memory_addr(self) -> bool {
        matches!(
            self,
            RelocType::MemoryAddrLeb
                | RelocType::MemoryAddrSleb
                | RelocType::MemoryAddrI32
                | RelocType::MemoryAddrRelSleb
        ) || matches!(self, RelocType::Other(c) if is_memory_addr_code(c))
    }

    /// Whether an entry of this type carries a trailing `addend: varint32`.
    ///
    /// Per tool-conventions this is the memory-address family plus the
    /// function/section *offset* relocations. The 64-bit variants (codes
    /// 14–25) are included so that a module built for `wasm64` still parses,
    /// even though meld does not model those variants by name.
    pub fn has_addend(self) -> bool {
        match self {
            RelocType::MemoryAddrLeb
            | RelocType::MemoryAddrSleb
            | RelocType::MemoryAddrI32
            | RelocType::FunctionOffsetI32
            | RelocType::SectionOffsetI32
            | RelocType::MemoryAddrRelSleb => true,
            RelocType::Other(c) => code_has_addend(c),
            _ => false,
        }
    }
}

/// Is this raw code one of the `MEMORY_ADDR_*` relocation types (incl. 64-bit)?
fn is_memory_addr_code(code: u8) -> bool {
    matches!(code, 3 | 4 | 5 | 11 | 14 | 15 | 16 | 19 | 21 | 23 | 25)
}

/// Does this raw code carry a trailing `addend`? Covers the memory-address
/// family and the function/section offset relocations, 32- and 64-bit.
fn code_has_addend(code: u8) -> bool {
    matches!(
        code,
        // 32-bit: MEMORY_ADDR_{LEB,SLEB,I32}, FUNCTION_OFFSET_I32,
        // SECTION_OFFSET_I32, MEMORY_ADDR_REL_SLEB.
        3 | 4 | 5 | 8 | 9 | 11
        // 64-bit: MEMORY_ADDR_{LEB64,SLEB64,I64}, MEMORY_ADDR_REL_SLEB64,
        // FUNCTION_OFFSET_I64, MEMORY_ADDR_TLS_SLEB,
        // MEMORY_ADDR_LOCREL_I32, MEMORY_ADDR_TLS_SLEB64.
        | 14 | 15 | 16 | 19 | 20 | 21 | 23 | 25
    )
}

/// A single relocation entry: a site in the target section whose encoded value
/// must be adjusted when the referenced symbol moves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RelocEntry {
    /// The relocation type.
    pub ty: RelocType,
    /// Byte offset of the relocation site within the target section's payload.
    pub offset: u32,
    /// Symbol index into the `linking` section's symbol table.
    pub index: u32,
    /// Constant added to the symbol's address/value. Meaningful only when
    /// [`RelocType::has_addend`] is true; 0 otherwise.
    pub addend: i32,
}

/// Which section a `reloc.*` custom section targets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelocTarget {
    /// `reloc.CODE`
    Code,
    /// `reloc.DATA`
    Data,
    /// Any other `reloc.<NAME>` target (the `<NAME>` suffix is preserved).
    Other(String),
}

/// A decoded `reloc.<SECTION>` custom section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelocSection {
    /// Which section these relocations apply to.
    pub target: RelocTarget,
    /// The target section's index within the module, as encoded in the reloc
    /// section's leading `target_section` field.
    pub target_section_index: u32,
    /// The relocation entries, in file order.
    pub entries: Vec<RelocEntry>,
}

/// A raw, still-encoded `linking` subsection `(id, bytes)`. Increment 1 exposes
/// these verbatim; the symbol-table decode (needed later to resolve an entry's
/// `index` to a symbol) is deferred to increment 2.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkingSubsection {
    /// Subsection id (e.g. 5 = `WASM_SEGMENT_INFO`, 8 = `WASM_SYMBOL_TABLE`).
    pub id: u8,
    /// Raw subsection payload bytes.
    pub bytes: Vec<u8>,
}

/// Well-known `linking` subsection ids (tool-conventions `Linking.md`).
pub mod linking_subsection {
    /// `WASM_SEGMENT_INFO`
    pub const SEGMENT_INFO: u8 = 5;
    /// `WASM_INIT_FUNCS`
    pub const INIT_FUNCS: u8 = 6;
    /// `WASM_COMDAT_INFO`
    pub const COMDAT_INFO: u8 = 7;
    /// `WASM_SYMBOL_TABLE`
    pub const SYMBOL_TABLE: u8 = 8;
}

/// The relocation metadata extracted from one module's custom sections.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RelocInfo {
    /// The `linking` section version, if a `linking` section was present.
    /// Expected to be 2.
    pub linking_version: Option<u32>,
    /// Raw `linking` subsections, in file order (empty if no `linking`).
    pub linking_subsections: Vec<LinkingSubsection>,
    /// The decoded `reloc.*` sections.
    pub sections: Vec<RelocSection>,
}

/// Errors from relocation-metadata parsing.
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum RelocError {
    /// A LEB128 value ran past the end of the buffer or overflowed.
    #[error("truncated or malformed LEB128 while parsing {context}")]
    BadLeb {
        /// Where the failure happened.
        context: &'static str,
    },
    /// The buffer ended before a required field could be read.
    #[error("unexpected end of {section} section at byte {offset}")]
    UnexpectedEof {
        /// Which section was being parsed.
        section: String,
        /// Byte offset at which the buffer was exhausted.
        offset: usize,
    },
    /// The `linking` section version was not the expected value 2.
    #[error("unsupported linking version {found} (expected 2)")]
    UnsupportedLinkingVersion {
        /// The version byte that was found.
        found: u32,
    },
}

impl From<RelocError> for Error {
    fn from(e: RelocError) -> Self {
        Error::ParseError(e.to_string())
    }
}

/// Read an unsigned LEB128 `u32` from `data[*pos..]`, advancing `*pos`.
fn read_uleb32(data: &[u8], pos: &mut usize, context: &'static str) -> Result<u32> {
    let mut result: u32 = 0;
    let mut shift = 0u32;
    loop {
        let byte = *data.get(*pos).ok_or(RelocError::BadLeb { context })?;
        *pos += 1;
        result |= ((byte & 0x7f) as u32)
            .checked_shl(shift)
            .ok_or(RelocError::BadLeb { context })?;
        if byte & 0x80 == 0 {
            return Ok(result);
        }
        shift += 7;
        if shift >= 32 {
            return Err(RelocError::BadLeb { context }.into());
        }
    }
}

/// Read a signed LEB128 `i32` from `data[*pos..]`, advancing `*pos`.
fn read_sleb32(data: &[u8], pos: &mut usize, context: &'static str) -> Result<i32> {
    let mut result: i32 = 0;
    let mut shift = 0u32;
    loop {
        let byte = *data.get(*pos).ok_or(RelocError::BadLeb { context })?;
        *pos += 1;
        result |= ((byte & 0x7f) as i32)
            .checked_shl(shift)
            .ok_or(RelocError::BadLeb { context })?;
        shift += 7;
        if byte & 0x80 == 0 {
            // Sign-extend if the sign bit of the final group is set.
            if shift < 32 && (byte & 0x40) != 0 {
                result |= !0i32 << shift;
            }
            return Ok(result);
        }
        if shift >= 32 {
            return Err(RelocError::BadLeb { context }.into());
        }
    }
}

/// True if any `linking` or `reloc.*` custom section is present. Cheap probe
/// used to decide whether address-rebasing metadata exists at all.
pub fn has_reloc_metadata(custom_sections: &[(String, Vec<u8>)]) -> bool {
    custom_sections
        .iter()
        .any(|(name, _)| name == "linking" || name.starts_with("reloc."))
}

/// Parse the `linking` + `reloc.*` custom sections captured by meld's parser
/// into structured [`RelocInfo`].
///
/// Modules with no such sections yield an empty (`Default`) `RelocInfo`.
pub fn parse_reloc_info(custom_sections: &[(String, Vec<u8>)]) -> Result<RelocInfo> {
    let mut info = RelocInfo::default();

    for (name, bytes) in custom_sections {
        if name == "linking" {
            let (version, subsections) = parse_linking(bytes)?;
            info.linking_version = Some(version);
            info.linking_subsections = subsections;
        } else if let Some(suffix) = name.strip_prefix("reloc.") {
            info.sections.push(parse_reloc_section(suffix, bytes)?);
        }
    }

    Ok(info)
}

/// Parse a `linking` custom-section body: `version: varuint32` then a sequence
/// of `(id: u8, size: varuint32, bytes)` subsections.
fn parse_linking(body: &[u8]) -> Result<(u32, Vec<LinkingSubsection>)> {
    let mut pos = 0usize;
    let version = read_uleb32(body, &mut pos, "linking version")?;
    if version != 2 {
        return Err(RelocError::UnsupportedLinkingVersion { found: version }.into());
    }

    let mut subsections = Vec::new();
    while pos < body.len() {
        let id = body[pos];
        pos += 1;
        let size = read_uleb32(body, &mut pos, "linking subsection size")? as usize;
        let end = pos
            .checked_add(size)
            .ok_or_else(|| RelocError::UnexpectedEof {
                section: "linking".to_string(),
                offset: pos,
            })?;
        let sub_bytes = body
            .get(pos..end)
            .ok_or_else(|| RelocError::UnexpectedEof {
                section: "linking".to_string(),
                offset: pos,
            })?
            .to_vec();
        subsections.push(LinkingSubsection {
            id,
            bytes: sub_bytes,
        });
        pos = end;
    }

    Ok((version, subsections))
}

/// Parse one `reloc.<suffix>` custom-section body:
/// `target_section: varuint32`, `count: varuint32`, then `count` entries of
/// `type: u8`, `offset: varuint32`, `index: varuint32`,
/// and `addend: varint32` (only when the type carries one).
fn parse_reloc_section(suffix: &str, body: &[u8]) -> Result<RelocSection> {
    let target = match suffix {
        "CODE" => RelocTarget::Code,
        "DATA" => RelocTarget::Data,
        other => RelocTarget::Other(other.to_string()),
    };

    let mut pos = 0usize;
    let target_section_index = read_uleb32(body, &mut pos, "reloc target section")?;
    let count = read_uleb32(body, &mut pos, "reloc count")?;

    let mut entries = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let type_byte = *body.get(pos).ok_or_else(|| RelocError::UnexpectedEof {
            section: format!("reloc.{suffix}"),
            offset: pos,
        })?;
        pos += 1;
        let ty = RelocType::from_code(type_byte);
        let offset = read_uleb32(body, &mut pos, "reloc entry offset")?;
        let index = read_uleb32(body, &mut pos, "reloc entry index")?;
        let addend = if ty.has_addend() {
            read_sleb32(body, &mut pos, "reloc entry addend")?
        } else {
            0
        };
        entries.push(RelocEntry {
            ty,
            offset,
            index,
            addend,
        });
    }

    Ok(RelocSection {
        target,
        target_section_index,
        entries,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    const SPIKE_DIR: &str = "/tmp/spike326";

    /// Ground-truth `reloc.CODE` entries, from `wasm-tools objdump`.
    fn expected_entries() -> Vec<RelocEntry> {
        vec![
            RelocEntry {
                ty: RelocType::MemoryAddrSleb,
                offset: 62,
                index: 3,
                addend: 32,
            },
            RelocEntry {
                ty: RelocType::MemoryAddrSleb,
                offset: 88,
                index: 3,
                addend: 0,
            },
            RelocEntry {
                ty: RelocType::MemoryAddrLeb,
                offset: 132,
                index: 4,
                addend: 0,
            },
            RelocEntry {
                ty: RelocType::MemoryAddrLeb,
                offset: 144,
                index: 4,
                addend: 0,
            },
        ]
    }

    /// Minimal custom-section extractor for a raw core module: walks the
    /// top-level section list and collects `(name, body)` for id-0 sections.
    /// Kept local so the test does not depend on the full meld parser.
    fn extract_custom_sections(module: &[u8]) -> Vec<(String, Vec<u8>)> {
        assert!(module.len() >= 8, "not a wasm module");
        assert_eq!(&module[0..4], b"\0asm", "bad magic");
        let mut pos = 8usize; // skip magic + version
        let mut out = Vec::new();
        while pos < module.len() {
            let id = module[pos];
            pos += 1;
            let mut p = pos;
            let size = read_uleb32(module, &mut p, "section size").expect("section size") as usize;
            let payload_start = p;
            let payload_end = payload_start + size;
            if id == 0 {
                // Custom section: name is a length-prefixed string.
                let mut np = payload_start;
                let name_len = read_uleb32(module, &mut np, "name len").expect("name len") as usize;
                let name = String::from_utf8(module[np..np + name_len].to_vec()).expect("utf8");
                let body = module[np + name_len..payload_end].to_vec();
                out.push((name, body));
            }
            pos = payload_end;
        }
        out
    }

    /// Find the first embedded core module inside a component by locating the
    /// nested `\0asm\x01\0\0\0` magic that starts a core module. Good enough
    /// for the single-core spike fixtures.
    fn embedded_core_module(component: &[u8]) -> Vec<u8> {
        let magic = b"\0asm\x01\0\0\0";
        // The component itself starts with the same magic; skip the first one.
        let mut search_from = 8;
        while let Some(rel) = find_subslice(&component[search_from..], magic) {
            let start = search_from + rel;
            // Heuristic: the core module we want carries reloc metadata.
            let candidate = &component[start..];
            if find_subslice(candidate, b"reloc.CODE").is_some() {
                return candidate.to_vec();
            }
            search_from = start + 8;
        }
        panic!("no embedded core module with reloc.CODE found");
    }

    fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
        haystack.windows(needle.len()).position(|w| w == needle)
    }

    #[test]
    fn parse_reloc_code_matches_spike_fixture() {
        let path = format!("{SPIKE_DIR}/reloc.wasm");
        if !Path::new(&path).exists() {
            eprintln!("skipping: fixture {path} absent");
            return;
        }
        let module = std::fs::read(&path).expect("read reloc.wasm");
        let customs = extract_custom_sections(&module);
        assert!(has_reloc_metadata(&customs));

        let info = parse_reloc_info(&customs).expect("parse");
        assert_eq!(info.linking_version, Some(2));
        assert_eq!(info.sections.len(), 1);
        let sec = &info.sections[0];
        assert_eq!(sec.target, RelocTarget::Code);
        assert_eq!(sec.entries, expected_entries());
    }

    #[test]
    fn reloc_metadata_survives_component_new() {
        let path = format!("{SPIKE_DIR}/reloc.component.wasm");
        if !Path::new(&path).exists() {
            eprintln!("skipping: fixture {path} absent");
            return;
        }
        let component = std::fs::read(&path).expect("read reloc.component.wasm");
        let core = embedded_core_module(&component);
        let customs = extract_custom_sections(&core);
        assert!(has_reloc_metadata(&customs));

        let info = parse_reloc_info(&customs).expect("parse");
        assert_eq!(info.linking_version, Some(2));
        let code = info
            .sections
            .iter()
            .find(|s| s.target == RelocTarget::Code)
            .expect("reloc.CODE present");
        assert_eq!(code.entries, expected_entries());
    }

    #[test]
    fn has_reloc_metadata_false_for_baseline() {
        let path = format!("{SPIKE_DIR}/baseline.component.wasm");
        if !Path::new(&path).exists() {
            eprintln!("skipping: fixture {path} absent");
            return;
        }
        let component = std::fs::read(&path).expect("read baseline.component.wasm");
        // Scan the whole component for any reloc/linking custom section by
        // extracting customs from every embedded core module we can find.
        let magic = b"\0asm\x01\0\0\0";
        let mut any_reloc = false;
        let mut from = 8;
        while let Some(rel) = find_subslice(&component[from..], magic) {
            let start = from + rel;
            let customs = extract_custom_sections(&component[start..]);
            if has_reloc_metadata(&customs) {
                any_reloc = true;
            }
            let info = parse_reloc_info(&customs).expect("parse baseline");
            assert!(info.sections.is_empty());
            from = start + 8;
        }
        assert!(!any_reloc, "baseline must carry no reloc metadata");
    }

    /// The real gate: a hand-built `reloc.CODE` buffer, no file dependency.
    #[test]
    fn parse_hand_built_reloc_bytes() {
        // target_section = 3, count = 2, then two entries.
        //   entry 0: MemoryAddrSleb(4) offset=62 index=3 addend=32
        //   entry 1: MemoryAddrLeb(3)  offset=132 index=4 addend=0
        let body: &[u8] = &[
            0x03, // target section index = 3 (CODE)
            0x02, // count = 2
            // entry 0
            0x04, // MemoryAddrSleb
            0x3e, // offset = 62
            0x03, // index = 3
            0x20, // addend = 32 (sleb)
            // entry 1
            0x03, // MemoryAddrLeb
            0x84, 0x01, // offset = 132 (uleb)
            0x04, // index = 4
            0x00, // addend = 0 (sleb, explicit zero)
        ];
        let customs = vec![("reloc.CODE".to_string(), body.to_vec())];

        assert!(has_reloc_metadata(&customs));
        let info = parse_reloc_info(&customs).expect("parse hand-built");
        assert_eq!(info.linking_version, None);
        assert_eq!(info.sections.len(), 1);
        let sec = &info.sections[0];
        assert_eq!(sec.target, RelocTarget::Code);
        assert_eq!(sec.target_section_index, 3);
        assert_eq!(
            sec.entries,
            vec![
                RelocEntry {
                    ty: RelocType::MemoryAddrSleb,
                    offset: 62,
                    index: 3,
                    addend: 32,
                },
                RelocEntry {
                    ty: RelocType::MemoryAddrLeb,
                    offset: 132,
                    index: 4,
                    addend: 0,
                },
            ]
        );
    }

    #[test]
    fn index_only_types_have_no_addend() {
        // FunctionIndexLeb(0) and GlobalIndexLeb(7) carry NO addend; the next
        // byte after `index` is the following entry's type, not an addend.
        let body: &[u8] = &[
            0x03, // target section index
            0x02, // count = 2
            0x00, 0x05, 0x01, // FunctionIndexLeb offset=5 index=1 (no addend)
            0x07, 0x0a, 0x02, // GlobalIndexLeb   offset=10 index=2 (no addend)
        ];
        let customs = vec![("reloc.CODE".to_string(), body.to_vec())];
        let info = parse_reloc_info(&customs).expect("parse");
        let entries = &info.sections[0].entries;
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].ty, RelocType::FunctionIndexLeb);
        assert_eq!(entries[0].addend, 0);
        assert_eq!(entries[1].ty, RelocType::GlobalIndexLeb);
        assert_eq!(entries[1].offset, 10);
        assert_eq!(entries[1].index, 2);
    }

    #[test]
    fn negative_addend_sign_extends() {
        // addend = -1 encodes as 0x7f in sleb128.
        let body: &[u8] = &[0x00, 0x01, 0x04, 0x00, 0x00, 0x7f];
        let customs = vec![("reloc.CODE".to_string(), body.to_vec())];
        let info = parse_reloc_info(&customs).expect("parse");
        assert_eq!(info.sections[0].entries[0].addend, -1);
    }

    #[test]
    fn reloc_type_predicates() {
        assert!(RelocType::MemoryAddrLeb.is_memory_addr());
        assert!(RelocType::MemoryAddrSleb.has_addend());
        assert!(RelocType::MemoryAddrLeb.has_addend());
        assert!(!RelocType::FunctionIndexLeb.has_addend());
        assert!(!RelocType::FunctionIndexLeb.is_memory_addr());
        assert!(RelocType::from_code(4) == RelocType::MemoryAddrSleb);
        assert!(matches!(RelocType::from_code(200), RelocType::Other(200)));
        assert_eq!(RelocType::Other(200).code(), 200);
    }

    #[test]
    fn empty_custom_sections_yield_empty_info() {
        let info = parse_reloc_info(&[]).expect("parse");
        assert!(info.sections.is_empty());
        assert_eq!(info.linking_version, None);
        assert!(!has_reloc_metadata(&[]));
    }
}
