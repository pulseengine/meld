//! FACT-style adapter generation
//!
//! This module implements adapter generation in the style of wasmtime's FACT
//! (Fused Adapter Compiler of Trampolines). It generates adapter functions
//! that handle:
//!
//! - Cross-memory data copying
//! - String transcoding (UTF-8 ↔ UTF-16 ↔ Latin-1)
//! - List/array copying
//! - Resource handle transfer
//!
//! ## FACT Overview
//!
//! FACT in wasmtime generates adapter modules that sit between components.
//! For static fusion, we generate similar adapters but inline them directly
//! into the fused module rather than keeping them as separate adapter modules.

use super::{
    AdapterClass, AdapterConfig, AdapterFunction, AdapterGenerator, AdapterOptions, StringEncoding,
};
use crate::Result;
use crate::merger::MergedModule;
use crate::parser::CanonStringEncoding;
use crate::resolver::{AdapterSite, DependencyGraph};
use wasm_encoder::{Function, Instruction};

/// Convert a canonical string encoding from the parser to the adapter's encoding enum
/// Parse a wit-bindgen-style `(import_module, import_field)` pair to extract
/// the interface name and (when present) the resource name.
///
/// `import_module` may carry the wit-bindgen `[export]` prefix when the
/// import refers to the importer's own export resource — strip it.
/// `import_field` looks like `[resource-rep]X`, `[resource-new]X`, or
/// `[resource-drop]X` for resource helpers; otherwise no resource name
/// is returned.
fn parse_resource_import(import_module: &str, import_field: &str) -> (String, Option<String>) {
    let iface = import_module
        .strip_prefix("[export]")
        .unwrap_or(import_module)
        .to_string();
    let rn = import_field
        .strip_prefix("[resource-rep]")
        .or_else(|| import_field.strip_prefix("[resource-new]"))
        .or_else(|| import_field.strip_prefix("[resource-drop]"))
        .map(|s| s.to_string());
    (iface, rn)
}

fn canon_to_string_encoding(enc: CanonStringEncoding) -> StringEncoding {
    match enc {
        CanonStringEncoding::Utf8 => StringEncoding::Utf8,
        CanonStringEncoding::Utf16 => StringEncoding::Utf16,
        // CompactUTF16 is latin1+utf16 — modelled as `Latin1`, which in meld
        // means the canonical-ABI `latin1+utf16` encoding (the length operand
        // is tag-bit encoded; see [`UTF16_TAG`]). It is NOT a pure-Latin-1
        // encoding: a tag-set string carries UTF-16 payload.
        CanonStringEncoding::CompactUtf16 => StringEncoding::Latin1,
    }
}

/// The canonical-ABI `latin1+utf16` length-operand tag bit (`1 << 31`).
///
/// A `latin1+utf16` string's length operand is *tagged*:
/// - tag **clear** → the payload is Latin-1 (1 byte per char); the byte length
///   equals the operand.
/// - tag **set** → the payload is UTF-16; the *code-unit count* is
///   `operand & !UTF16_TAG`, and the byte length is that count × 2.
///
/// meld models `latin1+utf16` as [`StringEncoding::Latin1`]; the transcoders
/// that have `Latin1` as a source must branch on this bit, and those that
/// produce `Latin1` set it when they fall back to UTF-16.
pub(crate) const UTF16_TAG: i32 = 1 << 31;

/// Return the required alignment for a cabi_realloc call for the given string encoding
fn alignment_for_encoding(encoding: StringEncoding) -> i32 {
    match encoding {
        StringEncoding::Utf8 => 1,
        // latin1+utf16: the destination buffer may hold UTF-16 code units, so
        // the canonical ABI requires 2-byte alignment for the string pointer
        // (the realloc backing the tag-set fallback writes i16s).
        StringEncoding::Latin1 | StringEncoding::Utf16 => 2,
    }
}

/// Build a lookup from `(module, field)` → merged function index for resource imports.
///
/// Emit a safe `cabi_realloc` call: traps via `unreachable` if the returned
/// pointer is 0 (OOM). Caller must have pushed the 4 realloc arguments onto
/// the stack (`old_ptr`, `old_size`, `align`, `new_size`) immediately before
/// calling this helper. After the call, the (checked, non-null) pointer is
/// stored in `result_local`.
///
/// This is the fix for LS-A-7 leg (b): an unchecked realloc return lets the
/// transcode/copy loop write into callee memory offset 0 on OOM.
pub(crate) fn emit_checked_realloc(body: &mut Function, realloc_func: u32, result_local: u32) {
    body.instruction(&Instruction::Call(realloc_func));
    body.instruction(&Instruction::LocalSet(result_local));
    body.instruction(&Instruction::LocalGet(result_local));
    body.instruction(&Instruction::I32Eqz);
    body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::Unreachable);
    body.instruction(&Instruction::End);
}

/// Emit an overflow guard: traps via `unreachable` if `len_local * k` would
/// wrap in 32-bit unsigned arithmetic. Caller supplies the local holding the
/// untrusted length and the constant multiplier `k`. No-op when `k <= 1`.
///
/// This is the fix for LS-A-7 leg (a): `i32.mul` is modulo 2^32, so a large
/// caller-chosen `len` can wrap to a small allocation size while the copy
/// loop still writes the full `len * k` bytes, producing an OOB write into
/// callee memory.
pub(crate) fn emit_overflow_guard(body: &mut Function, len_local: u32, k: u32) {
    if k <= 1 {
        return;
    }
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32Const((u32::MAX / k) as i32));
    body.instruction(&Instruction::I32GtU);
    body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::Unreachable);
    body.instruction(&Instruction::End);
}

/// Push the byte length of a copied string/list buffer onto the stack.
///
/// For a `latin1+utf16` string (the `Latin1` encoding, `byte_mult == 1`) the
/// `(ptr, len)` length operand is **tagged** (see [`UTF16_TAG`]): tag set ⇒ the
/// payload is UTF-16, so the byte length is `(len & !UTF16_TAG) * 2`; tag clear
/// ⇒ Latin-1, byte length `len`. A same-encoding cross-memory copy
/// ([`generate_memory_copy_adapter`]) must use this tag-aware byte count for
/// both the `cabi_realloc` size and the `memory.copy` length — copying the raw
/// tagged operand would copy `count | 0x8000_0000` bytes (~2 GiB OOB read).
/// The length operand FORWARDED to the callee stays tagged; only the internal
/// byte count is masked here.
///
/// For every other buffer (`byte_mult != 1`, or a non-Latin1 encoding) the
/// length is an untagged element count, byte length `len * byte_mult`. A plain
/// `list<u8>` (also `byte_mult == 1`) is unaffected: a legitimate byte count is
/// `< 2^31` (the [`emit_overflow_guard`] bound), so the tag bit is clear and
/// the tag-aware path returns `len` unchanged.
fn emit_copy_byte_count(
    func: &mut Function,
    len_local: u32,
    byte_mult: u32,
    is_compact_utf16: bool,
) {
    if is_compact_utf16 {
        // bytes = (len & UTF16_TAG) ? (len & !UTF16_TAG) * 2 : len
        func.instruction(&Instruction::LocalGet(len_local));
        func.instruction(&Instruction::I32Const(UTF16_TAG));
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Result(
            wasm_encoder::ValType::I32,
        )));
        func.instruction(&Instruction::LocalGet(len_local));
        func.instruction(&Instruction::I32Const(!UTF16_TAG));
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Mul);
        func.instruction(&Instruction::Else);
        func.instruction(&Instruction::LocalGet(len_local));
        func.instruction(&Instruction::End);
    } else {
        func.instruction(&Instruction::LocalGet(len_local));
        if byte_mult > 1 {
            func.instruction(&Instruction::I32Const(byte_mult as i32));
            func.instruction(&Instruction::I32Mul);
        }
    }
}

/// Emit the hardened UTF-8 → code-point decoder for one code point.
///
/// Reads the lead byte at `mem8[ptr_local + src_idx_local]`, decodes a full
/// UTF-8 sequence into `cp_local`, and advances `src_idx_local` past the bytes
/// consumed. `len_local` bounds the buffer. Malformed input (truncation,
/// invalid continuation, overlong, surrogate, out-of-range, lone continuation)
/// is replaced with U+FFFD, consuming only the lead byte (the #251/#249/LS-P-19
/// Canonical-ABI lossy-replacement convention). `byte_local` and `cont_local`
/// are scratch. `ptr_local` is the local holding the source base pointer
/// (param 0 for the standard caller-string layout).
///
/// Extracted from `emit_utf8_to_utf16_transcode` (#253) so the UTF-8 → Latin-1
/// scan/write phases share the exact same validated decoder rather than a
/// re-derived copy that could drift.
#[allow(clippy::too_many_arguments)]
fn emit_utf8_decode_codepoint(
    func: &mut Function,
    src_mem8: wasm_encoder::MemArg,
    ptr_local: u32,
    src_idx_local: u32,
    len_local: u32,
    byte_local: u32,
    cp_local: u32,
    cont_local: u32,
) {
    // Read lead byte from source memory.
    func.instruction(&Instruction::LocalGet(ptr_local));
    func.instruction(&Instruction::LocalGet(src_idx_local));
    func.instruction(&Instruction::I32Add);
    func.instruction(&Instruction::I32Load8U(src_mem8));
    func.instruction(&Instruction::LocalSet(byte_local));

    // Emit: cp = U+FFFD; src_idx += 1 (replacement, consume lead only).
    let emit_fffd_consume_lead = |func: &mut Function| {
        func.instruction(&Instruction::I32Const(0xFFFD));
        func.instruction(&Instruction::LocalSet(cp_local));
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(src_idx_local));
    };
    // Push mem8[ptr + src_idx + off] onto the stack (a continuation byte).
    let push_byte_at = |func: &mut Function, off: i32| {
        func.instruction(&Instruction::LocalGet(ptr_local));
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Const(off));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Load8U(src_mem8));
    };
    // Push: (cont_local & 0xC0) != 0x80  (true => NOT a continuation byte).
    let push_not_continuation = |func: &mut Function| {
        func.instruction(&Instruction::LocalGet(cont_local));
        func.instruction(&Instruction::I32Const(0xC0));
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::I32Const(0x80));
        func.instruction(&Instruction::I32Ne);
    };

    // if byte < 0x80: 1-byte ASCII
    func.instruction(&Instruction::LocalGet(byte_local));
    func.instruction(&Instruction::I32Const(0x80));
    func.instruction(&Instruction::I32LtU);
    func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    {
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::LocalSet(cp_local));
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(src_idx_local));
    }
    func.instruction(&Instruction::Else);
    {
        // if byte < 0xC2: invalid lead → U+FFFD, consume lead only.
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::I32Const(0xC2));
        func.instruction(&Instruction::I32LtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            emit_fffd_consume_lead(func);
        }
        func.instruction(&Instruction::Else);
        {
            // if byte < 0xE0: 2-byte sequence (lead 0xC2–0xDF).
            func.instruction(&Instruction::LocalGet(byte_local));
            func.instruction(&Instruction::I32Const(0xE0));
            func.instruction(&Instruction::I32LtU);
            func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
            {
                // Truncation guard.
                func.instruction(&Instruction::LocalGet(src_idx_local));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalGet(len_local));
                func.instruction(&Instruction::I32GeU);
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                {
                    emit_fffd_consume_lead(func);
                }
                func.instruction(&Instruction::Else);
                {
                    push_byte_at(func, 1);
                    func.instruction(&Instruction::LocalSet(cont_local));
                    push_not_continuation(func);
                    func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                    {
                        emit_fffd_consume_lead(func);
                    }
                    func.instruction(&Instruction::Else);
                    {
                        // cp = (byte & 0x1F) << 6 | (b1 & 0x3F)
                        func.instruction(&Instruction::LocalGet(byte_local));
                        func.instruction(&Instruction::I32Const(0x1F));
                        func.instruction(&Instruction::I32And);
                        func.instruction(&Instruction::I32Const(6));
                        func.instruction(&Instruction::I32Shl);
                        func.instruction(&Instruction::LocalGet(cont_local));
                        func.instruction(&Instruction::I32Const(0x3F));
                        func.instruction(&Instruction::I32And);
                        func.instruction(&Instruction::I32Or);
                        func.instruction(&Instruction::LocalSet(cp_local));
                        func.instruction(&Instruction::LocalGet(src_idx_local));
                        func.instruction(&Instruction::I32Const(2));
                        func.instruction(&Instruction::I32Add);
                        func.instruction(&Instruction::LocalSet(src_idx_local));
                    }
                    func.instruction(&Instruction::End);
                }
                func.instruction(&Instruction::End);
            }
            func.instruction(&Instruction::Else);
            {
                // if byte < 0xF0: 3-byte sequence (lead 0xE0–0xEF).
                func.instruction(&Instruction::LocalGet(byte_local));
                func.instruction(&Instruction::I32Const(0xF0));
                func.instruction(&Instruction::I32LtU);
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                {
                    func.instruction(&Instruction::LocalGet(src_idx_local));
                    func.instruction(&Instruction::I32Const(2));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::LocalGet(len_local));
                    func.instruction(&Instruction::I32GeU);
                    func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                    {
                        emit_fffd_consume_lead(func);
                    }
                    func.instruction(&Instruction::Else);
                    {
                        push_byte_at(func, 1);
                        func.instruction(&Instruction::LocalSet(cont_local));
                        push_not_continuation(func);
                        push_byte_at(func, 2);
                        func.instruction(&Instruction::LocalSet(cont_local));
                        push_not_continuation(func);
                        func.instruction(&Instruction::I32Or);
                        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                        {
                            emit_fffd_consume_lead(func);
                        }
                        func.instruction(&Instruction::Else);
                        {
                            func.instruction(&Instruction::LocalGet(byte_local));
                            func.instruction(&Instruction::I32Const(0x0F));
                            func.instruction(&Instruction::I32And);
                            func.instruction(&Instruction::I32Const(12));
                            func.instruction(&Instruction::I32Shl);
                            push_byte_at(func, 1);
                            func.instruction(&Instruction::I32Const(0x3F));
                            func.instruction(&Instruction::I32And);
                            func.instruction(&Instruction::I32Const(6));
                            func.instruction(&Instruction::I32Shl);
                            func.instruction(&Instruction::I32Or);
                            push_byte_at(func, 2);
                            func.instruction(&Instruction::I32Const(0x3F));
                            func.instruction(&Instruction::I32And);
                            func.instruction(&Instruction::I32Or);
                            func.instruction(&Instruction::LocalSet(cp_local));
                            // reject overlong (< 0x800) and surrogate.
                            func.instruction(&Instruction::LocalGet(cp_local));
                            func.instruction(&Instruction::I32Const(0x800));
                            func.instruction(&Instruction::I32LtU);
                            func.instruction(&Instruction::LocalGet(cp_local));
                            func.instruction(&Instruction::I32Const(0xD800));
                            func.instruction(&Instruction::I32GeU);
                            func.instruction(&Instruction::LocalGet(cp_local));
                            func.instruction(&Instruction::I32Const(0xE000));
                            func.instruction(&Instruction::I32LtU);
                            func.instruction(&Instruction::I32And);
                            func.instruction(&Instruction::I32Or);
                            func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                            {
                                emit_fffd_consume_lead(func);
                            }
                            func.instruction(&Instruction::Else);
                            {
                                func.instruction(&Instruction::LocalGet(src_idx_local));
                                func.instruction(&Instruction::I32Const(3));
                                func.instruction(&Instruction::I32Add);
                                func.instruction(&Instruction::LocalSet(src_idx_local));
                            }
                            func.instruction(&Instruction::End);
                        }
                        func.instruction(&Instruction::End);
                    }
                    func.instruction(&Instruction::End);
                }
                func.instruction(&Instruction::Else);
                {
                    // 4-byte sequence (byte >= 0xF0).
                    func.instruction(&Instruction::LocalGet(byte_local));
                    func.instruction(&Instruction::I32Const(0xF5));
                    func.instruction(&Instruction::I32GeU);
                    func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                    {
                        emit_fffd_consume_lead(func);
                    }
                    func.instruction(&Instruction::Else);
                    {
                        func.instruction(&Instruction::LocalGet(src_idx_local));
                        func.instruction(&Instruction::I32Const(3));
                        func.instruction(&Instruction::I32Add);
                        func.instruction(&Instruction::LocalGet(len_local));
                        func.instruction(&Instruction::I32GeU);
                        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                        {
                            emit_fffd_consume_lead(func);
                        }
                        func.instruction(&Instruction::Else);
                        {
                            push_byte_at(func, 1);
                            func.instruction(&Instruction::LocalSet(cont_local));
                            push_not_continuation(func);
                            push_byte_at(func, 2);
                            func.instruction(&Instruction::LocalSet(cont_local));
                            push_not_continuation(func);
                            func.instruction(&Instruction::I32Or);
                            push_byte_at(func, 3);
                            func.instruction(&Instruction::LocalSet(cont_local));
                            push_not_continuation(func);
                            func.instruction(&Instruction::I32Or);
                            func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                            {
                                emit_fffd_consume_lead(func);
                            }
                            func.instruction(&Instruction::Else);
                            {
                                func.instruction(&Instruction::LocalGet(byte_local));
                                func.instruction(&Instruction::I32Const(0x07));
                                func.instruction(&Instruction::I32And);
                                func.instruction(&Instruction::I32Const(18));
                                func.instruction(&Instruction::I32Shl);
                                push_byte_at(func, 1);
                                func.instruction(&Instruction::I32Const(0x3F));
                                func.instruction(&Instruction::I32And);
                                func.instruction(&Instruction::I32Const(12));
                                func.instruction(&Instruction::I32Shl);
                                func.instruction(&Instruction::I32Or);
                                push_byte_at(func, 2);
                                func.instruction(&Instruction::I32Const(0x3F));
                                func.instruction(&Instruction::I32And);
                                func.instruction(&Instruction::I32Const(6));
                                func.instruction(&Instruction::I32Shl);
                                func.instruction(&Instruction::I32Or);
                                push_byte_at(func, 3);
                                func.instruction(&Instruction::I32Const(0x3F));
                                func.instruction(&Instruction::I32And);
                                func.instruction(&Instruction::I32Or);
                                func.instruction(&Instruction::LocalSet(cp_local));
                                // reject overlong (< 0x10000) and oor (> 0x10FFFF).
                                func.instruction(&Instruction::LocalGet(cp_local));
                                func.instruction(&Instruction::I32Const(0x10000));
                                func.instruction(&Instruction::I32LtU);
                                func.instruction(&Instruction::LocalGet(cp_local));
                                func.instruction(&Instruction::I32Const(0x10FFFF));
                                func.instruction(&Instruction::I32GtU);
                                func.instruction(&Instruction::I32Or);
                                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                                {
                                    emit_fffd_consume_lead(func);
                                }
                                func.instruction(&Instruction::Else);
                                {
                                    func.instruction(&Instruction::LocalGet(src_idx_local));
                                    func.instruction(&Instruction::I32Const(4));
                                    func.instruction(&Instruction::I32Add);
                                    func.instruction(&Instruction::LocalSet(src_idx_local));
                                }
                                func.instruction(&Instruction::End);
                            }
                            func.instruction(&Instruction::End);
                        }
                        func.instruction(&Instruction::End);
                    }
                    func.instruction(&Instruction::End);
                }
                func.instruction(&Instruction::End); // end 3-byte vs 4-byte
            }
            func.instruction(&Instruction::End); // end 2-byte vs 3+byte
        }
        func.instruction(&Instruction::End); // end invalid-lead vs valid-multibyte
    }
    func.instruction(&Instruction::End); // end 1-byte vs 2+byte
}

/// Emit the UTF-16 → code-point decoder for one code point.
///
/// Reads the code unit at `mem16[ptr_local + src_idx_local*2]`, decodes a full
/// scalar value into `cp_local`, and advances `src_idx_local` (by 1 for a BMP
/// scalar / replaced lone surrogate, by 2 for a valid surrogate pair).
/// `len_local` bounds the buffer (code-unit count). Lone surrogates (high at
/// EOF, high not followed by low, or lone low) are replaced with U+FFFD per the
/// Canonical ABI, mirroring `emit_utf16_to_utf8_transcode`. `cu2_local` is
/// scratch. Extracted for #253 so the UTF-16 → Latin-1 scan/write phases share
/// one validated decoder.
#[allow(clippy::too_many_arguments)]
fn emit_utf16_decode_codepoint(
    func: &mut Function,
    src_mem16: wasm_encoder::MemArg,
    ptr_local: u32,
    src_idx_local: u32,
    len_local: u32,
    cu_local: u32,
    cp_local: u32,
    cu2_local: u32,
) {
    // cu = mem16[ptr + src_idx*2]
    func.instruction(&Instruction::LocalGet(ptr_local));
    func.instruction(&Instruction::LocalGet(src_idx_local));
    func.instruction(&Instruction::I32Const(1));
    func.instruction(&Instruction::I32Shl);
    func.instruction(&Instruction::I32Add);
    func.instruction(&Instruction::I32Load16U(src_mem16));
    func.instruction(&Instruction::LocalSet(cu_local));

    // if cu is a high surrogate (0xD800..0xDC00)
    func.instruction(&Instruction::LocalGet(cu_local));
    func.instruction(&Instruction::I32Const(0xD800_u32 as i32));
    func.instruction(&Instruction::I32GeU);
    func.instruction(&Instruction::LocalGet(cu_local));
    func.instruction(&Instruction::I32Const(0xDC00_u32 as i32));
    func.instruction(&Instruction::I32LtU);
    func.instruction(&Instruction::I32And);
    func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    {
        // High surrogate. If it's the last unit → U+FFFD, consume 1.
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalGet(len_local));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            func.instruction(&Instruction::I32Const(0xFFFD));
            func.instruction(&Instruction::LocalSet(cp_local));
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(src_idx_local));
        }
        func.instruction(&Instruction::Else);
        {
            // cu2 = mem16[ptr + (src_idx+1)*2]
            func.instruction(&Instruction::LocalGet(ptr_local));
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Shl);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Load16U(src_mem16));
            func.instruction(&Instruction::LocalSet(cu2_local));
            // is cu2 a low surrogate?
            func.instruction(&Instruction::LocalGet(cu2_local));
            func.instruction(&Instruction::I32Const(0xDC00_u32 as i32));
            func.instruction(&Instruction::I32GeU);
            func.instruction(&Instruction::LocalGet(cu2_local));
            func.instruction(&Instruction::I32Const(0xE000_u32 as i32));
            func.instruction(&Instruction::I32LtU);
            func.instruction(&Instruction::I32And);
            func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
            {
                // cp = 0x10000 + ((cu-0xD800)<<10) + (cu2-0xDC00); consume 2.
                func.instruction(&Instruction::I32Const(0x10000));
                func.instruction(&Instruction::LocalGet(cu_local));
                func.instruction(&Instruction::I32Const(0xD800_u32 as i32));
                func.instruction(&Instruction::I32Sub);
                func.instruction(&Instruction::I32Const(10));
                func.instruction(&Instruction::I32Shl);
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalGet(cu2_local));
                func.instruction(&Instruction::I32Const(0xDC00_u32 as i32));
                func.instruction(&Instruction::I32Sub);
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalSet(cp_local));
                func.instruction(&Instruction::LocalGet(src_idx_local));
                func.instruction(&Instruction::I32Const(2));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalSet(src_idx_local));
            }
            func.instruction(&Instruction::Else);
            {
                // Mid-string lone high surrogate → U+FFFD, consume 1.
                func.instruction(&Instruction::I32Const(0xFFFD));
                func.instruction(&Instruction::LocalSet(cp_local));
                func.instruction(&Instruction::LocalGet(src_idx_local));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalSet(src_idx_local));
            }
            func.instruction(&Instruction::End);
        }
        func.instruction(&Instruction::End);
    }
    func.instruction(&Instruction::Else);
    {
        // Not a high surrogate. Lone low surrogate → U+FFFD, else cp = cu.
        func.instruction(&Instruction::LocalGet(cu_local));
        func.instruction(&Instruction::I32Const(0xDC00_u32 as i32));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::LocalGet(cu_local));
        func.instruction(&Instruction::I32Const(0xE000_u32 as i32));
        func.instruction(&Instruction::I32LtU);
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            func.instruction(&Instruction::I32Const(0xFFFD));
            func.instruction(&Instruction::LocalSet(cp_local));
        }
        func.instruction(&Instruction::Else);
        {
            func.instruction(&Instruction::LocalGet(cu_local));
            func.instruction(&Instruction::LocalSet(cp_local));
        }
        func.instruction(&Instruction::End);
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(src_idx_local));
    }
    func.instruction(&Instruction::End);
}

/// Emit the code-point → UTF-16 encoder for one code point.
///
/// Writes `cp_local` to `mem16[out_ptr_local + dst_idx_local*2]` as one BMP
/// code unit, or as a surrogate pair for cp >= 0x10000, advancing
/// `dst_idx_local` by 1 or 2 code units. Mirrors the encoder in
/// `emit_utf8_to_utf16_transcode`. Extracted for #253.
fn emit_utf16_encode_codepoint(
    func: &mut Function,
    dst_mem16: wasm_encoder::MemArg,
    out_ptr_local: u32,
    dst_idx_local: u32,
    cp_local: u32,
) {
    func.instruction(&Instruction::LocalGet(cp_local));
    func.instruction(&Instruction::I32Const(0x10000));
    func.instruction(&Instruction::I32LtU);
    func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    {
        // BMP: one code unit.
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Shl);
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalGet(cp_local));
        func.instruction(&Instruction::I32Store16(dst_mem16));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(dst_idx_local));
    }
    func.instruction(&Instruction::Else);
    {
        // Supplementary: surrogate pair.
        // high = 0xD800 + ((cp - 0x10000) >> 10)
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Shl);
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Const(0xD800));
        func.instruction(&Instruction::LocalGet(cp_local));
        func.instruction(&Instruction::I32Const(0x10000));
        func.instruction(&Instruction::I32Sub);
        func.instruction(&Instruction::I32Const(10));
        func.instruction(&Instruction::I32ShrU);
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Store16(dst_mem16));
        // low = 0xDC00 + ((cp - 0x10000) & 0x3FF)
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Shl);
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Const(0xDC00));
        func.instruction(&Instruction::LocalGet(cp_local));
        func.instruction(&Instruction::I32Const(0x10000));
        func.instruction(&Instruction::I32Sub);
        func.instruction(&Instruction::I32Const(0x3FF));
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Store16(dst_mem16));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(dst_idx_local));
    }
    func.instruction(&Instruction::End);
}

/// Emit the code-point → UTF-8 encoder for one code point.
///
/// Writes `cp_local` to `mem8[out_ptr_local + dst_idx_local]` as 1–4 UTF-8
/// bytes (cp<0x80 → 1; <0x800 → 2; <0x10000 → 3; else → 4), advancing
/// `dst_idx_local` by the number of bytes written. Extracted verbatim from the
/// sync [`FactStyleGenerator::emit_utf16_to_utf8_transcode`] encode tail (#272
/// inc 2) so the sync transcoder and the async param transcoder
/// ([`emit_utf16_to_utf8_transcode_param`]) share ONE validated encoder and
/// cannot drift. Uses no scratch beyond `cp_local` / `dst_idx_local`.
fn emit_utf8_encode_codepoint(
    func: &mut Function,
    dst_mem8: wasm_encoder::MemArg,
    out_ptr_local: u32,
    dst_idx_local: u32,
    cp_local: u32,
) {
    // if code_point < 0x80: 1-byte
    func.instruction(&Instruction::LocalGet(cp_local));
    func.instruction(&Instruction::I32Const(0x80));
    func.instruction(&Instruction::I32LtU);
    func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    {
        // out[dst_idx] = code_point
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalGet(cp_local));
        func.instruction(&Instruction::I32Store8(dst_mem8));
        // dst_idx += 1
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(dst_idx_local));
    }
    func.instruction(&Instruction::Else);
    {
        // if code_point < 0x800: 2-byte
        func.instruction(&Instruction::LocalGet(cp_local));
        func.instruction(&Instruction::I32Const(0x800));
        func.instruction(&Instruction::I32LtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            // out[dst_idx] = 0xC0 | (cp >> 6)
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(0xC0));
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Const(6));
            func.instruction(&Instruction::I32ShrU);
            func.instruction(&Instruction::I32Or);
            func.instruction(&Instruction::I32Store8(dst_mem8));
            // out[dst_idx+1] = 0x80 | (cp & 0x3F)
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(0x80));
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Const(0x3F));
            func.instruction(&Instruction::I32And);
            func.instruction(&Instruction::I32Or);
            func.instruction(&Instruction::I32Store8(dst_mem8));
            // dst_idx += 2
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(2));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(dst_idx_local));
        }
        func.instruction(&Instruction::Else);
        {
            // if code_point < 0x10000: 3-byte
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Const(0x10000));
            func.instruction(&Instruction::I32LtU);
            func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
            {
                // out[dst_idx] = 0xE0 | (cp >> 12)
                func.instruction(&Instruction::LocalGet(out_ptr_local));
                func.instruction(&Instruction::LocalGet(dst_idx_local));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(0xE0_u32 as i32));
                func.instruction(&Instruction::LocalGet(cp_local));
                func.instruction(&Instruction::I32Const(12));
                func.instruction(&Instruction::I32ShrU);
                func.instruction(&Instruction::I32Or);
                func.instruction(&Instruction::I32Store8(dst_mem8));
                // out[dst_idx+1] = 0x80 | ((cp >> 6) & 0x3F)
                func.instruction(&Instruction::LocalGet(out_ptr_local));
                func.instruction(&Instruction::LocalGet(dst_idx_local));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(0x80));
                func.instruction(&Instruction::LocalGet(cp_local));
                func.instruction(&Instruction::I32Const(6));
                func.instruction(&Instruction::I32ShrU);
                func.instruction(&Instruction::I32Const(0x3F));
                func.instruction(&Instruction::I32And);
                func.instruction(&Instruction::I32Or);
                func.instruction(&Instruction::I32Store8(dst_mem8));
                // out[dst_idx+2] = 0x80 | (cp & 0x3F)
                func.instruction(&Instruction::LocalGet(out_ptr_local));
                func.instruction(&Instruction::LocalGet(dst_idx_local));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(2));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(0x80));
                func.instruction(&Instruction::LocalGet(cp_local));
                func.instruction(&Instruction::I32Const(0x3F));
                func.instruction(&Instruction::I32And);
                func.instruction(&Instruction::I32Or);
                func.instruction(&Instruction::I32Store8(dst_mem8));
                // dst_idx += 3
                func.instruction(&Instruction::LocalGet(dst_idx_local));
                func.instruction(&Instruction::I32Const(3));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalSet(dst_idx_local));
            }
            func.instruction(&Instruction::Else);
            {
                // 4-byte: code_point >= 0x10000
                // out[dst_idx] = 0xF0 | (cp >> 18)
                func.instruction(&Instruction::LocalGet(out_ptr_local));
                func.instruction(&Instruction::LocalGet(dst_idx_local));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(0xF0_u32 as i32));
                func.instruction(&Instruction::LocalGet(cp_local));
                func.instruction(&Instruction::I32Const(18));
                func.instruction(&Instruction::I32ShrU);
                func.instruction(&Instruction::I32Or);
                func.instruction(&Instruction::I32Store8(dst_mem8));
                // out[dst_idx+1] = 0x80 | ((cp >> 12) & 0x3F)
                func.instruction(&Instruction::LocalGet(out_ptr_local));
                func.instruction(&Instruction::LocalGet(dst_idx_local));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(0x80));
                func.instruction(&Instruction::LocalGet(cp_local));
                func.instruction(&Instruction::I32Const(12));
                func.instruction(&Instruction::I32ShrU);
                func.instruction(&Instruction::I32Const(0x3F));
                func.instruction(&Instruction::I32And);
                func.instruction(&Instruction::I32Or);
                func.instruction(&Instruction::I32Store8(dst_mem8));
                // out[dst_idx+2] = 0x80 | ((cp >> 6) & 0x3F)
                func.instruction(&Instruction::LocalGet(out_ptr_local));
                func.instruction(&Instruction::LocalGet(dst_idx_local));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(2));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(0x80));
                func.instruction(&Instruction::LocalGet(cp_local));
                func.instruction(&Instruction::I32Const(6));
                func.instruction(&Instruction::I32ShrU);
                func.instruction(&Instruction::I32Const(0x3F));
                func.instruction(&Instruction::I32And);
                func.instruction(&Instruction::I32Or);
                func.instruction(&Instruction::I32Store8(dst_mem8));
                // out[dst_idx+3] = 0x80 | (cp & 0x3F)
                func.instruction(&Instruction::LocalGet(out_ptr_local));
                func.instruction(&Instruction::LocalGet(dst_idx_local));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(3));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(0x80));
                func.instruction(&Instruction::LocalGet(cp_local));
                func.instruction(&Instruction::I32Const(0x3F));
                func.instruction(&Instruction::I32And);
                func.instruction(&Instruction::I32Or);
                func.instruction(&Instruction::I32Store8(dst_mem8));
                // dst_idx += 4
                func.instruction(&Instruction::LocalGet(dst_idx_local));
                func.instruction(&Instruction::I32Const(4));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalSet(dst_idx_local));
            }
            func.instruction(&Instruction::End); // end 3-byte vs 4-byte
        }
        func.instruction(&Instruction::End); // end 2-byte vs 3+byte
    }
    func.instruction(&Instruction::End); // end 1-byte vs 2+byte
}

/// Emit a UTF-8 → UTF-16 transcode of a single top-level `(ptr, len)` string
/// param on the async-lift cross-memory copy path (#272 inc 1).
///
/// Unlike the sync [`FactStyleGenerator::emit_utf8_to_utf16_transcode`], this
/// helper is FULLY parameterised by local indices and MemArgs (no hidden
/// local-0/1 / param-shape assumptions) and emits NO `Call` — it is composed
/// from the shared, validated [`emit_utf8_decode_codepoint`] +
/// [`emit_utf16_encode_codepoint`] codepoint helpers so it cannot drift from
/// the sync decoder/encoder.
///
/// Contract:
/// * `ptr_local` / `len_local` hold the CALLER-memory source pointer and the
///   source byte length. On return, `ptr_local` is rewritten to the freshly
///   reallocated CALLEE-memory output pointer and `len_local` is rewritten to
///   the output UTF-16 **code-unit count** (NOT a byte count) — the operand a
///   UTF-16 lifting callee reads. Failing to rewrite `len_local` would
///   silently mis-size the callee's view of the string.
/// * `out_ptr_local` receives the realloc result (the callee output buffer).
/// * `src_idx_local`, `dst_idx_local`, `cp_local`, `byte_local`,
///   `cont_local` are dedicated scratch i32 locals the caller must reserve;
///   they must not alias `ptr_local`/`len_local` or each other.
///
/// Sizing (mirrors the sync emitter's LS-A-7 guards): each UTF-8 byte yields
/// at most one UTF-16 code unit, so the worst case is `len` code units =
/// `2 * len` bytes. `2 * len` is computed with an i32-overflow guard before
/// the multiply (trap if `len > u32::MAX/2`), and the realloc return is
/// null-checked, both via the shared helpers.
#[allow(clippy::too_many_arguments)]
fn emit_utf8_to_utf16_transcode_param(
    body: &mut Function,
    realloc_func: u32,
    src_mem8: wasm_encoder::MemArg,
    dst_mem16: wasm_encoder::MemArg,
    ptr_local: u32,
    len_local: u32,
    out_ptr_local: u32,
    src_idx_local: u32,
    dst_idx_local: u32,
    cp_local: u32,
    byte_local: u32,
    cont_local: u32,
) {
    // Allocate output buffer = 2 * len bytes (each UTF-8 byte → ≤ 1 UTF-16
    // code unit = 2 bytes). LS-A-7 leg (a): guard the *2 against i32 wrap;
    // leg (b): emit_checked_realloc traps on a null return.
    emit_overflow_guard(body, len_local, 2);
    body.instruction(&Instruction::I32Const(0)); // old_ptr
    body.instruction(&Instruction::I32Const(0)); // old_size
    body.instruction(&Instruction::I32Const(2)); // align (utf16)
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32Const(2));
    body.instruction(&Instruction::I32Mul); // new_size = 2 * len
    emit_checked_realloc(body, realloc_func, out_ptr_local);

    // src_idx = 0; dst_idx = 0 (dst_idx is the running output code-unit count).
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(src_idx_local));
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(dst_idx_local));

    // Transcode loop.
    body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
    // if src_idx >= len: break.
    body.instruction(&Instruction::LocalGet(src_idx_local));
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32GeU);
    body.instruction(&Instruction::BrIf(1));
    // cp = decode_utf8(src); src_idx advances.
    emit_utf8_decode_codepoint(
        body,
        src_mem8,
        ptr_local,
        src_idx_local,
        len_local,
        byte_local,
        cp_local,
        cont_local,
    );
    // encode_utf16(cp) → dst; dst_idx advances by 1 or 2 code units.
    emit_utf16_encode_codepoint(body, dst_mem16, out_ptr_local, dst_idx_local, cp_local);
    body.instruction(&Instruction::Br(0));
    body.instruction(&Instruction::End); // loop
    body.instruction(&Instruction::End); // block

    // Rewrite the forwarded (ptr, len): ptr → callee output buffer, len →
    // output UTF-16 code-unit count.
    body.instruction(&Instruction::LocalGet(out_ptr_local));
    body.instruction(&Instruction::LocalSet(ptr_local));
    body.instruction(&Instruction::LocalGet(dst_idx_local));
    body.instruction(&Instruction::LocalSet(len_local));
}

/// Emit a UTF-16 → UTF-8 transcode of a single top-level `(ptr, len)` string
/// param on the async-lift cross-memory copy path (#272 inc 2).
///
/// The exact mirror of [`emit_utf8_to_utf16_transcode_param`] in the REVERSE
/// direction. Fully parameterised by local indices / MemArgs (no hidden
/// local-0/1 assumptions) and emits NO `Call` — composed from the shared,
/// validated [`emit_utf16_decode_codepoint`] (source side) +
/// [`emit_utf8_encode_codepoint`] (destination side, the same encoder the sync
/// [`FactStyleGenerator::emit_utf16_to_utf8_transcode`] now uses) so it cannot
/// drift from the sync decoder/encoder.
///
/// Contract:
/// * `ptr_local` / `len_local` hold the CALLER-memory source pointer and the
///   source length, which for a UTF-16 source is a **code-unit count** (NOT a
///   byte count). On return, `ptr_local` is rewritten to the freshly
///   reallocated CALLEE-memory output pointer and `len_local` is rewritten to
///   the output UTF-8 **byte count** — the operand a UTF-8 lifting callee
///   reads. Failing to rewrite `len_local` would silently mis-size the callee's
///   view of the string.
/// * `out_ptr_local` receives the realloc result (the callee output buffer).
/// * `src_idx_local`, `dst_idx_local`, `cp_local`, `cu_local`, `cu2_local`
///   are dedicated scratch i32 locals the caller must reserve; they must not
///   alias `ptr_local`/`len_local` or each other. (Same count — 5 — as the
///   inc-1 forward transcoder, so the async-adapter scratch budgets are
///   unchanged.)
///
/// Sizing (mirrors the sync emitter's LS-A-7 guards): the worst case is 3 UTF-8
/// bytes per UTF-16 code unit — a BMP non-ASCII unit (U+0800..U+FFFF) encodes
/// to 3 bytes, while a supplementary scalar uses a surrogate PAIR (2 units) for
/// 4 bytes = 2 bytes/unit < 3 — so the output is at most `3 * len` bytes.
/// `3 * len` is computed with an i32-overflow guard before the multiply (trap
/// if `len > u32::MAX/3`), and the realloc return is null-checked, both via the
/// shared helpers — the same `(*3, guard)` sizing the sync emitter uses.
#[allow(clippy::too_many_arguments)]
fn emit_utf16_to_utf8_transcode_param(
    body: &mut Function,
    realloc_func: u32,
    realloc_align: i32,
    src_mem16: wasm_encoder::MemArg,
    dst_mem8: wasm_encoder::MemArg,
    ptr_local: u32,
    len_local: u32,
    out_ptr_local: u32,
    src_idx_local: u32,
    dst_idx_local: u32,
    cp_local: u32,
    cu_local: u32,
    cu2_local: u32,
) {
    // Allocate output buffer = 3 * len bytes (each UTF-16 code unit → ≤ 3 UTF-8
    // bytes; a surrogate pair is 2 units → 4 bytes = 2 bytes/unit). LS-A-7 leg
    // (a): guard the *3 against i32 wrap; leg (b): emit_checked_realloc traps on
    // a null return.
    emit_overflow_guard(body, len_local, 3);
    body.instruction(&Instruction::I32Const(0)); // old_ptr
    body.instruction(&Instruction::I32Const(0)); // old_size
    body.instruction(&Instruction::I32Const(realloc_align)); // align
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32Const(3));
    body.instruction(&Instruction::I32Mul); // new_size = 3 * len
    emit_checked_realloc(body, realloc_func, out_ptr_local);

    // src_idx = 0 (code units); dst_idx = 0 (the running output BYTE count).
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(src_idx_local));
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(dst_idx_local));

    // Transcode loop.
    body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
    // if src_idx >= len: break.
    body.instruction(&Instruction::LocalGet(src_idx_local));
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32GeU);
    body.instruction(&Instruction::BrIf(1));
    // cp = decode_utf16(src); src_idx advances by 1 or 2 code units (lossy
    // U+FFFD for lone surrogates).
    emit_utf16_decode_codepoint(
        body,
        src_mem16,
        ptr_local,
        src_idx_local,
        len_local,
        cu_local,
        cp_local,
        cu2_local,
    );
    // encode_utf8(cp) → dst; dst_idx advances by 1..4 bytes.
    emit_utf8_encode_codepoint(body, dst_mem8, out_ptr_local, dst_idx_local, cp_local);
    body.instruction(&Instruction::Br(0));
    body.instruction(&Instruction::End); // loop
    body.instruction(&Instruction::End); // block

    // Rewrite the forwarded (ptr, len): ptr → callee output buffer, len →
    // output UTF-8 byte count.
    body.instruction(&Instruction::LocalGet(out_ptr_local));
    body.instruction(&Instruction::LocalSet(ptr_local));
    body.instruction(&Instruction::LocalGet(dst_idx_local));
    body.instruction(&Instruction::LocalSet(len_local));
}

/// Emit a `latin1+utf16` (CompactUTF16) → UTF-16 transcode of a single
/// top-level `(ptr, len)` string param on the async-lift cross-memory copy path
/// (#272 inc 4a).
///
/// The CALLER encoding is `latin1+utf16` — meld's [`StringEncoding::Latin1`] —
/// whose length operand is **tag-encoded** (see [`UTF16_TAG`]). This helper
/// mirrors the SYNC [`FactStyleGenerator::emit_latin1_to_utf16_transcode`] but
/// is FULLY parameterised by local indices / MemArgs (no hidden local-0/1
/// assumptions) and emits NO `Call`, so it composes into the async param-copy
/// step exactly like the inc-1/2 transcoders.
///
/// Runtime tag dispatch on `len_local`:
/// * tag **CLEAR** → the source is pure Latin-1: `count` (= `len`) bytes, each
///   0x00–0xFF zero-extended to one UTF-16 code unit (1:1, total). Output =
///   `count` code units.
/// * tag **SET** → the source is already UTF-16: `count` (= `len & !UTF16_TAG`)
///   code units, copied VERBATIM (2 bytes per unit, surrogate pairs preserved
///   byte-for-byte). Output = `count` code units.
///
/// Contract:
/// * `ptr_local` / `len_local` hold the CALLER-memory source pointer and the
///   TAGGED source length. On return, `ptr_local` is rewritten to the freshly
///   reallocated CALLEE-memory output pointer and `len_local` is rewritten to
///   the output UTF-16 **code-unit count** (UNTAGGED — a UTF-16 lifting callee
///   reads a plain code-unit count).
/// * `out_ptr_local` receives the realloc result.
/// * `tag_local`, `idx_local`, `count_local`, `unit_local` are dedicated
///   scratch i32 locals the caller must reserve; they must not alias
///   `ptr_local`/`len_local`/`out_ptr_local` or each other. 5 scratch locals
///   total (incl. `out_ptr_local`) — same count as the inc-1/2 forward
///   transcoders, so the async budgets are unchanged for THIS direction.
///
/// Sizing: BOTH interpretations produce at most `count` UTF-16 code units =
/// `2 * count` bytes (Latin-1 is 1 byte → 1 unit; verbatim UTF-16 is 1 unit →
/// 1 unit). After masking, `count == len_local`, so the worst-case output is
/// `2 * count` bytes — the larger-interpretation-safe size the sync emitter
/// uses. The `*2` is guarded against i32 wrap (LS-A-7 leg a) and the realloc
/// return is null-checked (leg b), both via the shared helpers.
#[allow(clippy::too_many_arguments)]
fn emit_latin1_to_utf16_transcode_param(
    body: &mut Function,
    realloc_func: u32,
    src_mem8: wasm_encoder::MemArg,
    src_mem16: wasm_encoder::MemArg,
    dst_mem16: wasm_encoder::MemArg,
    ptr_local: u32,
    len_local: u32,
    out_ptr_local: u32,
    tag_local: u32,
    idx_local: u32,
    count_local: u32,
    unit_local: u32,
) {
    // Decode the tag, then mask len_local to the untagged code/byte count.
    // tag := (len & UTF16_TAG) != 0 ; len := len & !UTF16_TAG.
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32Const(UTF16_TAG));
    body.instruction(&Instruction::I32And);
    body.instruction(&Instruction::LocalSet(tag_local));
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32Const(!UTF16_TAG));
    body.instruction(&Instruction::I32And);
    body.instruction(&Instruction::LocalSet(len_local));

    // count := len (the masked code/byte count, used by both arms).
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::LocalSet(count_local));

    // Allocate output buffer = 2 * count bytes (worst case for both
    // interpretations: Latin-1 1 byte → 1 unit, verbatim UTF-16 1 unit → 1
    // unit). LS-A-7 leg (a): guard the *2 against i32 wrap; leg (b):
    // emit_checked_realloc traps on a null return.
    emit_overflow_guard(body, count_local, 2);
    body.instruction(&Instruction::I32Const(0)); // old_ptr
    body.instruction(&Instruction::I32Const(0)); // old_size
    body.instruction(&Instruction::I32Const(2)); // align (utf16)
    body.instruction(&Instruction::LocalGet(count_local));
    body.instruction(&Instruction::I32Const(2));
    body.instruction(&Instruction::I32Mul); // new_size = 2 * count
    emit_checked_realloc(body, realloc_func, out_ptr_local);

    // idx = 0 (code-unit index, identical for src and dst in both arms).
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(idx_local));

    body.instruction(&Instruction::LocalGet(tag_local));
    body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    {
        // Tag SET: source is already UTF-16 → verbatim code-unit copy.
        body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::LocalGet(idx_local));
        body.instruction(&Instruction::LocalGet(count_local));
        body.instruction(&Instruction::I32GeU);
        body.instruction(&Instruction::BrIf(1));
        // unit = mem16[src_ptr + idx*2]
        body.instruction(&Instruction::LocalGet(ptr_local));
        body.instruction(&Instruction::LocalGet(idx_local));
        body.instruction(&Instruction::I32Const(1));
        body.instruction(&Instruction::I32Shl);
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::I32Load16U(src_mem16));
        body.instruction(&Instruction::LocalSet(unit_local));
        // mem16[out_ptr + idx*2] = unit
        body.instruction(&Instruction::LocalGet(out_ptr_local));
        body.instruction(&Instruction::LocalGet(idx_local));
        body.instruction(&Instruction::I32Const(1));
        body.instruction(&Instruction::I32Shl);
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::LocalGet(unit_local));
        body.instruction(&Instruction::I32Store16(dst_mem16));
        body.instruction(&Instruction::LocalGet(idx_local));
        body.instruction(&Instruction::I32Const(1));
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::LocalSet(idx_local));
        body.instruction(&Instruction::Br(0));
        body.instruction(&Instruction::End); // loop
        body.instruction(&Instruction::End); // block
    }
    body.instruction(&Instruction::Else);
    {
        // Tag CLEAR: pure Latin-1 → zero-extend each byte to one UTF-16 unit.
        body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::LocalGet(idx_local));
        body.instruction(&Instruction::LocalGet(count_local));
        body.instruction(&Instruction::I32GeU);
        body.instruction(&Instruction::BrIf(1));
        // unit = mem8[src_ptr + idx] (a u8 load is already the zero-extended
        // UTF-16 code unit).
        body.instruction(&Instruction::LocalGet(ptr_local));
        body.instruction(&Instruction::LocalGet(idx_local));
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::I32Load8U(src_mem8));
        body.instruction(&Instruction::LocalSet(unit_local));
        // mem16[out_ptr + idx*2] = unit
        body.instruction(&Instruction::LocalGet(out_ptr_local));
        body.instruction(&Instruction::LocalGet(idx_local));
        body.instruction(&Instruction::I32Const(1));
        body.instruction(&Instruction::I32Shl);
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::LocalGet(unit_local));
        body.instruction(&Instruction::I32Store16(dst_mem16));
        body.instruction(&Instruction::LocalGet(idx_local));
        body.instruction(&Instruction::I32Const(1));
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::LocalSet(idx_local));
        body.instruction(&Instruction::Br(0));
        body.instruction(&Instruction::End); // loop
        body.instruction(&Instruction::End); // block
    }
    body.instruction(&Instruction::End); // if/else

    // Rewrite the forwarded (ptr, len): ptr → callee output buffer, len →
    // output UTF-16 code-unit count (== count in both arms).
    body.instruction(&Instruction::LocalGet(out_ptr_local));
    body.instruction(&Instruction::LocalSet(ptr_local));
    body.instruction(&Instruction::LocalGet(count_local));
    body.instruction(&Instruction::LocalSet(len_local));
}

/// Emit a `latin1+utf16` (CompactUTF16) → UTF-8 transcode of a single top-level
/// `(ptr, len)` string param on the async-lift cross-memory copy path
/// (#272 inc 4a).
///
/// The CALLER encoding is `latin1+utf16` ([`StringEncoding::Latin1`]); its
/// length operand is **tag-encoded** (see [`UTF16_TAG`]). This helper mirrors
/// the SYNC [`FactStyleGenerator::emit_latin1_to_utf8_transcode`] but is fully
/// parameterised and emits NO `Call`. It is composed from the shared, validated
/// [`emit_utf16_decode_codepoint`] + [`emit_utf8_encode_codepoint`] helpers on
/// the tag-set arm so it cannot drift from the sync decoder/encoder.
///
/// Runtime tag dispatch on `len_local`:
/// * tag **CLEAR** → pure Latin-1: each byte 0x00–0x7F → 1 UTF-8 byte,
///   0x80–0xFF → 2 UTF-8 bytes (≤ 2 bytes per source byte).
/// * tag **SET** → UTF-16 source: full UTF-16 → UTF-8 transcode (surrogate
///   pairs, lossy U+FFFD for lone surrogates) via the shared decode+encode
///   helpers (≤ 3 UTF-8 bytes per code unit; a surrogate pair is 2 units → 4
///   bytes = 2 bytes/unit).
///
/// Contract:
/// * `ptr_local` / `len_local` hold the CALLER-memory source pointer and the
///   TAGGED source length. On return, `ptr_local` is rewritten to the freshly
///   reallocated CALLEE-memory output pointer and `len_local` is rewritten to
///   the output UTF-8 **byte count** — the operand a UTF-8 lifting callee reads.
/// * `out_ptr_local` receives the realloc result.
/// * `tag_local`, `src_idx_local`, `dst_idx_local`, `cp_local`, `cu_local`,
///   `cu2_local` are dedicated scratch i32 locals the caller must reserve; they
///   must not alias `ptr_local`/`len_local`/`out_ptr_local` or each other. 7
///   scratch locals total (incl. `out_ptr_local`) — the tag-set arm's shared
///   UTF-16 decoder needs `cu`/`cu2` on top of the byte/cp scratch, so this
///   direction uses MORE scratch than the inc-1/2 forward transcoders (the
///   async budgets are grown to fit it — see the callers).
///
/// Sizing: the worst case across both interpretations is `3 * count` bytes —
/// the tag-set UTF-16 arm's 3-bytes-per-unit bound dominates the tag-clear
/// Latin-1 arm's 2-bytes-per-byte bound (`count == len & !UTF16_TAG` after
/// masking). The `*3` is guarded against i32 wrap (LS-A-7 leg a) and the
/// realloc return is null-checked (leg b), both via the shared helpers — the
/// same `(*3, guard)` sizing the sync UTF-16 → UTF-8 path uses.
#[allow(clippy::too_many_arguments)]
fn emit_latin1_to_utf8_transcode_param(
    body: &mut Function,
    realloc_func: u32,
    realloc_align: i32,
    src_mem8: wasm_encoder::MemArg,
    src_mem16: wasm_encoder::MemArg,
    dst_mem8: wasm_encoder::MemArg,
    ptr_local: u32,
    len_local: u32,
    out_ptr_local: u32,
    tag_local: u32,
    src_idx_local: u32,
    dst_idx_local: u32,
    cp_local: u32,
    cu_local: u32,
    cu2_local: u32,
) {
    // Decode the tag, then mask len_local to the untagged code/byte count.
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32Const(UTF16_TAG));
    body.instruction(&Instruction::I32And);
    body.instruction(&Instruction::LocalSet(tag_local));
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32Const(!UTF16_TAG));
    body.instruction(&Instruction::I32And);
    body.instruction(&Instruction::LocalSet(len_local));

    // Allocate output buffer = 3 * count bytes (tag-set UTF-16 worst case of 3
    // bytes/unit dominates the tag-clear Latin-1 2 bytes/byte). LS-A-7 leg (a):
    // guard the *3 against i32 wrap; leg (b): emit_checked_realloc traps on a
    // null return.
    emit_overflow_guard(body, len_local, 3);
    body.instruction(&Instruction::I32Const(0)); // old_ptr
    body.instruction(&Instruction::I32Const(0)); // old_size
    body.instruction(&Instruction::I32Const(realloc_align)); // align
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32Const(3));
    body.instruction(&Instruction::I32Mul); // new_size = 3 * count
    emit_checked_realloc(body, realloc_func, out_ptr_local);

    // src_idx = 0; dst_idx = 0 (the running output BYTE count).
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(src_idx_local));
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(dst_idx_local));

    body.instruction(&Instruction::LocalGet(tag_local));
    body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    {
        // Tag SET: source is UTF-16 → decode code points, encode UTF-8.
        body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::LocalGet(src_idx_local));
        body.instruction(&Instruction::LocalGet(len_local));
        body.instruction(&Instruction::I32GeU);
        body.instruction(&Instruction::BrIf(1));
        // cp = decode_utf16(src); src_idx advances by 1 or 2 units (lossy
        // U+FFFD for lone surrogates).
        emit_utf16_decode_codepoint(
            body,
            src_mem16,
            ptr_local,
            src_idx_local,
            len_local,
            cu_local,
            cp_local,
            cu2_local,
        );
        // encode_utf8(cp) → dst; dst_idx advances by 1..4 bytes.
        emit_utf8_encode_codepoint(body, dst_mem8, out_ptr_local, dst_idx_local, cp_local);
        body.instruction(&Instruction::Br(0));
        body.instruction(&Instruction::End); // loop
        body.instruction(&Instruction::End); // block
    }
    body.instruction(&Instruction::Else);
    {
        // Tag CLEAR: pure Latin-1 → each byte ≤ 0xFF as 1–2 UTF-8 bytes. A
        // Latin-1 byte 0x00–0xFF is itself a code point U+0000–U+00FF, so we
        // feed it through the shared UTF-8 encoder (cp < 0x80 → 1 byte,
        // 0x80–0xFF → 2 bytes — exactly the sync Latin-1 → UTF-8 arm).
        body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::LocalGet(src_idx_local));
        body.instruction(&Instruction::LocalGet(len_local));
        body.instruction(&Instruction::I32GeU);
        body.instruction(&Instruction::BrIf(1));
        // cp = mem8[src_ptr + src_idx] (zero-extended Latin-1 code point).
        body.instruction(&Instruction::LocalGet(ptr_local));
        body.instruction(&Instruction::LocalGet(src_idx_local));
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::I32Load8U(src_mem8));
        body.instruction(&Instruction::LocalSet(cp_local));
        // encode_utf8(cp) → dst (1 or 2 bytes for U+0000–U+00FF).
        emit_utf8_encode_codepoint(body, dst_mem8, out_ptr_local, dst_idx_local, cp_local);
        // src_idx += 1
        body.instruction(&Instruction::LocalGet(src_idx_local));
        body.instruction(&Instruction::I32Const(1));
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::LocalSet(src_idx_local));
        body.instruction(&Instruction::Br(0));
        body.instruction(&Instruction::End); // loop
        body.instruction(&Instruction::End); // block
    }
    body.instruction(&Instruction::End); // if/else

    // Rewrite the forwarded (ptr, len): ptr → callee output buffer, len →
    // output UTF-8 byte count.
    body.instruction(&Instruction::LocalGet(out_ptr_local));
    body.instruction(&Instruction::LocalSet(ptr_local));
    body.instruction(&Instruction::LocalGet(dst_idx_local));
    body.instruction(&Instruction::LocalSet(len_local));
}

/// Emit a UTF-8 → `latin1+utf16` (CompactUTF16) transcode of a single top-level
/// `(ptr, len)` string param on the async-lift cross-memory copy path
/// (#272 inc 4b).
///
/// The CALLEE encoding is `latin1+utf16` — meld's [`StringEncoding::Latin1`] —
/// a **two-phase / tag-PRODUCING** encoder: it must decide a representation for
/// the WHOLE string before writing it, then emit a length operand carrying the
/// [`UTF16_TAG`] bit to tell the callee which representation was chosen. This
/// helper mirrors the SYNC
/// [`FactStyleGenerator::emit_utf8_to_latin1_transcode`] but is FULLY
/// parameterised by local indices / MemArgs (no hidden local-0/1 assumptions)
/// and emits NO `Call`, so it composes into the async param-copy step exactly
/// like the inc-1/2/4a transcoders. It is composed from the shared, validated
/// [`emit_utf8_decode_codepoint`] (source) + [`emit_utf16_encode_codepoint`]
/// (UTF-16-arm output) helpers so it cannot drift from the sync decoder/encoder.
///
/// Two phases over the UTF-8 source:
/// * **Phase A (scan):** decode every code point; if ANY code point is
///   `> 0xFF`, the string cannot be Latin-1, so set `needs_utf16`.
/// * **Phase B (write):**
///   * `needs_utf16` SET → re-decode and UTF-16-encode each code point
///     (surrogate pair for `> 0xFFFF`); output length = code-unit count with
///     [`UTF16_TAG`] **set**.
///   * `needs_utf16` CLEAR → write each code point (all `≤ 0xFF`) as one Latin-1
///     byte; output length = byte/char count, tag **clear**.
///
/// Contract:
/// * `ptr_local` / `len_local` hold the CALLER-memory source pointer and the
///   source UTF-8 **byte length**. On return, `ptr_local` is rewritten to the
///   freshly reallocated CALLEE-memory output pointer and `len_local` is
///   rewritten to the **tagged** output length: a Latin-1 byte count (tag clear)
///   or a UTF-16 code-unit count `| UTF16_TAG` (tag set) — exactly the operand a
///   `latin1+utf16` lifting callee reads.
/// * `out_ptr_local` receives the realloc result (the callee output buffer).
/// * `flag_local`, `src_idx_local`, `dst_idx_local`, `byte_local`, `cp_local`,
///   `cont_local` are dedicated scratch i32 locals the caller must reserve; they
///   must not alias `ptr_local`/`len_local`/`out_ptr_local` or each other. 6
///   scratch locals at the transcode base (`flag` is live only during the scan,
///   `dst_idx` only during the write, but kept as DISTINCT locals here so the
///   parameterised contract has no hidden reuse). This is the same scratch
///   COUNT inc-4a's `Latin1 → UTF-8` loop used, so the async budgets already
///   fit (see the callers).
///
/// Sizing: BOTH representations are bounded by `2 * len` bytes. The Latin-1 arm
/// writes one byte per char ≤ `len` bytes; the UTF-16 arm writes ≤ 1 code unit
/// per source code point — a UTF-8 ASCII byte is 1 cp → 1 unit (2 bytes), and a
/// 4-byte UTF-8 supplementary char is 1 cp → a surrogate PAIR (2 units = 4
/// bytes) = 1 byte-per-source-byte, so `2 * len` bounds the worst case. This is
/// the single worst-case alloc the sync emitter uses. The `*2` is guarded
/// against i32 wrap (LS-A-7 leg a) and the realloc return is null-checked (leg
/// b), both via the shared helpers.
#[allow(clippy::too_many_arguments)]
fn emit_utf8_to_latin1_transcode_param(
    body: &mut Function,
    realloc_func: u32,
    realloc_align: i32,
    src_mem8: wasm_encoder::MemArg,
    dst_mem8: wasm_encoder::MemArg,
    dst_mem16: wasm_encoder::MemArg,
    ptr_local: u32,
    len_local: u32,
    out_ptr_local: u32,
    flag_local: u32,
    src_idx_local: u32,
    dst_idx_local: u32,
    byte_local: u32,
    cp_local: u32,
    cont_local: u32,
) {
    // Allocate output buffer = 2 * len bytes (the UTF-16-verbatim worst case,
    // which also bounds the 1-byte-per-char Latin-1 arm). LS-A-7 leg (a): guard
    // the *2 against i32 wrap; leg (b): emit_checked_realloc traps on null.
    emit_overflow_guard(body, len_local, 2);
    body.instruction(&Instruction::I32Const(0)); // old_ptr
    body.instruction(&Instruction::I32Const(0)); // old_size
    body.instruction(&Instruction::I32Const(realloc_align)); // align (utf16: 2)
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32Const(2));
    body.instruction(&Instruction::I32Mul); // new_size = 2 * len
    emit_checked_realloc(body, realloc_func, out_ptr_local);

    // --- Phase A: scan to decide latin1-vs-utf16. ---
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(flag_local)); // needs_utf16 = 0
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(src_idx_local));

    body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::LocalGet(src_idx_local));
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32GeU);
    body.instruction(&Instruction::BrIf(1));
    emit_utf8_decode_codepoint(
        body,
        src_mem8,
        ptr_local,
        src_idx_local,
        len_local,
        byte_local,
        cp_local,
        cont_local,
    );
    // if cp > 0xFF: needs_utf16 = 1
    body.instruction(&Instruction::LocalGet(cp_local));
    body.instruction(&Instruction::I32Const(0xFF));
    body.instruction(&Instruction::I32GtU);
    body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::I32Const(1));
    body.instruction(&Instruction::LocalSet(flag_local));
    body.instruction(&Instruction::End);
    body.instruction(&Instruction::Br(0));
    body.instruction(&Instruction::End); // loop
    body.instruction(&Instruction::End); // block

    // --- Phase B: write, branching on the flag. ---
    body.instruction(&Instruction::LocalGet(flag_local));
    body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    {
        // UTF-16 representation (tag set): re-decode + UTF-16-encode.
        body.instruction(&Instruction::I32Const(0));
        body.instruction(&Instruction::LocalSet(src_idx_local));
        body.instruction(&Instruction::I32Const(0));
        body.instruction(&Instruction::LocalSet(dst_idx_local));

        body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::LocalGet(src_idx_local));
        body.instruction(&Instruction::LocalGet(len_local));
        body.instruction(&Instruction::I32GeU);
        body.instruction(&Instruction::BrIf(1));
        emit_utf8_decode_codepoint(
            body,
            src_mem8,
            ptr_local,
            src_idx_local,
            len_local,
            byte_local,
            cp_local,
            cont_local,
        );
        emit_utf16_encode_codepoint(body, dst_mem16, out_ptr_local, dst_idx_local, cp_local);
        body.instruction(&Instruction::Br(0));
        body.instruction(&Instruction::End); // loop
        body.instruction(&Instruction::End); // block

        // ptr → out_ptr; len → code_units | UTF16_TAG (tag set).
        body.instruction(&Instruction::LocalGet(out_ptr_local));
        body.instruction(&Instruction::LocalSet(ptr_local));
        body.instruction(&Instruction::LocalGet(dst_idx_local));
        body.instruction(&Instruction::I32Const(UTF16_TAG));
        body.instruction(&Instruction::I32Or);
        body.instruction(&Instruction::LocalSet(len_local));
    }
    body.instruction(&Instruction::Else);
    {
        // Latin-1 representation (tag clear): every cp ≤ 0xFF → one byte.
        body.instruction(&Instruction::I32Const(0));
        body.instruction(&Instruction::LocalSet(src_idx_local));
        body.instruction(&Instruction::I32Const(0));
        body.instruction(&Instruction::LocalSet(dst_idx_local));

        body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::LocalGet(src_idx_local));
        body.instruction(&Instruction::LocalGet(len_local));
        body.instruction(&Instruction::I32GeU);
        body.instruction(&Instruction::BrIf(1));
        emit_utf8_decode_codepoint(
            body,
            src_mem8,
            ptr_local,
            src_idx_local,
            len_local,
            byte_local,
            cp_local,
            cont_local,
        );
        // out[dst_idx] = cp (one Latin-1 byte); dst_idx += 1.
        body.instruction(&Instruction::LocalGet(out_ptr_local));
        body.instruction(&Instruction::LocalGet(dst_idx_local));
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::LocalGet(cp_local));
        body.instruction(&Instruction::I32Store8(dst_mem8));
        body.instruction(&Instruction::LocalGet(dst_idx_local));
        body.instruction(&Instruction::I32Const(1));
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::LocalSet(dst_idx_local));
        body.instruction(&Instruction::Br(0));
        body.instruction(&Instruction::End); // loop
        body.instruction(&Instruction::End); // block

        // ptr → out_ptr; len → char/byte count (tag clear).
        body.instruction(&Instruction::LocalGet(out_ptr_local));
        body.instruction(&Instruction::LocalSet(ptr_local));
        body.instruction(&Instruction::LocalGet(dst_idx_local));
        body.instruction(&Instruction::LocalSet(len_local));
    }
    body.instruction(&Instruction::End); // if/else
}

/// Emit a UTF-16 → `latin1+utf16` (CompactUTF16) transcode of a single
/// top-level `(ptr, len)` string param on the async-lift cross-memory copy path
/// (#272 inc 4b).
///
/// The exact mirror of [`emit_utf8_to_latin1_transcode_param`] for a UTF-16
/// SOURCE; mirrors the SYNC
/// [`FactStyleGenerator::emit_utf16_to_latin1_transcode`]. Two-phase,
/// tag-PRODUCING, fully parameterised, emits NO `Call`. Composed from the
/// shared [`emit_utf16_decode_codepoint`] (source) + [`emit_utf16_encode_codepoint`]
/// (UTF-16-arm output) helpers.
///
/// The source length operand (`len_local`) is a UTF-16 **code-unit count**.
/// Phase A decodes the code units (surrogate pairs combined, lone surrogates
/// normalised to U+FFFD) to decide latin1-vs-utf16; phase B re-decodes and
/// writes the chosen representation. The UTF-16 arm re-decodes and re-encodes
/// (rather than verbatim-copying) so lone surrogates normalise to U+FFFD
/// consistently with phase A's decision, exactly like the sync emitter.
///
/// Contract / output length: identical to [`emit_utf8_to_latin1_transcode_param`]
/// — `len_local` is rewritten to the tagged output length (Latin-1 char count,
/// tag clear; or UTF-16 code-unit count `| UTF16_TAG`, tag set).
/// * `flag_local`, `src_idx_local`, `dst_idx_local`, `cu_local`, `cp_local`,
///   `cu2_local` are dedicated scratch i32 locals (6 at the transcode base —
///   the same count as `Latin1 → UTF-8`), none aliasing the in/out locals or
///   each other.
///
/// Sizing: `2 * code_units` bytes — the UTF-16-verbatim worst case (each input
/// code unit → at most one output code unit; the Latin-1 arm writes ≤ 1 byte
/// per code point ≤ 1 byte per code unit). Single worst-case alloc, `*2`
/// overflow-guarded (LS-A-7 leg a), realloc null-checked (leg b).
#[allow(clippy::too_many_arguments)]
fn emit_utf16_to_latin1_transcode_param(
    body: &mut Function,
    realloc_func: u32,
    realloc_align: i32,
    src_mem16: wasm_encoder::MemArg,
    dst_mem8: wasm_encoder::MemArg,
    dst_mem16: wasm_encoder::MemArg,
    ptr_local: u32,
    len_local: u32,
    out_ptr_local: u32,
    flag_local: u32,
    src_idx_local: u32,
    dst_idx_local: u32,
    cu_local: u32,
    cp_local: u32,
    cu2_local: u32,
) {
    // Allocate output buffer = 2 * code_units bytes (UTF-16-verbatim worst
    // case). LS-A-7 leg (a): guard *2; leg (b): null-check the realloc.
    emit_overflow_guard(body, len_local, 2);
    body.instruction(&Instruction::I32Const(0)); // old_ptr
    body.instruction(&Instruction::I32Const(0)); // old_size
    body.instruction(&Instruction::I32Const(realloc_align)); // align (utf16: 2)
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32Const(2));
    body.instruction(&Instruction::I32Mul); // new_size = 2 * code_units
    emit_checked_realloc(body, realloc_func, out_ptr_local);

    // --- Phase A: scan to decide latin1-vs-utf16. ---
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(flag_local)); // needs_utf16 = 0
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(src_idx_local));

    body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::LocalGet(src_idx_local));
    body.instruction(&Instruction::LocalGet(len_local));
    body.instruction(&Instruction::I32GeU);
    body.instruction(&Instruction::BrIf(1));
    emit_utf16_decode_codepoint(
        body,
        src_mem16,
        ptr_local,
        src_idx_local,
        len_local,
        cu_local,
        cp_local,
        cu2_local,
    );
    body.instruction(&Instruction::LocalGet(cp_local));
    body.instruction(&Instruction::I32Const(0xFF));
    body.instruction(&Instruction::I32GtU);
    body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::I32Const(1));
    body.instruction(&Instruction::LocalSet(flag_local));
    body.instruction(&Instruction::End);
    body.instruction(&Instruction::Br(0));
    body.instruction(&Instruction::End); // loop
    body.instruction(&Instruction::End); // block

    // --- Phase B: write, branching on the flag. ---
    body.instruction(&Instruction::LocalGet(flag_local));
    body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    {
        // UTF-16 representation (tag set): re-decode + UTF-16-encode so lone
        // surrogates normalise to U+FFFD consistently with phase A.
        body.instruction(&Instruction::I32Const(0));
        body.instruction(&Instruction::LocalSet(src_idx_local));
        body.instruction(&Instruction::I32Const(0));
        body.instruction(&Instruction::LocalSet(dst_idx_local));

        body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::LocalGet(src_idx_local));
        body.instruction(&Instruction::LocalGet(len_local));
        body.instruction(&Instruction::I32GeU);
        body.instruction(&Instruction::BrIf(1));
        emit_utf16_decode_codepoint(
            body,
            src_mem16,
            ptr_local,
            src_idx_local,
            len_local,
            cu_local,
            cp_local,
            cu2_local,
        );
        emit_utf16_encode_codepoint(body, dst_mem16, out_ptr_local, dst_idx_local, cp_local);
        body.instruction(&Instruction::Br(0));
        body.instruction(&Instruction::End); // loop
        body.instruction(&Instruction::End); // block

        // ptr → out_ptr; len → code_units | UTF16_TAG (tag set).
        body.instruction(&Instruction::LocalGet(out_ptr_local));
        body.instruction(&Instruction::LocalSet(ptr_local));
        body.instruction(&Instruction::LocalGet(dst_idx_local));
        body.instruction(&Instruction::I32Const(UTF16_TAG));
        body.instruction(&Instruction::I32Or);
        body.instruction(&Instruction::LocalSet(len_local));
    }
    body.instruction(&Instruction::Else);
    {
        // Latin-1 representation (tag clear): every cp ≤ 0xFF → one byte.
        body.instruction(&Instruction::I32Const(0));
        body.instruction(&Instruction::LocalSet(src_idx_local));
        body.instruction(&Instruction::I32Const(0));
        body.instruction(&Instruction::LocalSet(dst_idx_local));

        body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::LocalGet(src_idx_local));
        body.instruction(&Instruction::LocalGet(len_local));
        body.instruction(&Instruction::I32GeU);
        body.instruction(&Instruction::BrIf(1));
        emit_utf16_decode_codepoint(
            body,
            src_mem16,
            ptr_local,
            src_idx_local,
            len_local,
            cu_local,
            cp_local,
            cu2_local,
        );
        // out[dst_idx] = cp (one Latin-1 byte); dst_idx += 1.
        body.instruction(&Instruction::LocalGet(out_ptr_local));
        body.instruction(&Instruction::LocalGet(dst_idx_local));
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::LocalGet(cp_local));
        body.instruction(&Instruction::I32Store8(dst_mem8));
        body.instruction(&Instruction::LocalGet(dst_idx_local));
        body.instruction(&Instruction::I32Const(1));
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::LocalSet(dst_idx_local));
        body.instruction(&Instruction::Br(0));
        body.instruction(&Instruction::End); // loop
        body.instruction(&Instruction::End); // block

        // ptr → out_ptr; len → char/code-point count (tag clear).
        body.instruction(&Instruction::LocalGet(out_ptr_local));
        body.instruction(&Instruction::LocalSet(ptr_local));
        body.instruction(&Instruction::LocalGet(dst_idx_local));
        body.instruction(&Instruction::LocalSet(len_local));
    }
    body.instruction(&Instruction::End); // if/else
}

/// Build a self-contained two-memory wasm module that exercises the EXACT
/// async-path UTF-8 → UTF-16 param transcode emitter
/// ([`emit_utf8_to_utf16_transcode_param`]) under a real engine, for the
/// #272 inc-1 runtime-differential oracle.
///
/// The async fuse+run harness cannot express a string-param async-lift callee
/// runnable under bare wasmtime (async-lift execution is deferred to a real
/// async runtime / kiln; the wat crate does not even parse `canon lift async`
/// — see `p3_async_lowering.rs`). This builder instead drives the production
/// transcode emitter directly: it places the caller's UTF-8 bytes in memory 0
/// ("caller memory"), transcodes them into a freshly bump-allocated buffer in
/// memory 1 ("callee memory"), and sums the resulting UTF-16 code units the
/// way a UTF-16-lifting callee would read them. A raw byte-copy (the pre-inc-1
/// behaviour) cannot produce the correct code-unit sum, so the oracle proves
/// transcoding rather than copying.
///
/// Module shape (exercises the real emitter, MemArgs distinct per memory):
/// * memory 0 (caller): the UTF-8 source bytes, written by the host before the
///   call.
/// * memory 1 (callee): the bump-allocated UTF-16 output.
/// * func 0 `cabi_realloc(old,oldsz,align,newsz) -> i32`: a 2-byte-aligned bump
///   allocator over a mutable global cursor in memory 1.
/// * func 1 `transcode_and_sum(src_ptr, src_len) -> i32` (exported): copies the
///   args into the `(ptr, len)` locals, runs the transcode (which reallocs in
///   memory 1 and rewrites the locals to `(out_ptr, code_unit_count)`), then
///   sums `mem1.u16[out_ptr + 2*i]` for `i in 0..code_unit_count`.
///
/// Exposed `#[doc(hidden)] pub` purely so the `async_cross_encoding` runtime
/// test (a separate integration crate, where `wasmtime` is available) can
/// instantiate it; it is not part of the supported API.
#[doc(hidden)]
pub fn build_utf8_to_utf16_transcode_test_module() -> Vec<u8> {
    use wasm_encoder::{
        CodeSection, ConstExpr, ExportKind, ExportSection, FunctionSection, GlobalSection,
        GlobalType, MemArg, MemorySection, MemoryType, Module, TypeSection, ValType,
    };

    let mut types = TypeSection::new();
    // type 0: cabi_realloc (i32,i32,i32,i32) -> i32
    types.ty().function(
        [ValType::I32, ValType::I32, ValType::I32, ValType::I32],
        [ValType::I32],
    );
    // type 1: transcode_and_sum (i32 src_ptr, i32 src_len) -> i32
    types
        .ty()
        .function([ValType::I32, ValType::I32], [ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0); // func 0: cabi_realloc
    functions.function(1); // func 1: transcode_and_sum

    // memory 0 = caller (UTF-8 src), memory 1 = callee (UTF-16 out).
    let mut memory = MemorySection::new();
    for _ in 0..2 {
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
    }

    // global 0: bump cursor for the memory-1 allocator (start at 16).
    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(16),
    );

    let mut exports = ExportSection::new();
    exports.export("transcode_and_sum", ExportKind::Func, 1);
    exports.export("caller_memory", ExportKind::Memory, 0);
    exports.export("callee_memory", ExportKind::Memory, 1);

    let mut code = CodeSection::new();

    // func 0: cabi_realloc — bump allocator over global 0, aligned to `align`.
    // params: 0=old_ptr, 1=old_size, 2=align, 3=new_size. local 4 = result.
    {
        let mut f = Function::new([(1, ValType::I32)]);
        // ptr = (cursor + align - 1) & ~(align - 1)
        f.instruction(&Instruction::GlobalGet(0));
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::I32Const(-1));
        f.instruction(&Instruction::I32Xor);
        f.instruction(&Instruction::I32And);
        f.instruction(&Instruction::LocalSet(4));
        // cursor = ptr + new_size
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::LocalGet(3));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::GlobalSet(0));
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 1: transcode_and_sum(src_ptr, src_len) -> i32
    // Locals: 0=ptr (in/out), 1=len (in/out), then the transcode scratch:
    //   2=out_ptr, 3=src_idx, 4=dst_idx/out_count, 5=cp, 6=byte, 7=cont,
    // plus 8=sum, 9=i for the summing loop.
    {
        let src_mem8 = MemArg {
            offset: 0,
            align: 0,
            memory_index: 0,
        };
        let dst_mem16 = MemArg {
            offset: 0,
            align: 1,
            memory_index: 1,
        };
        let mut f = Function::new([(8, ValType::I32)]);
        emit_utf8_to_utf16_transcode_param(
            &mut f, 0, // realloc func
            src_mem8, dst_mem16, 0, // ptr_local (src_ptr param, rewritten to out_ptr)
            1, // len_local (src_len param, rewritten to code-unit count)
            2, // out_ptr_local
            3, // src_idx
            4, // dst_idx / out code-unit count
            5, // cp
            6, // byte
            7, // cont
        );
        // sum = 0; i = 0
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalSet(8));
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalSet(9));
        f.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        f.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        // if i >= len (now the code-unit count): break
        f.instruction(&Instruction::LocalGet(9));
        f.instruction(&Instruction::LocalGet(1));
        f.instruction(&Instruction::I32GeU);
        f.instruction(&Instruction::BrIf(1));
        // sum += mem1.u16[ptr + i*2]
        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::LocalGet(9));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Shl);
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Load16U(dst_mem16));
        f.instruction(&Instruction::LocalGet(8));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(8));
        // i += 1
        f.instruction(&Instruction::LocalGet(9));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(9));
        f.instruction(&Instruction::Br(0));
        f.instruction(&Instruction::End); // loop
        f.instruction(&Instruction::End); // block
        f.instruction(&Instruction::LocalGet(8));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&globals)
        .section(&exports)
        .section(&code);
    module.finish()
}

/// Build a self-contained two-memory wasm module that exercises the EXACT
/// async-path UTF-16 → UTF-8 param transcode emitter
/// ([`emit_utf16_to_utf8_transcode_param`]) under a real engine, for the
/// #272 inc-2 runtime-differential oracle. The mirror of
/// [`build_utf8_to_utf16_transcode_test_module`] in the reverse direction.
///
/// Module shape (exercises the real emitter, MemArgs distinct per memory):
/// * memory 0 (caller): the UTF-16 source code units (little-endian), written
///   by the host before the call.
/// * memory 1 (callee): the bump-allocated UTF-8 output.
/// * func 0 `cabi_realloc(old,oldsz,align,newsz) -> i32`: a 1-byte-aligned bump
///   allocator over a mutable global cursor in memory 1.
/// * func 1 `transcode_and_sum(src_ptr, src_units) -> i32` (exported): copies
///   the args into the `(ptr, len)` locals, runs the transcode (which reallocs
///   in memory 1 and rewrites the locals to `(out_ptr, byte_count)`), then sums
///   `mem1.u8[out_ptr + i]` for `i in 0..byte_count`. A raw byte-copy (the
///   pre-inc-2 behaviour) cannot produce the correct UTF-8 byte sum, so the
///   oracle proves transcoding rather than copying.
///
/// Exposed `#[doc(hidden)] pub` purely so the `async_cross_encoding` runtime
/// test can instantiate it; it is not part of the supported API.
#[doc(hidden)]
pub fn build_utf16_to_utf8_transcode_test_module() -> Vec<u8> {
    use wasm_encoder::{
        CodeSection, ConstExpr, ExportKind, ExportSection, FunctionSection, GlobalSection,
        GlobalType, MemArg, MemorySection, MemoryType, Module, TypeSection, ValType,
    };

    let mut types = TypeSection::new();
    // type 0: cabi_realloc (i32,i32,i32,i32) -> i32
    types.ty().function(
        [ValType::I32, ValType::I32, ValType::I32, ValType::I32],
        [ValType::I32],
    );
    // type 1: transcode_and_sum (i32 src_ptr, i32 src_units) -> i32
    types
        .ty()
        .function([ValType::I32, ValType::I32], [ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0); // func 0: cabi_realloc
    functions.function(1); // func 1: transcode_and_sum

    // memory 0 = caller (UTF-16 src), memory 1 = callee (UTF-8 out).
    let mut memory = MemorySection::new();
    for _ in 0..2 {
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
    }

    // global 0: bump cursor for the memory-1 allocator (start at 16).
    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(16),
    );

    let mut exports = ExportSection::new();
    exports.export("transcode_and_sum", ExportKind::Func, 1);
    exports.export("caller_memory", ExportKind::Memory, 0);
    exports.export("callee_memory", ExportKind::Memory, 1);

    let mut code = CodeSection::new();

    // func 0: cabi_realloc — bump allocator over global 0, aligned to `align`.
    // params: 0=old_ptr, 1=old_size, 2=align, 3=new_size. local 4 = result.
    {
        let mut f = Function::new([(1, ValType::I32)]);
        // ptr = (cursor + align - 1) & ~(align - 1)
        f.instruction(&Instruction::GlobalGet(0));
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::I32Const(-1));
        f.instruction(&Instruction::I32Xor);
        f.instruction(&Instruction::I32And);
        f.instruction(&Instruction::LocalSet(4));
        // cursor = ptr + new_size
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::LocalGet(3));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::GlobalSet(0));
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 1: transcode_and_sum(src_ptr, src_units) -> i32
    // Locals: 0=ptr (in/out), 1=len (in/out), then the transcode scratch:
    //   2=out_ptr, 3=src_idx, 4=dst_idx/out_bytes, 5=cp, 6=cu, 7=cu2,
    // plus 8=sum, 9=i for the summing loop.
    {
        let src_mem16 = MemArg {
            offset: 0,
            align: 1,
            memory_index: 0,
        };
        let dst_mem8 = MemArg {
            offset: 0,
            align: 0,
            memory_index: 1,
        };
        let mut f = Function::new([(8, ValType::I32)]);
        emit_utf16_to_utf8_transcode_param(
            &mut f, 0, // realloc func
            1, // realloc align (utf-8: 1)
            src_mem16, dst_mem8, 0, // ptr_local (src_ptr param, rewritten to out_ptr)
            1, // len_local (src code-unit count, rewritten to byte count)
            2, // out_ptr_local
            3, // src_idx
            4, // dst_idx / out byte count
            5, // cp
            6, // cu
            7, // cu2
        );
        // sum = 0; i = 0
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalSet(8));
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalSet(9));
        f.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        f.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        // if i >= len (now the byte count): break
        f.instruction(&Instruction::LocalGet(9));
        f.instruction(&Instruction::LocalGet(1));
        f.instruction(&Instruction::I32GeU);
        f.instruction(&Instruction::BrIf(1));
        // sum += mem1.u8[ptr + i]
        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::LocalGet(9));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Load8U(dst_mem8));
        f.instruction(&Instruction::LocalGet(8));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(8));
        // i += 1
        f.instruction(&Instruction::LocalGet(9));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(9));
        f.instruction(&Instruction::Br(0));
        f.instruction(&Instruction::End); // loop
        f.instruction(&Instruction::End); // block
        f.instruction(&Instruction::LocalGet(8));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&globals)
        .section(&exports)
        .section(&code);
    module.finish()
}

/// Build a self-contained two-memory wasm module that exercises the EXACT
/// async-path `latin1+utf16` (CompactUTF16) → UTF-16 param transcode emitter
/// ([`emit_latin1_to_utf16_transcode_param`]) under a real engine, for the
/// #272 inc-4a runtime-differential oracle.
///
/// Mirrors [`build_utf8_to_utf16_transcode_test_module`]: the host writes the
/// CALLER bytes (Latin-1 bytes for a tag-clear string, or UTF-16 LE bytes for a
/// tag-set string) into memory 0, the exported `transcode_and_sum(src_ptr,
/// tagged_len)` runs the production transcode into a `cabi_realloc`'d UTF-16
/// buffer in memory 1, then sums the resulting code units. The host passes the
/// length with [`UTF16_TAG`] already set/clear to select the source
/// interpretation, exactly as a `latin1+utf16` caller's lowered length operand
/// carries the tag.
///
/// `#[doc(hidden)] pub` purely so the `async_cross_encoding` runtime test can
/// instantiate it; not a supported API.
#[doc(hidden)]
pub fn build_latin1_to_utf16_transcode_test_module() -> Vec<u8> {
    use wasm_encoder::{
        CodeSection, ConstExpr, ExportKind, ExportSection, FunctionSection, GlobalSection,
        GlobalType, MemArg, MemorySection, MemoryType, Module, TypeSection, ValType,
    };

    let mut types = TypeSection::new();
    types.ty().function(
        [ValType::I32, ValType::I32, ValType::I32, ValType::I32],
        [ValType::I32],
    );
    types
        .ty()
        .function([ValType::I32, ValType::I32], [ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0); // func 0: cabi_realloc
    functions.function(1); // func 1: transcode_and_sum

    let mut memory = MemorySection::new();
    for _ in 0..2 {
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
    }

    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(16),
    );

    let mut exports = ExportSection::new();
    exports.export("transcode_and_sum", ExportKind::Func, 1);
    exports.export("caller_memory", ExportKind::Memory, 0);
    exports.export("callee_memory", ExportKind::Memory, 1);

    let mut code = CodeSection::new();

    // func 0: cabi_realloc — bump allocator over global 0, aligned to `align`.
    {
        let mut f = Function::new([(1, ValType::I32)]);
        f.instruction(&Instruction::GlobalGet(0));
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::I32Const(-1));
        f.instruction(&Instruction::I32Xor);
        f.instruction(&Instruction::I32And);
        f.instruction(&Instruction::LocalSet(4));
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::LocalGet(3));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::GlobalSet(0));
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 1: transcode_and_sum(src_ptr, tagged_len) -> i32
    // Locals: 0=ptr (in/out), 1=len (in/out, tagged on entry), then the
    // transcode scratch: 2=out_ptr, 3=tag, 4=idx, 5=count, 6=unit,
    // plus 7=sum, 8=i for the summing loop.
    {
        let src_mem8 = MemArg {
            offset: 0,
            align: 0,
            memory_index: 0,
        };
        let src_mem16 = MemArg {
            offset: 0,
            align: 1,
            memory_index: 0,
        };
        let dst_mem16 = MemArg {
            offset: 0,
            align: 1,
            memory_index: 1,
        };
        let mut f = Function::new([(7, ValType::I32)]);
        emit_latin1_to_utf16_transcode_param(
            &mut f, 0, // realloc func
            src_mem8, src_mem16, dst_mem16, 0, // ptr_local
            1, // len_local (tagged on entry, rewritten to code-unit count)
            2, // out_ptr_local
            3, // tag
            4, // idx
            5, // count
            6, // unit
        );
        // sum = 0; i = 0
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalSet(7));
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalSet(8));
        f.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        f.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        // if i >= len (now the code-unit count): break
        f.instruction(&Instruction::LocalGet(8));
        f.instruction(&Instruction::LocalGet(1));
        f.instruction(&Instruction::I32GeU);
        f.instruction(&Instruction::BrIf(1));
        // sum += mem1.u16[ptr + i*2]
        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::LocalGet(8));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Shl);
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Load16U(dst_mem16));
        f.instruction(&Instruction::LocalGet(7));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(7));
        // i += 1
        f.instruction(&Instruction::LocalGet(8));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(8));
        f.instruction(&Instruction::Br(0));
        f.instruction(&Instruction::End); // loop
        f.instruction(&Instruction::End); // block
        f.instruction(&Instruction::LocalGet(7));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&globals)
        .section(&exports)
        .section(&code);
    module.finish()
}

/// Build a self-contained two-memory wasm module that exercises the EXACT
/// async-path `latin1+utf16` (CompactUTF16) → UTF-8 param transcode emitter
/// ([`emit_latin1_to_utf8_transcode_param`]) under a real engine, for the
/// #272 inc-4a runtime-differential oracle.
///
/// Mirrors [`build_utf16_to_utf8_transcode_test_module`]: the host writes the
/// CALLER bytes (Latin-1 bytes for tag-clear, or UTF-16 LE bytes for tag-set)
/// into memory 0, the exported `transcode_and_sum(src_ptr, tagged_len)` runs
/// the production transcode into a `cabi_realloc`'d UTF-8 buffer in memory 1,
/// then sums the resulting UTF-8 bytes. The host passes the tagged length to
/// select the source interpretation.
///
/// `#[doc(hidden)] pub` purely so the `async_cross_encoding` runtime test can
/// instantiate it; not a supported API.
#[doc(hidden)]
pub fn build_latin1_to_utf8_transcode_test_module() -> Vec<u8> {
    use wasm_encoder::{
        CodeSection, ConstExpr, ExportKind, ExportSection, FunctionSection, GlobalSection,
        GlobalType, MemArg, MemorySection, MemoryType, Module, TypeSection, ValType,
    };

    let mut types = TypeSection::new();
    types.ty().function(
        [ValType::I32, ValType::I32, ValType::I32, ValType::I32],
        [ValType::I32],
    );
    types
        .ty()
        .function([ValType::I32, ValType::I32], [ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0); // func 0: cabi_realloc
    functions.function(1); // func 1: transcode_and_sum

    let mut memory = MemorySection::new();
    for _ in 0..2 {
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
    }

    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(16),
    );

    let mut exports = ExportSection::new();
    exports.export("transcode_and_sum", ExportKind::Func, 1);
    exports.export("caller_memory", ExportKind::Memory, 0);
    exports.export("callee_memory", ExportKind::Memory, 1);

    let mut code = CodeSection::new();

    // func 0: cabi_realloc — bump allocator over global 0, aligned to `align`.
    {
        let mut f = Function::new([(1, ValType::I32)]);
        f.instruction(&Instruction::GlobalGet(0));
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::I32Const(-1));
        f.instruction(&Instruction::I32Xor);
        f.instruction(&Instruction::I32And);
        f.instruction(&Instruction::LocalSet(4));
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::LocalGet(3));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::GlobalSet(0));
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 1: transcode_and_sum(src_ptr, tagged_len) -> i32
    // Locals: 0=ptr (in/out), 1=len (in/out, tagged on entry), then the
    // transcode scratch: 2=out_ptr, 3=tag, 4=src_idx, 5=dst_idx/out_bytes,
    // 6=cp, 7=cu, 8=cu2, plus 9=sum, 10=i for the summing loop.
    {
        let src_mem8 = MemArg {
            offset: 0,
            align: 0,
            memory_index: 0,
        };
        let src_mem16 = MemArg {
            offset: 0,
            align: 1,
            memory_index: 0,
        };
        let dst_mem8 = MemArg {
            offset: 0,
            align: 0,
            memory_index: 1,
        };
        let mut f = Function::new([(9, ValType::I32)]);
        emit_latin1_to_utf8_transcode_param(
            &mut f, 0, // realloc func
            1, // realloc align (utf-8: 1)
            src_mem8, src_mem16, dst_mem8, 0, // ptr_local
            1, // len_local (tagged on entry, rewritten to byte count)
            2, // out_ptr_local
            3, // tag
            4, // src_idx
            5, // dst_idx / out byte count
            6, // cp
            7, // cu
            8, // cu2
        );
        // sum = 0; i = 0
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalSet(9));
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalSet(10));
        f.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        f.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        // if i >= len (now the byte count): break
        f.instruction(&Instruction::LocalGet(10));
        f.instruction(&Instruction::LocalGet(1));
        f.instruction(&Instruction::I32GeU);
        f.instruction(&Instruction::BrIf(1));
        // sum += mem1.u8[ptr + i]
        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::LocalGet(10));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Load8U(dst_mem8));
        f.instruction(&Instruction::LocalGet(9));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(9));
        // i += 1
        f.instruction(&Instruction::LocalGet(10));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(10));
        f.instruction(&Instruction::Br(0));
        f.instruction(&Instruction::End); // loop
        f.instruction(&Instruction::End); // block
        f.instruction(&Instruction::LocalGet(9));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&globals)
        .section(&exports)
        .section(&code);
    module.finish()
}

/// Build a self-contained two-memory wasm module that exercises the EXACT
/// async-path UTF-8 → `latin1+utf16` (CompactUTF16) param transcode emitter
/// ([`emit_utf8_to_latin1_transcode_param`]) under a real engine, for the
/// #272 inc-4b runtime-differential oracle (the DEST-latin1 / tag-PRODUCING
/// direction).
///
/// Unlike the inc-1/2/4a oracles whose output is a plain (untagged) buffer, the
/// DEST-latin1 output is itself a `latin1+utf16` buffer whose length carries the
/// [`UTF16_TAG`]. So this module exports the TAGGED output length directly
/// (`transcode(src_ptr, src_byte_len) -> tagged_len`) and stashes the output
/// pointer in global 1, letting the host inspect BOTH the tag bit and the raw
/// output bytes in callee memory 1. The host writes UTF-8 source bytes into
/// memory 0 and passes the UNTAGGED byte length (a UTF-8 source length is never
/// tagged). A raw copy could not produce the correct tagged length + Latin-1 /
/// UTF-16 output bytes, so a pass proves two-phase transcoding.
///
/// `#[doc(hidden)] pub` purely so the `async_cross_encoding` runtime test can
/// instantiate it; not a supported API.
#[doc(hidden)]
pub fn build_utf8_to_latin1_transcode_test_module() -> Vec<u8> {
    build_x_to_latin1_transcode_test_module(false)
}

/// Build a self-contained two-memory wasm module that exercises the EXACT
/// async-path UTF-16 → `latin1+utf16` (CompactUTF16) param transcode emitter
/// ([`emit_utf16_to_latin1_transcode_param`]) under a real engine, for the
/// #272 inc-4b runtime-differential oracle. The UTF-16-source mirror of
/// [`build_utf8_to_latin1_transcode_test_module`]; the host writes UTF-16 LE
/// source code units into memory 0 and passes the UNTAGGED code-unit count.
///
/// `#[doc(hidden)] pub` purely so the `async_cross_encoding` runtime test can
/// instantiate it; not a supported API.
#[doc(hidden)]
pub fn build_utf16_to_latin1_transcode_test_module() -> Vec<u8> {
    build_x_to_latin1_transcode_test_module(true)
}

/// Shared builder for the two inc-4b DEST-latin1 oracle modules. `utf16_source`
/// selects the UTF-16-source emitter (vs the UTF-8-source one); both produce a
/// `latin1+utf16` output buffer in memory 1, return the TAGGED output length,
/// and stash the output pointer in global 1.
fn build_x_to_latin1_transcode_test_module(utf16_source: bool) -> Vec<u8> {
    use wasm_encoder::{
        CodeSection, ConstExpr, ExportKind, ExportSection, FunctionSection, GlobalSection,
        GlobalType, MemArg, MemorySection, MemoryType, Module, TypeSection, ValType,
    };

    let mut types = TypeSection::new();
    // type 0: cabi_realloc (i32,i32,i32,i32) -> i32
    types.ty().function(
        [ValType::I32, ValType::I32, ValType::I32, ValType::I32],
        [ValType::I32],
    );
    // type 1: transcode (i32 src_ptr, i32 src_count) -> i32 tagged_len
    types
        .ty()
        .function([ValType::I32, ValType::I32], [ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0); // func 0: cabi_realloc
    functions.function(1); // func 1: transcode

    let mut memory = MemorySection::new();
    for _ in 0..2 {
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
    }

    // global 0: bump cursor for the memory-1 allocator (start at 16).
    // global 1: out_ptr the host reads back to inspect the output buffer.
    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(16),
    );
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(0),
    );

    let mut exports = ExportSection::new();
    exports.export("transcode", ExportKind::Func, 1);
    exports.export("caller_memory", ExportKind::Memory, 0);
    exports.export("callee_memory", ExportKind::Memory, 1);
    exports.export("out_ptr", ExportKind::Global, 1);

    let mut code = CodeSection::new();

    // func 0: cabi_realloc — bump allocator over global 0, aligned to `align`.
    {
        let mut f = Function::new([(1, ValType::I32)]);
        f.instruction(&Instruction::GlobalGet(0));
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::I32Const(-1));
        f.instruction(&Instruction::I32Xor);
        f.instruction(&Instruction::I32And);
        f.instruction(&Instruction::LocalSet(4));
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::LocalGet(3));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::GlobalSet(0));
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 1: transcode(src_ptr, src_count) -> tagged_len
    // Locals: 0=ptr (in/out), 1=len (in/out — untagged src count on entry,
    // tagged output length on return), then the transcode scratch:
    //   2=out_ptr, 3=flag, 4=src_idx, 5=dst_idx, 6=a, 7=b, 8=c.
    // (a/b/c map to byte/cp/cont for the UTF-8 source, or cu/cp/cu2 for the
    // UTF-16 source — both two-phase loops use 6 scratch at base 3.)
    {
        let src_mem8 = MemArg {
            offset: 0,
            align: 0,
            memory_index: 0,
        };
        let src_mem16 = MemArg {
            offset: 0,
            align: 1,
            memory_index: 0,
        };
        let dst_mem8 = MemArg {
            offset: 0,
            align: 0,
            memory_index: 1,
        };
        let dst_mem16 = MemArg {
            offset: 0,
            align: 1,
            memory_index: 1,
        };
        let mut f = Function::new([(7, ValType::I32)]);
        if utf16_source {
            emit_utf16_to_latin1_transcode_param(
                &mut f, 0, // realloc func
                2, // realloc align (latin1+utf16: 2)
                src_mem16, dst_mem8, dst_mem16, 0, // ptr_local
                1, // len_local (untagged code-unit count → tagged output length)
                2, // out_ptr_local
                3, // flag
                4, // src_idx
                5, // dst_idx
                6, // cu
                7, // cp
                8, // cu2
            );
        } else {
            emit_utf8_to_latin1_transcode_param(
                &mut f, 0, // realloc func
                2, // realloc align (latin1+utf16: 2)
                src_mem8, dst_mem8, dst_mem16, 0, // ptr_local
                1, // len_local (untagged byte count → tagged output length)
                2, // out_ptr_local
                3, // flag
                4, // src_idx
                5, // dst_idx
                6, // byte
                7, // cp
                8, // cont
            );
        }
        // out_ptr global = ptr (rewritten to the callee output buffer); return
        // the tagged output length the emitter wrote to local 1.
        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::GlobalSet(1));
        f.instruction(&Instruction::LocalGet(1));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&globals)
        .section(&exports)
        .section(&code);
    module.finish()
}

/// Build a self-contained two-memory wasm module that exercises the EXACT
/// async-path NESTED-result inner copy emitter
/// ([`emit_patch_nested_indirections`]) for a `list<string>` RESULT crossing
/// memory in the callee=Utf8 → caller=Utf16 direction, for the #272 inc-5a
/// runtime-differential oracle.
///
/// This is the RESULT direction (callee PRODUCES, caller READS): SRC = callee
/// memory 1 (where the async-lift callee wrote the UTF-8 inner strings + the
/// outer list of `(ptr, len)` records), DST = caller memory 0 (where the caller
/// reads UTF-16). The host pre-writes BOTH memories to simulate the post-outer-
/// bulk-copy state:
/// * callee memory 1: inner UTF-8 strings, and the outer list of 8-byte
///   `(inner_ptr, inner_len)` records pointing at them.
/// * caller memory 0: a verbatim copy of the outer records (the stale callee
///   ptrs + byte-lengths the outer `memory.copy` produced).
///
/// The exported `patch_and_sum(outer_caller, outer_callee, count) -> i32` runs
/// the production [`emit_patch_nested_indirections`] (UTF-8 → UTF-16), which for
/// EACH record transcodes the inner string into a freshly `cabi_realloc`'d
/// caller-memory buffer, rewrites the caller-side inner `(ptr, len)` header to
/// `(out_ptr, out_code_unit_count)`, then SUMS the UTF-16 code units of every
/// inner string by re-reading the PATCHED `(ptr, len)` headers from caller
/// memory. A raw byte-copy (the pre-inc-5a behaviour) would leave UTF-8 bytes
/// the summing loop reads as 16-bit units (a different sum) AND leave the inner
/// len as the UTF-8 byte count — so a passing assertion proves real transcoding
/// AND the NEW header-len rewrite, not a copy.
///
/// `#[doc(hidden)] pub` purely so the `async_cross_encoding` runtime test can
/// instantiate it; not a supported API.
#[doc(hidden)]
pub fn build_nested_list_string_utf8_to_utf16_result_test_module() -> Vec<u8> {
    use crate::parser::ComponentValType;
    // Element type of the outer `list<string>` is `string` (is_string == true).
    build_nested_list_result_test_module(ComponentValType::String, true)
}

/// Build the negative-side oracle: the SAME nested-result emitter, but for a
/// `list<list<u8>>` RESULT in the callee=Utf8 → caller=Utf16 direction. A nested
/// `list<u8>` (`is_string == false` from [`collect_indirections`]) is arbitrary
/// binary; it MUST be RAW-COPIED, never transcoded — transcoding it as UTF-8
/// would silently corrupt it (the inc-5a blocker). This module proves the inner
/// `list<u8>` bytes are copied VERBATIM (and its len header is unchanged) by
/// summing the inner bytes via the PATCHED `(ptr, len)` header; a (wrong)
/// transcode of a multi-byte UTF-8 sequence would change both the byte content
/// and the length.
///
/// `#[doc(hidden)] pub` purely so the `async_cross_encoding` runtime test can
/// instantiate it; not a supported API.
#[doc(hidden)]
pub fn build_nested_list_u8_result_not_transcoded_test_module() -> Vec<u8> {
    use crate::parser::{ComponentValType, PrimitiveValType};
    // Element type of the outer `list<list<u8>>` is `list<u8>` (is_string ==
    // false) — must be raw-copied, NOT transcoded.
    build_nested_list_result_test_module(
        ComponentValType::List(Box::new(ComponentValType::Primitive(PrimitiveValType::U8))),
        false,
    )
}

/// Shared builder for the two inc-5a nested-result oracle modules.
///
/// `elem_ty` is the OUTER list's element type (`string` or `list<u8>`).
/// `sum_as_u16` selects the summing read width: u16 code units (for the
/// transcoded string case) vs u8 bytes (for the raw-copied `list<u8>` case).
/// Both run the SAME production [`emit_patch_nested_indirections`]; the
/// string-ness gate inside it decides transcode-vs-raw-copy from `elem_ty`.
fn build_nested_list_result_test_module(
    elem_ty: crate::parser::ComponentValType,
    sum_as_u16: bool,
) -> Vec<u8> {
    use wasm_encoder::{
        BlockType, CodeSection, ConstExpr, ExportKind, ExportSection, FunctionSection,
        GlobalSection, GlobalType, MemArg, MemorySection, MemoryType, Module, TypeSection, ValType,
    };

    let mut types = TypeSection::new();
    // type 0: cabi_realloc (i32,i32,i32,i32) -> i32
    types.ty().function(
        [ValType::I32, ValType::I32, ValType::I32, ValType::I32],
        [ValType::I32],
    );
    // type 1: patch_and_sum (i32 outer_caller, i32 outer_callee, i32 count) -> i32
    types
        .ty()
        .function([ValType::I32, ValType::I32, ValType::I32], [ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0); // func 0: cabi_realloc (allocates in CALLER memory 0)
    functions.function(1); // func 1: patch_and_sum

    // memory 0 = caller (UTF-16 / raw-copy DST + realloc arena),
    // memory 1 = callee (UTF-8 inner strings + outer records SRC).
    let mut memory = MemorySection::new();
    for _ in 0..2 {
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
    }

    // global 0: bump cursor for the CALLER-memory-0 allocator (start high, above
    // the host-written outer records, so realloc never overwrites them).
    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(1024),
    );

    let mut exports = ExportSection::new();
    exports.export("patch_and_sum", ExportKind::Func, 1);
    exports.export("caller_memory", ExportKind::Memory, 0);
    exports.export("callee_memory", ExportKind::Memory, 1);

    let mut code = CodeSection::new();

    // func 0: cabi_realloc — bump allocator over global 0 in CALLER memory 0.
    {
        let mut f = Function::new([(1, ValType::I32)]);
        f.instruction(&Instruction::GlobalGet(0));
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::I32Const(-1));
        f.instruction(&Instruction::I32Xor);
        f.instruction(&Instruction::I32And);
        f.instruction(&Instruction::LocalSet(4));
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::LocalGet(3));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::GlobalSet(0));
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    // func 1: patch_and_sum(outer_caller, outer_callee, count) -> i32
    //
    // Params: 0=outer_caller (DST outer list, caller mem 0),
    //         1=outer_callee (SRC outer list, callee mem 1),
    //         2=count (element count).
    // Locals beyond params (declared block below):
    //   3..=15 : the 13-local scratch `emit_patch_nested_indirections` consumes
    //            (l_first_scratch = 3 ⇒ nested loop 3..=8; transcode_base = 9 ⇒
    //            9..=13; 14/15 spare) — DISJOINT regions exactly as the async
    //            adapters guarantee (here: 3..=8 nested vs 9..=13 transcode).
    //   16 = sum, 17 = i, 18 = rec (caller record ptr), 19 = inner_ptr,
    //   20 = inner_len, 21 = j.
    {
        // Inner (ptr, len) headers are read back from CALLER memory 0.
        let rec_mem = MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        };
        let rec_len_mem = MemArg {
            offset: 4,
            align: 2,
            memory_index: 0,
        };
        // The summed inner buffer lives in caller memory 0 (transcoded UTF-16,
        // or the raw-copied `list<u8>` bytes).
        let inner_u16 = MemArg {
            offset: 0,
            align: 1,
            memory_index: 0,
        };
        let inner_u8 = MemArg {
            offset: 0,
            align: 0,
            memory_index: 0,
        };

        let l_first_scratch = 3u32;
        let l_transcode_base = 9u32;
        let l_sum = 16u32;
        let l_i = 17u32;
        let l_rec = 18u32;
        let l_inner_ptr = 19u32;
        let l_inner_len = 20u32;
        let l_j = 21u32;

        let mut f = Function::new([(19, ValType::I32)]);

        // Run the production nested-indirection patcher: l_dst_ptr = param 0
        // (caller outer list), l_callee_src = param 1 (callee outer list),
        // l_src_len = param 2 (count), elem_size = 8 (one (ptr,len) record),
        // caller_memory = 0, callee_memory = 1, UTF-8 → UTF-16 direction.
        emit_patch_nested_indirections(
            &mut f,
            &elem_ty,
            0, // l_dst_ptr  (caller outer list)
            1, // l_callee_src (callee outer list)
            2, // l_src_len (count)
            8, // elem_size (one (ptr, len) record)
            l_first_scratch,
            0,     // realloc_func (allocates in caller memory 0)
            0,     // caller_memory
            1,     // callee_memory
            false, // callee_compact_utf16
            Some(crate::parser::CanonStringEncoding::Utf16), // caller_encoding
            Some(crate::parser::CanonStringEncoding::Utf8), // callee_encoding
            l_transcode_base,
        );

        // sum = 0; i = 0
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalSet(l_sum));
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalSet(l_i));

        // outer loop over records
        f.instruction(&Instruction::Block(BlockType::Empty));
        f.instruction(&Instruction::Loop(BlockType::Empty));
        f.instruction(&Instruction::LocalGet(l_i));
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::I32GeU);
        f.instruction(&Instruction::BrIf(1));

        // rec = outer_caller + i * 8
        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::LocalGet(l_i));
        f.instruction(&Instruction::I32Const(8));
        f.instruction(&Instruction::I32Mul);
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(l_rec));

        // inner_ptr = caller_mem0.load(rec + 0); inner_len = caller_mem0.load(rec + 4)
        f.instruction(&Instruction::LocalGet(l_rec));
        f.instruction(&Instruction::I32Load(rec_mem));
        f.instruction(&Instruction::LocalSet(l_inner_ptr));
        f.instruction(&Instruction::LocalGet(l_rec));
        f.instruction(&Instruction::I32Load(rec_len_mem));
        f.instruction(&Instruction::LocalSet(l_inner_len));

        // inner loop: j in 0..inner_len, sum the inner units (u16 or u8)
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalSet(l_j));
        f.instruction(&Instruction::Block(BlockType::Empty));
        f.instruction(&Instruction::Loop(BlockType::Empty));
        f.instruction(&Instruction::LocalGet(l_j));
        f.instruction(&Instruction::LocalGet(l_inner_len));
        f.instruction(&Instruction::I32GeU);
        f.instruction(&Instruction::BrIf(1));

        // addr = inner_ptr + j*(2 if u16 else 1)
        f.instruction(&Instruction::LocalGet(l_inner_ptr));
        f.instruction(&Instruction::LocalGet(l_j));
        if sum_as_u16 {
            f.instruction(&Instruction::I32Const(1));
            f.instruction(&Instruction::I32Shl);
        }
        f.instruction(&Instruction::I32Add);
        if sum_as_u16 {
            f.instruction(&Instruction::I32Load16U(inner_u16));
        } else {
            f.instruction(&Instruction::I32Load8U(inner_u8));
        }
        f.instruction(&Instruction::LocalGet(l_sum));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(l_sum));

        // j += 1
        f.instruction(&Instruction::LocalGet(l_j));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(l_j));
        f.instruction(&Instruction::Br(0));
        f.instruction(&Instruction::End); // inner loop
        f.instruction(&Instruction::End); // inner block

        // i += 1
        f.instruction(&Instruction::LocalGet(l_i));
        f.instruction(&Instruction::I32Const(1));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(l_i));
        f.instruction(&Instruction::Br(0));
        f.instruction(&Instruction::End); // outer loop
        f.instruction(&Instruction::End); // outer block

        f.instruction(&Instruction::LocalGet(l_sum));
        f.instruction(&Instruction::End);
        code.function(&f);
    }

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&memory)
        .section(&globals)
        .section(&exports)
        .section(&code);
    module.finish()
}

/// Emit a chain of `(disc == value)` checks for a [`ConditionalPointerPair`]'s
/// guards on the **flat-local** path — every guard in `cond.outer_guards`
/// followed by the pair's innermost discriminant. All checks are ANDed; the
/// resulting i32 (0/1) is left on the wasm stack so the caller can immediately
/// emit `If`. `flat_base` is added to every guard's `position` (use 0 for
/// param paths, `result_save_base` for the flat-result path).
///
/// Without this AND-chain, a `ConditionalPointerPair` inside a nested
/// option/result/variant payload would fire whenever the *inner* discriminant
/// slot happens to read as the inner value — *even in arms where the payload
/// type is something else entirely* — yielding an arbitrary cross-memory copy
/// with attacker-controlled `(ptr, len)` (LS-P-10).
pub(crate) fn emit_conditional_guard_chain_flat(
    body: &mut Function,
    cond: &crate::resolver::ConditionalPointerPair,
    flat_base: u32,
) {
    let mut emitted_any = false;
    for guard in &cond.outer_guards {
        body.instruction(&Instruction::LocalGet(flat_base + guard.position));
        body.instruction(&Instruction::I32Const(guard.value as i32));
        body.instruction(&Instruction::I32Eq);
        if emitted_any {
            body.instruction(&Instruction::I32And);
        }
        emitted_any = true;
    }
    // Innermost (current-level) guard.
    body.instruction(&Instruction::LocalGet(
        flat_base + cond.discriminant_position,
    ));
    body.instruction(&Instruction::I32Const(cond.discriminant_value as i32));
    body.instruction(&Instruction::I32Eq);
    if emitted_any {
        body.instruction(&Instruction::I32And);
    }
}

/// Emit a chain of `(disc == value)` checks for a [`ConditionalPointerPair`]'s
/// guards on the **byte-offset** path — every guard in `cond.outer_guards`
/// followed by the innermost discriminant, all ANDed. `base_ptr_local` holds
/// the pointer to the buffer (callee result area, etc.); each guard's
/// `byte_size` selects the load width (`I32Load8U` / `I32Load16U` /
/// `I32Load`). See [`emit_conditional_guard_chain_flat`] for the LS-P-10
/// rationale.
pub(crate) fn emit_conditional_guard_chain_byte(
    body: &mut Function,
    cond: &crate::resolver::ConditionalPointerPair,
    base_ptr_local: u32,
    memory_index: u32,
) {
    fn emit_disc_load(
        body: &mut Function,
        base_ptr_local: u32,
        byte_size: u32,
        offset: u32,
        memory_index: u32,
    ) {
        body.instruction(&Instruction::LocalGet(base_ptr_local));
        match byte_size {
            1 => body.instruction(&Instruction::I32Load8U(wasm_encoder::MemArg {
                offset: offset as u64,
                align: 0,
                memory_index,
            })),
            2 => body.instruction(&Instruction::I32Load16U(wasm_encoder::MemArg {
                offset: offset as u64,
                align: 1,
                memory_index,
            })),
            _ => body.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: offset as u64,
                align: 2,
                memory_index,
            })),
        };
    }
    let mut emitted_any = false;
    for guard in &cond.outer_guards {
        emit_disc_load(
            body,
            base_ptr_local,
            guard.byte_size,
            guard.position,
            memory_index,
        );
        body.instruction(&Instruction::I32Const(guard.value as i32));
        body.instruction(&Instruction::I32Eq);
        if emitted_any {
            body.instruction(&Instruction::I32And);
        }
        emitted_any = true;
    }
    emit_disc_load(
        body,
        base_ptr_local,
        cond.discriminant_byte_size,
        cond.discriminant_position,
        memory_index,
    );
    body.instruction(&Instruction::I32Const(cond.discriminant_value as i32));
    body.instruction(&Instruction::I32Eq);
    if emitted_any {
        body.instruction(&Instruction::I32And);
    }
}

/// Compute Canonical ABI (size, alignment) in bytes for a component value type.
///
/// Per Component Model Canonical ABI spec, every type has a fixed lowered
/// memory layout. List/string lower to a (ptr, len) pair (8 bytes, align 4).
/// Records pad each field to its alignment, then pad the whole record to
/// its max field alignment. We use this to compute typed byte counts when
/// copying lists across component memories.
///
/// Assumes `Type(idx)` references have already been resolved (see
/// `component_wrap::resolve_component_val_type`). Unresolved Type/handle
/// references fall back to a 4-byte handle-sized layout.
pub(crate) fn cabi_size_align(ty: &crate::parser::ComponentValType) -> (u32, u32) {
    use crate::parser::{ComponentValType as CVT, PrimitiveValType as P};
    fn align_up(n: u32, a: u32) -> u32 {
        (n + a - 1) & !(a - 1)
    }
    match ty {
        CVT::Primitive(p) => match p {
            P::Bool | P::S8 | P::U8 => (1, 1),
            P::S16 | P::U16 => (2, 2),
            P::S32 | P::U32 | P::F32 | P::Char => (4, 4),
            P::S64 | P::U64 | P::F64 => (8, 8),
        },
        CVT::String => (8, 4),
        CVT::List(_) => (8, 4),
        CVT::FixedSizeList(elem, n) => {
            let (es, ea) = cabi_size_align(elem);
            (es * n, ea)
        }
        CVT::Record(fields) => {
            let mut size = 0u32;
            let mut align = 1u32;
            for (_, fty) in fields {
                let (fs, fa) = cabi_size_align(fty);
                size = align_up(size, fa);
                size += fs;
                align = align.max(fa);
            }
            (align_up(size, align), align)
        }
        CVT::Tuple(elems) => {
            let mut size = 0u32;
            let mut align = 1u32;
            for ety in elems {
                let (es, ea) = cabi_size_align(ety);
                size = align_up(size, ea);
                size += es;
                align = align.max(ea);
            }
            (align_up(size, align), align)
        }
        CVT::Option(inner) => {
            let (is, ia) = cabi_size_align(inner);
            let align = ia.max(1);
            let body = align_up(1, align) + is;
            (align_up(body, align), align)
        }
        CVT::Result { ok, err } => {
            let (os, oa) = ok.as_ref().map(|t| cabi_size_align(t)).unwrap_or((0, 1));
            let (es, ea) = err.as_ref().map(|t| cabi_size_align(t)).unwrap_or((0, 1));
            let align = oa.max(ea).max(1);
            let body = align_up(1, align) + os.max(es);
            (align_up(body, align), align)
        }
        CVT::Variant(cases) => {
            let mut max_size = 0u32;
            let mut align = 1u32;
            for (_, case_ty) in cases {
                if let Some(ct) = case_ty {
                    let (cs, ca) = cabi_size_align(ct);
                    max_size = max_size.max(cs);
                    align = align.max(ca);
                }
            }
            let body = align_up(1, align) + max_size;
            (align_up(body, align), align)
        }
        CVT::Flags(names) => {
            // flags<N>: ceil(N/8) bytes padded to power-of-2 storage
            // class; align ∈ {1, 2, 4} per LS-A-20.
            let n = names.len() as u32;
            if n <= 8 {
                (1, 1)
            } else if n <= 16 {
                (2, 2)
            } else {
                (4u32.saturating_mul(n.div_ceil(32)), 4)
            }
        }
        CVT::Own(_) | CVT::Borrow(_) | CVT::Type(_) => (4, 4),
    }
}

/// Walk each element of a copied list and recursively patch up nested
/// (ptr, len) pairs that still point into callee memory. Allocates fresh
/// caller-side buffers, copies bytes across, and writes back the new ptr.
///
/// For frequencies-style `list<{ string, u32 }>` this scans each 12-byte
/// record, copies the string at offset 0 into caller memory, and overwrites
/// the (ptr, len) header. Nested lists/records recurse. Other field types
/// are left as-is (already byte-copied).
#[allow(clippy::too_many_arguments)]
fn emit_patch_nested_indirections(
    body: &mut Function,
    elem_ty: &crate::parser::ComponentValType,
    l_dst_ptr: u32,
    l_callee_src: u32,
    l_src_len: u32,
    elem_size: u32,
    l_first_scratch: u32,
    realloc_func: u32,
    caller_memory: u32,
    callee_memory: u32,
    // True when the *callee* string encoding (this is a result-side,
    // callee → caller copy) is `latin1+utf16` (CompactUtf16). A byte-granular
    // inner buffer (`sub_elem_size == 1`) is then a tag-encoded string whose
    // byte count must be masked/doubled. The inner (ptr, len) header keeps its
    // original (tagged) length — this function rewrites only the pointer.
    callee_compact_utf16: bool,
    // #272 inc 5a: the result-side string encodings (callee PRODUCES, caller
    // READS). When `Some`/`Some` AND callee=Utf8 / caller=Utf16 AND the inner
    // buffer is a `string` (`is_string == true` from `collect_indirections`),
    // the inner string is TRANSCODED (UTF-8 → UTF-16) into caller memory
    // instead of raw-copied, and its TRANSCODED code-unit count is written to
    // the inner len header. A nested `list<u8>` (`is_string == false`) and any
    // other direction keep the existing raw-copy + original len. This is the
    // RESULT direction (callee → caller), so SRC = callee memory, DST = caller
    // memory — the OPPOSITE memory direction from the flat-param transcode.
    caller_encoding: Option<crate::parser::CanonStringEncoding>,
    callee_encoding: Option<crate::parser::CanonStringEncoding>,
    // Base index of a disjoint scratch block of 5 i32 locals dedicated to the
    // inner UTF-8 → UTF-16 transcode loop (out_ptr/src_idx/dst_idx/cp+byte/cont
    // are packed into `emit_utf8_to_utf16_transcode_param`'s 5 scratch args
    // re-using `l_new_ptr` as the out-ptr sink — see the slot below). The
    // caller MUST guarantee `[l_transcode_base, l_transcode_base + 4]` does NOT
    // overlap `[l_first_scratch, l_first_scratch + 5]` (the nested-loop locals,
    // which stay live across the whole loop body) — the two regions are
    // SIMULTANEOUSLY LIVE because the transcode runs INSIDE the per-element
    // loop. The async callback / stackful emitters pass `l_p2 + 16` /
    // `l_scratch + 12`, which sit past the `l_*_scratch + 5` nested region.
    l_transcode_base: u32,
) {
    let indirections = collect_indirections(elem_ty, 0);
    if indirections.is_empty() {
        return;
    }

    // #272 inc 5a: an inner STRING (not a `list<u8>`) crossing memory in the
    // callee=Utf8 → caller=Utf16 RESULT direction is transcoded rather than
    // raw-copied. Computed once per call; the per-indirection slot below gates
    // on this AND the indirection's own `is_string`.
    let inner_transcode_utf8_to_utf16 = matches!(
        callee_encoding,
        Some(crate::parser::CanonStringEncoding::Utf8)
    ) && matches!(
        caller_encoding,
        Some(crate::parser::CanonStringEncoding::Utf16)
    );

    // Locals (caller has reserved scratch starting at l_first_scratch):
    //   l_i        = element index counter
    //   l_rec_dst  = caller-side pointer to current record
    //   l_rec_src  = callee-side pointer to current record (read source)
    //   l_old_ptr  = original src ptr (callee address)
    //   l_buf_len  = byte count to copy
    //   l_new_ptr  = freshly allocated caller buffer
    let l_i = l_first_scratch;
    let l_rec_dst = l_first_scratch + 1;
    let l_old_ptr = l_first_scratch + 2;
    let l_buf_len = l_first_scratch + 3;
    let l_new_ptr = l_first_scratch + 4;
    let l_rec_src = l_first_scratch + 5;

    // i = 0
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(l_i));

    body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

    // if i >= len break
    body.instruction(&Instruction::LocalGet(l_i));
    body.instruction(&Instruction::LocalGet(l_src_len));
    body.instruction(&Instruction::I32GeU);
    body.instruction(&Instruction::BrIf(1));

    // rec_dst = l_dst_ptr + i * elem_size
    body.instruction(&Instruction::LocalGet(l_dst_ptr));
    body.instruction(&Instruction::LocalGet(l_i));
    if elem_size != 1 {
        body.instruction(&Instruction::I32Const(elem_size as i32));
        body.instruction(&Instruction::I32Mul);
    }
    body.instruction(&Instruction::I32Add);
    body.instruction(&Instruction::LocalSet(l_rec_dst));

    // rec_src = l_callee_src + i * elem_size (in callee memory)
    body.instruction(&Instruction::LocalGet(l_callee_src));
    body.instruction(&Instruction::LocalGet(l_i));
    if elem_size != 1 {
        body.instruction(&Instruction::I32Const(elem_size as i32));
        body.instruction(&Instruction::I32Mul);
    }
    body.instruction(&Instruction::I32Add);
    body.instruction(&Instruction::LocalSet(l_rec_src));

    for (offset, sub_elem_size, is_string) in &indirections {
        let dst_mem_arg_ptr = wasm_encoder::MemArg {
            offset: *offset as u64,
            align: 2,
            memory_index: caller_memory,
        };
        let dst_mem_arg_len = wasm_encoder::MemArg {
            offset: (*offset + 4) as u64,
            align: 2,
            memory_index: caller_memory,
        };
        let src_mem_arg_ptr = wasm_encoder::MemArg {
            offset: *offset as u64,
            align: 2,
            memory_index: callee_memory,
        };
        let src_mem_arg_len = wasm_encoder::MemArg {
            offset: (*offset + 4) as u64,
            align: 2,
            memory_index: callee_memory,
        };

        // Read original (ptr, len) DIRECTLY from callee memory at rec_src.
        body.instruction(&Instruction::LocalGet(l_rec_src));
        body.instruction(&Instruction::I32Load(src_mem_arg_ptr));
        body.instruction(&Instruction::LocalSet(l_old_ptr));

        body.instruction(&Instruction::LocalGet(l_rec_src));
        body.instruction(&Instruction::I32Load(src_mem_arg_len));
        body.instruction(&Instruction::LocalSet(l_buf_len));

        // #272 inc 5a: an inner STRING (`is_string`) in the callee=Utf8 →
        // caller=Utf16 RESULT direction is TRANSCODED into caller memory rather
        // than raw-copied. A nested `list<u8>` (`is_string == false`) — which
        // also lowers to `sub_elem_size == 1` but is arbitrary binary —
        // explicitly does NOT take this branch; it keeps the raw-copy below so
        // its bytes are never mis-transcoded.
        let transcode_inner = *is_string && inner_transcode_utf8_to_utf16;

        if transcode_inner {
            // SRC = callee memory (UTF-8, where the callee wrote the inner
            // string), DST = caller memory (UTF-16, where the caller reads it).
            // `l_buf_len` currently holds the source UTF-8 BYTE length (read
            // above; a string's `sub_elem_size == 1`). The transcode loop fn
            // reallocs 2*len in caller memory, rewrites `l_old_ptr` → the caller
            // out-ptr and `l_buf_len` → the OUTPUT UTF-16 code-unit count.
            //
            // CRITICAL — MemArg memory direction is the REVERSE of the flat
            // param transcode: there SRC = caller, DST = callee; here, on the
            // result side, SRC = callee, DST = caller.
            let src_mem8 = wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: callee_memory,
            };
            let dst_mem16 = wasm_encoder::MemArg {
                offset: 0,
                align: 1,
                memory_index: caller_memory,
            };
            // The transcode helper takes 5 scratch locals plus a dedicated
            // out-ptr sink. Reuse `l_new_ptr` as the out-ptr sink and the
            // disjoint `l_transcode_base ..= l_transcode_base + 4` block for the
            // 5 loop scratch locals. `l_old_ptr`/`l_buf_len` are the in/out
            // (ptr, len) the loop rewrites.
            emit_utf8_to_utf16_transcode_param(
                body,
                realloc_func,
                src_mem8,
                dst_mem16,
                l_old_ptr, // ptr_local (callee src ptr → rewritten to caller out ptr)
                l_buf_len, // len_local (src byte len → rewritten to out code-unit count)
                l_new_ptr, // out_ptr_local
                l_transcode_base, // src_idx
                l_transcode_base + 1, // dst_idx / out code-unit count
                l_transcode_base + 2, // cp
                l_transcode_base + 3, // byte
                l_transcode_base + 4, // cont
            );

            // Store the transcoded out-ptr AND the NEW (transcoded) code-unit
            // count into the caller-memory inner (ptr, len) header. The len
            // store is NEW for inc 5a: the bulk `memory.copy` of the outer list
            // already copied the STALE callee len into caller memory, which is
            // now wrong (it counted UTF-8 bytes, not UTF-16 code units) — it
            // MUST be overwritten so the caller reads the correct length.
            body.instruction(&Instruction::LocalGet(l_rec_dst));
            body.instruction(&Instruction::LocalGet(l_old_ptr));
            body.instruction(&Instruction::I32Store(dst_mem_arg_ptr));
            body.instruction(&Instruction::LocalGet(l_rec_dst));
            body.instruction(&Instruction::LocalGet(l_buf_len));
            body.instruction(&Instruction::I32Store(dst_mem_arg_len));

            continue;
        }

        // LS-P-14: trap if `len * sub_elem_size` would wrap mod 2^32. Without
        // this guard a callee-supplied `len` near `u32::MAX / sub_elem_size`
        // wraps `buf_len` to a small value; the bounds check below uses
        // `old_ptr + buf_len > mem_bytes` (also `i32.add`-based and wrapping)
        // and is bypassed; the adapter then under-allocates the caller
        // buffer and under-copies the inner list contents while the caller-
        // side bulk-copy of the outer (ptr, len) keeps the original large
        // `len` — silent truncation and semantic drift between the fused
        // and composed executions.
        let inner_compact_utf16 = callee_compact_utf16 && *sub_elem_size == 1;
        emit_overflow_guard(body, l_buf_len, *sub_elem_size);
        if inner_compact_utf16 {
            // #253: byte count is tag-aware — (len & TAG) ? (len & !TAG)*2 : len.
            emit_copy_byte_count(body, l_buf_len, 1, true);
            body.instruction(&Instruction::LocalSet(l_buf_len));
        } else if *sub_elem_size != 1 {
            body.instruction(&Instruction::LocalGet(l_buf_len));
            body.instruction(&Instruction::I32Const(*sub_elem_size as i32));
            body.instruction(&Instruction::I32Mul);
            body.instruction(&Instruction::LocalSet(l_buf_len));
        }

        // Skip patch if (old_ptr, buf_len) doesn't fit in callee mem — guards
        // against garbage values triggering an unrecoverable trap.
        body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::LocalGet(l_old_ptr));
        body.instruction(&Instruction::LocalGet(l_buf_len));
        body.instruction(&Instruction::I32Add);
        body.instruction(&Instruction::MemorySize(callee_memory));
        body.instruction(&Instruction::I32Const(16));
        body.instruction(&Instruction::I32Shl);
        body.instruction(&Instruction::I32GtU);
        body.instruction(&Instruction::BrIf(0));

        // new_ptr = realloc(0, 0, align, buf_len) in caller memory.
        // align 2 for a compact-utf16 inner string (the buffer may hold a
        // UTF-16 payload), else 1 — matching the other tag-aware copy sites.
        body.instruction(&Instruction::I32Const(0));
        body.instruction(&Instruction::I32Const(0));
        body.instruction(&Instruction::I32Const(if inner_compact_utf16 {
            2
        } else {
            1
        }));
        body.instruction(&Instruction::LocalGet(l_buf_len));
        emit_checked_realloc(body, realloc_func, l_new_ptr);

        // memory.copy new_ptr <- old_ptr (callee → caller)
        body.instruction(&Instruction::LocalGet(l_new_ptr));
        body.instruction(&Instruction::LocalGet(l_old_ptr));
        body.instruction(&Instruction::LocalGet(l_buf_len));
        body.instruction(&Instruction::MemoryCopy {
            dst_mem: caller_memory,
            src_mem: callee_memory,
        });

        // caller_mem.store(rec_dst + offset, new_ptr). The len header is left as
        // the bulk-copied original (raw-copied buffers preserve their length).
        body.instruction(&Instruction::LocalGet(l_rec_dst));
        body.instruction(&Instruction::LocalGet(l_new_ptr));
        body.instruction(&Instruction::I32Store(dst_mem_arg_ptr));

        body.instruction(&Instruction::End);
    }

    // i++
    body.instruction(&Instruction::LocalGet(l_i));
    body.instruction(&Instruction::I32Const(1));
    body.instruction(&Instruction::I32Add);
    body.instruction(&Instruction::LocalSet(l_i));
    body.instruction(&Instruction::Br(0));

    body.instruction(&Instruction::End); // end loop
    body.instruction(&Instruction::End); // end block
}

/// For a given element type, find every field offset that holds a (ptr, len)
/// pair that needs cross-memory copying (currently strings and nested lists).
/// Returns `(byte_offset_within_element, sub_element_size_in_bytes, is_string)`.
///
/// `is_string` is the #272 inc-5a string-ness signal: `true` for a nested
/// `ComponentValType::String`, `false` for a nested `List` (e.g. `list<u8>`).
/// This is RECOVERABLE here, where the WIT type is still in hand, but NOT in
/// the lowered `CopyLayout` descriptor — a nested `string` and a nested
/// `list<u8>` BOTH lower to `Bulk{1}` (byte-granular, indistinguishable). The
/// emitter MUST consult this flag before transcoding an inner buffer:
/// transcoding an arbitrary-binary `list<u8>` as if it were UTF-8 would
/// silently corrupt it. Only `is_string == true` inner buffers may be
/// transcoded; everything else keeps the raw-copy.
pub(crate) fn collect_indirections(
    ty: &crate::parser::ComponentValType,
    base_offset: u32,
) -> Vec<(u32, u32, bool)> {
    use crate::parser::ComponentValType as CVT;
    fn align_up(n: u32, a: u32) -> u32 {
        (n + a - 1) & !(a - 1)
    }
    let mut out = Vec::new();
    match ty {
        CVT::String => out.push((base_offset, 1, true)),
        CVT::List(elem) => {
            let (es, _) = cabi_size_align(elem);
            out.push((base_offset, es, false));
        }
        CVT::Record(fields) => {
            let mut off = 0u32;
            for (_, fty) in fields {
                let (fs, fa) = cabi_size_align(fty);
                off = align_up(off, fa);
                out.extend(collect_indirections(fty, base_offset + off));
                off += fs;
            }
        }
        CVT::Tuple(elems) => {
            let mut off = 0u32;
            for ety in elems {
                let (es, ea) = cabi_size_align(ety);
                off = align_up(off, ea);
                out.extend(collect_indirections(ety, base_offset + off));
                off += es;
            }
        }
        // Option/Result/Variant: indirections inside payloads are skipped
        // for now — supporting them needs reading the discriminant before
        // walking the body. Keep behaviour conservative until a test case
        // exercises the path.
        _ => {}
    }
    out
}

/// Scans the merged module's imports to find `[resource-rep]` and `[resource-new]`
/// function imports and records their merged function indices.
type ResourceImportMap = std::collections::HashMap<(String, String), u32>;

fn build_resource_import_maps(merged: &MergedModule) -> (ResourceImportMap, ResourceImportMap) {
    use wasm_encoder::EntityType;
    let mut rep_map = std::collections::HashMap::new();
    let mut new_map = std::collections::HashMap::new();
    let mut func_idx = 0u32;
    for imp in &merged.imports {
        if matches!(imp.entity_type, EntityType::Function(_)) {
            if imp.name.starts_with("[resource-rep]") {
                rep_map.insert((imp.module.clone(), imp.name.clone()), func_idx);
            } else if imp.name.starts_with("[resource-new]") {
                new_map.insert((imp.module.clone(), imp.name.clone()), func_idx);
            }
            func_idx += 1;
        }
    }
    (rep_map, new_map)
}

/// Emit Phase 0: convert borrow resource handles for each `ResourceBorrowTransfer`.
fn emit_resource_borrow_phase0(func: &mut Function, transfers: &[super::ResourceBorrowTransfer]) {
    for t in transfers {
        func.instruction(&Instruction::LocalGet(t.param_idx));
        func.instruction(&Instruction::Call(t.rep_func));
        if let Some(new_func) = t.new_func {
            // 3-component chain: rep → new handle in callee's table
            func.instruction(&Instruction::Call(new_func));
        }
        func.instruction(&Instruction::LocalSet(t.param_idx));
    }
}

/// Emit Phase R-rep: extract representations from own<T> result handles.
///
/// Calls `resource.rep(handle)` for each own result, storing the rep in
/// scratch locals starting at `scratch_base`. The original handle locals
/// are NOT modified — post_return still needs them to drop the callee's handles.
fn emit_resource_rep_results(
    func: &mut Function,
    transfers: &[super::ResourceOwnResultTransfer],
    result_base: u32,
    scratch_base: u32,
) {
    for (i, t) in transfers.iter().enumerate() {
        let local_idx = result_base + t.position;
        func.instruction(&Instruction::LocalGet(local_idx));
        func.instruction(&Instruction::Call(t.rep_func));
        func.instruction(&Instruction::LocalSet(scratch_base + i as u32));
    }
}

/// Emit Phase R-new: mint fresh handles from extracted representations.
///
/// Calls `resource.new(rep)` for each own result, reading from scratch locals
/// and storing the new handle back into the result locals.
fn emit_resource_new_results(
    func: &mut Function,
    transfers: &[super::ResourceOwnResultTransfer],
    result_base: u32,
    scratch_base: u32,
) {
    for (i, t) in transfers.iter().enumerate() {
        let local_idx = result_base + t.position;
        func.instruction(&Instruction::LocalGet(scratch_base + i as u32));
        func.instruction(&Instruction::Call(t.new_func));
        func.instruction(&Instruction::LocalSet(local_idx));
    }
}

/// FACT-style adapter generator
pub struct FactStyleGenerator {
    #[allow(dead_code)]
    config: AdapterConfig,
}

impl FactStyleGenerator {
    /// Create a new generator with the given configuration
    pub fn new(config: AdapterConfig) -> Self {
        Self { config }
    }

    /// Generate an adapter for a specific call site
    fn generate_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
        _adapter_idx: usize,
        resource_rep_imports: &std::collections::HashMap<(String, String), u32>,
        resource_new_imports: &std::collections::HashMap<(String, String), u32>,
    ) -> Result<AdapterFunction> {
        let name = format!(
            "$adapter_{}_{}_to_{}_{}",
            site.from_component, site.from_module, site.to_component, site.to_module
        );

        // Determine adapter options based on call site
        let options =
            self.analyze_call_site(site, merged, resource_rep_imports, resource_new_imports);

        // Generate the adapter function body
        let (type_idx, body, class) = if site.crosses_memory && options.needs_transcoding() {
            let (t, b) = self.generate_transcoding_adapter(site, merged, &options)?;
            (t, b, AdapterClass::Transcode)
        } else if site.crosses_memory {
            let (t, b) =
                self.generate_memory_copy_adapter(site, merged, &options, resource_rep_imports)?;
            (t, b, AdapterClass::MemoryCopy)
        } else {
            let (t, b) = self.generate_direct_adapter(site, merged, &options)?;
            (t, b, AdapterClass::Direct)
        };

        Ok(AdapterFunction {
            name,
            type_idx,
            body,
            source_component: site.from_component,
            source_module: site.from_module,
            target_component: site.to_component,
            target_module: site.to_module,
            target_function: self.resolve_target_function(site, merged)?,
            class,
        })
    }

    /// Analyze a call site to determine adapter options
    fn analyze_call_site(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
        resource_rep_imports: &std::collections::HashMap<(String, String), u32>,
        resource_new_imports: &std::collections::HashMap<(String, String), u32>,
    ) -> AdapterOptions {
        let mut options = AdapterOptions::default();

        // Determine memory indices
        // In shared memory mode, all components use memory 0
        // In multi-memory mode, each component gets its own memory
        if let Some(&caller_mem) =
            merged
                .memory_index_map
                .get(&(site.from_component, site.from_module, 0))
        {
            options.caller_memory = caller_mem;
        }

        if let Some(&callee_mem) =
            merged
                .memory_index_map
                .get(&(site.to_component, site.to_module, 0))
        {
            options.callee_memory = callee_mem;
        }

        // Look up cabi_realloc for caller and callee
        if let Some(&realloc_idx) = merged
            .realloc_map
            .get(&(site.from_component, site.from_module))
        {
            options.caller_realloc = Some(realloc_idx);
        }
        if let Some(&realloc_idx) = merged.realloc_map.get(&(site.to_component, site.to_module)) {
            options.callee_realloc = Some(realloc_idx);
        }

        // Use canonical options from the resolver if available, fall back to UTF-8
        options.caller_string_encoding = site
            .requirements
            .caller_encoding
            .map(canon_to_string_encoding)
            .unwrap_or(StringEncoding::Utf8);
        options.callee_string_encoding = site
            .requirements
            .callee_encoding
            .map(canon_to_string_encoding)
            .unwrap_or(StringEncoding::Utf8);

        // Detect whether the target function returns a (ptr, len) pair.
        // Look up the target function's type in the merged module and check
        // if the result signature is exactly [I32, I32].
        if let Some(&merged_func_idx) = merged.function_index_map.get(&(
            site.to_component,
            site.to_module,
            site.export_func_idx,
        )) && let Some(func) = merged.defined_func(merged_func_idx)
            && let Some(func_type) = merged.types.get(func.type_idx as usize)
            && func_type.results.len() == 2
            && func_type.results[0] == wasm_encoder::ValType::I32
            && func_type.results[1] == wasm_encoder::ValType::I32
        {
            options.returns_pointer_pair = true;
        }

        // Populate post-return from canonical data (remap to merged index).
        // callee_post_return is pre-decomposed to (module_idx, module_local_func_idx)
        // by the resolver, so we can look up directly in function_index_map.
        if let Some((pr_mod_idx, pr_local_idx)) = site.requirements.callee_post_return
            && let Some(&merged_pr_idx) =
                merged
                    .function_index_map
                    .get(&(site.to_component, pr_mod_idx, pr_local_idx))
        {
            options.callee_post_return = Some(merged_pr_idx);
        }

        // Resolve resource BORROW params → [resource-rep] merged function indices.
        //
        // Per the canonical ABI spec, `borrow<T>` params where T is defined by
        // the callee receive the representation (raw pointer), not the handle.
        // The adapter must call resource.rep(handle) → rep for these.
        //
        // `own<T>` params receive the handle directly — the callee's core
        // function calls from_handle/resource.rep internally, so the adapter
        // must NOT convert them (that would cause double conversion).
        //
        for op in &site.requirements.resource_params {
            if op.is_owned {
                continue; // own<T>: callee handles conversion internally
            }

            if op.callee_defines_resource {
                // Callee defines the resource — convert handle→rep.
                // Skip if upstream adapter already converted (avoids double resource.rep).
                if !op.caller_already_converted {
                    // If the caller has a handle table for THIS specific
                    // resource, use ht_rep to extract rep from the memory-
                    // pointer handle. Otherwise use canonical resource.rep.
                    let (iface, rn_opt) =
                        parse_resource_import(&op.import_module, &op.import_field);
                    let rep_func = rn_opt
                        .as_deref()
                        .and_then(|rn| {
                            merged
                                .handle_tables
                                .get(&(site.from_component, iface.to_string(), rn.to_string()))
                                .map(|ht| ht.rep_func)
                        })
                        .or_else(|| {
                            resource_rep_imports
                                .get(&(op.import_module.clone(), op.import_field.clone()))
                                .copied()
                        });
                    // Option A Phase 3: when the callee ALSO has its own ht
                    // for the same resource (post-Phase-1 per-component-ht),
                    // bridge by also calling callee.ht_new(rep) so the
                    // value lands in callee's namespace. Without this the
                    // caller's memory-pointer handle would be deref'd by
                    // callee in CALLEE's memory at that offset → garbage
                    // (the resource_with_lists symptom). Match callee's ht
                    // by resource_name only (caller iface may differ from
                    // callee iface via `use` aliasing).
                    // Only bridge when ALL of:
                    //   - caller and callee are different components
                    //   - caller has its OWN ht for the resource (the
                    //     caller's rep_func came from the ht lookup, not
                    //     the canonical [resource-rep] fallback)
                    //   - callee has its own ht too
                    // Without ALL three, the bridge double-translates or
                    // converts canonical handles to memory pointers,
                    // either of which corrupts the value.
                    let caller_has_ht = rn_opt.as_deref().is_some_and(|rn| {
                        merged
                            .handle_tables
                            .iter()
                            .any(|((c, _, r), _)| *c == site.from_component && r == rn)
                    });
                    // For `[method]/[static]/[constructor]` exported by a
                    // component that LOCALLY defines the resource, the
                    // wit-bindgen cabi expects arg0 to be the REP (memory
                    // pointer to `_ThingRep<T>`). Adding callee.new would
                    // mint a fresh slot in callee's ht; the slot's address
                    // gets passed as arg0; the deref reads 4 bytes at the
                    // slot (the just-stored rep) but Option's discriminant
                    // is the LOW BYTE of that rep — 0 for typical aligned
                    // box pointers → Option::unwrap on None.
                    //
                    // For top-level functions or when the callee just uses
                    // the resource (not locally defines it), the cabi
                    // treats arg0 as a HANDLE — keep callee.new so the
                    // value lands in callee's namespace.
                    let is_method_like = site.import_name.starts_with("[method]")
                        || site.import_name.starts_with("[static]")
                        || site.import_name.starts_with("[constructor]");
                    let callee_new_func = if site.from_component != site.to_component
                        && caller_has_ht
                        && !is_method_like
                    {
                        rn_opt.as_deref().and_then(|rn| {
                            merged
                                .handle_tables
                                .iter()
                                .find(|((c, _, r), _)| *c == site.to_component && r == rn)
                                .map(|(_, ht)| ht.new_func)
                        })
                    } else {
                        None
                    };
                    if let Some(rep_func) = rep_func {
                        if let Some(new_func) = callee_new_func {
                            log::info!(
                                "borrow bridge: rn={:?} from={} to={} caller_rep={} callee_new={}",
                                rn_opt,
                                site.from_component,
                                site.to_component,
                                rep_func,
                                new_func,
                            );
                        }
                        options
                            .resource_rep_calls
                            .push(super::ResourceBorrowTransfer {
                                param_idx: op.flat_idx,
                                rep_func,
                                new_func: callee_new_func,
                            });
                    }
                }
            } else {
                // 3-component case: callee doesn't define the resource.
                // Use caller's [resource-rep] + callee's [resource-new].
                let resource_name = op
                    .import_field
                    .strip_prefix("[resource-rep]")
                    .unwrap_or(&op.import_field);

                // Primary: per-component map from MergedModule
                let caller_rep_func = merged
                    .resource_rep_by_component
                    .get(&(site.from_component, resource_name.to_string()))
                    .copied()
                    .or_else(|| {
                        // Fallback: find any [resource-rep] for this resource name
                        // that isn't the callee's (different component index).
                        merged
                            .resource_rep_by_component
                            .iter()
                            .find(|((comp, rn), _)| {
                                rn == resource_name && *comp != site.to_component
                            })
                            .map(|(_, &idx)| idx)
                    })
                    .or_else(|| {
                        // Last resort: flat map with different module heuristic
                        resource_rep_imports
                            .iter()
                            .find(|((module, field), _)| {
                                field.ends_with(resource_name)
                                    && field.starts_with("[resource-rep]")
                                    && *module != op.import_module
                            })
                            .map(|(_, &idx)| idx)
                    });

                // For re-exporter callees with handle tables, use ht_new
                // which returns memory-pointer handles that wit-bindgen expects.
                // Look up by (to_component, iface, resource_name) so multi-resource
                // re-exporters route per-resource, not per-component.
                let (callee_iface, _) = parse_resource_import(&op.import_module, &op.import_field);
                let callee_new_func = merged
                    .handle_tables
                    .get(&(
                        site.to_component,
                        callee_iface.to_string(),
                        resource_name.to_string(),
                    ))
                    .map(|ht| ht.new_func)
                    .or_else(|| {
                        merged
                            .resource_new_by_component
                            .get(&(site.to_component, resource_name.to_string()))
                            .copied()
                    })
                    .or_else(|| {
                        let new_field = op.import_field.replace("[resource-rep]", "[resource-new]");
                        resource_new_imports
                            .get(&(op.import_module.clone(), new_field))
                            .copied()
                    });

                // Distinguish two sub-cases of the 3-component branch:
                //
                // (a) Callee's exported function is a `[method]/[static]/
                //     [constructor]` on a resource the callee LOCALLY
                //     DEFINES via its own ht. wit-bindgen's `_export_*_cabi`
                //     wraps the rep in `_ThingRep<T>` and the cabi expects
                //     arg0 to be the REP (memory pointer). Emit
                //     `caller.rep` ONLY — callee.new would mint a new
                //     slot whose address gets passed as the rep, and the
                //     deref reads adjacent fresh memory → Option=None.
                //     This is the resource_with_lists `[method]thing.foo`
                //     case where the re-exporter classification masks the
                //     fact that the cabi still uses _ThingRep wrapping.
                //
                // (b) Top-level functions (no `[method]/[static]/
                //     [constructor]` prefix) taking borrow<T> on a
                //     `use`d resource. wit-bindgen's cabi calls
                //     `Float::from_handle(arg0 as u32)` and treats arg0 as
                //     a HANDLE. Emit `caller.rep + callee.new` so the
                //     value lands in callee's namespace as a fresh slot
                //     index the callee can pass back across downstream
                //     adapters. This is the resource_floats `add` case.
                //
                // Discriminator: function name prefix. Methods/statics/
                // constructors → case (a); top-level → case (b). Combined
                // with a sanity check that the callee has SOME ht for the
                // resource_name (so the rep-only path has somewhere
                // sensible to derive the rep from).
                let is_method_like = site.import_name.starts_with("[method]")
                    || site.import_name.starts_with("[static]")
                    || site.import_name.starts_with("[constructor]");
                let callee_has_any_ht = merged
                    .handle_tables
                    .iter()
                    .any(|((c, _, r), _)| *c == site.to_component && r == resource_name);
                let new_func_for_emit = if is_method_like && callee_has_any_ht {
                    None
                } else {
                    callee_new_func
                };
                if let Some(rep_func) = caller_rep_func {
                    options
                        .resource_rep_calls
                        .push(super::ResourceBorrowTransfer {
                            param_idx: op.flat_idx,
                            rep_func,
                            new_func: new_func_for_emit,
                        });
                } else {
                    log::warn!(
                        "3-component borrow: no caller [resource-rep] for '{}' \
                         (from_comp={}, to_comp={})",
                        resource_name,
                        site.from_component,
                        site.to_component,
                    );
                }
            }
        }

        // Resolve own<T> results that need [resource-rep] + [resource-new].
        //
        // Three cases:
        // 1. callee_defines_resource=false (3-component): caller and callee
        //    have separate tables, bridge via callee.rep + caller.new.
        // 2. callee_defines_resource=true AND both caller+callee have their
        //    own ht (post-Option-A-Phase-1): bridge via callee.ht_rep +
        //    caller.ht_new so the handle ends up in caller's namespace
        //    (memory-pointer in caller's memory). Without this bridge,
        //    caller stores callee's memory-pointer handle but later passes
        //    it back to callee for method calls — works for callee but
        //    breaks for any caller-side _resource_rep call (cross-memory
        //    deref of leaf-allocated rep in intermediate's memory →
        //    Option::unwrap on garbage).
        // 3. callee_defines_resource=true AND no caller ht: pass through
        //    (the wrapper's canon lift handles conversion).
        for op in &site.requirements.resource_results {
            if !op.is_owned {
                continue;
            }
            if op.callee_defines_resource {
                // Case 2 vs 3: only emit a bridge when BOTH sides have ht
                // for the same (iface, rn). Match by resource_name across
                // both sides (caller's iface may differ from callee's via
                // `use` aliasing).
                let resource_name = op
                    .import_field
                    .strip_prefix("[resource-new]")
                    .or_else(|| op.import_field.strip_prefix("[resource-rep]"))
                    .unwrap_or(&op.import_field);
                let callee_ht = merged
                    .handle_tables
                    .iter()
                    .find(|((c, _, r), _)| *c == site.to_component && r == resource_name)
                    .map(|(_, ht)| (ht.rep_func, ht.new_func));
                let caller_ht = merged
                    .handle_tables
                    .iter()
                    .find(|((c, _, r), _)| *c == site.from_component && r == resource_name)
                    .map(|(_, ht)| (ht.rep_func, ht.new_func));
                if let (Some((rep_func, _)), Some((_, new_func))) = (callee_ht, caller_ht) {
                    log::info!(
                        "own<T> bridge: resource '{}' from comp {} (callee) → comp {} (caller); rep={} new={}",
                        resource_name,
                        site.to_component,
                        site.from_component,
                        rep_func,
                        new_func,
                    );
                    options
                        .resource_new_calls
                        .push(super::ResourceOwnResultTransfer {
                            position: op.flat_idx,
                            byte_offset: op.byte_offset,
                            rep_func,
                            new_func,
                        });
                }
                continue;
            }
            let resource_name = op
                .import_field
                .strip_prefix("[resource-new]")
                .unwrap_or(&op.import_field);

            // Caller's [resource-new] (rep → caller handle)
            let new_func = merged
                .resource_new_by_component
                .get(&(site.from_component, resource_name.to_string()))
                .copied()
                .or_else(|| {
                    resource_new_imports
                        .get(&(op.import_module.clone(), op.import_field.clone()))
                        .copied()
                });

            // Callee's [resource-rep] (callee handle → rep).
            // For re-exporter callees with handle tables, use ht_rep —
            // per-resource lookup so multi-resource re-exporters work.
            let (callee_iface_r, _) = parse_resource_import(&op.import_module, &op.import_field);
            let rep_field = format!("[resource-rep]{}", resource_name);
            let rep_func = merged
                .handle_tables
                .get(&(
                    site.to_component,
                    callee_iface_r.to_string(),
                    resource_name.to_string(),
                ))
                .map(|ht| ht.rep_func)
                .or_else(|| {
                    merged
                        .resource_rep_by_component
                        .get(&(site.to_component, resource_name.to_string()))
                        .copied()
                })
                .or_else(|| {
                    resource_rep_imports
                        .get(&(op.import_module.clone(), rep_field.clone()))
                        .copied()
                });

            if let (Some(rep_func), Some(new_func)) = (rep_func, new_func) {
                options
                    .resource_new_calls
                    .push(super::ResourceOwnResultTransfer {
                        position: op.flat_idx,
                        byte_offset: op.byte_offset,
                        rep_func,
                        new_func,
                    });
            } else if let Some(new_func) = new_func {
                log::warn!(
                    "own<T> result transfer: no callee [resource-rep] for '{}' \
                     (from={}, to={}), falling back to new-only",
                    resource_name,
                    site.from_component,
                    site.to_component,
                );
                // Fallback: use new_func as both rep and new (may be wrong but
                // avoids a hard failure for fixtures that don't need rep)
                options
                    .resource_new_calls
                    .push(super::ResourceOwnResultTransfer {
                        position: op.flat_idx,
                        byte_offset: op.byte_offset,
                        rep_func: new_func,
                        new_func,
                    });
            }
        }

        // Resolve inner resource handles from param copy layouts.
        // When list elements contain borrow<T>, the adapter must convert
        // each handle after bulk-copying the list data to callee memory.
        // Each inner resource carries its own pre-resolved (module, field)
        // for the matching [resource-rep] import (filled in by the
        // resolver via the callee's resource_type_to_import map). Using
        // that lookup ensures the right rep_func per resource type even
        // when the callee imports multiple resources — the previous
        // `.values().next()` heuristic picked an arbitrary first match
        // and silently routed handle A through resource B's rep_func.
        for layout in &site.requirements.param_copy_layouts {
            if let crate::resolver::CopyLayout::Elements {
                inner_resources, ..
            } = layout
            {
                for inner in inner_resources {
                    if inner.is_owned {
                        continue; // own<T> in lists — callee handles internally
                    }
                    let rep_func = inner
                        .rep_import
                        .as_ref()
                        .and_then(|key| resource_rep_imports.get(key).copied());
                    if let Some(rep_func) = rep_func {
                        options
                            .inner_resource_fixups
                            .push(super::InnerResourceFixup {
                                byte_offset: inner.byte_offset,
                                rep_func,
                                guards: inner.guards.clone(),
                            });
                    } else {
                        log::warn!(
                            "inner-list borrow at offset {} (resource_type_id={}): \
                             no [resource-rep] import resolved — skipping fixup. \
                             from={} to={} import_name={:?}",
                            inner.byte_offset,
                            inner.resource_type_id,
                            site.from_component,
                            site.to_component,
                            site.import_name,
                        );
                    }
                }
            }
        }

        // Resolve resource handles inside the params-ptr buffer.
        // For borrow<T> where callee defines T, the adapter must convert
        // handle → rep at the byte offset within the buffer.
        for op in &site.requirements.params_area_resource_positions {
            if op.is_owned {
                continue; // own<T>: callee calls resource.rep internally
            }

            if op.callee_defines_resource {
                // 2-component: use callee's [resource-rep]
                if let Some(&rep_func) =
                    resource_rep_imports.get(&(op.import_module.clone(), op.import_field.clone()))
                {
                    options
                        .params_area_borrow_fixups
                        .push(super::ParamsAreaResourceFixup {
                            byte_offset: op.byte_offset,
                            rep_func,
                            is_owned: false,
                        });
                }
            }
            // 3-component chains for params-area borrows could be added here
        }

        options
    }

    /// Generate a simple direct call adapter (no memory crossing)
    fn generate_direct_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
        options: &AdapterOptions,
    ) -> Result<(u32, Function)> {
        let target_func = self.resolve_target_function(site, merged)?;

        // Find the target function's type (convert wasm index to array position)
        let type_idx = merged
            .defined_func(target_func)
            .map(|f| f.type_idx)
            .unwrap_or(0);

        let func_type = merged.types.get(type_idx as usize);
        let param_count = func_type.map(|t| t.params.len()).unwrap_or(0);
        let result_count = func_type.map(|t| t.results.len()).unwrap_or(0);
        let result_types: Vec<wasm_encoder::ValType> =
            func_type.map(|t| t.results.clone()).unwrap_or_default();

        let has_post_return = options.callee_post_return.is_some();
        let has_resource_ops = !options.resource_rep_calls.is_empty();
        let has_result_resource_ops = !options.resource_new_calls.is_empty();
        let needs_result_locals = (has_post_return || has_result_resource_ops) && result_count > 0;
        let scratch_count = options.resource_new_calls.len();

        if has_resource_ops || has_result_resource_ops || (has_post_return && result_count > 0) {
            let mut locals: Vec<(u32, wasm_encoder::ValType)> = Vec::new();
            let result_base = param_count as u32;
            if needs_result_locals {
                locals.extend(result_types.iter().map(|t| (1u32, *t)));
            }
            // Scratch locals for intermediate rep values (one i32 per own<T> result)
            let scratch_base = result_base + result_count as u32;
            if scratch_count > 0 {
                locals.extend(std::iter::repeat_n(
                    (1u32, wasm_encoder::ValType::I32),
                    scratch_count,
                ));
            }
            let mut func = Function::new(locals);

            // Phase 0: Convert borrow resource handles
            emit_resource_borrow_phase0(&mut func, &options.resource_rep_calls);

            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));

            if needs_result_locals {
                // Save results to locals (pop in reverse order)
                for i in (0..result_count).rev() {
                    func.instruction(&Instruction::LocalSet(result_base + i as u32));
                }

                // Phase R-rep: extract representations while handles are still alive
                emit_resource_rep_results(
                    &mut func,
                    &options.resource_new_calls,
                    result_base,
                    scratch_base,
                );

                // Call post-return with original handles (drops callee's handles)
                if has_post_return {
                    for i in 0..result_count {
                        func.instruction(&Instruction::LocalGet(result_base + i as u32));
                    }
                    func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
                }

                // Phase R-new: mint fresh handles from reps
                emit_resource_new_results(
                    &mut func,
                    &options.resource_new_calls,
                    result_base,
                    scratch_base,
                );

                // Push saved results back onto stack
                for i in 0..result_count {
                    func.instruction(&Instruction::LocalGet(result_base + i as u32));
                }
            } else if has_post_return {
                func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
            }

            func.instruction(&Instruction::End);
            Ok((type_idx, func))
        } else {
            // Simple trampoline (no post-return or no results)
            let mut func = Function::new([]);

            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));

            if has_post_return {
                func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
            }

            func.instruction(&Instruction::End);
            Ok((type_idx, func))
        }
    }

    /// Generate an adapter that copies data between memories
    ///
    /// When caller and callee use different memories, pointer arguments must
    /// be remapped: allocate in callee's memory via `cabi_realloc`, copy the
    /// data with `memory.copy $callee $caller`, then call the target with the
    /// new pointer.  Handles the common `(ptr, len)` pair pattern.
    ///
    /// When the caller uses the retptr calling convention (extra i32 param,
    /// void return) and the callee returns a return-area pointer (i32), the
    /// adapter reads flat results from the callee's return area, copies
    /// pointed-to data across memories, and writes fixed-up results at the
    /// caller's retptr.
    ///
    /// When the target function returns a `(ptr, len)` pair (detected via
    /// `AdapterOptions::returns_pointer_pair`), the adapter also copies the
    /// returned data from callee's memory back to caller's memory using
    /// `caller_realloc` and `memory.copy` in the reverse direction.
    fn generate_memory_copy_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
        options: &AdapterOptions,
        resource_rep_imports: &std::collections::HashMap<(String, String), u32>,
    ) -> Result<(u32, Function)> {
        let target_func = self.resolve_target_function(site, merged)?;

        // --- Determine callee's type (what we call) ---
        let callee_type_idx = merged
            .defined_func(target_func)
            .map(|f| f.type_idx)
            .unwrap_or(0);
        let callee_type = merged.types.get(callee_type_idx as usize);
        let callee_param_count = callee_type.map(|t| t.params.len()).unwrap_or(0);
        let callee_result_count = callee_type.map(|t| t.results.len()).unwrap_or(0);
        let callee_result_types: Vec<wasm_encoder::ValType> =
            callee_type.map(|t| t.results.clone()).unwrap_or_default();

        // --- Determine caller's type (what the adapter declares) ---
        // Use the caller's import type if available; otherwise fall back to callee's type.
        let caller_type_idx = site
            .import_func_type_idx
            .and_then(|local_ti| {
                merged
                    .type_index_map
                    .get(&(site.from_component, site.from_module, local_ti))
                    .copied()
            })
            .unwrap_or(callee_type_idx);
        let caller_type = merged.types.get(caller_type_idx as usize);
        let caller_param_count = caller_type
            .map(|t| t.params.len())
            .unwrap_or(callee_param_count);
        let caller_result_count = caller_type
            .map(|t| t.results.len())
            .unwrap_or(callee_result_count);

        // --- Detect retptr calling convention ---
        // The canonical ABI uses retptr when flat results > MAX_FLAT_RESULTS:
        //   caller (lowered): params..., retptr:i32 → void
        //   callee (lifted):  params...            → i32 (return area ptr)
        let uses_retptr = caller_param_count > callee_param_count
            && caller_result_count == 0
            && callee_result_count == 1
            && callee_result_types.first() == Some(&wasm_encoder::ValType::I32);

        if uses_retptr {
            return self.generate_retptr_adapter(
                site,
                merged,
                options,
                target_func,
                caller_type_idx,
                caller_param_count,
                callee_param_count,
            );
        }

        // --- Detect params-ptr calling convention ---
        // The canonical ABI uses params-ptr when flat params > MAX_FLAT_PARAMS (16):
        //   caller (lowered): (params_ptr: i32) → result...
        //   callee (lifted):  (params_ptr: i32) → result...
        // Both sides use a single i32 pointer to a buffer in linear memory.
        // When memories differ, the adapter must copy the buffer across.
        let uses_params_ptr = site.requirements.params_area_byte_size.is_some();

        if uses_params_ptr && options.caller_memory != options.callee_memory {
            log::debug!(
                "params-ptr adapter: generating for import={} (buffer={}B, {} ptr pairs, {} borrow fixups)",
                site.import_name,
                site.requirements.params_area_byte_size.unwrap_or(0),
                site.requirements.params_area_pointer_pair_offsets.len(),
                site.requirements
                    .params_area_resource_positions
                    .iter()
                    .filter(|p| !p.is_owned && p.callee_defines_resource)
                    .count(),
            );
            return self.generate_params_ptr_adapter(
                site,
                options,
                target_func,
                caller_type_idx,
                resource_rep_imports,
            );
        }

        // --- Non-retptr path: use callee's type so body is valid ---
        // wire_adapter_indices generates a widening wrapper if caller expects
        // wider result types (P3 async i64 vs i32).
        let adapter_type_idx = callee_type_idx;
        let param_count = callee_param_count;
        let result_count = callee_result_count;
        let result_types = callee_result_types;

        // If memories are the same, just do direct call (with post-return if needed)
        if options.caller_memory == options.callee_memory {
            let has_post_return = options.callee_post_return.is_some();
            let has_resource_ops = !options.resource_rep_calls.is_empty();

            if has_resource_ops || (has_post_return && result_count > 0) {
                let mut locals: Vec<(u32, wasm_encoder::ValType)> = Vec::new();
                let result_base = param_count as u32;
                if has_post_return && result_count > 0 {
                    locals.extend(result_types.iter().map(|t| (1u32, *t)));
                }
                let mut func = Function::new(locals);

                // Phase 0: Convert borrow resource handles
                emit_resource_borrow_phase0(&mut func, &options.resource_rep_calls);

                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));

                if has_post_return && result_count > 0 {
                    for i in (0..result_count).rev() {
                        func.instruction(&Instruction::LocalSet(result_base + i as u32));
                    }
                    for i in 0..result_count {
                        func.instruction(&Instruction::LocalGet(result_base + i as u32));
                    }
                    func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
                    for i in 0..result_count {
                        func.instruction(&Instruction::LocalGet(result_base + i as u32));
                    }
                } else if has_post_return {
                    func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
                }

                func.instruction(&Instruction::End);
                return Ok((adapter_type_idx, func));
            } else {
                let mut func = Function::new([]);
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));

                if has_post_return {
                    func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
                }

                func.instruction(&Instruction::End);
                return Ok((adapter_type_idx, func));
            }
        }

        // Only treat first two params as (ptr, len) when callee has realloc AND
        // there are pointer pairs to copy — without realloc we cannot allocate
        // in the callee's memory.
        let has_param_pointer_pairs = !site.requirements.pointer_pair_positions.is_empty();
        let has_conditional_pairs = !site.requirements.conditional_pointer_pairs.is_empty();
        let needs_outbound_copy =
            has_param_pointer_pairs && param_count >= 2 && options.callee_realloc.is_some();
        let needs_conditional_copy = has_conditional_pairs && options.callee_realloc.is_some();
        let needs_result_copy = options.returns_pointer_pair;
        let has_conditional_result_pairs =
            !site.requirements.conditional_result_flat_pairs.is_empty();
        let needs_conditional_result_copy =
            !needs_result_copy && has_conditional_result_pairs && options.caller_realloc.is_some();

        // Post-return with scalar results needs scratch locals to save/restore
        let needs_post_return_save =
            !needs_result_copy && options.callee_post_return.is_some() && result_count > 0;

        let has_result_resource_ops = !options.resource_new_calls.is_empty();

        // We need result-save locals for post-return, conditional result copy,
        // or resource result conversion.
        let needs_result_save =
            (needs_post_return_save || needs_conditional_result_copy || has_result_resource_ops)
                && result_count > 0;

        let has_resource_ops = !options.resource_rep_calls.is_empty();

        let has_inner_resource_fixups = !options.inner_resource_fixups.is_empty();

        // If no copying, no post-return save, and no resource ops needed, direct call
        if !needs_outbound_copy
            && !needs_conditional_copy
            && !needs_result_copy
            && !needs_conditional_result_copy
            && !needs_post_return_save
            && !has_resource_ops
            && !has_inner_resource_fixups
            && !has_result_resource_ops
        {
            let mut func = Function::new([]);
            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
            func.instruction(&Instruction::End);
            return Ok((adapter_type_idx, func));
        }

        // Compute fixup depth for non-retptr path (each level needs 4 scratch locals)
        let nonretptr_fixup_depth = if needs_outbound_copy {
            Self::max_fixup_depth(&site.requirements.param_copy_layouts)
        } else {
            0
        };
        let inner_fixup_locals: u32 = 4 * nonretptr_fixup_depth;
        let inner_resource_locals: u32 = if has_inner_resource_fixups { 1 } else { 0 }; // loop counter
        let num_param_pairs = site.requirements.pointer_pair_positions.len() as u32;
        let copy_scratch_count: u32 = if needs_outbound_copy && needs_result_copy {
            num_param_pairs.max(1) + 3 + inner_fixup_locals + inner_resource_locals
        } else if needs_result_copy {
            3 // callee_ret_ptr + callee_ret_len + caller_new_ptr
        } else if needs_outbound_copy {
            let num_pairs = site.requirements.pointer_pair_positions.len() as u32;
            num_pairs.max(1) + inner_fixup_locals + inner_resource_locals
        } else if needs_conditional_copy || needs_conditional_result_copy {
            1 // dest_ptr for conditional copy (param or result side)
        } else if has_inner_resource_fixups {
            1 + inner_resource_locals // dest_ptr + resource loop counter
        } else {
            0 // post-return-only path (no copy needed)
        };

        // Build local declarations: copy scratch (i32) + result save (typed)
        let mut local_decls: Vec<(u32, wasm_encoder::ValType)> = Vec::new();
        if copy_scratch_count > 0 {
            local_decls.push((copy_scratch_count, wasm_encoder::ValType::I32));
        }
        let result_save_base = param_count as u32 + copy_scratch_count;
        if needs_result_save {
            for ty in &result_types {
                local_decls.push((1, *ty));
            }
        }
        // Scratch locals for Phase R-rep intermediate rep values (one i32 per own<T> result)
        let own_result_scratch_count = options.resource_new_calls.len();
        let own_result_scratch_base = result_save_base + result_count as u32;
        if own_result_scratch_count > 0 {
            local_decls.push((own_result_scratch_count as u32, wasm_encoder::ValType::I32));
        }

        let mut func = Function::new(local_decls);

        // Phase 0: Convert borrow resource handles
        emit_resource_borrow_phase0(&mut func, &options.resource_rep_calls);

        // Assign scratch local indices (after params)
        let base = param_count as u32;
        // For outbound copy:
        let dest_ptr_local = base; // only used when needs_outbound_copy
        // For result copy:
        let result_locals_base = if needs_outbound_copy { base + 1 } else { base };
        let callee_ret_ptr_local = result_locals_base;
        let callee_ret_len_local = result_locals_base + 1;
        let caller_new_ptr_local = result_locals_base + 2;

        // --- Phase 1: Outbound argument copy (caller → callee) ---
        if needs_outbound_copy {
            // Requires callee's cabi_realloc to allocate destination buffer.
            let callee_realloc = match options.callee_realloc {
                Some(idx) => idx,
                None => {
                    log::warn!("Cross-memory copy: no callee realloc, falling back to direct call");
                    let mut func = Function::new([]);
                    for i in 0..param_count {
                        func.instruction(&Instruction::LocalGet(i as u32));
                    }
                    func.instruction(&Instruction::Call(target_func));
                    func.instruction(&Instruction::End);
                    return Ok((adapter_type_idx, func));
                }
            };

            // Copy ALL pointer pairs from caller to callee memory.
            let param_ptr_positions = &site.requirements.pointer_pair_positions;
            let param_layouts = &site.requirements.param_copy_layouts;
            for (pair_idx, &ptr_pos) in param_ptr_positions.iter().enumerate() {
                let len_pos = ptr_pos + 1;
                let dest_local = dest_ptr_local + pair_idx as u32;
                let byte_mult = param_layouts
                    .get(pair_idx)
                    .map(|cl| match cl {
                        crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                        crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                    })
                    .unwrap_or(1);

                // A param-side buffer carries a latin1+utf16 (CompactUTF16,
                // modelled as Latin1) string when the *caller* encoding is
                // Latin1 and the data is byte-granular (byte_mult == 1). Its
                // length operand is tag-encoded (UTF16_TAG): the byte count
                // must be masked/doubled (`emit_copy_byte_count`) for the
                // realloc size and the memory.copy length, while the length
                // FORWARDED to the callee stays tagged. A plain list<u8>
                // (also byte_mult == 1) is unaffected: its count is < 2^31,
                // so the tag bit is clear and the tag-aware path returns `len`.
                let is_compact_utf16 =
                    options.caller_string_encoding == StringEncoding::Latin1 && byte_mult == 1;
                let realloc_align = if is_compact_utf16 { 2 } else { 1 };

                // Allocate: dest = cabi_realloc(0, 0, align, <byte count>)
                emit_overflow_guard(&mut func, len_pos, byte_mult);
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(realloc_align));
                emit_copy_byte_count(&mut func, len_pos, byte_mult, is_compact_utf16);
                emit_checked_realloc(&mut func, callee_realloc, dest_local);

                // Copy: memory.copy callee_mem caller_mem (dest, src, <byte count>)
                func.instruction(&Instruction::LocalGet(dest_local));
                func.instruction(&Instruction::LocalGet(ptr_pos));
                emit_copy_byte_count(&mut func, len_pos, byte_mult, is_compact_utf16);
                func.instruction(&Instruction::MemoryCopy {
                    src_mem: options.caller_memory,
                    dst_mem: options.callee_memory,
                });

                // Fix up inner pointers if element type contains owned data
                if let Some(crate::resolver::CopyLayout::Elements {
                    element_size,
                    inner_pointers,
                    ..
                }) = param_layouts.get(pair_idx)
                    && !inner_pointers.is_empty()
                {
                    let fixup_base = dest_ptr_local + num_param_pairs.max(1);
                    Self::emit_inner_pointer_fixup(
                        &mut func,
                        inner_pointers,
                        *element_size,
                        ptr_pos,    // src_base (caller's original ptr)
                        dest_local, // dst_base (callee's copy)
                        len_pos,    // count
                        options.caller_memory,
                        options.callee_memory,
                        callee_realloc,
                        fixup_base,
                        // Param-side: governed by the caller's string encoding.
                        options.caller_string_encoding == StringEncoding::Latin1,
                    );
                }
            } // end for each pointer pair

            // 2c. Fix up inner resource handles if element type contains borrow<T>
            if !options.inner_resource_fixups.is_empty()
                && let Some(crate::resolver::CopyLayout::Elements { element_size, .. }) =
                    site.requirements.param_copy_layouts.first()
            {
                let element_size = *element_size;
                let loop_idx = dest_ptr_local + num_param_pairs.max(1) + inner_fixup_locals;
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::LocalSet(loop_idx));
                // block $exit { loop $cont {
                func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
                func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
                // if loop_idx >= len: break
                func.instruction(&Instruction::LocalGet(loop_idx));
                func.instruction(&Instruction::LocalGet(1)); // len
                func.instruction(&Instruction::I32GeU);
                func.instruction(&Instruction::BrIf(1));
                for fixup in &options.inner_resource_fixups {
                    let byte_offset = fixup.byte_offset;
                    let rep_func = fixup.rep_func;
                    // UCA-A-16: AND-evaluate this fixup's per-element
                    // discriminant guards before the borrow→rep conversion.
                    // Empty guards → unconditional (Record/Tuple path). Mirrors
                    // `emit_inner_pointer_fixup`: load each guard's disc byte
                    // from the per-element base at the right width, compare,
                    // AND-chain, and wrap the conversion in an `If`.
                    let guarded = Self::emit_inner_resource_guard_chain(
                        &mut func,
                        &fixup.guards,
                        dest_ptr_local,
                        loop_idx,
                        element_size,
                        options.callee_memory,
                    );
                    // addr = dest_ptr + loop_idx * element_size + byte_offset
                    // i32.store needs [addr, value] on stack.
                    // Emit: addr, addr, i32.load → handle, call rep → rep, i32.store
                    // First push addr for the store:
                    func.instruction(&Instruction::LocalGet(dest_ptr_local));
                    func.instruction(&Instruction::LocalGet(loop_idx));
                    func.instruction(&Instruction::I32Const(element_size as i32));
                    func.instruction(&Instruction::I32Mul);
                    func.instruction(&Instruction::I32Add);
                    // Stack: [addr_for_store]
                    // Now load handle from same addr using offset
                    func.instruction(&Instruction::LocalGet(dest_ptr_local));
                    func.instruction(&Instruction::LocalGet(loop_idx));
                    func.instruction(&Instruction::I32Const(element_size as i32));
                    func.instruction(&Instruction::I32Mul);
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                        offset: byte_offset as u64,
                        align: 2,
                        memory_index: options.callee_memory,
                    }));
                    // Stack: [addr_for_store, handle]
                    func.instruction(&Instruction::Call(rep_func));
                    // Stack: [addr_for_store, rep]
                    func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                        offset: byte_offset as u64,
                        align: 2,
                        memory_index: options.callee_memory,
                    }));
                    if guarded {
                        func.instruction(&Instruction::End); // end UCA-A-16 guard If
                    }
                }
                // loop_idx++
                func.instruction(&Instruction::LocalGet(loop_idx));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalSet(loop_idx));
                func.instruction(&Instruction::Br(0));
                func.instruction(&Instruction::End); // loop
                func.instruction(&Instruction::End); // block
            }

            // 3. Call target with remapped pointer pairs
            for i in 0..param_count as u32 {
                if let Some(pair_idx) = param_ptr_positions.iter().position(|&pos| pos == i) {
                    // Replace pointer with allocated copy in callee memory
                    func.instruction(&Instruction::LocalGet(dest_ptr_local + pair_idx as u32));
                } else {
                    func.instruction(&Instruction::LocalGet(i));
                }
            }
            func.instruction(&Instruction::Call(target_func));
        } else if needs_conditional_copy {
            // Conditional copy for option/result/variant params.
            // For each conditional pointer pair, check the discriminant and
            // copy the pointed-to data if the variant is active.
            let callee_realloc = options.callee_realloc.unwrap();

            // We need scratch locals: one dest_ptr per conditional pair
            // These were NOT allocated in the main scratch pool above,
            // so we extend the function with extra locals.
            // NOTE: We handle this by modifying the params in-place using
            // local.set on the original param slots.
            for cond in &site.requirements.conditional_pointer_pairs {
                let ptr_local = cond.ptr_position;
                let len_local = cond.ptr_position + 1;
                let byte_mult = match &cond.copy_layout {
                    crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                    crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                };
                // Param-side (caller → callee) tagged latin1+utf16 string: see
                // the unconditional param-copy loop above.
                let is_compact_utf16 =
                    options.caller_string_encoding == StringEncoding::Latin1 && byte_mult == 1;
                let realloc_align = if is_compact_utf16 { 2 } else { 1 };

                // if (all guards in chain hold) { copy and replace ptr }
                // — outer-guard ANDing matters for nested option/result/variant
                // payloads where reading only the inner disc byte could be
                // sampling unrelated payload bytes in another arm (LS-P-10).
                emit_conditional_guard_chain_flat(&mut func, cond, 0);
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));

                // Allocate: new_ptr = cabi_realloc(0, 0, align, <byte count>)
                emit_overflow_guard(&mut func, len_local, byte_mult);
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(realloc_align));
                emit_copy_byte_count(&mut func, len_local, byte_mult, is_compact_utf16);
                // Save as dest_ptr (reuse a scratch local)
                emit_checked_realloc(&mut func, callee_realloc, dest_ptr_local);

                // Copy: memory.copy callee caller (dest, src, <byte count>)
                func.instruction(&Instruction::LocalGet(dest_ptr_local));
                func.instruction(&Instruction::LocalGet(ptr_local));
                emit_copy_byte_count(&mut func, len_local, byte_mult, is_compact_utf16);
                func.instruction(&Instruction::MemoryCopy {
                    src_mem: options.caller_memory,
                    dst_mem: options.callee_memory,
                });

                // Replace the original ptr with the new ptr in callee memory
                func.instruction(&Instruction::LocalGet(dest_ptr_local));
                func.instruction(&Instruction::LocalSet(ptr_local));

                func.instruction(&Instruction::End); // end if
            }

            // Pass all args through (with modified ptr values)
            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
        } else {
            // No outbound copy — pass args through directly
            for i in 0..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
        }

        // --- Phase 2: Result copy (callee → caller) ---
        if needs_result_copy {
            let caller_realloc = match options.caller_realloc {
                Some(idx) => idx,
                None => {
                    log::warn!("Result copy: no caller realloc, returning callee pointers as-is");
                    func.instruction(&Instruction::End);
                    return Ok((adapter_type_idx, func));
                }
            };

            // After the call, stack has: [callee_ret_ptr, callee_ret_len]
            // Save them to locals (pop in reverse order: len first, then ptr)
            func.instruction(&Instruction::LocalSet(callee_ret_len_local));
            func.instruction(&Instruction::LocalSet(callee_ret_ptr_local));

            // The returned (ptr, len) pair was produced BY THE CALLEE in the
            // callee's string encoding, so its tag-encoding is governed by
            // `callee_string_encoding`. byte_mult is 1 here (bulk string /
            // list<u8> return). A latin1+utf16 return has its length tagged
            // with UTF16_TAG; copying the raw operand would copy
            // `count | 0x8000_0000` bytes (~2 GiB OOB). The length pushed back
            // to the caller stays tagged; only the byte count is masked.
            let result_is_compact_utf16 = options.callee_string_encoding == StringEncoding::Latin1;
            let result_realloc_align = if result_is_compact_utf16 { 2 } else { 1 };

            // Allocate in caller's memory:
            //   caller_new_ptr = cabi_realloc(0, 0, align, <byte count>)
            func.instruction(&Instruction::I32Const(0)); // original_ptr
            func.instruction(&Instruction::I32Const(0)); // original_size
            func.instruction(&Instruction::I32Const(result_realloc_align)); // alignment
            emit_copy_byte_count(&mut func, callee_ret_len_local, 1, result_is_compact_utf16);
            emit_checked_realloc(&mut func, caller_realloc, caller_new_ptr_local);

            // Copy data from callee's memory to caller's memory:
            //   memory.copy $caller_mem $callee_mem (caller_new_ptr, callee_ret_ptr, <byte count>)
            func.instruction(&Instruction::LocalGet(caller_new_ptr_local)); // dst
            func.instruction(&Instruction::LocalGet(callee_ret_ptr_local)); // src
            emit_copy_byte_count(&mut func, callee_ret_len_local, 1, result_is_compact_utf16);
            func.instruction(&Instruction::MemoryCopy {
                src_mem: options.callee_memory,
                dst_mem: options.caller_memory,
            });

            // Call post-return if specified (callee cleanup with original return values)
            if let Some(post_return_func) = options.callee_post_return {
                func.instruction(&Instruction::LocalGet(callee_ret_ptr_local));
                func.instruction(&Instruction::LocalGet(callee_ret_len_local));
                func.instruction(&Instruction::Call(post_return_func));
            }

            // Push results: (caller_new_ptr, callee_ret_len)
            func.instruction(&Instruction::LocalGet(caller_new_ptr_local));
            func.instruction(&Instruction::LocalGet(callee_ret_len_local));
        }

        // Post-return and/or conditional result copy
        if !needs_result_copy
            && (needs_conditional_result_copy
                || options.callee_post_return.is_some()
                || has_result_resource_ops)
        {
            if result_count > 0 && needs_result_save {
                // Save return values to scratch locals (pop in reverse order)
                for i in (0..result_count).rev() {
                    func.instruction(&Instruction::LocalSet(result_save_base + i as u32));
                }

                // Phase R-rep: extract representations while handles are still alive
                emit_resource_rep_results(
                    &mut func,
                    &options.resource_new_calls,
                    result_save_base,
                    own_result_scratch_base,
                );
            }

            // Call post-return with callee's original handles (drops them)
            if let Some(post_return_func) = options.callee_post_return {
                if result_count > 0 && needs_result_save {
                    for i in 0..result_count {
                        func.instruction(&Instruction::LocalGet(result_save_base + i as u32));
                    }
                }
                func.instruction(&Instruction::Call(post_return_func));
            }

            // Phase R-new: mint fresh handles from reps (after post_return dropped originals)
            if result_count > 0 && needs_result_save && has_result_resource_ops {
                emit_resource_new_results(
                    &mut func,
                    &options.resource_new_calls,
                    result_save_base,
                    own_result_scratch_base,
                );
            }

            // Conditional result copy: fix up pointer pairs in callee results
            if needs_conditional_result_copy && result_count > 0 {
                let caller_realloc = options.caller_realloc.unwrap();
                for cond in &site.requirements.conditional_result_flat_pairs {
                    let ptr_local = result_save_base + cond.ptr_position;
                    let len_local = result_save_base + cond.ptr_position + 1;
                    let byte_mult = match &cond.copy_layout {
                        crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                        crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                    };
                    // Result-side (callee → caller) string: tag-encoding is
                    // governed by `callee_string_encoding` (the callee produced
                    // it). See the unconditional result-copy above.
                    let is_compact_utf16 =
                        options.callee_string_encoding == StringEncoding::Latin1 && byte_mult == 1;
                    let realloc_align = if is_compact_utf16 { 2 } else { 1 };

                    // if (all guards in chain hold) { allocate in caller,
                    // copy, replace ptr } — outer-guard ANDing per LS-P-10.
                    emit_conditional_guard_chain_flat(&mut func, cond, result_save_base);
                    func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));

                    // Allocate in caller memory
                    emit_overflow_guard(&mut func, len_local, byte_mult);
                    func.instruction(&Instruction::I32Const(0));
                    func.instruction(&Instruction::I32Const(0));
                    func.instruction(&Instruction::I32Const(realloc_align));
                    emit_copy_byte_count(&mut func, len_local, byte_mult, is_compact_utf16);
                    emit_checked_realloc(&mut func, caller_realloc, dest_ptr_local);

                    // Copy from callee memory to caller memory
                    func.instruction(&Instruction::LocalGet(dest_ptr_local));
                    func.instruction(&Instruction::LocalGet(ptr_local));
                    emit_copy_byte_count(&mut func, len_local, byte_mult, is_compact_utf16);
                    func.instruction(&Instruction::MemoryCopy {
                        src_mem: options.callee_memory,
                        dst_mem: options.caller_memory,
                    });

                    // Replace ptr with caller's copy
                    func.instruction(&Instruction::LocalGet(dest_ptr_local));
                    func.instruction(&Instruction::LocalSet(ptr_local));

                    func.instruction(&Instruction::End); // end if
                }
            }

            // Push (modified) return values back onto the stack
            if result_count > 0 && needs_result_save {
                for i in 0..result_count {
                    func.instruction(&Instruction::LocalGet(result_save_base + i as u32));
                }
            }
        }

        func.instruction(&Instruction::End);

        Ok((adapter_type_idx, func))
    }

    /// Generate an adapter for the params-ptr calling convention.
    ///
    /// When flat param count > MAX_FLAT_PARAMS (16), the canonical ABI stores all
    /// params in a buffer in linear memory. Both caller and callee use:
    ///   (params_ptr: i32) → result...
    ///
    /// The adapter bridges different memories:
    /// 1. Allocate buffer in callee's memory via cabi_realloc
    /// 2. Bulk copy the params buffer from caller to callee memory
    /// 3. Fix up any (ptr, len) pairs inside the buffer — copy pointed-to data
    ///    from caller memory to callee memory and update the pointers
    /// 4. Call callee with new pointer
    /// 5. Return the result(s)
    fn generate_params_ptr_adapter(
        &self,
        site: &AdapterSite,
        options: &AdapterOptions,
        target_func: u32,
        caller_type_idx: u32,
        resource_rep_imports: &std::collections::HashMap<(String, String), u32>,
    ) -> Result<(u32, Function)> {
        let params_area_size = site.requirements.params_area_byte_size.unwrap_or(0);
        let params_area_align = site.requirements.params_area_max_align.max(1);
        let ptr_pair_offsets = &site.requirements.params_area_pointer_pair_offsets;
        let copy_layouts = &site.requirements.params_area_copy_layouts;

        let callee_realloc = options.callee_realloc.unwrap_or_else(|| {
            log::warn!("params-ptr adapter: no callee realloc, buffer copy may fail");
            0
        });

        // Check if any list copy layouts contain inner resources (borrow handles)
        let has_inner_resources = copy_layouts.iter().any(|cl| {
            matches!(cl,
                crate::resolver::CopyLayout::Elements { inner_resources, .. }
                if !inner_resources.is_empty()
            )
        });

        // Local layout:
        //   0: params_ptr (the function parameter — pointer to caller's memory)
        //   1: callee_ptr (allocated pointer in callee's memory)
        //   2..2+N: dest_ptr for each pointer pair copy
        //   2+N: loop_counter (if inner resources need fixup)
        //   last: pair_len_local (scratch for per-pair overflow guard)
        let num_ptr_pairs = ptr_pair_offsets.len() as u32;
        let loop_counter_count = if has_inner_resources { 1u32 } else { 0 };
        let pair_len_scratch_count = if num_ptr_pairs > 0 { 1u32 } else { 0 };
        let scratch_count = 1 + num_ptr_pairs + loop_counter_count + pair_len_scratch_count; // callee_ptr + per-pair dest ptrs + loop counter + pair_len

        // Post-return needs result save locals
        let has_post_return = options.callee_post_return.is_some();
        // For params-ptr, the results come from the callee directly.

        let mut local_decls: Vec<(u32, wasm_encoder::ValType)> = Vec::new();
        if scratch_count > 0 {
            local_decls.push((scratch_count, wasm_encoder::ValType::I32));
        }

        // We don't know result count from here, so we handle post-return simply:
        // if there's a post-return, we'll save and restore results.
        // But for params-ptr functions with resource results, result count should be 1 (i32).
        // For simplicity: if has_post_return, add 1 i32 result save local.
        let result_save_base = 1 + scratch_count; // after params_ptr(0) + scratch
        if has_post_return {
            local_decls.push((1, wasm_encoder::ValType::I32));
        }

        let mut func = Function::new(local_decls);

        let params_ptr_local: u32 = 0;
        let callee_ptr_local: u32 = 1;
        let pair_dest_base: u32 = 2;
        // Scratch local holding the length of the current (ptr, len) pair,
        // used by emit_overflow_guard. Only present when there is at least
        // one pointer pair.
        let pair_len_local: u32 = pair_dest_base + num_ptr_pairs + loop_counter_count;

        // --- Phase 1: Allocate buffer in callee's memory ---
        // callee_ptr = cabi_realloc(0, 0, align, size)
        func.instruction(&Instruction::I32Const(0)); // original_ptr
        func.instruction(&Instruction::I32Const(0)); // original_size
        func.instruction(&Instruction::I32Const(params_area_align as i32)); // alignment
        func.instruction(&Instruction::I32Const(params_area_size as i32)); // new_size
        emit_checked_realloc(&mut func, callee_realloc, callee_ptr_local);

        // --- Phase 2: Bulk copy the entire params buffer ---
        // memory.copy $callee_mem $caller_mem (callee_ptr, params_ptr, size)
        func.instruction(&Instruction::LocalGet(callee_ptr_local)); // dst
        func.instruction(&Instruction::LocalGet(params_ptr_local)); // src
        func.instruction(&Instruction::I32Const(params_area_size as i32)); // size
        func.instruction(&Instruction::MemoryCopy {
            src_mem: options.caller_memory,
            dst_mem: options.callee_memory,
        });

        // --- Phase 3: Fix up pointer pairs inside the buffer ---
        // For each (ptr, len) pair in the params buffer:
        //   1. Read ptr and len from callee's copy of the buffer
        //   2. Compute byte_size from len and the copy layout's byte_multiplier
        //   3. Allocate in callee's memory: new_ptr = cabi_realloc(0, 0, 1, byte_size)
        //   4. Copy data from caller's memory at old_ptr to callee's memory at new_ptr
        //   5. Write new_ptr back into callee's buffer at the same offset
        for (pair_idx, &byte_offset) in ptr_pair_offsets.iter().enumerate() {
            let dest_local = pair_dest_base + pair_idx as u32;
            let byte_mult = copy_layouts
                .get(pair_idx)
                .map(|cl| match cl {
                    crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                    crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                })
                .unwrap_or(1);

            // Read old_ptr from callee's buffer: i32.load callee_mem (callee_ptr + byte_offset)
            // Read old_len from callee's buffer: i32.load callee_mem (callee_ptr + byte_offset + 4)

            // Stash len into a scratch local so the overflow guard + realloc
            // can both reference it without re-loading from memory.
            func.instruction(&Instruction::LocalGet(callee_ptr_local));
            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: (byte_offset + 4) as u64,
                align: 2,
                memory_index: options.callee_memory,
            }));
            func.instruction(&Instruction::LocalSet(pair_len_local));

            // The params buffer was lowered by the caller, so a latin1+utf16
            // string inside it has its length tagged per the *caller* encoding.
            // byte_mult == 1 selects the byte-granular (string / list<u8>)
            // case; a plain list<u8> stays unaffected (count < 2^31 ⇒ tag clear).
            let is_compact_utf16 =
                options.caller_string_encoding == StringEncoding::Latin1 && byte_mult == 1;
            let realloc_align = if is_compact_utf16 { 2 } else { 1 };

            // Allocate: new_ptr = cabi_realloc(0, 0, align, <byte count>)
            emit_overflow_guard(&mut func, pair_len_local, byte_mult);
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::I32Const(realloc_align));
            emit_copy_byte_count(&mut func, pair_len_local, byte_mult, is_compact_utf16);
            emit_checked_realloc(&mut func, callee_realloc, dest_local);

            // Copy data: memory.copy callee caller (new_ptr, old_ptr, <byte count>)
            func.instruction(&Instruction::LocalGet(dest_local)); // dst (in callee mem)
            // Load old_ptr from callee's buffer (this was copied from caller's buffer,
            // so it points into caller's memory)
            func.instruction(&Instruction::LocalGet(callee_ptr_local));
            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: byte_offset as u64,
                align: 2,
                memory_index: options.callee_memory,
            })); // src (in caller mem)
            // Byte count from the stashed (still-tagged) length operand.
            emit_copy_byte_count(&mut func, pair_len_local, byte_mult, is_compact_utf16);
            func.instruction(&Instruction::MemoryCopy {
                src_mem: options.caller_memory,
                dst_mem: options.callee_memory,
            });

            // Write new_ptr back into callee's buffer at byte_offset
            func.instruction(&Instruction::LocalGet(callee_ptr_local));
            func.instruction(&Instruction::LocalGet(dest_local));
            func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                offset: byte_offset as u64,
                align: 2,
                memory_index: options.callee_memory,
            }));

            // Fix up inner resource handles in list elements.
            // After bulk copy, borrow handles in the list data still reference
            // the caller's resource table. Convert each borrow handle → rep.
            if let Some(crate::resolver::CopyLayout::Elements {
                element_size,
                inner_resources,
                ..
            }) = copy_layouts.get(pair_idx)
                && !inner_resources.is_empty()
            {
                let element_size = *element_size;
                let loop_local = pair_dest_base + num_ptr_pairs;

                // Initialize loop counter to 0
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::LocalSet(loop_local));

                // block $exit { loop $cont {
                func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
                func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

                // if loop_counter >= len: break
                func.instruction(&Instruction::LocalGet(loop_local));
                // Load len from callee's buffer
                func.instruction(&Instruction::LocalGet(callee_ptr_local));
                func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                    offset: (byte_offset + 4) as u64,
                    align: 2,
                    memory_index: options.callee_memory,
                }));
                func.instruction(&Instruction::I32GeU);
                func.instruction(&Instruction::BrIf(1)); // break to $exit

                for inner in inner_resources {
                    if inner.is_owned {
                        continue; // own<T>: callee handles internally
                    }
                    // Use the per-element pre-resolved [resource-rep]
                    // (filled at site-requirements time via the callee's
                    // resource_type_to_import map). The previous code
                    // picked an arbitrary first-fixup which silently
                    // routed handle A through resource B's rep_func when
                    // the callee imported >1 resource.
                    let res_byte_offset = inner.byte_offset;
                    let rep_func_opt = inner
                        .rep_import
                        .as_ref()
                        .and_then(|key| resource_rep_imports.get(key).copied());
                    if let Some(rep_func) = rep_func_opt {
                        // addr = dest_ptr + loop_counter * element_size + res_byte_offset
                        // Push addr for store
                        func.instruction(&Instruction::LocalGet(dest_local));
                        func.instruction(&Instruction::LocalGet(loop_local));
                        func.instruction(&Instruction::I32Const(element_size as i32));
                        func.instruction(&Instruction::I32Mul);
                        func.instruction(&Instruction::I32Add);
                        // Load handle from same addr + offset
                        func.instruction(&Instruction::LocalGet(dest_local));
                        func.instruction(&Instruction::LocalGet(loop_local));
                        func.instruction(&Instruction::I32Const(element_size as i32));
                        func.instruction(&Instruction::I32Mul);
                        func.instruction(&Instruction::I32Add);
                        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                            offset: res_byte_offset as u64,
                            align: 2,
                            memory_index: options.callee_memory,
                        }));
                        // Call [resource-rep](handle) → rep
                        func.instruction(&Instruction::Call(rep_func));
                        // Store rep back
                        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                            offset: res_byte_offset as u64,
                            align: 2,
                            memory_index: options.callee_memory,
                        }));
                    }
                }

                // loop_counter++
                func.instruction(&Instruction::LocalGet(loop_local));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalSet(loop_local));
                func.instruction(&Instruction::Br(0)); // continue to $cont
                func.instruction(&Instruction::End); // end loop
                func.instruction(&Instruction::End); // end block
            }
        }

        // --- Phase 3.5: Convert borrow resource handles inside the buffer ---
        // For borrow<T> where callee defines T, the adapter must convert
        // handle → rep by calling [resource-rep] and writing the rep back.
        for fixup in &options.params_area_borrow_fixups {
            // Stack: callee_ptr (for i32.store dest)
            func.instruction(&Instruction::LocalGet(callee_ptr_local));
            // Load handle from callee's buffer at byte_offset
            func.instruction(&Instruction::LocalGet(callee_ptr_local));
            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: fixup.byte_offset as u64,
                align: 2,
                memory_index: options.callee_memory,
            }));
            // Call [resource-rep](handle) → rep
            func.instruction(&Instruction::Call(fixup.rep_func));
            // Store rep back at the same offset
            func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                offset: fixup.byte_offset as u64,
                align: 2,
                memory_index: options.callee_memory,
            }));
        }

        // --- Phase 4: Call callee with the new pointer ---
        func.instruction(&Instruction::LocalGet(callee_ptr_local));
        func.instruction(&Instruction::Call(target_func));

        // --- Phase 5: Handle post-return if needed ---
        if has_post_return {
            // Save result (assume i32)
            func.instruction(&Instruction::LocalSet(result_save_base));
            // Call post-return (no args for params-ptr convention post-return)
            func.instruction(&Instruction::Call(options.callee_post_return.unwrap()));
            // Push result back
            func.instruction(&Instruction::LocalGet(result_save_base));
        }

        func.instruction(&Instruction::End);

        Ok((caller_type_idx, func))
    }

    /// Generate an adapter for the retptr calling convention.
    ///
    /// In the canonical ABI, when a function returns heap-allocated types
    /// (strings, lists, records containing them), the lowered import uses:
    ///   caller: (params..., retptr: i32) → void
    /// and the lifted export uses:
    ///   callee: (params...)               → i32 (return area pointer)
    ///
    /// The adapter bridges these conventions:
    /// 1. Copy ALL input pointer pairs from caller to callee memory
    /// 2. Call callee with remapped params (excluding retptr)
    /// 3. Read flat results from callee's return area
    /// 4. Copy pointed-to data for each result pointer pair to caller memory
    /// 5. Write fixed-up flat results at caller's retptr
    /// 6. Call post-return for callee cleanup
    #[allow(clippy::too_many_arguments)]
    fn generate_retptr_adapter(
        &self,
        site: &AdapterSite,
        _merged: &MergedModule,
        options: &AdapterOptions,
        target_func: u32,
        caller_type_idx: u32,
        caller_param_count: usize,
        callee_param_count: usize,
    ) -> Result<(u32, Function)> {
        let retptr_local = (caller_param_count - 1) as u32;
        let return_area_size = site.requirements.return_area_byte_size.unwrap_or(8);

        let param_ptr_positions = &site.requirements.pointer_pair_positions;
        let result_ptr_offsets = &site.requirements.result_pointer_pair_offsets;
        let num_param_pairs = param_ptr_positions.len();
        let _num_result_pairs = result_ptr_offsets.len();

        // Compute fixup depth: each nesting level needs 4 scratch locals
        let param_fixup_depth = Self::max_fixup_depth(&site.requirements.param_copy_layouts);
        let result_fixup_depth = Self::max_fixup_depth(&site.requirements.result_copy_layouts);
        let max_fixup_depth = param_fixup_depth.max(result_fixup_depth);

        let has_cond_param_pairs = !site.requirements.conditional_pointer_pairs.is_empty();
        let has_cond_result_pairs = !site
            .requirements
            .conditional_result_pointer_pairs
            .is_empty();

        // Scratch locals layout (all i32, after caller params):
        //   [dest_ptr_0..dest_ptr_N]  (one per param pointer pair)
        //   [cond_dest_ptr]           (reused for conditional param/result copies)
        //   [result_ptr]              (return area pointer from callee)
        //   [data_ptr] [data_len] [caller_new_ptr]  (reused for each result pair)
        //   [loop_idx, inner_ptr, inner_len, new_ptr] × depth  (for nested fixup loops)
        let mut scratch_count: u32 = 0;
        let dest_ptr_base = caller_param_count as u32;
        if num_param_pairs > 0 && options.callee_realloc.is_some() {
            scratch_count += num_param_pairs as u32;
        }
        let cond_dest_ptr_local = caller_param_count as u32 + scratch_count;
        if has_cond_param_pairs || has_cond_result_pairs {
            scratch_count += 1;
        }
        let result_ptr_local = caller_param_count as u32 + scratch_count;
        scratch_count += 1;
        let data_ptr_local = caller_param_count as u32 + scratch_count;
        scratch_count += 1;
        let data_len_local = caller_param_count as u32 + scratch_count;
        scratch_count += 1;
        let caller_new_ptr_local = caller_param_count as u32 + scratch_count;
        scratch_count += 1;
        let fixup_locals_base = caller_param_count as u32 + scratch_count;
        scratch_count += 4 * max_fixup_depth; // 4 locals per nesting level
        if !options.inner_resource_fixups.is_empty() {
            scratch_count += 1; // resource loop counter
        }

        let local_decls = vec![(scratch_count, wasm_encoder::ValType::I32)];
        let mut func = Function::new(local_decls);

        // Phase 0: Convert borrow resource handles
        emit_resource_borrow_phase0(&mut func, &options.resource_rep_calls);

        // --- Phase 1: Outbound copy of ALL pointer pairs (caller → callee) ---
        if let Some(callee_realloc) = options
            .callee_realloc
            .filter(|_| !param_ptr_positions.is_empty())
        {
            let param_layouts = &site.requirements.param_copy_layouts;
            for (pair_idx, &ptr_pos) in param_ptr_positions.iter().enumerate() {
                let len_pos = ptr_pos + 1;
                let dest_local = dest_ptr_base + pair_idx as u32;
                let byte_mult = param_layouts
                    .get(pair_idx)
                    .map(|cl| match cl {
                        crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                        crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                    })
                    .unwrap_or(1);

                // Param-side (caller → callee) tagged latin1+utf16 string —
                // governed by the caller encoding; byte_mult == 1 selects the
                // byte-granular string / list<u8> case. See the memory-copy
                // adapter's param-copy loop for the full reasoning.
                let is_compact_utf16 =
                    options.caller_string_encoding == StringEncoding::Latin1 && byte_mult == 1;
                let realloc_align = if is_compact_utf16 { 2 } else { 1 };

                // Allocate: dest = cabi_realloc(0, 0, align, <byte count>)
                emit_overflow_guard(&mut func, len_pos, byte_mult);
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(realloc_align));
                emit_copy_byte_count(&mut func, len_pos, byte_mult, is_compact_utf16);
                emit_checked_realloc(&mut func, callee_realloc, dest_local);

                // Copy: memory.copy callee_mem caller_mem (dest, src, <byte count>)
                func.instruction(&Instruction::LocalGet(dest_local));
                func.instruction(&Instruction::LocalGet(ptr_pos));
                emit_copy_byte_count(&mut func, len_pos, byte_mult, is_compact_utf16);
                func.instruction(&Instruction::MemoryCopy {
                    src_mem: options.caller_memory,
                    dst_mem: options.callee_memory,
                });

                // Fix up inner pointers if element type has owned data
                if let Some(crate::resolver::CopyLayout::Elements {
                    element_size,
                    inner_pointers,
                    ..
                }) = param_layouts.get(pair_idx)
                    && !inner_pointers.is_empty()
                {
                    Self::emit_inner_pointer_fixup(
                        &mut func,
                        inner_pointers,
                        *element_size,
                        ptr_pos,    // src_base (caller's original ptr)
                        dest_local, // dst_base (callee's copy)
                        len_pos,    // count (element count)
                        options.caller_memory,
                        options.callee_memory,
                        callee_realloc,
                        fixup_locals_base,
                        // Param-side: governed by the caller's string encoding.
                        options.caller_string_encoding == StringEncoding::Latin1,
                    );
                }

                // Fix up inner resource handles after bulk copy
                if let Some(crate::resolver::CopyLayout::Elements {
                    element_size,
                    inner_resources,
                    ..
                }) = param_layouts.get(pair_idx)
                    && !inner_resources.is_empty()
                    && !options.inner_resource_fixups.is_empty()
                {
                    let element_size = *element_size;
                    let res_loop_idx = fixup_locals_base + 4 * max_fixup_depth;
                    func.instruction(&Instruction::I32Const(0));
                    func.instruction(&Instruction::LocalSet(res_loop_idx));
                    func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
                    func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
                    func.instruction(&Instruction::LocalGet(res_loop_idx));
                    func.instruction(&Instruction::LocalGet(len_pos));
                    func.instruction(&Instruction::I32GeU);
                    func.instruction(&Instruction::BrIf(1));
                    for fixup in &options.inner_resource_fixups {
                        let byte_offset = fixup.byte_offset;
                        let rep_func = fixup.rep_func;
                        // UCA-A-16: per-element discriminant guards (see the
                        // sibling loop in `generate_adapter`). Empty =
                        // unconditional; mirrors `emit_inner_pointer_fixup`.
                        let guarded = Self::emit_inner_resource_guard_chain(
                            &mut func,
                            &fixup.guards,
                            dest_local,
                            res_loop_idx,
                            element_size,
                            options.callee_memory,
                        );
                        // Push addr for store
                        func.instruction(&Instruction::LocalGet(dest_local));
                        func.instruction(&Instruction::LocalGet(res_loop_idx));
                        func.instruction(&Instruction::I32Const(element_size as i32));
                        func.instruction(&Instruction::I32Mul);
                        func.instruction(&Instruction::I32Add);
                        // Load handle
                        func.instruction(&Instruction::LocalGet(dest_local));
                        func.instruction(&Instruction::LocalGet(res_loop_idx));
                        func.instruction(&Instruction::I32Const(element_size as i32));
                        func.instruction(&Instruction::I32Mul);
                        func.instruction(&Instruction::I32Add);
                        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                            offset: byte_offset as u64,
                            align: 2,
                            memory_index: options.callee_memory,
                        }));
                        func.instruction(&Instruction::Call(rep_func));
                        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                            offset: byte_offset as u64,
                            align: 2,
                            memory_index: options.callee_memory,
                        }));
                        if guarded {
                            func.instruction(&Instruction::End); // end UCA-A-16 guard If
                        }
                    }
                    func.instruction(&Instruction::LocalGet(res_loop_idx));
                    func.instruction(&Instruction::I32Const(1));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::LocalSet(res_loop_idx));
                    func.instruction(&Instruction::Br(0));
                    func.instruction(&Instruction::End);
                    func.instruction(&Instruction::End);
                }
            }
        }

        // --- Phase 1b: Conditional param copy (option/result/variant params) ---
        if let Some(callee_realloc) = options.callee_realloc.filter(|_| has_cond_param_pairs) {
            for cond in &site.requirements.conditional_pointer_pairs {
                let ptr_local = cond.ptr_position;
                let len_local = cond.ptr_position + 1;
                let byte_mult = match &cond.copy_layout {
                    crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                    crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                };
                // Param-side (caller → callee) tagged latin1+utf16 string.
                let is_compact_utf16 =
                    options.caller_string_encoding == StringEncoding::Latin1 && byte_mult == 1;
                let realloc_align = if is_compact_utf16 { 2 } else { 1 };

                // Outer-guard AND-chain (LS-P-10) before firing the copy.
                emit_conditional_guard_chain_flat(&mut func, cond, 0);
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));

                // Allocate in callee memory
                emit_overflow_guard(&mut func, len_local, byte_mult);
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(realloc_align));
                emit_copy_byte_count(&mut func, len_local, byte_mult, is_compact_utf16);
                emit_checked_realloc(&mut func, callee_realloc, cond_dest_ptr_local);

                // Copy from caller to callee memory
                func.instruction(&Instruction::LocalGet(cond_dest_ptr_local));
                func.instruction(&Instruction::LocalGet(ptr_local));
                emit_copy_byte_count(&mut func, len_local, byte_mult, is_compact_utf16);
                func.instruction(&Instruction::MemoryCopy {
                    src_mem: options.caller_memory,
                    dst_mem: options.callee_memory,
                });

                // Replace ptr with callee's copy
                func.instruction(&Instruction::LocalGet(cond_dest_ptr_local));
                func.instruction(&Instruction::LocalSet(ptr_local));

                func.instruction(&Instruction::End);
            }
        }

        // Push callee params (after all pointer remapping)
        if !param_ptr_positions.is_empty() && options.callee_realloc.is_some() {
            for i in 0..callee_param_count as u32 {
                if let Some(pair_idx) = param_ptr_positions.iter().position(|&pos| pos == i) {
                    func.instruction(&Instruction::LocalGet(dest_ptr_base + pair_idx as u32));
                } else {
                    func.instruction(&Instruction::LocalGet(i));
                }
            }
        } else {
            for i in 0..callee_param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
        }

        // --- Phase 2: Call callee → get return area pointer ---
        func.instruction(&Instruction::Call(target_func));
        func.instruction(&Instruction::LocalSet(result_ptr_local));

        // --- Phase 3+4+5: Process return area and write to retptr ---
        // For each result pointer pair, copy the pointed-to data and fix up.
        // For scalar values in the return area, copy them using correctly-sized
        // load/store instructions based on the canonical ABI memory layout.
        let result_layouts = &site.requirements.result_copy_layouts;
        let return_area_slots = &site.requirements.return_area_slots;

        if let Some(caller_realloc) = options
            .caller_realloc
            .filter(|_| !result_ptr_offsets.is_empty())
        {
            // Walk return area slots from the canonical ABI layout.
            // Pointer-pair slots trigger cross-memory data copy + fixup.
            // Scalar slots are copied with correctly-sized load/store.
            let mut result_pair_idx: usize = 0;
            for slot in return_area_slots {
                if slot.is_pointer_pair {
                    // This is a pointer pair [data_ptr, data_len] — need to copy data
                    let ptr_offset = slot.byte_offset;
                    let len_offset = slot.byte_offset + 4;
                    let byte_mult = result_layouts
                        .get(result_pair_idx)
                        .map(|cl| match cl {
                            crate::resolver::CopyLayout::Bulk { byte_multiplier } => {
                                *byte_multiplier
                            }
                            crate::resolver::CopyLayout::Elements { element_size, .. } => {
                                *element_size
                            }
                        })
                        .unwrap_or(1);

                    // Load data_ptr and data_len from callee's return area
                    func.instruction(&Instruction::LocalGet(result_ptr_local));
                    func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                        offset: ptr_offset as u64,
                        align: 2,
                        memory_index: options.callee_memory,
                    }));
                    func.instruction(&Instruction::LocalSet(data_ptr_local));

                    func.instruction(&Instruction::LocalGet(result_ptr_local));
                    func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                        offset: len_offset as u64,
                        align: 2,
                        memory_index: options.callee_memory,
                    }));
                    func.instruction(&Instruction::LocalSet(data_len_local));

                    // Result-side (callee → caller): a returned latin1+utf16
                    // string has its length tagged per the *callee* encoding.
                    // byte_mult == 1 selects the byte-granular string / list<u8>
                    // case; the length stored back into the caller's return area
                    // stays tagged (only the byte count is masked here).
                    let is_compact_utf16 =
                        options.callee_string_encoding == StringEncoding::Latin1 && byte_mult == 1;
                    let realloc_align = if is_compact_utf16 { 2 } else { 1 };

                    // Allocate in caller's memory: <byte count> bytes
                    emit_overflow_guard(&mut func, data_len_local, byte_mult);
                    func.instruction(&Instruction::I32Const(0));
                    func.instruction(&Instruction::I32Const(0));
                    func.instruction(&Instruction::I32Const(realloc_align));
                    emit_copy_byte_count(&mut func, data_len_local, byte_mult, is_compact_utf16);
                    emit_checked_realloc(&mut func, caller_realloc, caller_new_ptr_local);

                    // Copy data bytes from callee → caller
                    func.instruction(&Instruction::LocalGet(caller_new_ptr_local));
                    func.instruction(&Instruction::LocalGet(data_ptr_local));
                    emit_copy_byte_count(&mut func, data_len_local, byte_mult, is_compact_utf16);
                    func.instruction(&Instruction::MemoryCopy {
                        src_mem: options.callee_memory,
                        dst_mem: options.caller_memory,
                    });

                    // Fix up inner pointers in the result (callee → caller direction)
                    if let Some(crate::resolver::CopyLayout::Elements {
                        element_size,
                        inner_pointers,
                        ..
                    }) = result_layouts.get(result_pair_idx)
                        && !inner_pointers.is_empty()
                    {
                        Self::emit_inner_pointer_fixup(
                            &mut func,
                            inner_pointers,
                            *element_size,
                            data_ptr_local,       // src_base (callee's original)
                            caller_new_ptr_local, // dst_base (caller's copy)
                            data_len_local,       // count
                            options.callee_memory,
                            options.caller_memory,
                            caller_realloc,
                            fixup_locals_base,
                            // Result-side: governed by the callee's string encoding.
                            options.callee_string_encoding == StringEncoding::Latin1,
                        );
                    }

                    // Write fixed-up [new_ptr, data_len] to retptr
                    func.instruction(&Instruction::LocalGet(retptr_local));
                    func.instruction(&Instruction::LocalGet(caller_new_ptr_local));
                    func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                        offset: ptr_offset as u64,
                        align: 2,
                        memory_index: options.caller_memory,
                    }));

                    func.instruction(&Instruction::LocalGet(retptr_local));
                    func.instruction(&Instruction::LocalGet(data_len_local));
                    func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                        offset: len_offset as u64,
                        align: 2,
                        memory_index: options.caller_memory,
                    }));

                    result_pair_idx += 1;
                } else {
                    // Scalar value — copy with correctly-sized load/store
                    let byte_offset = slot.byte_offset;
                    func.instruction(&Instruction::LocalGet(retptr_local));
                    func.instruction(&Instruction::LocalGet(result_ptr_local));
                    match slot.byte_size {
                        8 => {
                            func.instruction(&Instruction::I64Load(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 3, // 2^3 = 8
                                memory_index: options.callee_memory,
                            }));
                            func.instruction(&Instruction::I64Store(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 3,
                                memory_index: options.caller_memory,
                            }));
                        }
                        2 => {
                            func.instruction(&Instruction::I32Load16U(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 1, // 2^1 = 2
                                memory_index: options.callee_memory,
                            }));
                            func.instruction(&Instruction::I32Store16(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 1,
                                memory_index: options.caller_memory,
                            }));
                        }
                        1 => {
                            func.instruction(&Instruction::I32Load8U(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 0, // 2^0 = 1
                                memory_index: options.callee_memory,
                            }));
                            func.instruction(&Instruction::I32Store8(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 0,
                                memory_index: options.caller_memory,
                            }));
                        }
                        _ => {
                            // 4 bytes (i32/f32) or fallback
                            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 2, // 2^2 = 4
                                memory_index: options.callee_memory,
                            }));
                            func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                                offset: byte_offset as u64,
                                align: 2,
                                memory_index: options.caller_memory,
                            }));
                        }
                    }
                }
            }
        } else {
            // No result pointer pairs — bulk copy the entire return area
            func.instruction(&Instruction::LocalGet(retptr_local)); // dst
            func.instruction(&Instruction::LocalGet(result_ptr_local)); // src
            func.instruction(&Instruction::I32Const(return_area_size as i32)); // size
            func.instruction(&Instruction::MemoryCopy {
                src_mem: options.callee_memory,
                dst_mem: options.caller_memory,
            });
        }

        // --- Phase 5b: Conditional result copy (option/result/variant in return area) ---
        if let Some(caller_realloc) = options.caller_realloc.filter(|_| has_cond_result_pairs) {
            for cond in &site.requirements.conditional_result_pointer_pairs {
                let ptr_offset = cond.ptr_position;
                let len_offset = cond.ptr_position + 4;
                let byte_mult = match &cond.copy_layout {
                    crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                    crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                };

                // Outer-guard AND-chain (LS-P-10) before firing the copy.
                // Each guard's discriminant is loaded from the callee's
                // return area at its byte offset using the matching width.
                emit_conditional_guard_chain_byte(
                    &mut func,
                    cond,
                    result_ptr_local,
                    options.callee_memory,
                );
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));

                // Load ptr and len from callee's return area
                func.instruction(&Instruction::LocalGet(result_ptr_local));
                func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                    offset: ptr_offset as u64,
                    align: 2,
                    memory_index: options.callee_memory,
                }));
                func.instruction(&Instruction::LocalSet(data_ptr_local));

                func.instruction(&Instruction::LocalGet(result_ptr_local));
                func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                    offset: len_offset as u64,
                    align: 2,
                    memory_index: options.callee_memory,
                }));
                func.instruction(&Instruction::LocalSet(data_len_local));

                // Result-side (callee → caller) conditional string: tagged per
                // the *callee* encoding. byte_mult == 1 ⇒ byte-granular string /
                // list<u8>; the length written back to the retptr stays tagged.
                let is_compact_utf16 =
                    options.callee_string_encoding == StringEncoding::Latin1 && byte_mult == 1;
                let realloc_align = if is_compact_utf16 { 2 } else { 1 };

                // Allocate in caller memory
                emit_overflow_guard(&mut func, data_len_local, byte_mult);
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::I32Const(realloc_align));
                emit_copy_byte_count(&mut func, data_len_local, byte_mult, is_compact_utf16);
                emit_checked_realloc(&mut func, caller_realloc, caller_new_ptr_local);

                // Copy data from callee → caller
                func.instruction(&Instruction::LocalGet(caller_new_ptr_local));
                func.instruction(&Instruction::LocalGet(data_ptr_local));
                emit_copy_byte_count(&mut func, data_len_local, byte_mult, is_compact_utf16);
                func.instruction(&Instruction::MemoryCopy {
                    src_mem: options.callee_memory,
                    dst_mem: options.caller_memory,
                });

                // Write fixed-up ptr to caller's retptr
                func.instruction(&Instruction::LocalGet(retptr_local));
                func.instruction(&Instruction::LocalGet(caller_new_ptr_local));
                func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                    offset: ptr_offset as u64,
                    align: 2,
                    memory_index: options.caller_memory,
                }));

                func.instruction(&Instruction::End);
            }
        }

        // --- Phase 6: Call post-return for callee cleanup ---
        if let Some(post_return_func) = options.callee_post_return {
            func.instruction(&Instruction::LocalGet(result_ptr_local));
            func.instruction(&Instruction::Call(post_return_func));
        }

        // Return void (retptr convention — results written to memory)
        func.instruction(&Instruction::End);

        Ok((caller_type_idx, func))
    }

    /// Compute the maximum nesting depth of inner pointer fixups.
    /// Each level needs 4 scratch locals (loop_idx, inner_ptr, inner_len, new_ptr).
    fn max_fixup_depth(layouts: &[crate::resolver::CopyLayout]) -> u32 {
        fn depth(layout: &crate::resolver::CopyLayout) -> u32 {
            match layout {
                crate::resolver::CopyLayout::Bulk { .. } => 0,
                crate::resolver::CopyLayout::Elements { inner_pointers, .. } => {
                    if inner_pointers.is_empty() {
                        0
                    } else {
                        1 + inner_pointers
                            .iter()
                            .map(|ip| depth(&ip.copy_layout))
                            .max()
                            .unwrap_or(0)
                    }
                }
            }
        }
        layouts.iter().map(depth).max().unwrap_or(0)
    }

    /// Emit the per-element discriminant-guard chain for an inner-resource
    /// fixup, returning `true` if an `If` was opened (caller must close it
    /// with `End` after the conversion). Mirrors the guard emission inside
    /// [`Self::emit_inner_pointer_fixup`] (UCA-A-16): each guard's
    /// discriminant byte is loaded from the per-element base
    /// (`dst_base + loop_idx * element_size + guard.position`) at the width
    /// selected by `guard.byte_size`, compared to `guard.value`, AND-chained,
    /// and the result drives an `If`. Empty guards → no `If` (unconditional).
    fn emit_inner_resource_guard_chain(
        func: &mut Function,
        guards: &[crate::resolver::DiscriminantGuard],
        dst_base_local: u32,
        loop_idx: u32,
        element_size: u32,
        dst_mem: u32,
    ) -> bool {
        if guards.is_empty() {
            return false;
        }
        let mut emitted_any = false;
        for guard in guards {
            func.instruction(&Instruction::LocalGet(dst_base_local));
            func.instruction(&Instruction::LocalGet(loop_idx));
            func.instruction(&Instruction::I32Const(element_size as i32));
            func.instruction(&Instruction::I32Mul);
            func.instruction(&Instruction::I32Add);
            let mem_arg = wasm_encoder::MemArg {
                offset: guard.position as u64,
                align: 0,
                memory_index: dst_mem,
            };
            match guard.byte_size {
                1 => func.instruction(&Instruction::I32Load8U(mem_arg)),
                2 => func.instruction(&Instruction::I32Load16U(wasm_encoder::MemArg {
                    align: 1,
                    ..mem_arg
                })),
                _ => func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                    align: 2,
                    ..mem_arg
                })),
            };
            func.instruction(&Instruction::I32Const(guard.value as i32));
            func.instruction(&Instruction::I32Eq);
            if emitted_any {
                func.instruction(&Instruction::I32And);
            }
            emitted_any = true;
        }
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        true
    }

    /// Emit wasm instructions that fix up inner pointers after a bulk copy.
    ///
    /// After bulk-copying `count` elements of `element_size` bytes from one
    /// memory to another, inner (ptr, len) pairs within each element still
    /// reference the source memory. This method generates a wasm loop that:
    /// 1. Iterates over each element
    /// 2. For each inner pointer pair at a known offset:
    ///    a. Reads (ptr, len) from the destination copy
    ///    b. Allocates `len * inner_byte_mult` bytes in the destination memory
    ///    c. Copies data from source memory to destination memory
    ///    d. Writes the new pointer back into the destination element
    ///
    /// `locals_base` is the first available scratch local index (all i32).
    /// This method uses 4 scratch locals: [loop_idx, inner_ptr, inner_len, new_ptr].
    #[allow(clippy::too_many_arguments)]
    fn emit_inner_pointer_fixup(
        func: &mut Function,
        inner_pointers: &[crate::resolver::InnerPointer],
        element_size: u32,
        _src_base_local: u32, // local holding source array base pointer (reserved for future deep copy)
        dst_base_local: u32,  // local holding destination array base pointer
        count_local: u32,     // local holding element count
        src_mem: u32,
        dst_mem: u32,
        realloc_func: u32,
        locals_base: u32,
        // True when the governing canonical-ABI string encoding (caller's for
        // param-side copies, callee's for result-side copies) is `latin1+utf16`
        // (modelled as `StringEncoding::Latin1`). When set, a byte-granular
        // inner buffer (`byte_mult == 1`) is treated as a tag-encoded string:
        // its byte count is masked/doubled via `emit_copy_byte_count`. The
        // pointer-pair length stored back into the destination element is the
        // ORIGINAL (still-tagged) operand, so the callee/caller decoder still
        // sees the tag. `CopyLayout` cannot distinguish a nested `string` from
        // a nested `list<u8>`, but the latter is unaffected: a legitimate
        // list<u8> count is < 2^31, so its tag bit is clear and the tag-aware
        // path returns `len` unchanged (see `emit_copy_byte_count`).
        is_compact_utf16: bool,
    ) {
        if inner_pointers.is_empty() {
            return;
        }
        let loop_idx = locals_base;
        let inner_ptr = locals_base + 1;
        let inner_len = locals_base + 2;
        let new_ptr = locals_base + 3;

        // Initialize loop counter to 0
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(loop_idx));

        // block $exit { loop $cont {
        func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        // if loop_idx >= count: break
        func.instruction(&Instruction::LocalGet(loop_idx));
        func.instruction(&Instruction::LocalGet(count_local));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::BrIf(1)); // break to $exit

        // For each inner pointer descriptor:
        for ip in inner_pointers {
            let inner_offset = ip.byte_offset;
            let inner_layout = &ip.copy_layout;
            let byte_mult = match inner_layout {
                crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
            };

            // LS-P-12: AND-evaluate this descriptor's per-element discriminant
            // guards. Empty guards → unconditional fixup (the historic
            // Record/Tuple/List path). Non-empty → load each guard's
            // discriminant byte from the per-element base
            // (`dst_base + loop_idx * element_size + guard.position`) at the
            // right width (`I32Load{8U,16U,_}` per `guard.byte_size`),
            // compare with `guard.value`, AND-chain the results, and wrap
            // the entire fixup body in an `If` so it only fires when every
            // enclosing option/result/variant arm holds.
            let guarded = !ip.guards.is_empty();
            if guarded {
                let mut emitted_any = false;
                for guard in &ip.guards {
                    func.instruction(&Instruction::LocalGet(dst_base_local));
                    func.instruction(&Instruction::LocalGet(loop_idx));
                    func.instruction(&Instruction::I32Const(element_size as i32));
                    func.instruction(&Instruction::I32Mul);
                    func.instruction(&Instruction::I32Add);
                    let mem_arg = wasm_encoder::MemArg {
                        offset: guard.position as u64,
                        align: 0,
                        memory_index: dst_mem,
                    };
                    match guard.byte_size {
                        1 => func.instruction(&Instruction::I32Load8U(mem_arg)),
                        2 => func.instruction(&Instruction::I32Load16U(wasm_encoder::MemArg {
                            align: 1,
                            ..mem_arg
                        })),
                        _ => func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                            align: 2,
                            ..mem_arg
                        })),
                    };
                    func.instruction(&Instruction::I32Const(guard.value as i32));
                    func.instruction(&Instruction::I32Eq);
                    if emitted_any {
                        func.instruction(&Instruction::I32And);
                    }
                    emitted_any = true;
                }
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
            }

            // elem_offset = loop_idx * element_size + inner_offset
            // Read inner_ptr from dst_base[elem_offset]
            func.instruction(&Instruction::LocalGet(dst_base_local));
            func.instruction(&Instruction::LocalGet(loop_idx));
            func.instruction(&Instruction::I32Const(element_size as i32));
            func.instruction(&Instruction::I32Mul);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(inner_offset as i32));
            func.instruction(&Instruction::I32Add);
            // Now stack has: dst_base + loop_idx * element_size + inner_offset
            // But we need to load from the SOURCE memory (the pointer values
            // in the dst copy still point to src memory after bulk copy)
            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: 0,
                align: 2,
                memory_index: dst_mem,
            }));
            func.instruction(&Instruction::LocalSet(inner_ptr));

            // Read inner_len from dst_base[elem_offset + 4]
            func.instruction(&Instruction::LocalGet(dst_base_local));
            func.instruction(&Instruction::LocalGet(loop_idx));
            func.instruction(&Instruction::I32Const(element_size as i32));
            func.instruction(&Instruction::I32Mul);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(inner_offset as i32 + 4));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                offset: 0,
                align: 2,
                memory_index: dst_mem,
            }));
            func.instruction(&Instruction::LocalSet(inner_len));

            // A byte-granular inner buffer in a latin1+utf16 component is a
            // tag-encoded string; mask/double its byte count. Non-byte-granular
            // inner buffers and list<u8> are handled by the plain path.
            let inner_is_compact_utf16 = is_compact_utf16 && byte_mult == 1;

            // Allocate inner data in dst memory: new_ptr = realloc(0, 0, align, <byte count>)
            emit_overflow_guard(func, inner_len, byte_mult);
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::I32Const(if inner_is_compact_utf16 {
                2
            } else {
                1
            }));
            emit_copy_byte_count(func, inner_len, byte_mult, inner_is_compact_utf16);
            emit_checked_realloc(func, realloc_func, new_ptr);

            // Copy data from src memory to dst memory
            // memory.copy dst_mem src_mem (new_ptr, inner_ptr, <byte count>)
            func.instruction(&Instruction::LocalGet(new_ptr));
            func.instruction(&Instruction::LocalGet(inner_ptr));
            emit_copy_byte_count(func, inner_len, byte_mult, inner_is_compact_utf16);
            func.instruction(&Instruction::MemoryCopy { src_mem, dst_mem });

            // Recursively fix up inner-inner pointers if the inner layout
            // itself has pointer pairs (e.g., list<list<string>>).
            if let crate::resolver::CopyLayout::Elements {
                element_size: inner_elem_size,
                inner_pointers: inner_inner,
                ..
            } = inner_layout
                && !inner_inner.is_empty()
            {
                // Use the next set of 4 scratch locals for the recursive level
                Self::emit_inner_pointer_fixup(
                    func,
                    inner_inner,
                    *inner_elem_size,
                    inner_ptr, // src_base: the original source ptr
                    new_ptr,   // dst_base: the newly allocated copy
                    inner_len, // count: element count
                    src_mem,
                    dst_mem,
                    realloc_func,
                    locals_base + 4, // next level gets next 4 scratch locals
                    is_compact_utf16,
                );
            }

            // Write new_ptr back to dst element
            func.instruction(&Instruction::LocalGet(dst_base_local));
            func.instruction(&Instruction::LocalGet(loop_idx));
            func.instruction(&Instruction::I32Const(element_size as i32));
            func.instruction(&Instruction::I32Mul);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(inner_offset as i32));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalGet(new_ptr));
            func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                offset: 0,
                align: 2,
                memory_index: dst_mem,
            }));
            // len stays the same — no need to update it

            if guarded {
                func.instruction(&Instruction::End); // end LS-P-12 per-element guard If
            }
        }

        // Increment loop counter
        func.instruction(&Instruction::LocalGet(loop_idx));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(loop_idx));

        // Continue loop
        func.instruction(&Instruction::Br(0)); // br $cont

        // }} end loop, end block
        func.instruction(&Instruction::End); // end loop
        func.instruction(&Instruction::End); // end block
    }

    /// Generate an adapter with string transcoding
    fn generate_transcoding_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
        options: &AdapterOptions,
    ) -> Result<(u32, Function)> {
        let target_func = self.resolve_target_function(site, merged)?;
        let type_idx = merged
            .defined_func(target_func)
            .map(|f| f.type_idx)
            .unwrap_or(0);

        let func_type = merged.types.get(type_idx as usize);
        let param_count = func_type.map(|t| t.params.len()).unwrap_or(0);
        let result_count = func_type.map(|t| t.results.len()).unwrap_or(0);
        let result_types: Vec<wasm_encoder::ValType> =
            func_type.map(|t| t.results.clone()).unwrap_or_default();
        let needs_post_return_save = options.callee_post_return.is_some() && result_count > 0;

        // Determine how many scratch locals are needed for transcoding
        let needs_transcoding_locals = !matches!(
            (
                options.caller_string_encoding,
                options.callee_string_encoding
            ),
            (StringEncoding::Utf8, StringEncoding::Utf8)
        );

        // Scratch locals: src_idx, dst_idx, out_ptr, cu/byte, code_point, and
        // a 6th unit. In the UTF-16→UTF-8 direction the 6th unit is `cu2`
        // (the second surrogate unit, used by the low-surrogate validation —
        // LS-P-16 mid-string mitigation). In the UTF-8→UTF-16 direction the
        // 6th unit is `cont` (a continuation byte being validated — #251
        // malformed-UTF-8 hardening: invalid continuation / lead / overlong /
        // surrogate / out-of-range detection). Only one direction's transcoder
        // runs per generated function, so the two uses never alias.
        let scratch_locals: u32 = if needs_transcoding_locals { 6 } else { 0 };
        let post_return_base = param_count as u32 + scratch_locals;

        let mut local_decls: Vec<(u32, wasm_encoder::ValType)> = Vec::new();
        if scratch_locals > 0 {
            local_decls.push((scratch_locals, wasm_encoder::ValType::I32));
        }
        if needs_post_return_save {
            for ty in &result_types {
                local_decls.push((1, *ty));
            }
        }
        let mut func = Function::new(local_decls);

        // Phase 0: Convert borrow resource handles
        emit_resource_borrow_phase0(&mut func, &options.resource_rep_calls);

        // The #253 latin1+utf16 transcoders dispatch on the length tag with an
        // `If`/`Else` whose two legs each call the target and leave the
        // function's result on the stack. The block must therefore carry the
        // function's result type so the value isn't trapped inside the block.
        // Flat string-call results are 0 or 1 value (multi-value returns go
        // through a retptr param); we only need Empty / single-result here.
        let transcode_block_ty = match result_types.as_slice() {
            [] => wasm_encoder::BlockType::Empty,
            [ty] => wasm_encoder::BlockType::Result(*ty),
            _ => {
                return Err(crate::Error::AdapterGeneration(format!(
                    "string transcoding with {} flat results is unsupported \
                     (expected 0 or 1; multi-value returns use a retptr) — see #253",
                    result_types.len()
                )));
            }
        };

        // Generate transcoding logic based on encoding pair

        match (
            options.caller_string_encoding,
            options.callee_string_encoding,
        ) {
            (StringEncoding::Utf8, StringEncoding::Utf8) => {
                // No transcoding needed, just copy
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
            }

            (StringEncoding::Utf8, StringEncoding::Utf16) => {
                // UTF-8 to UTF-16 transcoding
                // This would call a transcoding helper function
                self.emit_utf8_to_utf16_transcode(&mut func, param_count, target_func, options);
            }

            (StringEncoding::Utf16, StringEncoding::Utf8) => {
                // UTF-16 to UTF-8 transcoding
                self.emit_utf16_to_utf8_transcode(&mut func, param_count, target_func, options);
            }

            (StringEncoding::Latin1, StringEncoding::Utf8) => {
                // latin1+utf16 → UTF-8. Branches on the source length tag
                // (#253): tag-clear takes the 1-byte Latin-1 path; tag-set
                // re-reads the source as UTF-16 and transcodes to UTF-8.
                self.emit_latin1_to_utf8_transcode(
                    &mut func,
                    param_count,
                    target_func,
                    options,
                    transcode_block_ty,
                );
            }

            (StringEncoding::Latin1, StringEncoding::Utf16) => {
                // #253: latin1+utf16 → UTF-16. Branches on the source length
                // tag: tag-clear zero-extends each Latin-1 byte; tag-set does a
                // verbatim UTF-16 code-unit copy.
                self.emit_latin1_to_utf16_transcode(
                    &mut func,
                    param_count,
                    target_func,
                    options,
                    transcode_block_ty,
                );
            }

            (StringEncoding::Utf8, StringEncoding::Latin1) => {
                // #253: UTF-8 → latin1+utf16. Two-phase encoder: if every code
                // point ≤ 0xFF, write Latin-1 (tag clear); else write UTF-16
                // (tag set).
                self.emit_utf8_to_latin1_transcode(
                    &mut func,
                    param_count,
                    target_func,
                    options,
                    transcode_block_ty,
                );
            }

            (StringEncoding::Utf16, StringEncoding::Latin1) => {
                // #253: UTF-16 → latin1+utf16. Two-phase encoder mirroring the
                // UTF-8 case but scanning UTF-16 code units / surrogate pairs.
                self.emit_utf16_to_latin1_transcode(
                    &mut func,
                    param_count,
                    target_func,
                    options,
                    transcode_block_ty,
                );
            }

            (caller_enc, callee_enc) if caller_enc == callee_enc => {
                // Same encoding (e.g. Utf16→Utf16, Latin1→Latin1): no
                // transcoding needed, a verbatim copy is correct.
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
            }

            (caller_enc, callee_enc) => {
                // #253: a cross-encoding pair with no transcoder implemented
                // (e.g. Latin1→Utf16, Utf8→Latin1, Utf16→Latin1 — note
                // CompactUTF16 maps to Latin1). Previously this fell through
                // to a verbatim byte copy, silently MIS-transcoding
                // well-formed input (H-4.4). Fail loudly instead of emitting
                // a wrong adapter — the per-pair transcoders are tracked as
                // follow-up work. Reaching here means the resolver requested
                // a transcoding meld cannot yet perform correctly.
                return Err(crate::Error::AdapterGeneration(format!(
                    "unsupported string transcoding: {caller_enc:?} -> {callee_enc:?} \
                     (no transcoder implemented; a verbatim copy would silently \
                     corrupt well-formed input — see #253)"
                )));
            }
        }

        // Post-return: call cabi_post_return with the function's flat return values
        if let Some(post_return_func) = options.callee_post_return {
            if result_count > 0 {
                // Save return values to scratch locals (pop in reverse order)
                for i in (0..result_count).rev() {
                    func.instruction(&Instruction::LocalSet(post_return_base + i as u32));
                }
                // Pass saved values to cabi_post_return
                for i in 0..result_count {
                    func.instruction(&Instruction::LocalGet(post_return_base + i as u32));
                }
                func.instruction(&Instruction::Call(post_return_func));
                // Push return values back for the caller
                for i in 0..result_count {
                    func.instruction(&Instruction::LocalGet(post_return_base + i as u32));
                }
            } else {
                // No results — just call post-return
                func.instruction(&Instruction::Call(post_return_func));
            }
        }

        func.instruction(&Instruction::End);

        Ok((type_idx, func))
    }

    /// Emit UTF-8 to UTF-16 transcoding
    ///
    /// Decodes variable-length UTF-8 (1-4 bytes per code point) and encodes
    /// as UTF-16 (1-2 code units per code point, with surrogate pairs for
    /// code points >= U+10000).
    ///
    /// Assumes params start with (ptr: i32, len: i32) where len is byte count.
    /// Calls target with (out_ptr: i32, code_unit_count: i32, ...rest).
    fn emit_utf8_to_utf16_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        options: &AdapterOptions,
    ) {
        let callee_realloc = match options.callee_realloc {
            Some(idx) => idx,
            None => {
                log::warn!(
                    "UTF-8→UTF-16 transcode: no callee realloc, falling back to direct call"
                );
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
                return;
            }
        };

        // Scratch locals: src_idx, dst_idx (code units), out_ptr, byte,
        // code_point, and cont (a continuation byte being validated — #251).
        let src_idx_local = param_count as u32;
        let dst_idx_local = param_count as u32 + 1;
        let out_ptr_local = param_count as u32 + 2;
        let byte_local = param_count as u32 + 3;
        let cp_local = param_count as u32 + 4;
        let cont_local = param_count as u32 + 5;

        // Source reads use caller_memory, destination writes use callee_memory
        let src_mem8 = wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: options.caller_memory,
        };
        let dst_mem16 = wasm_encoder::MemArg {
            offset: 0,
            align: 1,
            memory_index: options.callee_memory,
        };

        // Step 1: Allocate output buffer = 2 * input_len bytes via cabi_realloc
        // (each UTF-8 byte produces at most one UTF-16 code unit = 2 bytes).
        // Guards against the two memory-safety hazards identified in LS-A-7:
        //   (a) i32.mul is modulo 2^32 — trap if len > u32::MAX/2 before the
        //       multiply, so alloc_size cannot wrap below the actual required
        //       byte count that the transcode loop will write.
        //   (b) cabi_realloc may return 0 on OOM — trap before writing so
        //       the loop cannot corrupt callee memory at offset 0.
        let callee_align = alignment_for_encoding(options.callee_string_encoding);
        func.instruction(&Instruction::LocalGet(1)); // input_len
        func.instruction(&Instruction::I32Const((u32::MAX / 2) as i32));
        func.instruction(&Instruction::I32GtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        func.instruction(&Instruction::I32Const(0)); // original_ptr
        func.instruction(&Instruction::I32Const(0)); // original_size
        func.instruction(&Instruction::I32Const(callee_align)); // alignment
        func.instruction(&Instruction::LocalGet(1)); // input_len
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Mul); // alloc_size = 2 * input_len
        func.instruction(&Instruction::Call(callee_realloc));
        func.instruction(&Instruction::LocalSet(out_ptr_local));

        // Trap on null return from cabi_realloc (LS-A-7 leg b).
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::I32Eqz);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        // Step 2: Initialize loop counters
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(src_idx_local));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(dst_idx_local));

        // Step 3: Transcoding loop
        func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        // if src_idx >= input_len, break
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::BrIf(1));

        // Read lead byte from caller memory
        func.instruction(&Instruction::LocalGet(0));
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Load8U(src_mem8));
        func.instruction(&Instruction::LocalSet(byte_local));

        // --- Decode UTF-8 sequence into code_point, advance src_idx ---
        //
        // #251 malformed-UTF-8 hardening. The decode arms below validate the
        // *content* of every multi-byte sequence, not just (LS-P-19)
        // truncation. The Canonical ABI mandates lossy U+FFFD replacement for
        // any ill-formed UTF-8 (H-4.4 incorrect transcoding); on detection we
        // follow the established LS-P-19 convention of emitting U+FFFD (one
        // UTF-16 code unit) and consuming ONLY the lead byte (src_idx += 1),
        // so the offending continuation/trailing byte is reprocessed on the
        // next iteration. This always makes progress (>= 1 byte consumed) and
        // is consistent with the existing truncation handling. It can emit
        // more U+FFFDs than the strict Unicode "maximal subpart" rule for
        // some multi-continuation cases, but never decodes to a wrong scalar.
        //
        // Helper closures keep the repeated WASM emission DRY:

        // Emit: cp = U+FFFD; src_idx += 1 (replacement, consume lead only).
        let emit_fffd_consume_lead = |func: &mut Function| {
            func.instruction(&Instruction::I32Const(0xFFFD));
            func.instruction(&Instruction::LocalSet(cp_local));
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(src_idx_local));
        };

        // Push mem8[ptr + src_idx + off] onto the stack (a continuation byte).
        let push_byte_at = |func: &mut Function, off: i32| {
            func.instruction(&Instruction::LocalGet(0));
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(off));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Load8U(src_mem8));
        };

        // Push: (cont_local & 0xC0) != 0x80  (true => NOT a continuation byte).
        let push_not_continuation = |func: &mut Function| {
            func.instruction(&Instruction::LocalGet(cont_local));
            func.instruction(&Instruction::I32Const(0xC0));
            func.instruction(&Instruction::I32And);
            func.instruction(&Instruction::I32Const(0x80));
            func.instruction(&Instruction::I32Ne);
        };

        // if byte < 0x80: 1-byte ASCII
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::I32Const(0x80));
        func.instruction(&Instruction::I32LtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            // code_point = byte
            func.instruction(&Instruction::LocalGet(byte_local));
            func.instruction(&Instruction::LocalSet(cp_local));
            // src_idx += 1
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(src_idx_local));
        }
        func.instruction(&Instruction::Else);
        {
            // if byte < 0xC2: invalid lead — a lone continuation byte
            // (0x80–0xBF) masquerading as a lead, or an overlong 2-byte lead
            // (0xC0, 0xC1). #251 case 2. Reject before the 2-byte arm so these
            // never enter the decoder. → U+FFFD, consume lead only.
            func.instruction(&Instruction::LocalGet(byte_local));
            func.instruction(&Instruction::I32Const(0xC2));
            func.instruction(&Instruction::I32LtU);
            func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
            {
                emit_fffd_consume_lead(func);
            }
            func.instruction(&Instruction::Else);
            {
                // if byte < 0xE0: 2-byte sequence (lead 0xC2–0xDF, well-formed).
                func.instruction(&Instruction::LocalGet(byte_local));
                func.instruction(&Instruction::I32Const(0xE0));
                func.instruction(&Instruction::I32LtU);
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                {
                    // LS-P-19: emit U+FFFD when the 2-byte sequence's
                    // continuation byte would be read past the end of input
                    // (truncated multi-byte lead). Pre-v0.11 trapped via
                    // `unreachable`; the Canonical-ABI-correct behaviour is
                    // lossy replacement with U+FFFD (a single UTF-16 code
                    // unit), consuming only the lead byte. The continuations
                    // would have started a valid sequence in another world;
                    // by not consuming bytes past the lead we leave that
                    // possibility open for the next iteration.
                    func.instruction(&Instruction::LocalGet(src_idx_local));
                    func.instruction(&Instruction::I32Const(1));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::LocalGet(1));
                    func.instruction(&Instruction::I32GeU);
                    func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                    {
                        // Truncated 2-byte lead → U+FFFD.
                        emit_fffd_consume_lead(func);
                    }
                    func.instruction(&Instruction::Else);
                    {
                        // #251 case 1: validate the continuation byte.
                        push_byte_at(func, 1);
                        func.instruction(&Instruction::LocalSet(cont_local));
                        push_not_continuation(func);
                        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                        {
                            // b1 is not a continuation byte → U+FFFD, consume lead.
                            emit_fffd_consume_lead(func);
                        }
                        func.instruction(&Instruction::Else);
                        {
                            // cp = (byte & 0x1F) << 6 | (b1 & 0x3F).
                            // Lead >= 0xC2 guarantees cp >= 0x80, so no overlong
                            // check is needed (the 0xC0/0xC1 leads were rejected
                            // above).
                            func.instruction(&Instruction::LocalGet(byte_local));
                            func.instruction(&Instruction::I32Const(0x1F));
                            func.instruction(&Instruction::I32And);
                            func.instruction(&Instruction::I32Const(6));
                            func.instruction(&Instruction::I32Shl);
                            func.instruction(&Instruction::LocalGet(cont_local));
                            func.instruction(&Instruction::I32Const(0x3F));
                            func.instruction(&Instruction::I32And);
                            func.instruction(&Instruction::I32Or);
                            func.instruction(&Instruction::LocalSet(cp_local));
                            // src_idx += 2
                            func.instruction(&Instruction::LocalGet(src_idx_local));
                            func.instruction(&Instruction::I32Const(2));
                            func.instruction(&Instruction::I32Add);
                            func.instruction(&Instruction::LocalSet(src_idx_local));
                        }
                        func.instruction(&Instruction::End); // end 2-byte continuation check
                    }
                    func.instruction(&Instruction::End); // end LS-P-19 (2-byte) check
                }
                func.instruction(&Instruction::Else);
                {
                    // if byte < 0xF0: 3-byte sequence (lead 0xE0–0xEF).
                    func.instruction(&Instruction::LocalGet(byte_local));
                    func.instruction(&Instruction::I32Const(0xF0));
                    func.instruction(&Instruction::I32LtU);
                    func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                    {
                        // LS-P-19: emit U+FFFD when the 3-byte sequence's
                        // continuation bytes would extend past the end of
                        // input. Pre-v0.11 trapped; now substitutes the
                        // truncated lead with U+FFFD and consumes only the
                        // lead byte.
                        func.instruction(&Instruction::LocalGet(src_idx_local));
                        func.instruction(&Instruction::I32Const(2));
                        func.instruction(&Instruction::I32Add);
                        func.instruction(&Instruction::LocalGet(1));
                        func.instruction(&Instruction::I32GeU);
                        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                        {
                            // Truncated 3-byte lead → U+FFFD.
                            emit_fffd_consume_lead(func);
                        }
                        func.instruction(&Instruction::Else);
                        {
                            // #251 case 1: validate BOTH continuation bytes.
                            // not_cont(b1) | not_cont(b2) → reject.
                            push_byte_at(func, 1);
                            func.instruction(&Instruction::LocalSet(cont_local));
                            push_not_continuation(func);
                            push_byte_at(func, 2);
                            func.instruction(&Instruction::LocalSet(cont_local));
                            push_not_continuation(func);
                            func.instruction(&Instruction::I32Or);
                            func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                            {
                                // A continuation byte is not 10xxxxxx → U+FFFD.
                                emit_fffd_consume_lead(func);
                            }
                            func.instruction(&Instruction::Else);
                            {
                                // cp = (byte & 0x0F) << 12 | (b1 & 0x3F) << 6 | (b2 & 0x3F)
                                func.instruction(&Instruction::LocalGet(byte_local));
                                func.instruction(&Instruction::I32Const(0x0F));
                                func.instruction(&Instruction::I32And);
                                func.instruction(&Instruction::I32Const(12));
                                func.instruction(&Instruction::I32Shl);
                                // b1
                                push_byte_at(func, 1);
                                func.instruction(&Instruction::I32Const(0x3F));
                                func.instruction(&Instruction::I32And);
                                func.instruction(&Instruction::I32Const(6));
                                func.instruction(&Instruction::I32Shl);
                                func.instruction(&Instruction::I32Or);
                                // b2
                                push_byte_at(func, 2);
                                func.instruction(&Instruction::I32Const(0x3F));
                                func.instruction(&Instruction::I32And);
                                func.instruction(&Instruction::I32Or);
                                func.instruction(&Instruction::LocalSet(cp_local));
                                // #251 cases 3 & 4: reject overlong
                                // (cp < 0x800) and UTF-8-encoded surrogates
                                // (0xD800 <= cp < 0xE000). overlong | surrogate.
                                func.instruction(&Instruction::LocalGet(cp_local));
                                func.instruction(&Instruction::I32Const(0x800));
                                func.instruction(&Instruction::I32LtU);
                                func.instruction(&Instruction::LocalGet(cp_local));
                                func.instruction(&Instruction::I32Const(0xD800));
                                func.instruction(&Instruction::I32GeU);
                                func.instruction(&Instruction::LocalGet(cp_local));
                                func.instruction(&Instruction::I32Const(0xE000));
                                func.instruction(&Instruction::I32LtU);
                                func.instruction(&Instruction::I32And);
                                func.instruction(&Instruction::I32Or);
                                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                                {
                                    // Overlong or surrogate → U+FFFD, consume lead.
                                    emit_fffd_consume_lead(func);
                                }
                                func.instruction(&Instruction::Else);
                                {
                                    // Well-formed 3-byte. src_idx += 3.
                                    func.instruction(&Instruction::LocalGet(src_idx_local));
                                    func.instruction(&Instruction::I32Const(3));
                                    func.instruction(&Instruction::I32Add);
                                    func.instruction(&Instruction::LocalSet(src_idx_local));
                                }
                                func.instruction(&Instruction::End); // end 3-byte overlong/surrogate check
                            }
                            func.instruction(&Instruction::End); // end 3-byte continuation check
                        }
                        func.instruction(&Instruction::End); // end LS-P-19 (3-byte) check
                    }
                    func.instruction(&Instruction::Else);
                    {
                        // 4-byte sequence (byte >= 0xF0).
                        // #251 case 2: leads 0xF5–0xFF can only produce
                        // out-of-range code points; reject them up front so
                        // they never enter the 4-byte decoder.
                        func.instruction(&Instruction::LocalGet(byte_local));
                        func.instruction(&Instruction::I32Const(0xF5));
                        func.instruction(&Instruction::I32GeU);
                        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                        {
                            emit_fffd_consume_lead(func);
                        }
                        func.instruction(&Instruction::Else);
                        {
                            // LS-P-19: emit U+FFFD when the 4-byte sequence's
                            // continuation bytes would extend past the end of
                            // input — without this guard a truncated 4-byte
                            // lead at the buffer tail reads up to 3 bytes of
                            // attacker-adjacent caller memory and folds them
                            // into the encoded code point. Pre-v0.11 trapped;
                            // now substitutes the truncated lead with U+FFFD
                            // and consumes only the lead byte.
                            func.instruction(&Instruction::LocalGet(src_idx_local));
                            func.instruction(&Instruction::I32Const(3));
                            func.instruction(&Instruction::I32Add);
                            func.instruction(&Instruction::LocalGet(1));
                            func.instruction(&Instruction::I32GeU);
                            func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                            {
                                // Truncated 4-byte lead → U+FFFD.
                                emit_fffd_consume_lead(func);
                            }
                            func.instruction(&Instruction::Else);
                            {
                                // #251 case 1: validate all THREE continuation bytes.
                                push_byte_at(func, 1);
                                func.instruction(&Instruction::LocalSet(cont_local));
                                push_not_continuation(func);
                                push_byte_at(func, 2);
                                func.instruction(&Instruction::LocalSet(cont_local));
                                push_not_continuation(func);
                                func.instruction(&Instruction::I32Or);
                                push_byte_at(func, 3);
                                func.instruction(&Instruction::LocalSet(cont_local));
                                push_not_continuation(func);
                                func.instruction(&Instruction::I32Or);
                                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                                {
                                    // A continuation byte is not 10xxxxxx → U+FFFD.
                                    emit_fffd_consume_lead(func);
                                }
                                func.instruction(&Instruction::Else);
                                {
                                    // cp = (byte & 0x07) << 18 | (b1 & 0x3F) << 12 | (b2 & 0x3F) << 6 | (b3 & 0x3F)
                                    func.instruction(&Instruction::LocalGet(byte_local));
                                    func.instruction(&Instruction::I32Const(0x07));
                                    func.instruction(&Instruction::I32And);
                                    func.instruction(&Instruction::I32Const(18));
                                    func.instruction(&Instruction::I32Shl);
                                    // b1
                                    push_byte_at(func, 1);
                                    func.instruction(&Instruction::I32Const(0x3F));
                                    func.instruction(&Instruction::I32And);
                                    func.instruction(&Instruction::I32Const(12));
                                    func.instruction(&Instruction::I32Shl);
                                    func.instruction(&Instruction::I32Or);
                                    // b2
                                    push_byte_at(func, 2);
                                    func.instruction(&Instruction::I32Const(0x3F));
                                    func.instruction(&Instruction::I32And);
                                    func.instruction(&Instruction::I32Const(6));
                                    func.instruction(&Instruction::I32Shl);
                                    func.instruction(&Instruction::I32Or);
                                    // b3
                                    push_byte_at(func, 3);
                                    func.instruction(&Instruction::I32Const(0x3F));
                                    func.instruction(&Instruction::I32And);
                                    func.instruction(&Instruction::I32Or);
                                    func.instruction(&Instruction::LocalSet(cp_local));
                                    // #251 cases 3 & 5: reject overlong
                                    // (cp < 0x10000) and out-of-range
                                    // (cp > 0x10FFFF). overlong | oor.
                                    func.instruction(&Instruction::LocalGet(cp_local));
                                    func.instruction(&Instruction::I32Const(0x10000));
                                    func.instruction(&Instruction::I32LtU);
                                    func.instruction(&Instruction::LocalGet(cp_local));
                                    func.instruction(&Instruction::I32Const(0x10FFFF));
                                    func.instruction(&Instruction::I32GtU);
                                    func.instruction(&Instruction::I32Or);
                                    func.instruction(&Instruction::If(
                                        wasm_encoder::BlockType::Empty,
                                    ));
                                    {
                                        // Overlong or out-of-range → U+FFFD, consume lead.
                                        emit_fffd_consume_lead(func);
                                    }
                                    func.instruction(&Instruction::Else);
                                    {
                                        // Well-formed 4-byte. src_idx += 4.
                                        func.instruction(&Instruction::LocalGet(src_idx_local));
                                        func.instruction(&Instruction::I32Const(4));
                                        func.instruction(&Instruction::I32Add);
                                        func.instruction(&Instruction::LocalSet(src_idx_local));
                                    }
                                    func.instruction(&Instruction::End); // end 4-byte overlong/oor check
                                }
                                func.instruction(&Instruction::End); // end 4-byte continuation check
                            }
                            func.instruction(&Instruction::End); // end LS-P-19 (4-byte) check
                        }
                        func.instruction(&Instruction::End); // end 4-byte invalid-lead check
                    }
                    func.instruction(&Instruction::End); // end 3-byte vs 4-byte
                }
                func.instruction(&Instruction::End); // end 2-byte vs 3+byte
            }
            func.instruction(&Instruction::End); // end invalid-lead vs valid-multibyte
        }
        func.instruction(&Instruction::End); // end 1-byte vs 2+byte

        // --- Encode code_point as UTF-16 ---

        // if code_point < 0x10000: BMP, single code unit
        func.instruction(&Instruction::LocalGet(cp_local));
        func.instruction(&Instruction::I32Const(0x10000));
        func.instruction(&Instruction::I32LtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            // out[dst_idx * 2] = code_point as u16
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Shl);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Store16(dst_mem16));
            // dst_idx += 1
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(dst_idx_local));
        }
        func.instruction(&Instruction::Else);
        {
            // Supplementary plane: surrogate pair
            // high = 0xD800 + ((code_point - 0x10000) >> 10)
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Shl);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(0xD800));
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Const(0x10000));
            func.instruction(&Instruction::I32Sub);
            func.instruction(&Instruction::I32Const(10));
            func.instruction(&Instruction::I32ShrU);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Store16(dst_mem16));

            // low = 0xDC00 + ((code_point - 0x10000) & 0x3FF)
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Shl);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(2));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Const(0xDC00));
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Const(0x10000));
            func.instruction(&Instruction::I32Sub);
            func.instruction(&Instruction::I32Const(0x3FF));
            func.instruction(&Instruction::I32And);
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::I32Store16(dst_mem16));

            // dst_idx += 2 (two code units)
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(2));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(dst_idx_local));
        }
        func.instruction(&Instruction::End); // end BMP vs supplementary

        // Continue loop
        func.instruction(&Instruction::Br(0));

        func.instruction(&Instruction::End); // end loop
        func.instruction(&Instruction::End); // end block

        // Step 4: Call target with (out_ptr, code_unit_count, ...rest params)
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        for i in 2..param_count {
            func.instruction(&Instruction::LocalGet(i as u32));
        }
        func.instruction(&Instruction::Call(target_func));
    }

    /// Emit UTF-16 to UTF-8 transcoding
    ///
    /// Reads UTF-16 code units (2 bytes each), handles surrogate pairs for
    /// code points >= U+10000, and encodes as variable-length UTF-8 (1-4 bytes).
    ///
    /// Assumes params start with (ptr: i32, len: i32) where len is code unit count.
    /// Calls target with (out_ptr: i32, byte_len: i32, ...rest).
    fn emit_utf16_to_utf8_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        options: &AdapterOptions,
    ) {
        let callee_realloc = match options.callee_realloc {
            Some(idx) => idx,
            None => {
                log::warn!(
                    "UTF-16→UTF-8 transcode: no callee realloc, falling back to direct call"
                );
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
                return;
            }
        };

        // Scratch locals: src_idx (code units), dst_idx (bytes), out_ptr, cu, code_point
        let src_idx_local = param_count as u32;
        let dst_idx_local = param_count as u32 + 1;
        let out_ptr_local = param_count as u32 + 2;
        let cu_local = param_count as u32 + 3;
        let cp_local = param_count as u32 + 4;
        let cu2_local = param_count as u32 + 5;

        // Source reads (UTF-16) use caller_memory, destination writes (UTF-8) use callee_memory
        let src_mem16 = wasm_encoder::MemArg {
            offset: 0,
            align: 1,
            memory_index: options.caller_memory,
        };
        let dst_mem8 = wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: options.callee_memory,
        };

        // Step 1: Allocate output buffer = 3 * input_code_units bytes
        // (worst case: all BMP chars in U+0800-U+FFFF → 3 bytes UTF-8 each).
        // See LS-A-7: guard against i32.mul wrap (leg a) and cabi_realloc
        // OOM (leg b) before writing into callee memory.
        let callee_align = alignment_for_encoding(options.callee_string_encoding);
        func.instruction(&Instruction::LocalGet(1)); // input_len
        func.instruction(&Instruction::I32Const((u32::MAX / 3) as i32));
        func.instruction(&Instruction::I32GtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        func.instruction(&Instruction::I32Const(0)); // original_ptr
        func.instruction(&Instruction::I32Const(0)); // original_size
        func.instruction(&Instruction::I32Const(callee_align)); // alignment
        func.instruction(&Instruction::LocalGet(1)); // input_len (code units)
        func.instruction(&Instruction::I32Const(3));
        func.instruction(&Instruction::I32Mul); // alloc_size = 3 * code_units
        func.instruction(&Instruction::Call(callee_realloc));
        func.instruction(&Instruction::LocalSet(out_ptr_local));

        // Trap on null return from cabi_realloc (LS-A-7 leg b).
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::I32Eqz);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        // Step 2: Initialize loop counters
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(src_idx_local));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(dst_idx_local));

        // Step 3: Transcoding loop
        func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        // if src_idx >= input_len (code units), break
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::BrIf(1));

        // Read code unit: cu = mem16[ptr + src_idx * 2]
        func.instruction(&Instruction::LocalGet(0));
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Shl);
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Load16U(src_mem16));
        func.instruction(&Instruction::LocalSet(cu_local));

        // --- Detect surrogate pairs ---
        // if cu >= 0xD800 && cu < 0xDC00: high surrogate
        func.instruction(&Instruction::LocalGet(cu_local));
        func.instruction(&Instruction::I32Const(0xD800_u32 as i32));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::LocalGet(cu_local));
        func.instruction(&Instruction::I32Const(0xDC00_u32 as i32));
        func.instruction(&Instruction::I32LtU);
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            // LS-P-16: emit U+FFFD replacement when a lone high surrogate
            // sits at the last code unit of the input. Pre-v0.11, this site
            // trapped via `unreachable` (the conservative mitigation that
            // closed a 2-byte OOB read into adjacent caller linear memory).
            // The Canonical ABI's correct behaviour for malformed UTF-16 is
            // **lossy replacement**, not abort — so we now substitute the
            // lone high surrogate with the Unicode replacement character
            // U+FFFD (3-byte UTF-8 `EF BF BD`) and continue. The existing
            // 3-byte UTF-8 encoder below handles `cp = 0xFFFD` directly
            // (it lives in the BMP), so the only restructure here is to
            // turn the trap into an `If/Else`: when `src_idx + 1 >=
            // input_len`, take the replacement path; otherwise read the
            // low surrogate and compute the full code point.
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalGet(1));
            func.instruction(&Instruction::I32GeU);
            func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
            {
                // Lone high surrogate at end of input → U+FFFD replacement.
                func.instruction(&Instruction::I32Const(0xFFFD));
                func.instruction(&Instruction::LocalSet(cp_local));
                // Consume only the lone high surrogate.
                func.instruction(&Instruction::LocalGet(src_idx_local));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::LocalSet(src_idx_local));
            }
            func.instruction(&Instruction::Else);
            {
                // High surrogate with at least one more code unit available.
                // LS-P-16 (mid-string mitigation): validate that the next
                // unit is actually a low surrogate before treating this as a
                // pair. An unvalidated second unit (e.g. a high surrogate
                // followed by an ASCII char) underflows `cu2 - 0xDC00` and
                // yields a garbage code point that the 4-byte encoder writes
                // into callee memory (H-4.4 incorrect transcoding). The
                // Canonical ABI mandates lossy U+FFFD replacement instead.
                // cu2 = mem16[ptr + (src_idx + 1) * 2]
                func.instruction(&Instruction::LocalGet(0));
                func.instruction(&Instruction::LocalGet(src_idx_local));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::I32Shl);
                func.instruction(&Instruction::I32Add);
                func.instruction(&Instruction::I32Load16U(src_mem16));
                func.instruction(&Instruction::LocalSet(cu2_local));

                // is_low_surrogate = (cu2 >= 0xDC00) && (cu2 < 0xE000)
                func.instruction(&Instruction::LocalGet(cu2_local));
                func.instruction(&Instruction::I32Const(0xDC00_u32 as i32));
                func.instruction(&Instruction::I32GeU);
                func.instruction(&Instruction::LocalGet(cu2_local));
                func.instruction(&Instruction::I32Const(0xE000_u32 as i32));
                func.instruction(&Instruction::I32LtU);
                func.instruction(&Instruction::I32And);
                func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                {
                    // Valid surrogate pair:
                    // cp = 0x10000 + ((cu - 0xD800) << 10) + (cu2 - 0xDC00)
                    func.instruction(&Instruction::I32Const(0x10000));
                    func.instruction(&Instruction::LocalGet(cu_local));
                    func.instruction(&Instruction::I32Const(0xD800_u32 as i32));
                    func.instruction(&Instruction::I32Sub);
                    func.instruction(&Instruction::I32Const(10));
                    func.instruction(&Instruction::I32Shl);
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::LocalGet(cu2_local));
                    func.instruction(&Instruction::I32Const(0xDC00_u32 as i32));
                    func.instruction(&Instruction::I32Sub);
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::LocalSet(cp_local));
                    // src_idx += 2 (consume both units)
                    func.instruction(&Instruction::LocalGet(src_idx_local));
                    func.instruction(&Instruction::I32Const(2));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::LocalSet(src_idx_local));
                }
                func.instruction(&Instruction::Else);
                {
                    // Mid-string lone high surrogate → U+FFFD, consuming only
                    // the high surrogate so the next unit is reprocessed
                    // normally on the following iteration.
                    func.instruction(&Instruction::I32Const(0xFFFD));
                    func.instruction(&Instruction::LocalSet(cp_local));
                    func.instruction(&Instruction::LocalGet(src_idx_local));
                    func.instruction(&Instruction::I32Const(1));
                    func.instruction(&Instruction::I32Add);
                    func.instruction(&Instruction::LocalSet(src_idx_local));
                }
                func.instruction(&Instruction::End); // end low-surrogate validation
            }
            func.instruction(&Instruction::End); // end LS-P-16 lone-surrogate check
        }
        func.instruction(&Instruction::Else);
        {
            // Not a high surrogate. A lone LOW surrogate (cu in
            // [0xDC00, 0xE000)) cannot legitimately appear unpaired here —
            // the high-surrogate arm above consumes both halves of every
            // valid pair, so any low surrogate reaching this branch is
            // malformed input. Replace it with U+FFFD per the Canonical
            // ABI (#249) rather than emitting the malformed 3-byte UTF-8 of
            // a surrogate code point (ED B0 80 .. ED BF BF). Any other unit
            // is a genuine BMP scalar value, encoded directly. Either way
            // exactly one code unit is consumed.
            // cp = is_low_surrogate(cu) ? 0xFFFD : cu
            func.instruction(&Instruction::LocalGet(cu_local));
            func.instruction(&Instruction::I32Const(0xDC00_u32 as i32));
            func.instruction(&Instruction::I32GeU);
            func.instruction(&Instruction::LocalGet(cu_local));
            func.instruction(&Instruction::I32Const(0xE000_u32 as i32));
            func.instruction(&Instruction::I32LtU);
            func.instruction(&Instruction::I32And);
            func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
            {
                func.instruction(&Instruction::I32Const(0xFFFD));
                func.instruction(&Instruction::LocalSet(cp_local));
            }
            func.instruction(&Instruction::Else);
            {
                func.instruction(&Instruction::LocalGet(cu_local));
                func.instruction(&Instruction::LocalSet(cp_local));
            }
            func.instruction(&Instruction::End); // end lone-low-surrogate check
            // src_idx += 1
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(src_idx_local));
        }
        func.instruction(&Instruction::End); // end surrogate detection

        // --- Encode code_point as UTF-8 ---
        // Shared with the async param transcoder via the extracted free fn
        // (#272 inc 2) so both paths use one validated 1–4-byte encoder.
        emit_utf8_encode_codepoint(func, dst_mem8, out_ptr_local, dst_idx_local, cp_local);

        // Continue loop
        func.instruction(&Instruction::Br(0));

        func.instruction(&Instruction::End); // end loop
        func.instruction(&Instruction::End); // end block

        // Step 4: Call target with (out_ptr, byte_count, ...rest params)
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        for i in 2..param_count {
            func.instruction(&Instruction::LocalGet(i as u32));
        }
        func.instruction(&Instruction::Call(target_func));
    }

    /// Emit `latin1+utf16` → UTF-8 transcoding.
    ///
    /// meld models the canonical-ABI `latin1+utf16` encoding as
    /// [`StringEncoding::Latin1`]. The length operand (local 1) is **tagged**
    /// (see [`UTF16_TAG`]):
    /// - tag **clear** → the source is Latin-1 (1 byte/char); decode each byte
    ///   0x00–0xFF as code point U+0000–U+00FF and re-encode as UTF-8. This is
    ///   the path the pre-#253 implementation always took.
    /// - tag **set** → the source is UTF-16 (`count = len & !UTF16_TAG` code
    ///   units); the correct behaviour is a full UTF-16 → UTF-8 transcode
    ///   (surrogate pairs, lossy U+FFFD for malformed units — the exact
    ///   semantics of [`Self::emit_utf16_to_utf8_transcode`]).
    ///
    /// We dispatch at runtime on the tag. The two arms share the destination
    /// target call: each inner emitter reads the (now-masked) code count from
    /// local 1 and emits its own `Call(target_func)`, so the `If`/`Else` is two
    /// complete, self-contained sub-programs.
    fn emit_latin1_to_utf8_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        options: &AdapterOptions,
        block_ty: wasm_encoder::BlockType,
    ) {
        // Decode the tag, then rewrite local 1 to the *masked* count so the
        // inner emitters (which read local 1) see the untagged code/byte count.
        // tag_set := (len & UTF16_TAG) != 0 ; len := len & !UTF16_TAG
        let tag_local = param_count as u32; // reuse first scratch local
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32Const(UTF16_TAG));
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::LocalSet(tag_local));
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32Const(!UTF16_TAG));
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::LocalSet(1));

        func.instruction(&Instruction::LocalGet(tag_local));
        func.instruction(&Instruction::If(block_ty));
        {
            // Tag set: the latin1+utf16 source is UTF-16 — transcode as such.
            self.emit_utf16_to_utf8_transcode(func, param_count, target_func, options);
        }
        func.instruction(&Instruction::Else);
        {
            // Tag clear: pure Latin-1 source — the original 1-byte path.
            self.emit_latin1_pure_to_utf8_transcode(func, param_count, target_func, options);
        }
        func.instruction(&Instruction::End);
    }

    /// The tag-clear (pure Latin-1) leg of `latin1+utf16` → UTF-8.
    ///
    /// Latin-1 (ISO 8859-1) maps 1:1 to Unicode code points 0x00-0xFF.
    /// UTF-8 encoding: 0x00-0x7F → 1 byte, 0x80-0xFF → 2 bytes.
    /// Max output size = 2 * input length.
    ///
    /// Assumes params start with (ptr: i32, len: i32) where `len` is the
    /// (already tag-masked) Latin-1 byte count.
    fn emit_latin1_pure_to_utf8_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        options: &AdapterOptions,
    ) {
        let callee_realloc = match options.callee_realloc {
            Some(idx) => idx,
            None => {
                // No realloc available — fall back to direct call
                log::warn!(
                    "Latin-1→UTF-8 transcode: no callee realloc, falling back to direct call"
                );
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
                return;
            }
        };

        // Scratch locals start after the function's original params.
        // We use local indices: param_count+0 = src_idx, +1 = dst_idx,
        // +2 = out_ptr, +3 = byte
        let src_idx_local = param_count as u32;
        let dst_idx_local = param_count as u32 + 1;
        let out_ptr_local = param_count as u32 + 2;
        let byte_local = param_count as u32 + 3;

        // Source reads (Latin-1) use caller_memory, destination writes (UTF-8) use callee_memory
        let src_mem = wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: options.caller_memory,
        };
        let dst_mem = wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: options.callee_memory,
        };

        // Step 1: Allocate output buffer = 2 * input_len via cabi_realloc.
        // See LS-A-7: guard against i32.mul wrap (leg a) and cabi_realloc
        // OOM (leg b) before writing into callee memory.
        let callee_align = alignment_for_encoding(options.callee_string_encoding);
        func.instruction(&Instruction::LocalGet(1)); // input_len
        func.instruction(&Instruction::I32Const((u32::MAX / 2) as i32));
        func.instruction(&Instruction::I32GtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        func.instruction(&Instruction::I32Const(0)); // original_ptr
        func.instruction(&Instruction::I32Const(0)); // original_size
        func.instruction(&Instruction::I32Const(callee_align)); // alignment
        func.instruction(&Instruction::LocalGet(1)); // input_len
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Mul); // alloc_size = 2 * input_len
        func.instruction(&Instruction::Call(callee_realloc));
        func.instruction(&Instruction::LocalSet(out_ptr_local));

        // Trap on null return from cabi_realloc (LS-A-7 leg b).
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::I32Eqz);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        // Step 2: Initialize loop counters
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(src_idx_local));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(dst_idx_local));

        // Step 3: Transcoding loop
        func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        // if src_idx >= input_len, break
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::LocalGet(1)); // input_len
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::BrIf(1)); // br to outer block (done)

        // Read byte from source: memory[string_ptr + src_idx]
        func.instruction(&Instruction::LocalGet(0)); // string_ptr
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Load8U(src_mem));
        func.instruction(&Instruction::LocalSet(byte_local));

        // if byte < 0x80: ASCII — write single byte
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::I32Const(0x80));
        func.instruction(&Instruction::I32LtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));

        // ASCII path: out[dst_idx] = byte
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::I32Store8(dst_mem));
        // dst_idx += 1
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(dst_idx_local));

        func.instruction(&Instruction::Else);

        // Non-ASCII (0x80-0xFF): encode as 2-byte UTF-8
        // First byte: 0xC0 | (byte >> 6)
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Const(0xC0));
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::I32Const(6));
        func.instruction(&Instruction::I32ShrU);
        func.instruction(&Instruction::I32Or);
        func.instruction(&Instruction::I32Store8(dst_mem));

        // Second byte: 0x80 | (byte & 0x3F)
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Const(0x80));
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::I32Const(0x3F));
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::I32Or);
        func.instruction(&Instruction::I32Store8(dst_mem));

        // dst_idx += 2
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(dst_idx_local));

        func.instruction(&Instruction::End); // end if/else

        // src_idx += 1
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(src_idx_local));

        // Continue loop
        func.instruction(&Instruction::Br(0));

        func.instruction(&Instruction::End); // end loop
        func.instruction(&Instruction::End); // end block

        // Step 4: Call target with (out_ptr, dst_idx, ...rest params)
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(dst_idx_local));
        // Pass remaining params through
        for i in 2..param_count {
            func.instruction(&Instruction::LocalGet(i as u32));
        }
        func.instruction(&Instruction::Call(target_func));
    }

    /// Emit `latin1+utf16` → UTF-16 transcoding (#253).
    ///
    /// The source length operand (local 1) is **tagged** (see [`UTF16_TAG`]):
    /// - tag **clear** → the source is Latin-1; zero-extend each byte
    ///   0x00–0xFF to one UTF-16 code unit U+0000–U+00FF (the #253 increment-2
    ///   path, total and unambiguous).
    /// - tag **set** → the source is *already* UTF-16 (`count = len &
    ///   !UTF16_TAG` code units); the destination is UTF-16, so this is a
    ///   verbatim code-unit copy (2 bytes per unit, preserving surrogate pairs
    ///   byte-for-byte).
    ///
    /// We dispatch at runtime on the tag, masking local 1 to the code count
    /// first so the inner emitters see the untagged count.
    fn emit_latin1_to_utf16_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        options: &AdapterOptions,
        block_ty: wasm_encoder::BlockType,
    ) {
        let tag_local = param_count as u32; // reuse first scratch local
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32Const(UTF16_TAG));
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::LocalSet(tag_local));
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32Const(!UTF16_TAG));
        func.instruction(&Instruction::I32And);
        func.instruction(&Instruction::LocalSet(1));

        func.instruction(&Instruction::LocalGet(tag_local));
        func.instruction(&Instruction::If(block_ty));
        {
            // Tag set: source is UTF-16 already → verbatim code-unit copy.
            self.emit_utf16_verbatim_copy(func, param_count, target_func, options);
        }
        func.instruction(&Instruction::Else);
        {
            // Tag clear: pure Latin-1 → zero-extend each byte.
            self.emit_latin1_pure_to_utf16_transcode(func, param_count, target_func, options);
        }
        func.instruction(&Instruction::End);
    }

    /// Verbatim UTF-16 → UTF-16 code-unit copy across memories.
    ///
    /// Used by the `latin1+utf16` → UTF-16 transcoder when the source's tag
    /// bit is set (the source is already UTF-16). Copies `count` (local 1)
    /// code units = `2 * count` bytes from caller to callee memory, preserving
    /// surrogate pairs byte-for-byte. Calls target with (out_ptr, count,
    /// ...rest).
    fn emit_utf16_verbatim_copy(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        options: &AdapterOptions,
    ) {
        let callee_realloc = match options.callee_realloc {
            Some(idx) => idx,
            None => {
                log::warn!("UTF-16 verbatim copy: no callee realloc, falling back to direct call");
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
                return;
            }
        };

        // Scratch (after params): +1 = idx (code unit), +2 = out_ptr, +3 = cu.
        // (+0 holds the tag flag, set by the caller; do not reuse it.)
        let idx_local = param_count as u32 + 1;
        let out_ptr_local = param_count as u32 + 2;
        let cu_local = param_count as u32 + 3;

        let src_mem16 = wasm_encoder::MemArg {
            offset: 0,
            align: 1,
            memory_index: options.caller_memory,
        };
        let dst_mem16 = wasm_encoder::MemArg {
            offset: 0,
            align: 1,
            memory_index: options.callee_memory,
        };

        // Allocate 2 * count bytes (LS-A-7: wrap guard + OOM guard).
        let callee_align = alignment_for_encoding(options.callee_string_encoding);
        func.instruction(&Instruction::LocalGet(1)); // count
        func.instruction(&Instruction::I32Const((u32::MAX / 2) as i32));
        func.instruction(&Instruction::I32GtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::I32Const(callee_align));
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Mul);
        func.instruction(&Instruction::Call(callee_realloc));
        func.instruction(&Instruction::LocalSet(out_ptr_local));

        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::I32Eqz);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(idx_local));

        func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        func.instruction(&Instruction::LocalGet(idx_local));
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::BrIf(1));

        // cu = mem16[src_ptr + idx*2]
        func.instruction(&Instruction::LocalGet(0));
        func.instruction(&Instruction::LocalGet(idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Shl);
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Load16U(src_mem16));
        func.instruction(&Instruction::LocalSet(cu_local));

        // mem16[out_ptr + idx*2] = cu
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Shl);
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalGet(cu_local));
        func.instruction(&Instruction::I32Store16(dst_mem16));

        func.instruction(&Instruction::LocalGet(idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(idx_local));

        func.instruction(&Instruction::Br(0));
        func.instruction(&Instruction::End); // loop
        func.instruction(&Instruction::End); // block

        // Call target with (out_ptr, count, ...rest).
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(1));
        for i in 2..param_count {
            func.instruction(&Instruction::LocalGet(i as u32));
        }
        func.instruction(&Instruction::Call(target_func));
    }

    /// The tag-clear (pure Latin-1) leg of `latin1+utf16` → UTF-16.
    ///
    /// This direction is **total and unambiguous**: every Latin-1 byte
    /// 0x00–0xFF maps to exactly one UTF-16 code unit U+0000–U+00FF by
    /// zero-extension. There are no surrogates, no multi-unit forms, and no
    /// malformed inputs to reject — a u8 load is already the final code unit.
    /// The UTF-16 code-unit count therefore equals the Latin-1 byte count
    /// (1:1), and the output buffer is exactly `2 * byte_len` bytes.
    ///
    /// Assumes params start with (ptr: i32, byte_len: i32) where byte_len is
    /// the (tag-masked) Latin-1 byte count (== char count). Calls target with
    /// (out_ptr: i32, code_unit_count: i32, ...rest); code_unit_count ==
    /// byte_len.
    fn emit_latin1_pure_to_utf16_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        options: &AdapterOptions,
    ) {
        let callee_realloc = match options.callee_realloc {
            Some(idx) => idx,
            None => {
                // No realloc available — fall back to direct call.
                log::warn!(
                    "Latin-1→UTF-16 transcode: no callee realloc, falling back to direct call"
                );
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
                return;
            }
        };

        // Scratch locals start after the function's original params:
        //   param_count+0 = src_idx (also the destination code-unit index, 1:1)
        //   param_count+1 = out_ptr
        //   param_count+2 = byte
        // Stays within the shared scratch-local budget (param_count+0..+5).
        let src_idx_local = param_count as u32;
        let out_ptr_local = param_count as u32 + 1;
        let byte_local = param_count as u32 + 2;

        // Source reads (Latin-1, 1 byte) use caller_memory; destination writes
        // (UTF-16, 2 bytes per code unit) use callee_memory.
        let src_mem = wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: options.caller_memory,
        };
        let dst_mem16 = wasm_encoder::MemArg {
            offset: 0,
            align: 1,
            memory_index: options.callee_memory,
        };

        // Step 1: Allocate output buffer = 2 * byte_len via cabi_realloc (each
        // Latin-1 byte produces exactly one UTF-16 code unit = 2 bytes). See
        // LS-A-7: guard against i32.mul wrap (leg a) and cabi_realloc OOM
        // (leg b) before writing into callee memory.
        let callee_align = alignment_for_encoding(options.callee_string_encoding);
        func.instruction(&Instruction::LocalGet(1)); // byte_len
        func.instruction(&Instruction::I32Const((u32::MAX / 2) as i32));
        func.instruction(&Instruction::I32GtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        func.instruction(&Instruction::I32Const(0)); // original_ptr
        func.instruction(&Instruction::I32Const(0)); // original_size
        func.instruction(&Instruction::I32Const(callee_align)); // alignment
        func.instruction(&Instruction::LocalGet(1)); // byte_len
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Mul); // alloc_size = 2 * byte_len
        func.instruction(&Instruction::Call(callee_realloc));
        func.instruction(&Instruction::LocalSet(out_ptr_local));

        // Trap on null return from cabi_realloc (LS-A-7 leg b).
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::I32Eqz);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        // Step 2: Initialize loop counter.
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(src_idx_local));

        // Step 3: Transcoding loop over each source byte.
        func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        // if src_idx >= byte_len, break
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::LocalGet(1)); // byte_len
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::BrIf(1)); // br to outer block (done)

        // Read byte from source: memory[string_ptr + src_idx].
        // A u8 load is already zero-extended, so it IS the UTF-16 code unit.
        func.instruction(&Instruction::LocalGet(0)); // string_ptr
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::I32Load8U(src_mem));
        func.instruction(&Instruction::LocalSet(byte_local));

        // Store as a 16-bit code unit: out[src_idx * 2] = byte.
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Shl); // src_idx * 2
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalGet(byte_local));
        func.instruction(&Instruction::I32Store16(dst_mem16));

        // src_idx += 1
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Add);
        func.instruction(&Instruction::LocalSet(src_idx_local));

        // Continue loop
        func.instruction(&Instruction::Br(0));

        func.instruction(&Instruction::End); // end loop
        func.instruction(&Instruction::End); // end block

        // Step 4: Call target with (out_ptr, code_unit_count, ...rest params).
        // code_unit_count == byte_len (1:1 Latin-1 byte → UTF-16 code unit).
        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::LocalGet(1)); // byte_len == code_unit_count
        for i in 2..param_count {
            func.instruction(&Instruction::LocalGet(i as u32));
        }
        func.instruction(&Instruction::Call(target_func));
    }

    /// Emit UTF-8 → `latin1+utf16` transcoding (#253).
    ///
    /// `latin1+utf16` (meld's [`StringEncoding::Latin1`]) is the Component
    /// Model's compact representation: each string is EITHER pure Latin-1 (1
    /// byte/char, length operand tag-clear) OR UTF-16 (2 bytes/code-unit,
    /// length operand tagged with [`UTF16_TAG`]). This is therefore an
    /// *encoder*, not a lossy down-conversion — it represents every input.
    ///
    /// Two-phase:
    /// - **Phase A (scan):** decode the UTF-8 source; set `needs_utf16` if any
    ///   decoded code point exceeds 0xFF (malformed input decodes to U+FFFD,
    ///   which is > 0xFF, so it forces the UTF-16 representation).
    /// - **Phase B (write):**
    ///   - tag clear: decode again, write each code point as one Latin-1 byte;
    ///     length = char count (no tag).
    ///   - tag set: decode again, write UTF-16 (surrogate pairs for > 0xFFFF);
    ///     length = `code_units | UTF16_TAG`.
    ///
    /// Output buffer is `2 * byte_len` bytes (the UTF-16 worst case, which also
    /// bounds the Latin-1 case since char count ≤ byte_len). Mirrors the
    /// LS-A-7 realloc/OOM/overflow guards.
    fn emit_utf8_to_latin1_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        options: &AdapterOptions,
        block_ty: wasm_encoder::BlockType,
    ) {
        let callee_realloc = match options.callee_realloc {
            Some(idx) => idx,
            None => {
                log::warn!(
                    "UTF-8→latin1+utf16 transcode: no callee realloc, falling back to direct call"
                );
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
                return;
            }
        };

        // Locals: +0 src_idx, +1 flag/dst_idx, +2 out_ptr, +3 byte, +4 cp,
        // +5 cont. `flag` (needs_utf16) lives in +1 only during the scan; the
        // write phases re-use +1 as dst_idx.
        let src_idx_local = param_count as u32;
        let flag_local = param_count as u32 + 1;
        let dst_idx_local = param_count as u32 + 1;
        let out_ptr_local = param_count as u32 + 2;
        let byte_local = param_count as u32 + 3;
        let cp_local = param_count as u32 + 4;
        let cont_local = param_count as u32 + 5;

        let src_mem8 = wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: options.caller_memory,
        };
        let dst_mem8 = wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: options.callee_memory,
        };
        let dst_mem16 = wasm_encoder::MemArg {
            offset: 0,
            align: 1,
            memory_index: options.callee_memory,
        };

        // Allocate 2 * byte_len bytes (UTF-16 worst case; bounds Latin-1 too).
        let callee_align = alignment_for_encoding(options.callee_string_encoding);
        func.instruction(&Instruction::LocalGet(1)); // byte_len
        func.instruction(&Instruction::I32Const((u32::MAX / 2) as i32));
        func.instruction(&Instruction::I32GtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::I32Const(callee_align));
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Mul);
        func.instruction(&Instruction::Call(callee_realloc));
        func.instruction(&Instruction::LocalSet(out_ptr_local));

        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::I32Eqz);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        // --- Phase A: scan to decide latin1-vs-utf16. ---
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(flag_local)); // needs_utf16 = 0
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(src_idx_local));

        func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::BrIf(1));

        emit_utf8_decode_codepoint(
            func,
            src_mem8,
            0,
            src_idx_local,
            1,
            byte_local,
            cp_local,
            cont_local,
        );
        // if cp > 0xFF: needs_utf16 = 1
        func.instruction(&Instruction::LocalGet(cp_local));
        func.instruction(&Instruction::I32Const(0xFF));
        func.instruction(&Instruction::I32GtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::LocalSet(flag_local));
        func.instruction(&Instruction::End);

        func.instruction(&Instruction::Br(0));
        func.instruction(&Instruction::End); // loop
        func.instruction(&Instruction::End); // block

        // --- Phase B: write, branching on the flag. ---
        func.instruction(&Instruction::LocalGet(flag_local));
        func.instruction(&Instruction::If(block_ty));
        {
            // UTF-16 representation (tag set).
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::LocalSet(src_idx_local));
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::LocalSet(dst_idx_local));

            func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
            func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::LocalGet(1));
            func.instruction(&Instruction::I32GeU);
            func.instruction(&Instruction::BrIf(1));

            emit_utf8_decode_codepoint(
                func,
                src_mem8,
                0,
                src_idx_local,
                1,
                byte_local,
                cp_local,
                cont_local,
            );
            emit_utf16_encode_codepoint(func, dst_mem16, out_ptr_local, dst_idx_local, cp_local);

            func.instruction(&Instruction::Br(0));
            func.instruction(&Instruction::End); // loop
            func.instruction(&Instruction::End); // block

            // Call target with (out_ptr, code_units | UTF16_TAG, ...rest).
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(UTF16_TAG));
            func.instruction(&Instruction::I32Or);
            for i in 2..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
        }
        func.instruction(&Instruction::Else);
        {
            // Latin-1 representation (tag clear). cp <= 0xFF for all chars.
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::LocalSet(src_idx_local));
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::LocalSet(dst_idx_local));

            func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
            func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::LocalGet(1));
            func.instruction(&Instruction::I32GeU);
            func.instruction(&Instruction::BrIf(1));

            emit_utf8_decode_codepoint(
                func,
                src_mem8,
                0,
                src_idx_local,
                1,
                byte_local,
                cp_local,
                cont_local,
            );
            // out[dst_idx] = cp (one Latin-1 byte)
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Store8(dst_mem8));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(dst_idx_local));

            func.instruction(&Instruction::Br(0));
            func.instruction(&Instruction::End); // loop
            func.instruction(&Instruction::End); // block

            // Call target with (out_ptr, char_count, ...rest) — tag clear.
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            for i in 2..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
        }
        func.instruction(&Instruction::End); // end flag branch
    }

    /// Emit UTF-16 → `latin1+utf16` transcoding (#253).
    ///
    /// The mirror of [`Self::emit_utf8_to_latin1_transcode`] for a UTF-16
    /// source. The source length operand (local 1) is a code-unit count.
    /// Two-phase: scan the UTF-16 code units (decoding surrogate pairs and
    /// replacing lone surrogates with U+FFFD per the Canonical ABI) to decide
    /// latin1-vs-utf16; then write the chosen representation. The output buffer
    /// is `2 * code_units` bytes (the UTF-16-verbatim worst case).
    fn emit_utf16_to_latin1_transcode(
        &self,
        func: &mut Function,
        param_count: usize,
        target_func: u32,
        options: &AdapterOptions,
        block_ty: wasm_encoder::BlockType,
    ) {
        let callee_realloc = match options.callee_realloc {
            Some(idx) => idx,
            None => {
                log::warn!(
                    "UTF-16→latin1+utf16 transcode: no callee realloc, falling back to direct call"
                );
                for i in 0..param_count {
                    func.instruction(&Instruction::LocalGet(i as u32));
                }
                func.instruction(&Instruction::Call(target_func));
                return;
            }
        };

        // Locals: +0 src_idx (code units), +1 flag/dst_idx, +2 out_ptr,
        // +3 cu, +4 cp, +5 cu2.
        let src_idx_local = param_count as u32;
        let flag_local = param_count as u32 + 1;
        let dst_idx_local = param_count as u32 + 1;
        let out_ptr_local = param_count as u32 + 2;
        let cu_local = param_count as u32 + 3;
        let cp_local = param_count as u32 + 4;
        let cu2_local = param_count as u32 + 5;

        let src_mem16 = wasm_encoder::MemArg {
            offset: 0,
            align: 1,
            memory_index: options.caller_memory,
        };
        let dst_mem8 = wasm_encoder::MemArg {
            offset: 0,
            align: 0,
            memory_index: options.callee_memory,
        };
        let dst_mem16 = wasm_encoder::MemArg {
            offset: 0,
            align: 1,
            memory_index: options.callee_memory,
        };

        // Allocate 2 * code_units bytes.
        let callee_align = alignment_for_encoding(options.callee_string_encoding);
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32Const((u32::MAX / 2) as i32));
        func.instruction(&Instruction::I32GtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::I32Const(callee_align));
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32Const(2));
        func.instruction(&Instruction::I32Mul);
        func.instruction(&Instruction::Call(callee_realloc));
        func.instruction(&Instruction::LocalSet(out_ptr_local));

        func.instruction(&Instruction::LocalGet(out_ptr_local));
        func.instruction(&Instruction::I32Eqz);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Unreachable);
        func.instruction(&Instruction::End);

        // --- Phase A: scan to decide latin1-vs-utf16. ---
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(flag_local));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::LocalSet(src_idx_local));

        func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::LocalGet(src_idx_local));
        func.instruction(&Instruction::LocalGet(1));
        func.instruction(&Instruction::I32GeU);
        func.instruction(&Instruction::BrIf(1));

        emit_utf16_decode_codepoint(
            func,
            src_mem16,
            0,
            src_idx_local,
            1,
            cu_local,
            cp_local,
            cu2_local,
        );
        func.instruction(&Instruction::LocalGet(cp_local));
        func.instruction(&Instruction::I32Const(0xFF));
        func.instruction(&Instruction::I32GtU);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::LocalSet(flag_local));
        func.instruction(&Instruction::End);

        func.instruction(&Instruction::Br(0));
        func.instruction(&Instruction::End); // loop
        func.instruction(&Instruction::End); // block

        // --- Phase B: write, branching on the flag. ---
        func.instruction(&Instruction::LocalGet(flag_local));
        func.instruction(&Instruction::If(block_ty));
        {
            // UTF-16 representation (tag set). Re-decode and re-encode rather
            // than verbatim-copy so lone surrogates are normalised to U+FFFD
            // consistently with phase A's decision.
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::LocalSet(src_idx_local));
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::LocalSet(dst_idx_local));

            func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
            func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::LocalGet(1));
            func.instruction(&Instruction::I32GeU);
            func.instruction(&Instruction::BrIf(1));

            emit_utf16_decode_codepoint(
                func,
                src_mem16,
                0,
                src_idx_local,
                1,
                cu_local,
                cp_local,
                cu2_local,
            );
            emit_utf16_encode_codepoint(func, dst_mem16, out_ptr_local, dst_idx_local, cp_local);

            func.instruction(&Instruction::Br(0));
            func.instruction(&Instruction::End); // loop
            func.instruction(&Instruction::End); // block

            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(UTF16_TAG));
            func.instruction(&Instruction::I32Or);
            for i in 2..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
        }
        func.instruction(&Instruction::Else);
        {
            // Latin-1 representation (tag clear). cp <= 0xFF for all code points.
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::LocalSet(src_idx_local));
            func.instruction(&Instruction::I32Const(0));
            func.instruction(&Instruction::LocalSet(dst_idx_local));

            func.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
            func.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));
            func.instruction(&Instruction::LocalGet(src_idx_local));
            func.instruction(&Instruction::LocalGet(1));
            func.instruction(&Instruction::I32GeU);
            func.instruction(&Instruction::BrIf(1));

            emit_utf16_decode_codepoint(
                func,
                src_mem16,
                0,
                src_idx_local,
                1,
                cu_local,
                cp_local,
                cu2_local,
            );
            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalGet(cp_local));
            func.instruction(&Instruction::I32Store8(dst_mem8));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            func.instruction(&Instruction::I32Const(1));
            func.instruction(&Instruction::I32Add);
            func.instruction(&Instruction::LocalSet(dst_idx_local));

            func.instruction(&Instruction::Br(0));
            func.instruction(&Instruction::End); // loop
            func.instruction(&Instruction::End); // block

            func.instruction(&Instruction::LocalGet(out_ptr_local));
            func.instruction(&Instruction::LocalGet(dst_idx_local));
            for i in 2..param_count {
                func.instruction(&Instruction::LocalGet(i as u32));
            }
            func.instruction(&Instruction::Call(target_func));
        }
        func.instruction(&Instruction::End); // end flag branch
    }

    /// Resolve the target function index in the merged module
    fn resolve_target_function(&self, site: &AdapterSite, merged: &MergedModule) -> Result<u32> {
        // Look up the exported function's merged index using the original export index.
        // If the index is missing, this indicates a bug in the resolution or merging
        // pipeline -- we must not silently fall back to an arbitrary function (such as
        // index 0) because that would cause the adapter to call the wrong function at
        // runtime with no visible error.
        merged
            .function_index_map
            .get(&(site.to_component, site.to_module, site.export_func_idx))
            .copied()
            .ok_or_else(|| {
                crate::Error::AdapterGeneration(format!(
                    "Cannot resolve target function for adapter: {} -> {} \
                     (component={}, module={}, export_func_idx={}). \
                     The export may be missing or the function index map is incomplete.",
                    site.import_name,
                    site.export_name,
                    site.to_component,
                    site.to_module,
                    site.export_func_idx,
                ))
            })
    }

    /// Generate a callback-driving adapter for P3 async cross-component calls.
    ///
    /// Instead of canon lift/lower (which triggers call_might_be_recursive),
    /// the adapter drives the callee's `[async-lift]` + `[callback]` loop
    /// directly in core wasm. This emits the **single canonical trampoline
    /// shape** documented in [`crate::p3_async`] (see "Async-export callback
    /// trampoline"). The shape is the same regardless of which P3 built-ins
    /// the guest happens to use — `stream.read`, `future.read`,
    /// `task.wait`, etc. — because the trampoline only speaks to the
    /// callee through `[async-lift]` / `[callback]` and to the host
    /// through `[waitable-set-poll]`.
    ///
    /// Protocol:
    ///   1. Call `[async-lift]` entry → packed i32; low 4 bits =
    ///      [`crate::p3_async::callback::EXIT`] / `YIELD` / `WAIT` / `POLL`,
    ///      high 28 bits = waitable-set payload.
    ///   2. Loop: on `WAIT`/`POLL`, dispatch `[waitable-set-poll]`,
    ///      read the `(event_code, p1, p2)` tuple from scratch memory
    ///      (event codes per [`crate::p3_async::event`]), call `[callback]`.
    ///   3. After `EXIT`, read result globals written by the task.return
    ///      shim and return to the caller.
    fn generate_async_callback_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
    ) -> Result<AdapterFunction> {
        let name = format!(
            "$async_adapter_{}_to_{}",
            site.from_component, site.to_component
        );

        // Find the [async-lift] entry function's merged index
        let async_lift_func = self.resolve_target_function(site, merged)?;

        // Find the [callback] function's merged index by deriving its export name
        let callback_export_name = format!("[callback]{}", site.export_name);
        let callback_func = merged
            .exports
            .iter()
            .find(|e| e.kind == wasm_encoder::ExportKind::Func && e.name == callback_export_name)
            .map(|e| e.index)
            .ok_or_else(|| {
                crate::error::Error::EncodingError(format!(
                    "async adapter: cannot find callback export '{}' for '{}'",
                    callback_export_name, site.export_name,
                ))
            })?;

        // Find the waitable-set-poll host import. It's an unresolved import
        // from $root with name [waitable-set-poll] (possibly with $N suffix).
        let wsp_func = merged
            .imports
            .iter()
            .enumerate()
            .find(|(_, imp)| imp.name.starts_with("[waitable-set-poll]"))
            .map(|(i, _)| i as u32)
            .ok_or_else(|| {
                crate::error::Error::EncodingError(
                    "async adapter: cannot find [waitable-set-poll] import".to_string(),
                )
            })?;

        // Determine the caller's type (what the caller expects to call)
        let caller_type_idx = site
            .import_func_type_idx
            .and_then(|local_ti| {
                merged
                    .type_index_map
                    .get(&(site.from_component, site.from_module, local_ti))
                    .copied()
            })
            .unwrap_or(0);

        let caller_type = merged
            .types
            .get(caller_type_idx as usize)
            .cloned()
            .unwrap_or_else(|| crate::merger::MergedFuncType {
                params: Vec::new(),
                results: Vec::new(),
            });
        let caller_param_count = caller_type.params.len();
        let _caller_result_count = caller_type.results.len();

        // Find memory indices for cross-memory operations
        let callee_memory = crate::merger::component_memory_index(merged, site.to_component);
        let caller_memory = crate::merger::component_memory_index(merged, site.from_component);

        // Determine the [async-lift] entry's param count from its type.
        // The caller may have extra params (e.g., retptr for multi-value results)
        // that shouldn't be passed to the callee.
        let callee_param_count = merged
            .defined_func(async_lift_func)
            .and_then(|f| merged.types.get(f.type_idx as usize))
            .map(|t| t.params.len())
            .unwrap_or(caller_param_count);

        // Build the adapter function body
        //
        // Locals layout:
        //   0..caller_param_count: params from caller
        //   caller_param_count+0: $packed (i32) — packed return from entry/callback
        //   caller_param_count+1: $code (i32) — unpacked callback code
        //   caller_param_count+2: $payload (i32) — unpacked payload (waitable set idx)
        //   caller_param_count+3: $event_code (i32)
        //   caller_param_count+4: $p1 (i32)
        //   caller_param_count+5: $p2 (i32)
        let l_packed = caller_param_count as u32;
        let l_code = l_packed + 1;
        let l_payload = l_packed + 2;
        let l_event_code = l_packed + 3;
        let l_p1 = l_packed + 4;
        let l_p2 = l_packed + 5;

        // 6 locals for callback loop + 4 for string copy (src_ptr, src_len, dst_ptr, new_ptr)
        // + 6 for nested indirection patching (i, rec_dst, old_ptr, buf_len, new_ptr, rec_src)
        // + (#272 inc 1) the UTF-8→UTF-16 param transcode loop, which uses
        // `transcode_base ..= transcode_base+4` (src_idx, out_count, cp, byte,
        // cont) where `transcode_base = l_p2 + 16` — past the result-writeback
        // / nested-patch region so it cannot collide. That top index is
        // `l_p2 + 20 = caller_param_count + 25`, i.e. offset 25 into the local
        // block, so the block must declare 26 i32 locals (offsets 0..=25). The
        // budget was previously 22, leaving the four transcode tail locals
        // undeclared → the generated callback adapter failed wasm validation
        // ("unknown local 24") for exactly the inc-1 UTF-8→UTF-16 string-param
        // case (the stackful variant was sized correctly). #272 inc 1 fix.
        //
        // #272 inc 3 (RESULT-side transcode): the result-writeback transcode
        // REUSES the same `transcode_base = l_p2 + 16` block (offsets 21..=25,
        // already declared). The param transcode (step 0.5) and the result
        // transcode (step 3) are never simultaneously live, and that block does
        // not overlap the result-writeback/nested-patch region `l_p2 + 1 ..=
        // l_p2 + 10` (offsets 6..=15) live during step 3 — so no growth is
        // needed; top addressable index stays offset 25 < 26.
        //
        // #272 inc 4a (latin1-SOURCE param transcode): the
        // `Latin1 → UTF-8` tag-dispatch loop needs 6 scratch locals
        // (tag, src_idx, dst_idx, cp, cu, cu2) at `transcode_base = l_p2 + 16`,
        // i.e. offsets 21..=26 — one PAST the prior budget of 26. (`Latin1 →
        // UTF-16` needs only 4 — tag, idx, count, unit — offsets 21..=24, which
        // already fit.) The tag-set arm reuses the shared UTF-16 decoder, so it
        // needs `cu`/`cu2` on top of the byte/cp scratch the utf8↔utf16 loops
        // used. Grow the budget 26 → 27 so offset 26 is declared; the new tail
        // local sits past the prior budget, so nothing else uses it. Top
        // addressable index becomes offset 26 < 27 (proven by
        // `inc4a_callback_adapter_latin1_source_locals_within_budget`).
        //
        // #272 inc 4b (DEST-latin1 / tag-PRODUCING param transcode): the two
        // two-phase loops (`UTF-8 → latin1+utf16`, `UTF-16 → latin1+utf16`)
        // each use 6 scratch locals at `transcode_base = l_p2 + 16` (UTF-8:
        // flag, src_idx, dst_idx, byte, cp, cont; UTF-16: flag, src_idx,
        // dst_idx, cu, cp, cu2) — offsets 21..=26, the SAME six the inc-4a
        // `Latin1 → UTF-8` loop occupies. Two-phase needs one scan + two write
        // loops, but the scratch is reused across phases, so the per-loop scratch
        // count does not exceed 6. Top addressable index stays offset 26 < 27 —
        // the inc-4a budget already fits, no further growth. Proven by
        // `inc4b_callback_adapter_dest_latin1_locals_within_budget`.
        //
        // #272 inc 4c (latin1 RESULT-side transcode): the result-writeback REUSES
        // the SAME `transcode_base = l_p2 + 16` block for the FOUR latin1 result
        // directions (callee→caller), each using the same ≤ 6 scratch
        // (`l_p2 + 16 ..= l_p2 + 21`, offsets 21..=26) the inc-4a/4b PARAM loops
        // occupy. Param transcode (step 0.5) and result transcode (step 3) are
        // never simultaneously live, and offsets 21..=26 do not overlap the
        // result-writeback/nested region `l_p2 + 1 ..= l_p2 + 10` (offsets
        // 6..=15) live during step 3 — so NO growth; top index stays offset 26
        // < 27. Proven by
        // `inc4c_callback_adapter_latin1_result_locals_within_budget`.
        //
        // #272 inc 5a (NESTED `list<string>` RESULT transcode — SIMULTANEOUS
        // LIVENESS, the highest-risk budget case): the inner UTF-8 → UTF-16
        // transcode now runs INSIDE `emit_patch_nested_indirections`' per-element
        // loop, so the nested-loop locals AND the inner transcode-loop locals are
        // LIVE AT THE SAME TIME — unlike inc 3/4c where the result transcode and
        // the nested walk were mutually exclusive. The nested loop occupies
        // `scratch_base + 4 ..= scratch_base + 9` = `l_p2 + 5 ..= l_p2 + 10`
        // (offsets 10..=15, 6 locals: i, rec_dst, old_ptr, buf_len, new_ptr,
        // rec_src). The inner transcode uses `l_transcode_base = l_p2 + 16` for
        // its 5 scratch (offsets 21..=25) plus `l_new_ptr = l_p2 + 9` as the
        // out-ptr sink (already inside the nested region). The two regions are
        // DISJOINT (offsets 10..=15 vs 21..=25, gap at 16..=20), verified to not
        // overlap. Top index = `l_p2 + 20` = `caller_param_count + 25` = offset
        // 25 < 27 — so the existing budget already fits with NO growth. Proven
        // under the REAL adapter by
        // `inc5a_callback_adapter_nested_result_locals_within_budget`.
        let mut body = Function::new([(27, wasm_encoder::ValType::I32)]);

        // Step 0.5: copy string/list params from caller to callee memory.
        // Shared with the stackful emitter (SR-32, #140); see
        // `emit_param_copy_step` for the full contract.
        self.emit_param_copy_step(
            &mut body,
            site,
            merged,
            &caller_type,
            caller_param_count,
            callee_param_count,
            l_p2 + 4,
            l_p2 + 16,
        );

        // Step 1: Call [async-lift] entry with callee's params
        // (skip retptr if caller has more params than callee)
        for i in 0..callee_param_count {
            body.instruction(&Instruction::LocalGet(i as u32));
        }
        body.instruction(&Instruction::Call(async_lift_func));
        body.instruction(&Instruction::LocalSet(l_packed));

        // Unpack: code = packed & CODE_MASK, payload = packed >> PAYLOAD_SHIFT
        // (constants: see meld_core::p3_async::callback)
        body.instruction(&Instruction::LocalGet(l_packed));
        body.instruction(&Instruction::I32Const(crate::p3_async::callback::CODE_MASK));
        body.instruction(&Instruction::I32And);
        body.instruction(&Instruction::LocalSet(l_code));
        body.instruction(&Instruction::LocalGet(l_packed));
        body.instruction(&Instruction::I32Const(
            crate::p3_async::callback::PAYLOAD_SHIFT as i32,
        ));
        body.instruction(&Instruction::I32ShrU);
        body.instruction(&Instruction::LocalSet(l_payload));

        // Step 2: Callback-driving loop — single canonical shape per
        // meld_core::p3_async docs ("Async-export callback trampoline").
        // block $exit
        //   loop $drive
        //     if code == EXIT: break
        //     if code == WAIT: call waitable-set-poll
        //     else (YIELD): event = (EVENT_NONE, 0, 0)
        //     call callback(event_code, p1, p2)
        //     unpack result
        //     br $drive
        //   end
        // end
        body.instruction(&Instruction::Block(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::Loop(wasm_encoder::BlockType::Empty));

        // if code == EXIT (0): br $exit (block index 1)
        body.instruction(&Instruction::LocalGet(l_code));
        body.instruction(&Instruction::I32Eqz);
        body.instruction(&Instruction::BrIf(1)); // break to $exit block

        // if code == WAIT (2) OR code == POLL (3): call
        // waitable-set-poll(payload, event_ptr).
        // Use scratch space at address 0 in callee memory for the 3xi32 event tuple
        // (This is safe because the callee isn't running — we're driving it).
        // POLL is the non-blocking variant of WAIT against the same call;
        // both must dispatch to the host. LS-A-9: a previous version
        // matched only WAIT, silently treating POLL as YIELD which sent
        // (EVENT_NONE, 0, 0) to [callback] and dropped the event the host
        // had ready, producing semantic drift between fused and composed
        // modules.
        body.instruction(&Instruction::LocalGet(l_code));
        body.instruction(&Instruction::I32Const(crate::p3_async::callback::WAIT));
        body.instruction(&Instruction::I32Eq);
        body.instruction(&Instruction::LocalGet(l_code));
        body.instruction(&Instruction::I32Const(crate::p3_async::callback::POLL));
        body.instruction(&Instruction::I32Eq);
        body.instruction(&Instruction::I32Or);
        body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        {
            // waitable-set-poll(set_handle, event_ptr) → i32
            body.instruction(&Instruction::LocalGet(l_payload));
            body.instruction(&Instruction::I32Const(0)); // event result ptr (scratch)
            body.instruction(&Instruction::Call(wsp_func));
            body.instruction(&Instruction::Drop); // drop poll return value

            // Read event tuple from scratch memory: [event_code, p1, p2] at addr 0
            let mem_arg = wasm_encoder::MemArg {
                offset: 0,
                align: 2,
                memory_index: callee_memory,
            };
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Load(mem_arg));
            body.instruction(&Instruction::LocalSet(l_event_code));

            let mem_arg_4 = wasm_encoder::MemArg {
                offset: 4,
                align: 2,
                memory_index: callee_memory,
            };
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Load(mem_arg_4));
            body.instruction(&Instruction::LocalSet(l_p1));

            let mem_arg_8 = wasm_encoder::MemArg {
                offset: 8,
                align: 2,
                memory_index: callee_memory,
            };
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Load(mem_arg_8));
            body.instruction(&Instruction::LocalSet(l_p2));
        }
        body.instruction(&Instruction::Else);
        {
            // YIELD (1): set event to (EVENT_NONE, 0, 0)
            body.instruction(&Instruction::I32Const(crate::p3_async::event::NONE));
            body.instruction(&Instruction::LocalSet(l_event_code));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::LocalSet(l_p1));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::LocalSet(l_p2));
        }
        body.instruction(&Instruction::End); // end if WAIT/YIELD

        // Call callback(event_code, p1, p2) → packed i32
        body.instruction(&Instruction::LocalGet(l_event_code));
        body.instruction(&Instruction::LocalGet(l_p1));
        body.instruction(&Instruction::LocalGet(l_p2));
        body.instruction(&Instruction::Call(callback_func));
        body.instruction(&Instruction::LocalSet(l_packed));

        // Unpack new result (same scheme as initial unpack above)
        body.instruction(&Instruction::LocalGet(l_packed));
        body.instruction(&Instruction::I32Const(crate::p3_async::callback::CODE_MASK));
        body.instruction(&Instruction::I32And);
        body.instruction(&Instruction::LocalSet(l_code));
        body.instruction(&Instruction::LocalGet(l_packed));
        body.instruction(&Instruction::I32Const(
            crate::p3_async::callback::PAYLOAD_SHIFT as i32,
        ));
        body.instruction(&Instruction::I32ShrU);
        body.instruction(&Instruction::LocalSet(l_payload));

        body.instruction(&Instruction::Br(0)); // br $drive (loop)
        body.instruction(&Instruction::End); // end loop
        body.instruction(&Instruction::End); // end block

        // Step 3: After EXIT, read result values from shim globals.
        //
        // The task.return shim (generated in step 2.5) stored the result
        // values to globals when the callee called task.return during the
        // callback loop. Read them back and return to the caller.
        //
        // Find the matching shim by looking for task_return_shims entries
        // belonging to the callee component.
        // Match by function name: extract the func name from the
        // async-lift export name (after the last '#') and find the
        // shim with the matching original_func_name.
        let adapter_func_name = site
            .export_name
            .rsplit_once('#')
            .map(|(_, name)| name)
            .unwrap_or(&site.export_name);

        // Look up result globals. First try element-segment-based mapping
        // (correct for components with forwarding modules), then fall back
        // to name-based matching (for direct task.return calls).
        let result_globals_direct = merged
            .async_result_globals
            .get(&(site.to_component, adapter_func_name.to_string()));

        let shim_info = if let Some(globals) = result_globals_direct {
            // Recover the WIT result_type from the underlying shim. The
            // direct-globals lookup gives us per-(component, func) globals;
            // find the source shim by matching globals to get its type info.
            let result_type = merged
                .task_return_shims
                .values()
                .find(|info| {
                    info.component_idx == site.to_component && info.result_globals == *globals
                })
                .and_then(|info| info.result_type.clone());
            Some(crate::merger::TaskReturnShimInfo {
                shim_func: 0,
                result_globals: globals.clone(),
                component_idx: site.to_component,
                import_name: String::new(),
                original_func_name: adapter_func_name.to_string(),
                result_type,
            })
        } else {
            // Fallback: match by component + original function name
            merged
                .task_return_shims
                .values()
                .find(|info| {
                    info.component_idx == site.to_component
                        && info.original_func_name == adapter_func_name
                })
                .cloned()
        };
        let shim_info = shim_info.as_ref();

        // Detect retptr convention: caller has more params than callee
        // and returns void — the last caller param is the result pointer.
        let uses_retptr = caller_type.results.is_empty() && caller_param_count > callee_param_count;

        // Find caller's cabi_realloc for cross-memory string copying
        let caller_realloc = crate::merger::component_realloc_index(merged, site.from_component);
        log::debug!(
            "async adapter '{}' from={} to={} caller_realloc={:?} callee_mem={} caller_mem={}",
            adapter_func_name,
            site.from_component,
            site.to_component,
            caller_realloc,
            callee_memory,
            caller_memory,
        );

        if let Some(info) = shim_info {
            if uses_retptr {
                // Retptr convention: write results to caller's return area.
                // For (ptr, len) pairs that reference callee memory, copy
                // the data to caller memory first.
                let retptr_local = callee_param_count as u32;

                // Check if this is a pointer pair: exactly 2 i32 globals
                // and memories differ (cross-memory copy needed).
                let is_ptr_len_pair = info.result_globals.len() == 2
                    && info
                        .result_globals
                        .iter()
                        .all(|(_, t)| *t == wasm_encoder::ValType::I32)
                    && callee_memory != caller_memory
                    && caller_realloc.is_some();

                if is_ptr_len_pair {
                    // Shared helper handles realloc + memory.copy +
                    // nested-indirection walk + retptr writeback.
                    self.emit_ptr_pair_result_writeback(
                        &mut body,
                        info,
                        retptr_local,
                        caller_realloc.unwrap(),
                        caller_memory,
                        callee_memory,
                        l_p2 + 1,
                        // #272 inc 3: the result transcode's 5 scratch locals.
                        // SAME index passed to `emit_param_copy_step` above
                        // (`l_p2 + 16`) — the param transcode (step 0.5) and the
                        // result transcode (step 3) are never simultaneously
                        // live, and `l_p2 + 16 ..= l_p2 + 20` (block offsets
                        // 21..=25, declared by the budget of 26) does not
                        // overlap the writeback/nested region `l_p2 + 1 ..=
                        // l_p2 + 10` that IS live here.
                        l_p2 + 16,
                        site.requirements.caller_encoding,
                        site.requirements.callee_encoding,
                        // Result-side: governed by the callee's string encoding.
                        matches!(
                            site.requirements.callee_encoding,
                            Some(crate::parser::CanonStringEncoding::CompactUtf16)
                        ),
                    );
                } else {
                    // Non-pointer results: write globals directly to retptr
                    // with canonical-ABI alignment padding between fields.
                    self.emit_globals_to_retptr_cabi(
                        &mut body,
                        retptr_local,
                        &info.result_globals,
                        caller_memory,
                    );
                }
            } else {
                // Push result values onto the stack
                for (global_idx, _) in &info.result_globals {
                    body.instruction(&Instruction::GlobalGet(*global_idx));
                }
            }
        } else {
            // Fallback: return default values if no matching shim found
            for result_ty in &caller_type.results {
                match result_ty {
                    wasm_encoder::ValType::I32 => {
                        body.instruction(&Instruction::I32Const(0));
                    }
                    wasm_encoder::ValType::I64 => {
                        body.instruction(&Instruction::I64Const(0));
                    }
                    wasm_encoder::ValType::F32 => {
                        body.instruction(&Instruction::F32Const(0.0_f32.into()));
                    }
                    wasm_encoder::ValType::F64 => {
                        body.instruction(&Instruction::F64Const(0.0_f64.into()));
                    }
                    _ => {
                        body.instruction(&Instruction::I32Const(0));
                    }
                }
            }
        }

        body.instruction(&Instruction::End);

        let target_func = self.resolve_target_function(site, merged)?;

        Ok(AdapterFunction {
            name,
            type_idx: caller_type_idx,
            body,
            source_component: site.from_component,
            source_module: site.from_module,
            target_component: site.to_component,
            target_module: site.to_module,
            target_function: target_func,
            class: AdapterClass::Async,
        })
    }

    /// Step 0.5 of any async-lift adapter: copy `string` / `list<T>` params
    /// from caller memory into callee memory, allocating callee buffers via
    /// `cabi_realloc` and patching the caller's locals to point at the new
    /// callee-side buffers. Shared between callback and stackful emitters so
    /// the cross-memory contract has a single source of truth (SR-12,
    /// SR-17).
    ///
    /// `scratch_local` is the local index the helper uses to hold the
    /// realloc result. Callers must reserve at least one i32 local at that
    /// index. Both emitters allocate their local layout so the scratch sits
    /// just past the caller's params and per-emitter loop locals.
    ///
    /// `transcode_base` is the first of 5 DEDICATED i32 scratch locals
    /// (`transcode_base ..= transcode_base + 4`: src_idx, dst_idx/out_count,
    /// cp, byte, cont) the UTF-8 → UTF-16 transcode path (#272 inc 1) uses;
    /// they must not alias the param locals, `scratch_local`, or the
    /// result-writeback / nested-patch scratch. Same-encoding copies never
    /// touch them.
    #[allow(clippy::too_many_arguments)]
    fn emit_param_copy_step(
        &self,
        body: &mut Function,
        site: &AdapterSite,
        merged: &MergedModule,
        caller_type: &crate::merger::MergedFuncType,
        caller_param_count: usize,
        callee_param_count: usize,
        scratch_local: u32,
        transcode_base: u32,
    ) {
        // `pointer_pair_positions` from the resolver are flat indices into
        // the component-type param list, computed by
        // `pointer_pair_param_positions` walking the function's params with
        // `flat_count`. Canonical lowering preserves param order, so those
        // flat indices apply equally to the caller's lowered param locals
        // (the retptr the adapter inserts for results is appended after the
        // component-type params, so it never collides with a position from
        // this slice). LS-P-13: the previous code walked `caller_type.params`
        // looking for consecutive `(i32, i32)` slots and joined each with
        // `pointer_pair_positions.iter().any(|_| true)` — semantically
        // `!is_empty()`. Every adjacent integer-pair argument was then
        // treated as a (ptr, len) string/list and rewritten via
        // `cabi_realloc` + `memory.copy`, corrupting plain integer args at
        // the callee. Replaces that with the resolver's positions directly.
        let _ = (caller_type, caller_param_count, callee_param_count);
        let callee_realloc = crate::merger::component_realloc_index(merged, site.to_component);
        let callee_memory = crate::merger::component_memory_index(merged, site.to_component);
        let caller_memory = crate::merger::component_memory_index(merged, site.from_component);

        let caller_ptr_positions: Vec<u32> = if site.crosses_memory && callee_realloc.is_some() {
            site.requirements.pointer_pair_positions.clone()
        } else {
            Vec::new()
        };

        if caller_ptr_positions.is_empty() {
            return;
        }

        log::debug!(
            "async adapter param copy: export={} caller_positions={:?} resolver_positions={:?}",
            site.export_name,
            caller_ptr_positions,
            site.requirements.pointer_pair_positions,
        );
        let realloc = callee_realloc.unwrap();
        let param_layouts = &site.requirements.param_copy_layouts;
        for (pair_idx, &ptr_pos) in caller_ptr_positions.iter().enumerate() {
            let ptr_local = ptr_pos;
            let len_local = ptr_local + 1;
            let l_new_ptr = scratch_local;

            let byte_mult = param_layouts
                .get(pair_idx)
                .map(|cl| match cl {
                    crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier,
                    crate::resolver::CopyLayout::Elements { element_size, .. } => *element_size,
                })
                .unwrap_or(1);

            // Param-side (caller → callee) async copy. This path has no
            // `AdapterOptions`, but the governing caller string encoding is
            // carried by `site.requirements.caller_encoding`; CompactUtf16 is
            // the `latin1+utf16` encoding (mapped to `StringEncoding::Latin1`
            // by `canon_to_string_encoding`). A byte-granular buffer
            // (byte_mult == 1) in such a component is a tag-encoded string,
            // so mask/double its byte count; the forwarded length stays tagged.
            let is_compact_utf16 = matches!(
                site.requirements.caller_encoding,
                Some(crate::parser::CanonStringEncoding::CompactUtf16)
            ) && byte_mult == 1;
            let realloc_align = if is_compact_utf16 { 2 } else { 1 };

            // #272 inc 1: a TOP-LEVEL byte-granular (byte_mult == 1) string
            // param crossing memory from a UTF-8 caller to a UTF-16 callee is
            // TRANSCODED — UTF-8 bytes decoded to code points and re-encoded as
            // UTF-16 code units — rather than raw-copied (which would leave the
            // callee reading UTF-8 bytes as UTF-16 code units: the H-4.4 defect
            // the LS-F-27 guard otherwise fails loud on). Every other case
            // (same-encoding, other directions, nested strings, result strings)
            // is either handled by the raw-copy path below or rejected by
            // `guard_async_cross_encoding_strings`. The guard is narrowed in
            // lockstep so ONLY this combo reaches this branch.
            let transcode_utf8_to_utf16 = byte_mult == 1
                && matches!(
                    site.requirements.caller_encoding,
                    Some(crate::parser::CanonStringEncoding::Utf8)
                )
                && matches!(
                    site.requirements.callee_encoding,
                    Some(crate::parser::CanonStringEncoding::Utf16)
                );

            if transcode_utf8_to_utf16 {
                let src_mem8 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 0,
                    memory_index: caller_memory,
                };
                let dst_mem16 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 1,
                    memory_index: callee_memory,
                };
                emit_utf8_to_utf16_transcode_param(
                    body,
                    realloc,
                    src_mem8,
                    dst_mem16,
                    ptr_local,
                    len_local,
                    l_new_ptr,
                    transcode_base,     // src_idx
                    transcode_base + 1, // dst_idx / out code-unit count
                    transcode_base + 2, // cp
                    transcode_base + 3, // byte
                    transcode_base + 4, // cont
                );
                continue;
            }

            // #272 inc 2: the REVERSE direction — a TOP-LEVEL byte-granular
            // (byte_mult == 1) string param crossing memory from a UTF-16
            // caller to a UTF-8 callee is TRANSCODED (UTF-16 code units decoded
            // to code points and re-encoded as UTF-8 bytes) rather than
            // raw-copied (which would leave the callee reading UTF-16 code
            // units as UTF-8 bytes — the H-4.4 defect). The guard is narrowed
            // in lockstep so ONLY this combo (in addition to inc 1's) reaches
            // this branch.
            let transcode_utf16_to_utf8 = byte_mult == 1
                && matches!(
                    site.requirements.caller_encoding,
                    Some(crate::parser::CanonStringEncoding::Utf16)
                )
                && matches!(
                    site.requirements.callee_encoding,
                    Some(crate::parser::CanonStringEncoding::Utf8)
                );

            if transcode_utf16_to_utf8 {
                let src_mem16 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 1,
                    memory_index: caller_memory,
                };
                let dst_mem8 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 0,
                    memory_index: callee_memory,
                };
                emit_utf16_to_utf8_transcode_param(
                    body,
                    realloc,
                    1, // realloc align (utf-8 callee, byte-granular)
                    src_mem16,
                    dst_mem8,
                    ptr_local,
                    len_local,
                    l_new_ptr,
                    transcode_base,     // src_idx (code units)
                    transcode_base + 1, // dst_idx / out byte count
                    transcode_base + 2, // cp
                    transcode_base + 3, // cu
                    transcode_base + 4, // cu2
                );
                continue;
            }

            // #272 inc 4a: a TOP-LEVEL byte-granular string param crossing
            // memory from a `latin1+utf16` (CompactUtf16) caller to a UTF-16 or
            // UTF-8 callee is TRANSCODED with runtime tag dispatch (the
            // CompactUtf16 length operand is tag-encoded: tag-clear → Latin-1
            // source, tag-set → UTF-16 source). A raw copy would leave the
            // callee reading the tagged operand and tag-set UTF-16 bytes with
            // the wrong shape (the H-4.4 defect the LS-F-27 guard otherwise
            // fails loud on). The DEST-latin1 directions (X → CompactUtf16) are
            // a later sub-increment and still fail loud. The guard is narrowed
            // in lockstep so ONLY these combos (plus inc 1/2) reach this branch.
            let caller_is_latin1 = matches!(
                site.requirements.caller_encoding,
                Some(crate::parser::CanonStringEncoding::CompactUtf16)
            );
            let transcode_latin1_to_utf16 = byte_mult == 1
                && caller_is_latin1
                && matches!(
                    site.requirements.callee_encoding,
                    Some(crate::parser::CanonStringEncoding::Utf16)
                );
            let transcode_latin1_to_utf8 = byte_mult == 1
                && caller_is_latin1
                && matches!(
                    site.requirements.callee_encoding,
                    Some(crate::parser::CanonStringEncoding::Utf8)
                );

            if transcode_latin1_to_utf16 {
                // Source reads are Latin-1 (1 byte) on the tag-clear arm or
                // UTF-16 (2 bytes) on the tag-set arm — both from caller memory.
                let src_mem8 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 0,
                    memory_index: caller_memory,
                };
                let src_mem16 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 1,
                    memory_index: caller_memory,
                };
                let dst_mem16 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 1,
                    memory_index: callee_memory,
                };
                emit_latin1_to_utf16_transcode_param(
                    body,
                    realloc,
                    src_mem8,
                    src_mem16,
                    dst_mem16,
                    ptr_local,
                    len_local,
                    l_new_ptr,
                    transcode_base,     // tag
                    transcode_base + 1, // idx
                    transcode_base + 2, // count
                    transcode_base + 3, // unit
                );
                continue;
            }

            if transcode_latin1_to_utf8 {
                let src_mem8 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 0,
                    memory_index: caller_memory,
                };
                let src_mem16 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 1,
                    memory_index: caller_memory,
                };
                let dst_mem8 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 0,
                    memory_index: callee_memory,
                };
                emit_latin1_to_utf8_transcode_param(
                    body,
                    realloc,
                    1, // realloc align (utf-8 callee, byte-granular)
                    src_mem8,
                    src_mem16,
                    dst_mem8,
                    ptr_local,
                    len_local,
                    l_new_ptr,
                    transcode_base,     // tag
                    transcode_base + 1, // src_idx
                    transcode_base + 2, // dst_idx / out byte count
                    transcode_base + 3, // cp
                    transcode_base + 4, // cu
                    transcode_base + 5, // cu2
                );
                continue;
            }

            // #272 inc 4b: a TOP-LEVEL byte-granular string param crossing
            // memory from a UTF-8 or UTF-16 caller to a `latin1+utf16`
            // (CompactUtf16) callee is TRANSCODED two-phase (scan the source to
            // decide latin1-vs-utf16, then write the chosen representation with
            // the [`UTF16_TAG`]-tagged length). These are the two DEST-latin1 /
            // tag-PRODUCING directions that completed the latin1 tail (the
            // latin1-SOURCE directions landed in inc 4a). A raw copy would leave
            // the callee reading an untagged length + the wrong byte shape (the
            // H-4.4 defect the LS-F-27 guard otherwise fails loud on). Result-
            // side latin1 and nested strings are later sub-increments and still
            // fail loud. The guard is narrowed in lockstep so ONLY these combos
            // (plus inc 1/2/4a) reach this branch.
            let callee_is_latin1 = matches!(
                site.requirements.callee_encoding,
                Some(crate::parser::CanonStringEncoding::CompactUtf16)
            );
            let transcode_utf8_to_latin1 = byte_mult == 1
                && callee_is_latin1
                && matches!(
                    site.requirements.caller_encoding,
                    Some(crate::parser::CanonStringEncoding::Utf8)
                );
            let transcode_utf16_to_latin1 = byte_mult == 1
                && callee_is_latin1
                && matches!(
                    site.requirements.caller_encoding,
                    Some(crate::parser::CanonStringEncoding::Utf16)
                );

            if transcode_utf8_to_latin1 {
                // Source is UTF-8 (caller mem); dest is latin1+utf16: the
                // tag-clear arm writes Latin-1 bytes (1 byte), the tag-set arm
                // writes UTF-16 code units (2 bytes) — both into callee mem.
                let src_mem8 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 0,
                    memory_index: caller_memory,
                };
                let dst_mem8 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 0,
                    memory_index: callee_memory,
                };
                let dst_mem16 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 1,
                    memory_index: callee_memory,
                };
                emit_utf8_to_latin1_transcode_param(
                    body,
                    realloc,
                    2, // realloc align (latin1+utf16 callee, utf16-worst-case)
                    src_mem8,
                    dst_mem8,
                    dst_mem16,
                    ptr_local,
                    len_local,
                    l_new_ptr,
                    transcode_base,     // flag (needs_utf16)
                    transcode_base + 1, // src_idx
                    transcode_base + 2, // dst_idx
                    transcode_base + 3, // byte
                    transcode_base + 4, // cp
                    transcode_base + 5, // cont
                );
                continue;
            }

            if transcode_utf16_to_latin1 {
                let src_mem16 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 1,
                    memory_index: caller_memory,
                };
                let dst_mem8 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 0,
                    memory_index: callee_memory,
                };
                let dst_mem16 = wasm_encoder::MemArg {
                    offset: 0,
                    align: 1,
                    memory_index: callee_memory,
                };
                emit_utf16_to_latin1_transcode_param(
                    body,
                    realloc,
                    2, // realloc align (latin1+utf16 callee, utf16-worst-case)
                    src_mem16,
                    dst_mem8,
                    dst_mem16,
                    ptr_local,
                    len_local,
                    l_new_ptr,
                    transcode_base,     // flag (needs_utf16)
                    transcode_base + 1, // src_idx
                    transcode_base + 2, // dst_idx
                    transcode_base + 3, // cu
                    transcode_base + 4, // cp
                    transcode_base + 5, // cu2
                );
                continue;
            }

            // Allocate: cabi_realloc(0, 0, align, <byte count>)
            emit_overflow_guard(body, len_local, byte_mult);
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Const(realloc_align));
            emit_copy_byte_count(body, len_local, byte_mult, is_compact_utf16);
            emit_checked_realloc(body, realloc, l_new_ptr);

            // Copy: memory.copy new_ptr <- old_ptr, <byte count>
            body.instruction(&Instruction::LocalGet(l_new_ptr));
            body.instruction(&Instruction::LocalGet(ptr_local));
            emit_copy_byte_count(body, len_local, byte_mult, is_compact_utf16);
            body.instruction(&Instruction::MemoryCopy {
                dst_mem: callee_memory,
                src_mem: caller_memory,
            });

            // Replace the ptr param with the new callee-memory ptr
            body.instruction(&Instruction::LocalGet(l_new_ptr));
            body.instruction(&Instruction::LocalSet(ptr_local));
        }
    }

    /// Return true if a `[callback]<export>` companion export exists in the
    /// merged module. The Component Model spec attaches `(callback ...)` to a
    /// canonical lift to opt into callback-mode async; meld surfaces that
    /// option as a sibling export so the adapter can find the callback by
    /// name. Absence of the companion means the canonical used stackful
    /// lifting (SR-32, #140).
    fn has_callback_export(&self, site: &AdapterSite, merged: &MergedModule) -> bool {
        let callback_export_name = format!("[callback]{}", site.export_name);
        merged
            .exports
            .iter()
            .any(|e| e.kind == wasm_encoder::ExportKind::Func && e.name == callback_export_name)
    }

    /// Emit the cross-memory writeback for an async-lift result that is a
    /// `(ptr, len)` pair (string / list<T>). Allocates a buffer in caller
    /// memory via `cabi_realloc`, copies the source bytes from callee
    /// memory, walks nested indirections if the list element type
    /// contains them, and writes `(new_ptr, len)` to the caller's retptr.
    ///
    /// Shared between callback and stackful async-lift emitters so the
    /// cross-memory contract has a single source of truth (SR-12 /
    /// SR-17). The caller must reserve at least 4 consecutive scratch
    /// i32 locals starting at `scratch_base`, plus the 6 locals
    /// `emit_patch_nested_indirections` consumes starting at
    /// `scratch_base + 4`.
    ///
    /// `transcode_base` is the first of 5 DEDICATED i32 scratch locals
    /// (`transcode_base ..= transcode_base + 4`) the #272 inc-3 RESULT
    /// transcode path uses (src_idx, dst_idx/out_count, cp, + two decode/encode
    /// scratch). They must not alias the param locals, `scratch_base ..
    /// scratch_base + 9` (the writeback + nested-patch region that IS live
    /// during this call), or the retptr local. Both async emitters pass the
    /// SAME local index they pass to `emit_param_copy_step` as its
    /// `transcode_base`: the param-side transcode runs in step 0.5 (before the
    /// lift call) and the result-side transcode runs in step 3 (after it), so
    /// those locals are never simultaneously live and may be shared. The
    /// same-encoding raw-copy + compact-utf16 path never touches them.
    ///
    /// `caller_encoding` / `callee_encoding` are the raw canon string
    /// encodings. A RESULT string is PRODUCED by the callee (in
    /// `callee_encoding`) and READ by the caller (in `caller_encoding`), so the
    /// result transcode direction is `callee_enc → caller_enc` — the REVERSE of
    /// the param side. When the result is a TOP-LEVEL byte-granular string and
    /// that direction is UTF-8 → UTF-16 or UTF-16 → UTF-8 (#272 inc 3), the raw
    /// `memory.copy` is replaced by the matching transcode loop (SOURCE =
    /// callee memory, DEST = caller memory) and the OUTPUT code-unit/byte count
    /// — not the source length — is written to the retptr. Everything else
    /// keeps the raw-copy + compact-utf16 tag path; the guard
    /// `guard_async_cross_encoding_strings` fails loud on any direction this
    /// branch does not transcode.
    #[allow(clippy::too_many_arguments)]
    fn emit_ptr_pair_result_writeback(
        &self,
        body: &mut Function,
        info: &crate::merger::TaskReturnShimInfo,
        retptr_local: u32,
        caller_realloc_func: u32,
        caller_memory: u32,
        callee_memory: u32,
        scratch_base: u32,
        transcode_base: u32,
        caller_encoding: Option<crate::parser::CanonStringEncoding>,
        callee_encoding: Option<crate::parser::CanonStringEncoding>,
        // True when the *callee* string encoding is `latin1+utf16`
        // (CompactUtf16). A byte-granular result buffer (`elem_size == 1`,
        // i.e. a top-level `string`) then carries a tag-encoded length whose
        // byte count must be masked/doubled. The len written back to the
        // retptr stays tagged. #253.
        callee_compact_utf16: bool,
    ) {
        let (ptr_global, _) = info.result_globals[0];
        let (len_global, _) = info.result_globals[1];

        // Determine the per-element byte size and alignment from the
        // WIT result type. For string the element is 1 byte; for
        // list<u32> it's 4; for list<record{...}> it's the record's
        // CABI size. Without a known type we fall back to 1 (string-
        // like).
        let (elem_size, elem_align, list_elem_ty) = match &info.result_type {
            Some(crate::parser::ComponentValType::List(elem))
            | Some(crate::parser::ComponentValType::FixedSizeList(elem, _)) => {
                let (s, a) = cabi_size_align(elem);
                (s, a, Some(elem.as_ref().clone()))
            }
            Some(crate::parser::ComponentValType::String) => (1, 1, None),
            _ => (1, 1, None),
        };

        let l_src_ptr = scratch_base;
        let l_src_len = scratch_base + 1;
        let l_dst_ptr = scratch_base + 2;
        let l_byte_count = scratch_base + 3;

        // Read source ptr and len from shim globals
        body.instruction(&Instruction::GlobalGet(ptr_global));
        body.instruction(&Instruction::LocalSet(l_src_ptr));
        body.instruction(&Instruction::GlobalGet(len_global));
        body.instruction(&Instruction::LocalSet(l_src_len));

        // #272 inc 3: a TOP-LEVEL byte-granular RESULT string crossing memory
        // is TRANSCODED, for the utf8↔utf16 directions, instead of raw-copied.
        //
        // DIRECTION SUBTLETY: a result string is PRODUCED BY THE CALLEE (in
        // `callee_encoding`) and READ BY THE CALLER (in `caller_encoding`), so
        // the result transcode direction is `callee_enc → caller_enc` — the
        // REVERSE of the param side (caller_enc → callee_enc). SOURCE = callee
        // memory (where the callee wrote the result), DEST = caller memory
        // (where the caller reads it).
        //   * callee Utf8  → caller Utf16  ⇒ emit_utf8_to_utf16_transcode_param
        //   * callee Utf16 → caller Utf8   ⇒ emit_utf16_to_utf8_transcode_param
        // A nested result (`list<string>`, so `list_elem_ty.is_some()`), a
        // latin1/CompactUtf16 direction, or a non-byte-granular result keeps
        // the raw-copy + compact-utf16 tag path below; the guard fails loud on
        // any cross-encoding result this branch does not transcode. The
        // top-level string is exactly `elem_size == 1 && list_elem_ty.is_none()`
        // (a top-level `string` result, or the `None`/unknown fallback).
        let top_level_byte_string = elem_size == 1 && list_elem_ty.is_none();
        let result_transcode_utf8_to_utf16 = top_level_byte_string
            && matches!(
                callee_encoding,
                Some(crate::parser::CanonStringEncoding::Utf8)
            )
            && matches!(
                caller_encoding,
                Some(crate::parser::CanonStringEncoding::Utf16)
            );
        let result_transcode_utf16_to_utf8 = top_level_byte_string
            && matches!(
                callee_encoding,
                Some(crate::parser::CanonStringEncoding::Utf16)
            )
            && matches!(
                caller_encoding,
                Some(crate::parser::CanonStringEncoding::Utf8)
            );

        // #272 inc 4c: the FOUR latin1 (CompactUtf16) RESULT directions —
        // mirroring the inc-4a/4b latin1 PARAM directions but `callee → caller`
        // (a result is produced by the callee, read by the caller). SOURCE =
        // callee memory, DEST = caller memory, realloc in CALLER memory via
        // `caller_realloc_func`. Each calls the matching already-runtime-verified
        // loop fn (inc 4a/4b); the loop fn does its OWN realloc internally (the
        // writeback does NOT pre-size), rewrites `l_src_ptr` → out_ptr and
        // `l_src_len` → the (possibly tagged) OUTPUT length, and `out_ptr_local =
        // l_dst_ptr` keeps the `(l_dst_ptr, l_src_len)` retptr write below
        // correct.
        //   * callee CompactUtf16 → caller Utf16 ⇒ emit_latin1_to_utf16 (2*count)
        //   * callee CompactUtf16 → caller Utf8  ⇒ emit_latin1_to_utf8  (3*count)
        //   * callee Utf8  → caller CompactUtf16 ⇒ emit_utf8_to_latin1  (2*len)
        //   * callee Utf16 → caller CompactUtf16 ⇒ emit_utf16_to_latin1 (2*len)
        let callee_is_latin1 = matches!(
            callee_encoding,
            Some(crate::parser::CanonStringEncoding::CompactUtf16)
        );
        let caller_is_latin1 = matches!(
            caller_encoding,
            Some(crate::parser::CanonStringEncoding::CompactUtf16)
        );
        let result_transcode_latin1_to_utf16 = top_level_byte_string
            && callee_is_latin1
            && matches!(
                caller_encoding,
                Some(crate::parser::CanonStringEncoding::Utf16)
            );
        let result_transcode_latin1_to_utf8 = top_level_byte_string
            && callee_is_latin1
            && matches!(
                caller_encoding,
                Some(crate::parser::CanonStringEncoding::Utf8)
            );
        let result_transcode_utf8_to_latin1 = top_level_byte_string
            && caller_is_latin1
            && matches!(
                callee_encoding,
                Some(crate::parser::CanonStringEncoding::Utf8)
            );
        let result_transcode_utf16_to_latin1 = top_level_byte_string
            && caller_is_latin1
            && matches!(
                callee_encoding,
                Some(crate::parser::CanonStringEncoding::Utf16)
            );

        if result_transcode_utf8_to_utf16 {
            // SOURCE = callee memory (UTF-8 bytes), DEST = caller memory
            // (UTF-16 code units). Realloc worst case 2*len bytes (each UTF-8
            // byte → ≤ 1 UTF-16 code unit) — handled by the loop fn (align 2,
            // overflow guard). The loop rewrites `l_src_ptr` → out_ptr (caller
            // mem) and `l_src_len` → output UTF-16 code-unit count; passing
            // `out_ptr_local = l_dst_ptr` makes `l_dst_ptr` hold that out_ptr
            // too, so the existing `(l_dst_ptr, l_src_len)` retptr write below
            // forwards the transcoded pointer + OUTPUT length.
            let src_mem8 = wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: callee_memory,
            };
            let dst_mem16 = wasm_encoder::MemArg {
                offset: 0,
                align: 1,
                memory_index: caller_memory,
            };
            emit_utf8_to_utf16_transcode_param(
                body,
                caller_realloc_func,
                src_mem8,
                dst_mem16,
                l_src_ptr,
                l_src_len,
                l_dst_ptr,
                transcode_base,     // src_idx
                transcode_base + 1, // dst_idx / out code-unit count
                transcode_base + 2, // cp
                transcode_base + 3, // byte
                transcode_base + 4, // cont
            );
        } else if result_transcode_utf16_to_utf8 {
            // SOURCE = callee memory (UTF-16 code units), DEST = caller memory
            // (UTF-8 bytes). Realloc worst case 3*len bytes (≤ 3 UTF-8 bytes
            // per UTF-16 code unit) — handled by the loop fn (align 1, overflow
            // guard). The loop rewrites `l_src_ptr` → out_ptr and `l_src_len` →
            // output UTF-8 byte count; `out_ptr_local = l_dst_ptr` keeps the
            // retptr write below correct.
            let src_mem16 = wasm_encoder::MemArg {
                offset: 0,
                align: 1,
                memory_index: callee_memory,
            };
            let dst_mem8 = wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: caller_memory,
            };
            emit_utf16_to_utf8_transcode_param(
                body,
                caller_realloc_func,
                1, // realloc align (utf-8 caller, byte-granular)
                src_mem16,
                dst_mem8,
                l_src_ptr,
                l_src_len,
                l_dst_ptr,
                transcode_base,     // src_idx (code units)
                transcode_base + 1, // dst_idx / out byte count
                transcode_base + 2, // cp
                transcode_base + 3, // cu
                transcode_base + 4, // cu2
            );
        } else if result_transcode_latin1_to_utf16 {
            // callee CompactUtf16 → caller Utf16. SOURCE = callee memory (a
            // tag-encoded latin1+utf16 buffer; tag-clear → Latin-1 bytes,
            // tag-set → verbatim UTF-16 code units), DEST = caller memory
            // (UTF-16). `l_src_len` holds the TAGGED source length; the loop
            // masks it and rewrites `l_src_len` to the UNTAGGED output code-unit
            // count. The loop reallocs internally (2*count, align 2). 4 scratch.
            let src_mem8 = wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: callee_memory,
            };
            let src_mem16 = wasm_encoder::MemArg {
                offset: 0,
                align: 1,
                memory_index: callee_memory,
            };
            let dst_mem16 = wasm_encoder::MemArg {
                offset: 0,
                align: 1,
                memory_index: caller_memory,
            };
            emit_latin1_to_utf16_transcode_param(
                body,
                caller_realloc_func,
                src_mem8,
                src_mem16,
                dst_mem16,
                l_src_ptr,
                l_src_len,
                l_dst_ptr,
                transcode_base,     // tag
                transcode_base + 1, // idx
                transcode_base + 2, // count
                transcode_base + 3, // unit
            );
        } else if result_transcode_latin1_to_utf8 {
            // callee CompactUtf16 → caller Utf8. SOURCE = callee memory
            // (tag-encoded), DEST = caller memory (UTF-8). The loop reallocs
            // internally (3*count, align 1) and rewrites `l_src_len` to the
            // output UTF-8 byte count. 6 scratch.
            let src_mem8 = wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: callee_memory,
            };
            let src_mem16 = wasm_encoder::MemArg {
                offset: 0,
                align: 1,
                memory_index: callee_memory,
            };
            let dst_mem8 = wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: caller_memory,
            };
            emit_latin1_to_utf8_transcode_param(
                body,
                caller_realloc_func,
                1, // realloc align (utf-8 caller, byte-granular)
                src_mem8,
                src_mem16,
                dst_mem8,
                l_src_ptr,
                l_src_len,
                l_dst_ptr,
                transcode_base,     // tag
                transcode_base + 1, // src_idx
                transcode_base + 2, // dst_idx / out byte count
                transcode_base + 3, // cp
                transcode_base + 4, // cu
                transcode_base + 5, // cu2
            );
        } else if result_transcode_utf8_to_latin1 {
            // callee Utf8 → caller CompactUtf16. SOURCE = callee memory (UTF-8),
            // DEST = caller memory (latin1+utf16, two-phase tag-PRODUCING). The
            // loop reallocs internally (2*len, align 2) and rewrites `l_src_len`
            // to the TAGGED output length (Latin-1 byte count, tag clear; or
            // UTF-16 code-unit count | UTF16_TAG, tag set) — the retptr len stays
            // tagged, exactly as a latin1+utf16 caller reads it. 6 scratch.
            let src_mem8 = wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: callee_memory,
            };
            let dst_mem8 = wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: caller_memory,
            };
            let dst_mem16 = wasm_encoder::MemArg {
                offset: 0,
                align: 1,
                memory_index: caller_memory,
            };
            emit_utf8_to_latin1_transcode_param(
                body,
                caller_realloc_func,
                2, // realloc align (latin1+utf16 caller, utf16-worst-case)
                src_mem8,
                dst_mem8,
                dst_mem16,
                l_src_ptr,
                l_src_len,
                l_dst_ptr,
                transcode_base,     // flag (needs_utf16)
                transcode_base + 1, // src_idx
                transcode_base + 2, // dst_idx
                transcode_base + 3, // byte
                transcode_base + 4, // cp
                transcode_base + 5, // cont
            );
        } else if result_transcode_utf16_to_latin1 {
            // callee Utf16 → caller CompactUtf16. SOURCE = callee memory
            // (UTF-16), DEST = caller memory (latin1+utf16, two-phase
            // tag-PRODUCING). The loop reallocs internally (2*len, align 2) and
            // rewrites `l_src_len` to the TAGGED output length. 6 scratch.
            let src_mem16 = wasm_encoder::MemArg {
                offset: 0,
                align: 1,
                memory_index: callee_memory,
            };
            let dst_mem8 = wasm_encoder::MemArg {
                offset: 0,
                align: 0,
                memory_index: caller_memory,
            };
            let dst_mem16 = wasm_encoder::MemArg {
                offset: 0,
                align: 1,
                memory_index: caller_memory,
            };
            emit_utf16_to_latin1_transcode_param(
                body,
                caller_realloc_func,
                2, // realloc align (latin1+utf16 caller, utf16-worst-case)
                src_mem16,
                dst_mem8,
                dst_mem16,
                l_src_ptr,
                l_src_len,
                l_dst_ptr,
                transcode_base,     // flag (needs_utf16)
                transcode_base + 1, // src_idx
                transcode_base + 2, // dst_idx
                transcode_base + 3, // cu
                transcode_base + 4, // cp
                transcode_base + 5, // cu2
            );
        } else {
            // A top-level byte-granular result (elem_size == 1) in a latin1+utf16
            // callee is a tag-encoded string; its byte count must be masked/doubled.
            let top_compact_utf16 = callee_compact_utf16 && elem_size == 1;
            // byte_count = <tag-aware byte count> | len * elem_size, with LS-A-7 guard
            emit_overflow_guard(body, l_src_len, elem_size);
            emit_copy_byte_count(body, l_src_len, elem_size, top_compact_utf16);
            body.instruction(&Instruction::LocalSet(l_byte_count));

            // Allocate in caller memory: cabi_realloc(0, 0, align, byte_count).
            // A utf16 payload needs 2-byte alignment.
            let realloc_align = if top_compact_utf16 { 2 } else { elem_align };
            body.instruction(&Instruction::I32Const(0)); // old_ptr
            body.instruction(&Instruction::I32Const(0)); // old_size
            body.instruction(&Instruction::I32Const(realloc_align as i32));
            body.instruction(&Instruction::LocalGet(l_byte_count));
            emit_checked_realloc(body, caller_realloc_func, l_dst_ptr);

            // Copy from callee memory to caller memory
            body.instruction(&Instruction::LocalGet(l_dst_ptr));
            body.instruction(&Instruction::LocalGet(l_src_ptr));
            body.instruction(&Instruction::LocalGet(l_byte_count));
            body.instruction(&Instruction::MemoryCopy {
                dst_mem: caller_memory,
                src_mem: callee_memory,
            });

            // Walk nested indirections (string fields, nested lists) if the
            // list element type carries them. #272 inc 5a: an inner `string`
            // (NOT a `list<u8>`) in the callee=Utf8 → caller=Utf16 RESULT
            // direction is transcoded; the encodings + a disjoint transcode
            // scratch block (`transcode_base`, past the nested-loop region) are
            // threaded through. SRC = callee, DST = caller (the result
            // direction).
            if let Some(elem_ty) = &list_elem_ty {
                emit_patch_nested_indirections(
                    body,
                    elem_ty,
                    l_dst_ptr,
                    l_src_ptr,
                    l_src_len,
                    elem_size,
                    scratch_base + 4,
                    caller_realloc_func,
                    caller_memory,
                    callee_memory,
                    callee_compact_utf16,
                    caller_encoding,
                    callee_encoding,
                    transcode_base,
                );
            }
        }

        // Write (new_ptr, len) to retptr at offsets 0 and 4 (both i32,
        // align 2). The pair layout is fixed by the canonical ABI for
        // string and list<T> returns, so no align_up needed here.
        let mem_arg_0 = wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: caller_memory,
        };
        let mem_arg_4 = wasm_encoder::MemArg {
            offset: 4,
            align: 2,
            memory_index: caller_memory,
        };
        body.instruction(&Instruction::LocalGet(retptr_local));
        body.instruction(&Instruction::LocalGet(l_dst_ptr));
        body.instruction(&Instruction::I32Store(mem_arg_0));
        body.instruction(&Instruction::LocalGet(retptr_local));
        body.instruction(&Instruction::LocalGet(l_src_len));
        body.instruction(&Instruction::I32Store(mem_arg_4));
    }

    /// Emit the canonical-ABI store sequence that writes each task.return
    /// result global to the caller's retptr buffer at the spec-required
    /// offset. Both the callback and stackful async-lift emitters use
    /// this so the writeback contract has a single source of truth.
    ///
    /// Critical invariant — alignment padding between fields:
    ///
    /// The canonical ABI aligns every record/tuple field up to its
    /// natural alignment before placing it. For example, a result whose
    /// flat lowering contains `[I32, I64]` lays out as i32 at offset 0,
    /// 4 bytes of padding, i64 at offset 8 (record size 16). A naïve
    /// "advance offset by flat byte size" loop would write the i64 at
    /// offset 4 — the caller's canon.lower then reads stale/zero bytes
    /// at offset 8. Wasm engines treat `MemArg.align` as a hint and do
    /// not trap on misalignment, so the bug is silent data corruption.
    ///
    /// Surfaced by the v0.8.0 pre-release Mythos delta-pass; pinned by
    /// `cabi_alignment_stackful_retptr_writes_i64_at_offset_8`.
    fn emit_globals_to_retptr_cabi(
        &self,
        body: &mut Function,
        retptr_local: u32,
        result_globals: &[(u32, wasm_encoder::ValType)],
        caller_memory: u32,
    ) {
        fn align_up(n: u32, a: u32) -> u32 {
            (n + a - 1) & !(a - 1)
        }
        fn natural(val_ty: &wasm_encoder::ValType) -> (u32, u32) {
            // (size, alignment) per canonical-ABI flattening; align is
            // identical to size for primitive numeric types.
            match val_ty {
                wasm_encoder::ValType::I64 | wasm_encoder::ValType::F64 => (8, 8),
                wasm_encoder::ValType::I32 | wasm_encoder::ValType::F32 => (4, 4),
                _ => (4, 4),
            }
        }

        let mut offset = 0u32;
        for (global_idx, val_ty) in result_globals {
            let (size, align) = natural(val_ty);
            offset = align_up(offset, align);
            body.instruction(&Instruction::LocalGet(retptr_local));
            body.instruction(&Instruction::GlobalGet(*global_idx));
            let mem_arg = wasm_encoder::MemArg {
                offset: offset as u64,
                align: match val_ty {
                    wasm_encoder::ValType::I64 | wasm_encoder::ValType::F64 => 3,
                    _ => 2,
                },
                memory_index: caller_memory,
            };
            match val_ty {
                wasm_encoder::ValType::I32 => {
                    body.instruction(&Instruction::I32Store(mem_arg));
                }
                wasm_encoder::ValType::I64 => {
                    body.instruction(&Instruction::I64Store(mem_arg));
                }
                wasm_encoder::ValType::F32 => {
                    body.instruction(&Instruction::F32Store(mem_arg));
                }
                wasm_encoder::ValType::F64 => {
                    body.instruction(&Instruction::F64Store(mem_arg));
                }
                _ => {
                    body.instruction(&Instruction::I32Store(mem_arg));
                }
            }
            offset += size;
        }
    }

    /// Emit the stackful-mode async-lift trampoline (SR-32, #140).
    ///
    /// Stackful lifting per the Component Model spec: a canonical lift
    /// with `(canon lift ... async ...)` but **no** `(callback ...)`
    /// option. The runtime treats the lifted call as a fiber boundary —
    /// the wasm code inside may call `task.wait`/`task.yield` to suspend,
    /// and the runtime resumes the fiber transparently. From the
    /// adapter's perspective, the call looks synchronous: invoke the
    /// lift, await its return, read result globals.
    ///
    /// Generated wasm shape:
    ///
    /// ```wat
    /// (func $async_stackful_adapter_<from>_to_<to>
    ///   ;; step 0.5: cross-memory param copy (shared with callback path)
    ///   ;; step 1:   call [async-lift]<export> — runtime-managed fiber
    ///   ;; step 1.5: drop the lift's stackful return value (irrelevant —
    ///   ;;           result has already been written via task.return)
    ///   ;; step 3:   read result from async_result_globals and return
    ///   ;;           to caller (push-on-stack OR write-to-retptr)
    /// )
    /// ```
    ///
    /// The Phase 1 `thread::*` host-intrinsic ABI (thread_new,
    /// thread_switch_to, thread_yield, thread_exit) remains valid for
    /// component-internal concurrency but is **not** consumed by this
    /// trampoline; see ADR-1's 2026-05-13 addendum.
    ///
    /// Result readback covers:
    /// - Push-results-onto-stack: caller expects direct results
    /// - Retptr with non-pointer scalars: write globals at offset to
    ///   caller's return buffer
    ///
    /// Returning lists / strings from stackful mode (cross-memory copy
    /// of `(ptr, len)` results) is deferred to a follow-up; this emitter
    /// errors clearly if asked to handle that case for now.
    fn generate_async_stackful_adapter(
        &self,
        site: &AdapterSite,
        merged: &MergedModule,
    ) -> Result<AdapterFunction> {
        let name = format!(
            "$async_stackful_adapter_{}_to_{}",
            site.from_component, site.to_component
        );

        let async_lift_func = self.resolve_target_function(site, merged)?;

        let caller_type_idx = site
            .import_func_type_idx
            .and_then(|local_ti| {
                merged
                    .type_index_map
                    .get(&(site.from_component, site.from_module, local_ti))
                    .copied()
            })
            .unwrap_or(0);

        let caller_type = merged
            .types
            .get(caller_type_idx as usize)
            .cloned()
            .unwrap_or_else(|| crate::merger::MergedFuncType {
                params: Vec::new(),
                results: Vec::new(),
            });
        let caller_param_count = caller_type.params.len();

        let caller_memory = crate::merger::component_memory_index(merged, site.from_component);

        let callee_param_count = merged
            .defined_func(async_lift_func)
            .and_then(|f| merged.types.get(f.type_idx as usize))
            .map(|t| t.params.len())
            .unwrap_or(caller_param_count);

        // Locals layout (simpler than callback mode — no packed/code/payload):
        //   0..caller_param_count: params from caller
        //   +0:        $scratch — used by step 0.5 helper for new_ptr
        //   +1..+4:    ptr-pair result writeback scratch (src_ptr,
        //              src_len, dst_ptr, byte_count)
        //   +5..+10:   nested-indirection patching scratch (consumed by
        //              `emit_patch_nested_indirections`)
        let l_scratch = caller_param_count as u32;

        // 11 locals total: 1 for step 0.5 + 4 for ptr-pair writeback +
        // 6 for nested-indirection patching. Plus 1 headroom = 12. + 6
        // (#272 inc 1) for the UTF-8→UTF-16 param transcode loop (src_idx,
        // out_count, cp, byte, cont — at `l_scratch + 12 ..`, past the
        // writeback / nested-patch region) = 18.
        //
        // #272 inc 3 (RESULT-side transcode): REUSES the same
        // `l_scratch + 12 ..= l_scratch + 16` transcode block (already
        // declared). Param (step 0.5) and result (step 3) transcodes never
        // run simultaneously, and that block does not overlap the
        // writeback/nested region `l_scratch + 1 ..= l_scratch + 10` live in
        // step 3 — so no growth; top index stays `l_scratch + 16` < 18.
        //
        // #272 inc 4a (latin1-SOURCE param transcode): the `Latin1 → UTF-8`
        // tag-dispatch loop uses 6 scratch locals (tag, src_idx, dst_idx, cp,
        // cu, cu2) at `transcode_base = l_scratch + 12`, i.e. offsets 12..=17 —
        // top `l_scratch + 17` < 18, so the existing budget already fits the
        // STACKFUL variant (only the callback variant, whose transcode block
        // starts higher, needed growing). (`Latin1 → UTF-16` needs only 4 —
        // offsets 12..=15.) Proven by
        // `inc4a_stackful_adapter_latin1_source_locals_within_budget`.
        //
        // #272 inc 4b (DEST-latin1 / tag-PRODUCING param transcode): the two
        // two-phase loops (`UTF-8 → latin1+utf16`, `UTF-16 → latin1+utf16`) each
        // use 6 scratch locals at `transcode_base = l_scratch + 12`, i.e.
        // offsets 12..=17 — the SAME six the inc-4a `Latin1 → UTF-8` loop
        // occupies (scratch reused across the scan + write phases). Top index
        // stays `l_scratch + 17` < 18, so the budget already fits with NO
        // growth. Proven by
        // `inc4b_stackful_adapter_dest_latin1_locals_within_budget`.
        //
        // #272 inc 4c (latin1 RESULT-side transcode): the result-writeback REUSES
        // the SAME `transcode_base = l_scratch + 12` block for the FOUR latin1
        // result directions (callee→caller), each using ≤ 6 scratch
        // (`l_scratch + 12 ..= l_scratch + 17`, offsets 12..=17). Param (step
        // 0.5) and result (step 3) transcodes are never simultaneously live, and
        // offsets 12..=17 do not overlap the writeback/nested region `l_scratch +
        // 1 ..= l_scratch + 10` (offsets 1..=10) live during step 3 — so NO
        // growth; top index stays `l_scratch + 17` < 18. Proven by
        // `inc4c_stackful_adapter_latin1_result_locals_within_budget`.
        //
        // #272 inc 5a (NESTED `list<string>` RESULT transcode — SIMULTANEOUS
        // LIVENESS): the inner UTF-8 → UTF-16 transcode runs INSIDE the
        // per-element nested loop, so both regions are live at once. The nested
        // loop occupies `l_scratch + 1 + 4 ..= l_scratch + 1 + 9` = `l_scratch +
        // 5 ..= l_scratch + 10` (offsets 5..=10, 6 locals). The inner transcode
        // uses `l_transcode_base = l_scratch + 12` for its 5 scratch (offsets
        // 12..=16) plus `l_new_ptr = l_scratch + 9` as the out-ptr sink (inside
        // the nested region). The two regions are DISJOINT (offsets 5..=10 vs
        // 12..=16, gap at 11). Top index = `l_scratch + 16` = offset 16 < 18 —
        // existing budget fits with NO growth. Proven under the REAL adapter by
        // `inc5a_stackful_adapter_nested_result_locals_within_budget`.
        let mut body = Function::new([(18, wasm_encoder::ValType::I32)]);

        // Step 0.5: cross-memory param copy (shared with callback path)
        self.emit_param_copy_step(
            &mut body,
            site,
            merged,
            &caller_type,
            caller_param_count,
            callee_param_count,
            l_scratch,
            l_scratch + 12,
        );

        // Step 1: call [async-lift] entry. In stackful mode the runtime
        // treats this call as a fiber boundary; control returns once the
        // fiber has run to completion (including any task.wait suspensions
        // the body issues internally).
        for i in 0..callee_param_count {
            body.instruction(&Instruction::LocalGet(i as u32));
        }
        body.instruction(&Instruction::Call(async_lift_func));

        // Step 1.5: drop any return value the lift function produces. In
        // stackful mode the real result has already been written to the
        // task.return shim globals from inside the lift body; the wasm-
        // level return value (if any) is a control word the runtime owns.
        let lift_result_count = merged
            .defined_func(async_lift_func)
            .and_then(|f| merged.types.get(f.type_idx as usize))
            .map(|t| t.results.len())
            .unwrap_or(0);
        for _ in 0..lift_result_count {
            body.instruction(&Instruction::Drop);
        }

        // Step 3: read result values from task.return shim globals.
        let adapter_func_name = site
            .export_name
            .rsplit_once('#')
            .map(|(_, name)| name)
            .unwrap_or(&site.export_name);

        let result_globals_direct = merged
            .async_result_globals
            .get(&(site.to_component, adapter_func_name.to_string()));

        let shim_info = if let Some(globals) = result_globals_direct {
            let result_type = merged
                .task_return_shims
                .values()
                .find(|info| {
                    info.component_idx == site.to_component && info.result_globals == *globals
                })
                .and_then(|info| info.result_type.clone());
            Some(crate::merger::TaskReturnShimInfo {
                shim_func: 0,
                result_globals: globals.clone(),
                component_idx: site.to_component,
                import_name: String::new(),
                original_func_name: adapter_func_name.to_string(),
                result_type,
            })
        } else {
            merged
                .task_return_shims
                .values()
                .find(|info| {
                    info.component_idx == site.to_component
                        && info.original_func_name == adapter_func_name
                })
                .cloned()
        };

        let uses_retptr = caller_type.results.is_empty() && caller_param_count > callee_param_count;

        if let Some(info) = shim_info.as_ref() {
            if uses_retptr {
                let retptr_local = callee_param_count as u32;
                let callee_memory =
                    crate::merger::component_memory_index(merged, site.to_component);
                let caller_realloc =
                    crate::merger::component_realloc_index(merged, site.from_component);
                let is_ptr_pair = info.result_globals.len() == 2
                    && info
                        .result_globals
                        .iter()
                        .all(|(_, t)| *t == wasm_encoder::ValType::I32)
                    && callee_memory != caller_memory
                    && caller_realloc.is_some();

                if is_ptr_pair {
                    // Cross-memory (string / list<T>) return: realloc
                    // in caller memory, copy, walk nested indirections,
                    // write (new_ptr, len) to retptr. Shared with the
                    // callback path; see `emit_ptr_pair_result_writeback`.
                    self.emit_ptr_pair_result_writeback(
                        &mut body,
                        info,
                        retptr_local,
                        caller_realloc.unwrap(),
                        caller_memory,
                        callee_memory,
                        l_scratch + 1,
                        // #272 inc 3: the result transcode's 5 scratch locals.
                        // SAME index passed to `emit_param_copy_step` above
                        // (`l_scratch + 12`) — param (step 0.5) and result
                        // (step 3) transcodes are never simultaneously live, and
                        // `l_scratch + 12 ..= l_scratch + 16` (declared by the
                        // budget of 18) does not overlap the writeback/nested
                        // region `l_scratch + 1 ..= l_scratch + 10` live here.
                        l_scratch + 12,
                        site.requirements.caller_encoding,
                        site.requirements.callee_encoding,
                        // Result-side: governed by the callee's string encoding.
                        matches!(
                            site.requirements.callee_encoding,
                            Some(crate::parser::CanonStringEncoding::CompactUtf16)
                        ),
                    );
                } else {
                    // Non-pointer results: write globals directly to retptr
                    // with canonical-ABI alignment padding between fields
                    // (shared helper, see `emit_globals_to_retptr_cabi`).
                    self.emit_globals_to_retptr_cabi(
                        &mut body,
                        retptr_local,
                        &info.result_globals,
                        caller_memory,
                    );
                }
            } else {
                // Push result values onto the stack for the caller.
                for (global_idx, _) in &info.result_globals {
                    body.instruction(&Instruction::GlobalGet(*global_idx));
                }
            }
        } else {
            // No matching task.return shim — emit default values per
            // caller result types so the adapter is still a valid wasm
            // function. The merger should always wire shims for
            // async-lifted exports, so reaching here implies a parse-
            // time invariant violation; logging keeps the path visible.
            log::warn!(
                "stackful adapter '{}': no task.return shim found; \
                 emitting default results",
                site.export_name,
            );
            for result_ty in &caller_type.results {
                match result_ty {
                    wasm_encoder::ValType::I32 => {
                        body.instruction(&Instruction::I32Const(0));
                    }
                    wasm_encoder::ValType::I64 => {
                        body.instruction(&Instruction::I64Const(0));
                    }
                    wasm_encoder::ValType::F32 => {
                        body.instruction(&Instruction::F32Const(0.0_f32.into()));
                    }
                    wasm_encoder::ValType::F64 => {
                        body.instruction(&Instruction::F64Const(0.0_f64.into()));
                    }
                    _ => {
                        body.instruction(&Instruction::I32Const(0));
                    }
                }
            }
        }

        body.instruction(&Instruction::End);

        let target_func = self.resolve_target_function(site, merged)?;

        Ok(AdapterFunction {
            name,
            type_idx: caller_type_idx,
            body,
            source_component: site.from_component,
            source_module: site.from_module,
            target_component: site.to_component,
            target_module: site.to_module,
            target_function: target_func,
            class: AdapterClass::Async,
        })
    }
}

impl FactStyleGenerator {
    /// #272 / LS-F-27 cross-encoding async-string guard.
    ///
    /// Returns `Ok` (allow-through) for an async-lift site ONLY when both:
    ///   * there is nothing to transcode — the call doesn't cross memory, the
    ///     encodings match, or there is no byte-granular `(ptr, len)` buffer at
    ///     all (a `list<u32>`/record-only call is encoding-independent); OR
    ///   * EVERY byte-granular PARAM is **top-level** AND its caller→callee
    ///     direction is one of the 6 implemented combos — utf8↔utf16 (#272 inc
    ///     1/2), latin1↔utf8/utf16 (#272 inc 4a/4b) — (`emit_param_copy_step`
    ///     transcodes it), AND EVERY byte-granular RESULT is **top-level** AND
    ///     its callee→caller direction is one of the SAME 6 implemented combos —
    ///     utf8↔utf16 (#272 inc 3), latin1↔utf8/utf16 (#272 inc 4c) —
    ///     (`emit_ptr_pair_result_writeback` transcodes it). All 6 param AND all
    ///     6 result directions are now implemented.
    ///
    /// DIRECTION SUBTLETY: a param crosses caller→callee, but a RESULT is
    /// produced by the callee and read by the caller, so its transcode
    /// direction is callee→caller — the REVERSE. The result-allow predicate
    /// therefore checks `callee_enc → caller_enc`, matching the
    /// `result_transcode_*` triggers in `emit_ptr_pair_result_writeback`.
    ///
    /// EVERY other cross-encoding combo — a NESTED (`list<string>`) param OR
    /// result (its inner string is still raw-copied by
    /// `emit_patch_nested_indirections`) — still FAILS LOUD, because the
    /// emitters would otherwise raw-copy the bytes and silently mis-transcode
    /// (the H-4.4 defect). This is safety-critical: the guard's allow-predicate
    /// and the UNION of the emitter transcode-triggers (the param triggers plus
    /// the result triggers) must be IDENTICAL — any allow-but-not-transcode is
    /// silent corruption.
    fn guard_async_cross_encoding_strings(site: &AdapterSite) -> Result<()> {
        if !site.crosses_memory {
            return Ok(());
        }
        let caller_enc = site
            .requirements
            .caller_encoding
            .map(canon_to_string_encoding);
        let callee_enc = site
            .requirements
            .callee_encoding
            .map(canon_to_string_encoding);
        // Only meaningful when both sides have a known, differing encoding.
        let (caller_enc, callee_enc) = match (caller_enc, callee_enc) {
            (Some(a), Some(b)) if a != b => (a, b),
            _ => return Ok(()),
        };

        // Is there a byte-granular (ptr, len) param or result whose bytes the
        // async emitter would raw-copy — at ANY nesting depth? A nested string
        // (e.g. `list<string>`) has a non-byte-granular TOP-LEVEL layout
        // (`Elements{element_size: 8}`) but a byte-granular inner pointer that
        // `emit_patch_nested_indirections` raw-copies; the detection recurses
        // into `inner_pointers` to match the emitter's depth (LS-F-27
        // under-trip fix). A ptr-pair position with no recorded layout defaults
        // to byte-granular in the emitters (`byte_mult` falls back to 1), so
        // treat a bare position (no parallel layout) as a string too.
        let param_has_string = site
            .requirements
            .pointer_pair_positions
            .iter()
            .enumerate()
            .any(|(i, _)| {
                site.requirements
                    .param_copy_layouts
                    .get(i)
                    .map(Self::layout_bears_byte_granular_buffer)
                    .unwrap_or(true)
            });
        let result_has_string = site
            .requirements
            .result_pointer_pair_offsets
            .iter()
            .enumerate()
            .any(|(i, _)| {
                site.requirements
                    .result_copy_layouts
                    .get(i)
                    .map(Self::layout_bears_byte_granular_buffer)
                    .unwrap_or(true)
            });

        if !param_has_string && !result_has_string {
            // Encoding-independent (no string-like buffer): nothing to
            // transcode, nothing to raw-copy-corrupt.
            return Ok(());
        }

        // The implemented async transcodes are a TOP-LEVEL string PARAM in
        // EITHER UTF-8 → UTF-16 (#272 inc 1) or UTF-16 → UTF-8 (#272 inc 2).
        // Allow those through; reject everything else. The direction is
        // compared on the raw canon enums (UTF-8 / UTF-16 strictly, not the
        // StringEncoding mapping that collapses latin1+utf16 onto Latin1), so a
        // CompactUtf16 endpoint never satisfies either predicate. This MUST
        // stay identical to the `transcode_*` triggers in `emit_param_copy_step`
        // — any divergence between the guard's allow-set and the emitter's
        // transcode-set is silent corruption.
        let direction_is_utf8_to_utf16 = matches!(
            site.requirements.caller_encoding,
            Some(crate::parser::CanonStringEncoding::Utf8)
        ) && matches!(
            site.requirements.callee_encoding,
            Some(crate::parser::CanonStringEncoding::Utf16)
        );
        let direction_is_utf16_to_utf8 = matches!(
            site.requirements.caller_encoding,
            Some(crate::parser::CanonStringEncoding::Utf16)
        ) && matches!(
            site.requirements.callee_encoding,
            Some(crate::parser::CanonStringEncoding::Utf8)
        );
        // #272 inc 4a: the latin1-SOURCE param directions — a `latin1+utf16`
        // (CompactUtf16) CALLER to a UTF-16 or UTF-8 callee. The
        // `emit_param_copy_step` tag-dispatch loops
        // (`emit_latin1_to_{utf16,utf8}_transcode_param`) transcode exactly
        // these; the DEST-latin1 directions (`X → CompactUtf16`) are a later
        // sub-increment and stay fail-loud, so the callee side is matched on the
        // raw canon enum (UTF-16 / UTF-8 strictly), NOT a StringEncoding mapping.
        let direction_is_latin1_to_utf16 = matches!(
            site.requirements.caller_encoding,
            Some(crate::parser::CanonStringEncoding::CompactUtf16)
        ) && matches!(
            site.requirements.callee_encoding,
            Some(crate::parser::CanonStringEncoding::Utf16)
        );
        let direction_is_latin1_to_utf8 = matches!(
            site.requirements.caller_encoding,
            Some(crate::parser::CanonStringEncoding::CompactUtf16)
        ) && matches!(
            site.requirements.callee_encoding,
            Some(crate::parser::CanonStringEncoding::Utf8)
        );
        // #272 inc 4b: the DEST-latin1 / tag-PRODUCING param directions — a
        // UTF-8 or UTF-16 CALLER to a `latin1+utf16` (CompactUtf16) callee. The
        // `emit_param_copy_step` two-phase loops
        // (`emit_{utf8,utf16}_to_latin1_transcode_param`) transcode exactly
        // these (scan → pick representation → tagged-length output), completing
        // all 6 PARAM directions. RESULT-side latin1 (a CompactUtf16 callee
        // PRODUCING a result) is completed in #272 inc 4c below; only NESTED
        // latin1 strings stay fail-loud.
        let direction_is_utf8_to_latin1 = matches!(
            site.requirements.caller_encoding,
            Some(crate::parser::CanonStringEncoding::Utf8)
        ) && matches!(
            site.requirements.callee_encoding,
            Some(crate::parser::CanonStringEncoding::CompactUtf16)
        );
        let direction_is_utf16_to_latin1 = matches!(
            site.requirements.caller_encoding,
            Some(crate::parser::CanonStringEncoding::Utf16)
        ) && matches!(
            site.requirements.callee_encoding,
            Some(crate::parser::CanonStringEncoding::CompactUtf16)
        );
        let direction_is_implemented = direction_is_utf8_to_utf16
            || direction_is_utf16_to_utf8
            || direction_is_latin1_to_utf16
            || direction_is_latin1_to_utf8
            || direction_is_utf8_to_latin1
            || direction_is_utf16_to_latin1;
        // #272 inc 3: a top-level byte-granular RESULT string is now transcoded
        // by `emit_ptr_pair_result_writeback`, for the utf8↔utf16 directions.
        // The RESULT transcode direction is `callee_enc → caller_enc` (the
        // callee PRODUCES the result, the caller READS it) — the REVERSE of the
        // param side. So the result is implemented iff `callee → caller` is
        // UTF-8 → UTF-16 or UTF-16 → UTF-8. This MUST stay identical to the
        // `result_transcode_*` triggers in `emit_ptr_pair_result_writeback`.
        let result_dir_is_utf8_to_utf16 = matches!(
            site.requirements.callee_encoding,
            Some(crate::parser::CanonStringEncoding::Utf8)
        ) && matches!(
            site.requirements.caller_encoding,
            Some(crate::parser::CanonStringEncoding::Utf16)
        );
        let result_dir_is_utf16_to_utf8 = matches!(
            site.requirements.callee_encoding,
            Some(crate::parser::CanonStringEncoding::Utf16)
        ) && matches!(
            site.requirements.caller_encoding,
            Some(crate::parser::CanonStringEncoding::Utf8)
        );
        // #272 inc 4c: the FOUR latin1 (CompactUtf16) RESULT directions are now
        // transcoded by `emit_ptr_pair_result_writeback` (mirroring the inc-4a/4b
        // latin1 PARAM directions, but `callee → caller`). This MUST stay
        // identical to the `result_transcode_latin1_*` / `result_transcode_*_to_latin1`
        // triggers in `emit_ptr_pair_result_writeback`.
        let result_callee_is_latin1 = matches!(
            site.requirements.callee_encoding,
            Some(crate::parser::CanonStringEncoding::CompactUtf16)
        );
        let result_caller_is_latin1 = matches!(
            site.requirements.caller_encoding,
            Some(crate::parser::CanonStringEncoding::CompactUtf16)
        );
        let result_dir_is_latin1_to_utf16 = result_callee_is_latin1
            && matches!(
                site.requirements.caller_encoding,
                Some(crate::parser::CanonStringEncoding::Utf16)
            );
        let result_dir_is_latin1_to_utf8 = result_callee_is_latin1
            && matches!(
                site.requirements.caller_encoding,
                Some(crate::parser::CanonStringEncoding::Utf8)
            );
        let result_dir_is_utf8_to_latin1 = result_caller_is_latin1
            && matches!(
                site.requirements.callee_encoding,
                Some(crate::parser::CanonStringEncoding::Utf8)
            );
        let result_dir_is_utf16_to_latin1 = result_caller_is_latin1
            && matches!(
                site.requirements.callee_encoding,
                Some(crate::parser::CanonStringEncoding::Utf16)
            );
        let result_dir_is_implemented = result_dir_is_utf8_to_utf16
            || result_dir_is_utf16_to_utf8
            || result_dir_is_latin1_to_utf16
            || result_dir_is_latin1_to_utf8
            || result_dir_is_utf8_to_latin1
            || result_dir_is_utf16_to_latin1;
        // Every byte-granular RESULT must be a TOP-LEVEL byte-granular string
        // (directly `Bulk{1}` or a bare offset) AND the callee→caller direction
        // must be implemented — `emit_ptr_pair_result_writeback` only transcodes
        // a top-level string; a nested (`list<string>`) result's inner string is
        // still raw-copied by `emit_patch_nested_indirections`, so it stays
        // fail-loud, as does any latin1/CompactUtf16 result direction. When
        // there is NO byte-granular result this is trivially satisfied.
        let result_top_level_ok = !result_has_string
            || (result_dir_is_implemented
                && site
                    .requirements
                    .result_pointer_pair_offsets
                    .iter()
                    .enumerate()
                    .all(
                        |(i, _)| match site.requirements.result_copy_layouts.get(i) {
                            // Bare offset (no recorded layout) → emitter treats it as
                            // a top-level byte-granular string.
                            None => true,
                            // Bears a byte-granular buffer ⇒ must be a TOP-LEVEL one;
                            // a nested string stays raw-copied / fail-loud.
                            Some(cl) if Self::layout_bears_byte_granular_buffer(cl) => {
                                Self::layout_is_top_level_byte_granular(cl)
                            }
                            // Not a string (e.g. list<u32>): encoding-independent.
                            Some(_) => true,
                        },
                    ));

        // #272 inc 5a: a NESTED `list<string>` RESULT (one level of nesting) is
        // now ALLOWED — but ONLY in the callee=Utf8 → caller=Utf16 direction AND
        // ONLY when every nested byte-granular indirection is a `string` (not a
        // `list<u8>`). `emit_patch_nested_indirections` transcodes exactly those
        // inner strings and raw-copies everything else; a nested `list<u8>` in
        // this direction would be raw-copied (CORRECT — never transcoded), but
        // the *guard* must NOT allow that case through, because the allow-set
        // must equal the transcode-set: allowing a raw-copied `list<u8>` here
        // would not corrupt it (it is correctly raw-copied), yet a MIXED
        // `list<{ string, list<u8> }>` would have its string inner transcoded
        // and its list<u8> inner raw-copied — which IS correct — but deeper /
        // record / other-direction nesting is out of inc-5a scope and stays
        // fail-loud. So we allow the nested case ONLY when ALL nested
        // indirections are strings (a pure `list<string>` shape), reading the
        // SAME `collect_indirections` string-ness signal the emitter consults.
        //
        // The WIT result types are walked via `collect_indirections`: for a
        // `list<T>` result the inner element `T` is descended; the result is
        // nested-string-allowed iff there is at least one nested indirection and
        // every one is `is_string == true`.
        let result_inner_all_strings = !site.requirements.result_wit_types.is_empty()
            && site.requirements.result_wit_types.iter().all(|ty| {
                let inner_indirections = match ty {
                    crate::parser::ComponentValType::List(elem)
                    | crate::parser::ComponentValType::FixedSizeList(elem, _) => {
                        collect_indirections(elem, 0)
                    }
                    // A non-list result has no inner-element indirections to walk
                    // for the nested case; the top-level path handles it.
                    _ => Vec::new(),
                };
                // Every inner indirection of THIS result must be a string for the
                // nested transcode to be safe; a `list<u8>` inner (is_string ==
                // false) makes the whole result NOT nested-string-allowed.
                inner_indirections.iter().all(|(_, _, is_string)| *is_string)
            })
            // At least one result must actually carry a nested string for this
            // predicate to widen the allow-set (a pure `list<u32>` has no inner
            // indirections — `all` is vacuously true — but is already handled by
            // the top-level path and must not be mistaken for a nested string).
            && site.requirements.result_wit_types.iter().any(|ty| match ty {
                crate::parser::ComponentValType::List(elem)
                | crate::parser::ComponentValType::FixedSizeList(elem, _) => {
                    let inner = collect_indirections(elem, 0);
                    !inner.is_empty() && inner.iter().all(|(_, _, is_string)| *is_string)
                }
                _ => false,
            });
        let result_nested_string_ok = result_dir_is_utf8_to_utf16 && result_inner_all_strings;

        let result_ok = result_top_level_ok || result_nested_string_ok;
        // Every param that bears a byte-granular buffer must be TOP-LEVEL
        // byte-granular (directly `Bulk{1}` or a bare position) — a nested
        // (`list<string>`) param's inner string is still raw-copied by
        // `emit_patch_nested_indirections`, so it stays fail-loud.
        let all_param_strings_top_level = site
            .requirements
            .pointer_pair_positions
            .iter()
            .enumerate()
            .all(|(i, _)| match site.requirements.param_copy_layouts.get(i) {
                // Bare position (no recorded layout) → emitter treats it as a
                // top-level byte-granular string (byte_mult falls back to 1).
                None => true,
                // Bears a byte-granular buffer ⇒ must be a TOP-LEVEL one (a
                // direct `Bulk{1}`); a nested string (`list<string>`) is still
                // raw-copied so it stays fail-loud.
                Some(cl) if Self::layout_bears_byte_granular_buffer(cl) => {
                    Self::layout_is_top_level_byte_granular(cl)
                }
                // Not a string at all (e.g. list<u32>): copied verbatim and
                // encoding-independent — does not block the allow-through.
                Some(_) => true,
            });

        // Params allowed iff there is no byte-granular param OR every one is
        // top-level AND the caller→callee direction is implemented (utf8↔utf16).
        let param_ok =
            !param_has_string || (direction_is_implemented && all_param_strings_top_level);

        if param_ok && result_ok {
            return Ok(());
        }

        Err(crate::Error::AdapterGeneration(format!(
            "async cross-encoding string transcoding is not yet supported \
             (caller {caller_enc:?} != callee {callee_enc:?}); only a \
             top-level string param (all 6 directions — UTF-8 ↔ UTF-16 #272 inc \
             1/2, latin1+utf16 ↔ UTF-16/UTF-8 #272 inc 4a/4b) or a top-level \
             string result (all 6 directions — UTF-8 ↔ UTF-16 #272 inc 3, \
             latin1+utf16 ↔ UTF-16/UTF-8 #272 inc 4c) is implemented — a \
             verbatim copy of any other case (a NESTED list<string> param or \
             result) would silently mis-transcode — see #272"
        )))
    }

    /// Is this copy layout a TOP-LEVEL byte-granular `(ptr, len)` buffer — i.e.
    /// a direct `Bulk{1}` — as opposed to a NESTED byte-granular buffer reached
    /// through an `Elements`' `inner_pointers` (e.g. the inner string of a
    /// `list<string>`)? The #272 inc-1 transcode only rewrites the top-level
    /// param `(ptr, len)`; a nested inner string is still raw-copied by
    /// `emit_patch_nested_indirections`, so the guard must keep failing loud on
    /// it. An `Elements{element_size: 1}` is itself a top-level byte buffer
    /// (a `list<u8>` lowering shape) but is encoding-independent; it never
    /// reaches this check because `transcode_utf8_to_utf16` only fires for the
    /// `Bulk` byte_mult==1 string shape. Treated conservatively as NOT
    /// top-level-string so it cannot widen the allow-through.
    fn layout_is_top_level_byte_granular(cl: &crate::resolver::CopyLayout) -> bool {
        matches!(cl, crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 })
    }

    /// Recursively: does this copy layout carry a byte-granular `(ptr, len)`
    /// buffer at ANY nesting depth — the conservative proxy for "a string the
    /// async emitter would raw-copy without transcoding"? `Bulk{1}` /
    /// `Elements{element_size: 1}` are byte-granular; an `Elements` is also a
    /// carrier if any of its `inner_pointers` is (e.g. `list<string>`, whose
    /// top-level `Elements{element_size: 8}` holds a `Bulk{1}` inner string).
    /// This must match the depth of `emit_patch_nested_indirections`, which
    /// copies inner buffers — otherwise a nested cross-encoding string
    /// under-trips the guard and silently mis-transcodes (LS-F-27).
    fn layout_bears_byte_granular_buffer(cl: &crate::resolver::CopyLayout) -> bool {
        match cl {
            crate::resolver::CopyLayout::Bulk { byte_multiplier } => *byte_multiplier == 1,
            crate::resolver::CopyLayout::Elements {
                element_size,
                inner_pointers,
                ..
            } => {
                *element_size == 1
                    || inner_pointers
                        .iter()
                        .any(|ip| Self::layout_bears_byte_granular_buffer(&ip.copy_layout))
            }
        }
    }
}

impl AdapterGenerator for FactStyleGenerator {
    fn generate(
        &self,
        merged: &MergedModule,
        graph: &DependencyGraph,
    ) -> Result<Vec<AdapterFunction>> {
        let (resource_rep_imports, resource_new_imports) = build_resource_import_maps(merged);
        let mut adapters = Vec::new();

        for (idx, site) in graph.adapter_sites.iter().enumerate() {
            if site.is_async_lift {
                // #272 / H-4.4 LS-F-27: the async emitters (`emit_param_copy_step`
                // / `emit_ptr_pair_result_writeback`) copy string/(ptr,len)
                // buffers via `memory.copy` with no transcoding. The sync
                // dispatch routes cross-encoding string calls to
                // `generate_transcoding_adapter`; the async branch never did.
                // A cross-memory async-lift call passing/returning a string in
                // one encoding while the other side expects a different
                // encoding would therefore raw-copy the bytes and silently
                // mis-transcode (the H-4.4 defect #253/#271 closed for sync).
                // Full async transcoding is the tracked #272 capability; until
                // then we FAIL LOUD rather than emit a silently-corrupting copy.
                Self::guard_async_cross_encoding_strings(site)?;
                let adapter = if self.has_callback_export(site, merged) {
                    self.generate_async_callback_adapter(site, merged)?
                } else {
                    self.generate_async_stackful_adapter(site, merged)?
                };
                adapters.push(adapter);
                continue;
            }
            let adapter = self.generate_adapter(
                site,
                merged,
                idx,
                &resource_rep_imports,
                &resource_new_imports,
            )?;
            adapters.push(adapter);
        }

        Ok(adapters)
    }
}

impl AdapterOptions {
    /// Check if this call site needs string transcoding
    pub fn needs_transcoding(&self) -> bool {
        self.caller_string_encoding != self.callee_string_encoding
    }

    /// Check if this call site crosses memory boundaries
    pub fn crosses_memory(&self) -> bool {
        self.caller_memory != self.callee_memory
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_adapter_options_default() {
        let options = AdapterOptions::default();
        assert_eq!(options.caller_string_encoding, StringEncoding::Utf8);
        assert_eq!(options.callee_string_encoding, StringEncoding::Utf8);
        assert!(!options.needs_transcoding());
    }

    /// LS-P-19 — `emit_utf8_to_utf16_transcode` must replace truncated
    /// multi-byte UTF-8 sequences with U+FFFD instead of reading past the
    /// end of the input buffer.
    ///
    /// The mirror of LS-P-16 on the UTF-8→UTF-16 direction. Before the
    /// v0.10 mitigation, each multi-byte branch (2-byte, 3-byte, 4-byte)
    /// unconditionally read continuation bytes at `src_idx + 1`, `+2`,
    /// `+3` via `I32Load8U` without checking against `input_len` — a
    /// UTF-8 string ending on a truncated multi-byte lead byte caused
    /// the adapter to load 1–3 bytes of attacker-adjacent caller memory,
    /// incorporate them into a synthesized code point, and emit the
    /// result as UTF-16 in the callee. v0.10 trapped via `unreachable`
    /// (conservative). **v0.11.0 substitutes U+FFFD per the Canonical
    /// ABI's lossy-replacement rule**: when the continuation bytes are
    /// out of range, set `cp = 0xFFFD` and consume only the lead byte;
    /// the loop continues with the next byte as a potential new lead.
    ///
    /// Pinned structurally: the LS-P-19 marker must appear at all three
    /// branches AND the U+FFFD code point must be emitted at each.
    #[test]
    fn ls_p_19_utf8_to_utf16_continuation_byte_emits_replacement() {
        const SRC: &str = include_str!("fact.rs");
        let marker = "LS-P-19: emit U+FFFD when the";
        let marker_count = SRC.matches(marker).count();
        assert!(
            marker_count >= 3,
            "fact.rs must retain LS-P-19 U+FFFD markers for all three \
             multi-byte branches (2-byte, 3-byte, 4-byte) in \
             emit_utf8_to_utf16_transcode; found {marker_count}",
        );
        // The Canonical ABI's replacement character is U+FFFD (decimal
        // 65533). The emitter sets `cp_local = 0xFFFD` at each of the
        // three multi-byte truncation paths, plus once at the LS-P-16
        // lone-high-surrogate path in emit_utf16_to_utf8_transcode →
        // at least 4 occurrences of `I32Const(0xFFFD)` in fact.rs.
        let fffd_count = SRC.matches("I32Const(0xFFFD)").count();
        assert!(
            fffd_count >= 4,
            "expected at least 4 I32Const(0xFFFD) emissions in fact.rs \
             (LS-P-16 + LS-P-19 replacement paths); found {fffd_count}",
        );
    }

    /// LS-P-16 — `emit_utf16_to_utf8_transcode` must replace a lone high
    /// surrogate at end-of-input with U+FFFD rather than reading past the
    /// buffer.
    ///
    /// Before the v0.10 mitigation, the surrogate-pair `If` arm
    /// unconditionally emitted a second `I32Load16U` at `mem16[ptr +
    /// (src_idx + 1) * 2]` — for an input whose last code unit is a high
    /// surrogate, that read 2 bytes past the buffer. v0.10 added a
    /// `src_idx + 1 >= input_len` trap (conservative mitigation).
    /// **v0.11.0 substitutes U+FFFD** (3-byte UTF-8 `EF BF BD`) per the
    /// Canonical ABI's lossy-replacement rule, consuming only the lone
    /// high surrogate and continuing the loop. The existing 3-byte UTF-8
    /// encoder handles `cp = 0xFFFD` directly (it lives in the BMP).
    ///
    /// Pinned structurally: the LS-P-16 U+FFFD marker must remain in the
    /// source AND `cp_local` must be set to `0xFFFD` in the bounds-
    /// failure path. A refactor that drops the marker or the replacement
    /// code point is caught here.
    #[test]
    fn ls_p_16_utf16_lone_high_surrogate_emits_replacement() {
        const SRC: &str = include_str!("fact.rs");
        let marker = "LS-P-16: emit U+FFFD replacement";
        let pos = SRC.find(marker).unwrap_or_else(|| {
            panic!(
                "fact.rs must retain the LS-P-16 U+FFFD marker `{marker}`; \
                 without the replacement, the surrogate-pair If arm reads \
                 2 bytes past the UTF-16 input buffer when input ends on a \
                 lone high surrogate",
            )
        });
        // The replacement-code-point emission lives within ~2000 bytes of
        // the marker; assert U+FFFD is set there.
        let after = &SRC[pos..];
        let block = &after[..after.len().min(3000)];
        assert!(
            block.contains("I32Const(0xFFFD)"),
            "LS-P-16 replacement path must set cp_local = 0xFFFD via \
             I32Const(0xFFFD); the segment after the LS-P-16 marker is \
             missing the replacement code point",
        );
        // Bounds-check still has to be there — the replacement path is
        // gated on `src_idx + 1 >= input_len`.
        assert!(
            block.contains("I32GeU"),
            "LS-P-16 path must still gate on an I32GeU comparison against \
             input_len",
        );
    }

    /// LS-P-14 — the nested-list inner copy in `emit_patch_nested_indirections`
    /// must guard `len * sub_elem_size` against 32-bit overflow before
    /// computing `buf_len` for `cabi_realloc` + `memory.copy`.
    ///
    /// Before the fix, the inner copy path loaded the callee-supplied `len`
    /// from callee memory, multiplied by `sub_elem_size` with a bare
    /// `i32.mul` (wrapping mod 2³²), stored to `l_buf_len`, then used
    /// `l_buf_len` for the buffer allocation and `memory.copy`. A callee-
    /// controlled `len` near `u32::MAX / sub_elem_size` wrapped `buf_len`
    /// to a small value; the subsequent `old_ptr + buf_len > mem_bytes`
    /// bounds check used `i32.add` which also wrapped and was bypassed;
    /// the adapter then under-allocated and under-copied the inner list
    /// while the caller's bulk-copied outer `(ptr, len)` retained the
    /// original large `len` — silent truncation. Surfaced by the mythos-
    /// auto delta-pass on PR #179. Fix calls `emit_overflow_guard(body,
    /// l_buf_len, sub_elem_size as u32)` after loading `len` and before
    /// the multiplication.
    ///
    /// This test pins the contract by emitting the function via
    /// `emit_patch_nested_indirections` for an element type that has an
    /// inner `list<u32>` indirection (`sub_elem_size = 4`, non-trivial),
    /// extracts the encoded body bytes, and asserts they contain at least
    /// one `Unreachable` opcode (`0x00`) — the only place that opcode is
    /// emitted along this path is inside `emit_overflow_guard`.
    #[test]
    fn ls_p_14_nested_list_inner_copy_emits_overflow_guard() {
        use crate::parser::{ComponentValType, PrimitiveValType};
        use wasm_encoder::{Function, ValType};

        // Element type: `record { items: list<u32> }`. The record has one
        // inner pointer pair (the list) with sub_elem_size = element_size
        // of u32 = 4. That's the dangerous `len * 4` multiplication path.
        let elem_ty = ComponentValType::Record(vec![(
            "items".to_string(),
            ComponentValType::List(Box::new(ComponentValType::Primitive(PrimitiveValType::U32))),
        )]);

        // Function with enough locals to cover l_first_scratch..+5 plus a
        // few spare. Six i32 locals starting at index 0.
        let mut func = Function::new(vec![(12, ValType::I32)]);

        // The dst/src/len locals and the scratch base are all i32 indices
        // we just point at slots 0..11 — the function body only cares
        // about local references being in-range.
        emit_patch_nested_indirections(
            &mut func, &elem_ty, /* l_dst_ptr = */ 0, /* l_callee_src = */ 1,
            /* l_src_len = */ 2,
            /* elem_size = */ 8, // record { ptr:i32, len:i32 } = 8 bytes
            /* l_first_scratch = */ 3, /* realloc_func = */ 99,
            /* caller_memory = */ 0, /* callee_memory = */ 1,
            /* callee_compact_utf16 = */ false,
            // No encodings ⇒ inner `list<u32>` stays raw-copied (no transcode).
            /* caller_encoding = */
            None, /* callee_encoding = */ None,
            // Transcode block is never entered here; any in-range base is fine.
            /* l_transcode_base = */
            9,
        );

        // wasm_encoder::Function has no public bytes() accessor on stable;
        // round-trip through a Module to get encoded bytes we can scan.
        func.instruction(&wasm_encoder::Instruction::End);
        let mut module = wasm_encoder::Module::new();
        let mut code_section = wasm_encoder::CodeSection::new();
        code_section.function(&func);
        module.section(&code_section);
        let body_bytes: Vec<u8> = module.finish();

        // Unreachable opcode is 0x00; it only appears in
        // emit_overflow_guard along this path. Without the fix, no
        // Unreachable is emitted by the inner copy and the buf_len
        // computation wraps silently.
        assert!(
            body_bytes.contains(&0x00),
            "emit_patch_nested_indirections must emit an Unreachable \
             (LS-P-14 overflow guard) for the inner len * sub_elem_size \
             multiplication; before the fix, no Unreachable was emitted \
             and a callee-controlled len could wrap buf_len silently",
        );
    }

    #[test]
    fn test_adapter_options_needs_transcoding() {
        let options = AdapterOptions {
            callee_string_encoding: StringEncoding::Utf16,
            ..Default::default()
        };
        assert!(options.needs_transcoding());
    }

    #[test]
    fn test_adapter_options_crosses_memory() {
        let mut options = AdapterOptions::default();
        assert!(!options.crosses_memory());

        options.callee_memory = 1;
        assert!(options.crosses_memory());
    }

    #[test]
    fn test_fact_generator_creation() {
        let config = AdapterConfig::default();
        let _generator = FactStyleGenerator::new(config);
    }

    // ---------------------------------------------------------------
    // SR-17: String transcoding correctness
    //
    // These tests verify the adapter's string encoding handling:
    //   - canon_to_string_encoding mapping
    //   - alignment_for_encoding values
    //   - needs_transcoding detection for all encoding pairs
    //   - Scratch local allocation for transcoding paths
    //
    // Currently supported transcoding paths:
    //   - UTF-8  <-> UTF-8  (no-op, direct call)
    //   - UTF-8   -> UTF-16 (emit_utf8_to_utf16_transcode)
    //   - UTF-16  -> UTF-8  (emit_utf16_to_utf8_transcode)
    //   - Latin-1 -> UTF-8  (emit_latin1_to_utf8_transcode)
    //
    // Edge cases NOT yet tested at runtime:
    //   - UTF-8  -> Latin-1 (falls through to direct call, no transcoding)
    //   - UTF-16 -> Latin-1 (falls through to direct call, no transcoding)
    //   - Latin-1 -> UTF-16 (falls through to direct call, no transcoding)
    //   - Latin-1 <-> Latin-1 (no-op, direct call)
    //   - Surrogate pair handling for non-BMP characters (U+10000+)
    //   - Overlong UTF-8 sequences (malformed input)
    //   - Lone surrogates in UTF-16 input
    //
    // For full SR-17 coverage, runtime tests with wasmtime are needed
    // to verify actual byte-level correctness of the transcoding loops.
    // See tests/adapter_safety.rs for the runtime harness pattern.
    // ---------------------------------------------------------------

    #[test]
    fn test_sr17_canon_to_string_encoding_utf8() {
        assert_eq!(
            canon_to_string_encoding(CanonStringEncoding::Utf8),
            StringEncoding::Utf8,
            "SR-17: CanonStringEncoding::Utf8 should map to StringEncoding::Utf8"
        );
    }

    #[test]
    fn test_sr17_canon_to_string_encoding_utf16() {
        assert_eq!(
            canon_to_string_encoding(CanonStringEncoding::Utf16),
            StringEncoding::Utf16,
            "SR-17: CanonStringEncoding::Utf16 should map to StringEncoding::Utf16"
        );
    }

    #[test]
    fn test_sr17_canon_to_string_encoding_compact_utf16() {
        // CompactUTF16 (latin1+utf16) is treated as Latin1 for adapter purposes.
        // The canonical ABI spec defines CompactUTF16 as an optimization where
        // strings that fit in Latin-1 use 1 byte/char, otherwise UTF-16.
        // The adapter treats it as Latin-1 because that's the worst-case element
        // size (1 byte), and the caller is responsible for the compact encoding.
        assert_eq!(
            canon_to_string_encoding(CanonStringEncoding::CompactUtf16),
            StringEncoding::Latin1,
            "SR-17: CompactUTF16 should map to Latin1 for adapter purposes"
        );
    }

    #[test]
    fn test_sr17_alignment_for_utf8() {
        assert_eq!(
            alignment_for_encoding(StringEncoding::Utf8),
            1,
            "SR-17: UTF-8 alignment should be 1 (byte-aligned)"
        );
    }

    #[test]
    fn test_sr17_alignment_for_utf16() {
        assert_eq!(
            alignment_for_encoding(StringEncoding::Utf16),
            2,
            "SR-17: UTF-16 alignment should be 2 (2-byte aligned for code units)"
        );
    }

    #[test]
    fn test_sr17_alignment_for_latin1() {
        // #253: `Latin1` is meld's model of the canonical-ABI `latin1+utf16`
        // encoding. Its string buffer may hold UTF-16 code units (the tag-set
        // representation), so the canonical ABI requires 2-byte alignment for
        // the string pointer — NOT 1. (A pure-Latin-1-only encoding would be 1,
        // but meld has no such encoding; Latin1 IS latin1+utf16.)
        assert_eq!(
            alignment_for_encoding(StringEncoding::Latin1),
            2,
            "#253: latin1+utf16 alignment should be 2 (buffer may hold UTF-16)"
        );
    }

    #[test]
    fn test_sr17_needs_transcoding_same_encoding() {
        // No transcoding needed when both sides use the same encoding
        let utf8_utf8 = AdapterOptions {
            caller_string_encoding: StringEncoding::Utf8,
            callee_string_encoding: StringEncoding::Utf8,
            ..Default::default()
        };
        assert!(
            !utf8_utf8.needs_transcoding(),
            "SR-17: UTF-8 to UTF-8 should not need transcoding"
        );

        let utf16_utf16 = AdapterOptions {
            caller_string_encoding: StringEncoding::Utf16,
            callee_string_encoding: StringEncoding::Utf16,
            ..Default::default()
        };
        assert!(
            !utf16_utf16.needs_transcoding(),
            "SR-17: UTF-16 to UTF-16 should not need transcoding"
        );

        let latin1_latin1 = AdapterOptions {
            caller_string_encoding: StringEncoding::Latin1,
            callee_string_encoding: StringEncoding::Latin1,
            ..Default::default()
        };
        assert!(
            !latin1_latin1.needs_transcoding(),
            "SR-17: Latin-1 to Latin-1 should not need transcoding"
        );
    }

    #[test]
    fn test_sr17_needs_transcoding_different_encodings() {
        // All cross-encoding pairs must require transcoding
        let pairs = [
            (StringEncoding::Utf8, StringEncoding::Utf16),
            (StringEncoding::Utf8, StringEncoding::Latin1),
            (StringEncoding::Utf16, StringEncoding::Utf8),
            (StringEncoding::Utf16, StringEncoding::Latin1),
            (StringEncoding::Latin1, StringEncoding::Utf8),
            (StringEncoding::Latin1, StringEncoding::Utf16),
        ];
        for (caller, callee) in &pairs {
            let options = AdapterOptions {
                caller_string_encoding: *caller,
                callee_string_encoding: *callee,
                ..Default::default()
            };
            assert!(
                options.needs_transcoding(),
                "SR-17: {:?} to {:?} should need transcoding",
                caller,
                callee
            );
        }
    }

    #[test]
    fn test_sr17_needs_transcoding_independent_of_memory() {
        // Transcoding depends on encoding, not memory indices.
        // Same encoding with different memories should NOT need transcoding.
        let options = AdapterOptions {
            caller_string_encoding: StringEncoding::Utf8,
            callee_string_encoding: StringEncoding::Utf8,
            caller_memory: 0,
            callee_memory: 1,
            ..Default::default()
        };
        assert!(
            !options.needs_transcoding(),
            "SR-17: same encoding across different memories should not need transcoding"
        );
        assert!(
            options.crosses_memory(),
            "SR-17: different memory indices should cross memory boundaries"
        );
    }

    #[test]
    fn test_sr17_needs_transcoding_and_crosses_memory() {
        // When both encoding differs AND memory differs, both flags should be true.
        let options = AdapterOptions {
            caller_string_encoding: StringEncoding::Utf8,
            callee_string_encoding: StringEncoding::Utf16,
            caller_memory: 0,
            callee_memory: 1,
            ..Default::default()
        };
        assert!(
            options.needs_transcoding(),
            "SR-17: UTF-8 to UTF-16 should need transcoding"
        );
        assert!(
            options.crosses_memory(),
            "SR-17: different memory indices should cross memory boundaries"
        );
    }

    // ---------------------------------------------------------------
    // LS-A-7: Transcoder overflow + null-check guards
    //
    // The three transcode emitters must emit, for every generated
    // adapter:
    //   (a) an I32GtU check on input_len against u32::MAX/K followed
    //       by an `if ... unreachable end` trap — prevents i32.mul
    //       wrapping to a small alloc_size.
    //   (b) an I32Eqz check on the cabi_realloc return followed by
    //       `if ... unreachable end` — prevents the transcode loop
    //       writing to callee memory offset 0 when OOM returns null.
    //
    // These byte-scan tests are the PoC referenced in loss-scenarios
    // LS-A-7. They fail on the unfixed emitter and pass once both
    // guards are present.
    // ---------------------------------------------------------------

    /// Return `true` iff the byte-encoded function body `body` contains
    /// an `i32.eqz; if; unreachable; end` sequence. The `if` block byte
    /// is 0x04, `unreachable` is 0x00, `end` is 0x0B, `i32.eqz` is 0x45.
    /// The block type that follows 0x04 is 0x40 (empty block type).
    #[cfg(test)]
    fn body_has_eqz_if_unreachable(body: &[u8]) -> bool {
        // Pattern: 0x45 0x04 0x40 0x00 0x0B
        body.windows(5).any(|w| w == [0x45, 0x04, 0x40, 0x00, 0x0B])
    }

    /// Return `true` iff the byte-encoded function body `body` contains
    /// a `i32.gt_u; if; unreachable; end` sequence.
    /// Opcodes: i32.gt_u = 0x4B, if = 0x04, block type empty = 0x40,
    /// unreachable = 0x00, end = 0x0B.
    #[cfg(test)]
    fn body_has_gtu_if_unreachable(body: &[u8]) -> bool {
        body.windows(5).any(|w| w == [0x4B, 0x04, 0x40, 0x00, 0x0B])
    }

    fn emit_transcode(options: AdapterOptions) -> Vec<u8> {
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let mut f = Function::new([(8, wasm_encoder::ValType::I32)]);
        // param_count=2 matches string param (ptr, len) lowered shape.
        // target_func=0 is a placeholder — the emitter only uses it for
        // the tail call, which this test doesn't execute.
        if options.caller_string_encoding == StringEncoding::Utf8
            && options.callee_string_encoding == StringEncoding::Utf16
        {
            gen_.emit_utf8_to_utf16_transcode(&mut f, 2, 0, &options);
        } else if options.caller_string_encoding == StringEncoding::Utf16
            && options.callee_string_encoding == StringEncoding::Utf8
        {
            gen_.emit_utf16_to_utf8_transcode(&mut f, 2, 0, &options);
        } else if options.caller_string_encoding == StringEncoding::Latin1
            && options.callee_string_encoding == StringEncoding::Utf8
        {
            // The test only inspects the emitted byte patterns (it never
            // validates or runs the body), so the tag-dispatch block type is
            // immaterial here; Empty keeps the raw body well-formed for the
            // structural pattern checks.
            gen_.emit_latin1_to_utf8_transcode(
                &mut f,
                2,
                0,
                &options,
                wasm_encoder::BlockType::Empty,
            );
        } else {
            panic!("unsupported encoding pair for test");
        }
        f.into_raw_body()
    }

    fn transcode_options(caller: StringEncoding, callee: StringEncoding) -> AdapterOptions {
        AdapterOptions {
            caller_string_encoding: caller,
            callee_string_encoding: callee,
            caller_memory: 0,
            callee_memory: 1,
            callee_realloc: Some(0),
            ..Default::default()
        }
    }

    #[test]
    fn ls_a_7_utf8_to_utf16_emits_overflow_and_null_guards() {
        let body = emit_transcode(transcode_options(
            StringEncoding::Utf8,
            StringEncoding::Utf16,
        ));
        assert!(
            body_has_gtu_if_unreachable(&body),
            "LS-A-7: UTF-8→UTF-16 transcoder missing overflow guard \
             (i32.gt_u; if; unreachable; end) before the i32.mul"
        );
        assert!(
            body_has_eqz_if_unreachable(&body),
            "LS-A-7: UTF-8→UTF-16 transcoder missing cabi_realloc null \
             guard (i32.eqz; if; unreachable; end) after the call"
        );
    }

    #[test]
    fn ls_a_7_utf16_to_utf8_emits_overflow_and_null_guards() {
        let body = emit_transcode(transcode_options(
            StringEncoding::Utf16,
            StringEncoding::Utf8,
        ));
        assert!(
            body_has_gtu_if_unreachable(&body),
            "LS-A-7: UTF-16→UTF-8 transcoder missing overflow guard"
        );
        assert!(
            body_has_eqz_if_unreachable(&body),
            "LS-A-7: UTF-16→UTF-8 transcoder missing cabi_realloc null guard"
        );
    }

    #[test]
    fn ls_a_7_latin1_to_utf8_emits_overflow_and_null_guards() {
        let body = emit_transcode(transcode_options(
            StringEncoding::Latin1,
            StringEncoding::Utf8,
        ));
        assert!(
            body_has_gtu_if_unreachable(&body),
            "LS-A-7: Latin-1→UTF-8 transcoder missing overflow guard"
        );
        assert!(
            body_has_eqz_if_unreachable(&body),
            "LS-A-7: Latin-1→UTF-8 transcoder missing cabi_realloc null guard"
        );
    }

    // ---------------------------------------------------------------
    // SR-32 / #140 phase 2 — stackful lifting routing
    //
    // The dispatcher must detect a stackful lift (an `[async-lift]`
    // export with no `[callback]<export>` companion in the merged
    // module) and route it to the stackful emitter rather than the
    // callback emitter. Until commit 3 lands the trampoline body, the
    // stackful emitter returns a clear error that names SR-32 / #140
    // so audit and CI surface the path.

    fn empty_merged() -> crate::merger::MergedModule {
        use crate::merger::MergedModule;
        MergedModule {
            types: Vec::new(),
            imports: Vec::new(),
            functions: Vec::new(),
            tables: Vec::new(),
            memories: Vec::new(),
            globals: Vec::new(),
            exports: Vec::new(),
            start_function: None,
            elements: Vec::new(),
            data_segments: Vec::new(),
            custom_sections: Vec::new(),
            function_index_map: std::collections::HashMap::new(),
            memory_index_map: std::collections::HashMap::new(),
            table_index_map: std::collections::HashMap::new(),
            global_index_map: std::collections::HashMap::new(),
            type_index_map: std::collections::HashMap::new(),
            realloc_map: std::collections::HashMap::new(),
            import_counts: Default::default(),
            import_memory_indices: Vec::new(),
            import_realloc_indices: Vec::new(),
            resource_rep_by_component: std::collections::HashMap::new(),
            resource_new_by_component: std::collections::HashMap::new(),
            handle_tables: std::collections::HashMap::new(),
            task_return_shims: std::collections::HashMap::new(),
            async_result_globals: std::collections::HashMap::new(),
            segment_bases: std::collections::HashMap::new(),
        }
    }

    fn async_lift_site(export_name: &str) -> crate::resolver::AdapterSite {
        use crate::resolver::AdapterSite;
        AdapterSite {
            from_component: 0,
            from_module: 0,
            import_name: "x".into(),
            import_module: "m".into(),
            import_func_type_idx: None,
            to_component: 1,
            to_module: 0,
            export_name: export_name.into(),
            export_func_idx: 0,
            crosses_memory: false,
            is_async_lift: true,
            requirements: Default::default(),
        }
    }

    /// Build a cross-memory async-lift site carrying a single byte-granular
    /// `(ptr, len)` string param, parameterised by caller/callee canon
    /// encodings. Used by the #272 / LS-F-27 guard matrix.
    fn async_xenc_string_param_site(
        caller: crate::parser::CanonStringEncoding,
        callee: crate::parser::CanonStringEncoding,
    ) -> crate::resolver::AdapterSite {
        let mut site = async_lift_site("[async-lift]greet");
        site.crosses_memory = true;
        site.requirements.pointer_pair_positions = vec![0];
        site.requirements.param_copy_layouts =
            vec![crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 }];
        site.requirements.caller_encoding = Some(caller);
        site.requirements.callee_encoding = Some(callee);
        site
    }

    /// Build a cross-memory async-lift site whose param or result is a
    /// `list<string>`: top-level `Elements{element_size: 8}` (NOT byte-granular)
    /// with a byte-granular `Bulk{1}` inner string. Exercises the LS-F-27
    /// under-trip fix — the guard must recurse into `inner_pointers`.
    fn async_xenc_nested_list_string_site(on_result: bool) -> crate::resolver::AdapterSite {
        use crate::parser::CanonStringEncoding;
        use crate::resolver::{CopyLayout, InnerPointer};
        let list_of_string = CopyLayout::Elements {
            element_size: 8,
            inner_pointers: vec![InnerPointer::unconditional(
                0,
                CopyLayout::Bulk { byte_multiplier: 1 },
            )],
            inner_resources: vec![],
        };
        let mut site = async_lift_site("[async-lift]greet");
        site.crosses_memory = true;
        if on_result {
            site.requirements.result_pointer_pair_offsets = vec![0];
            site.requirements.result_copy_layouts = vec![list_of_string];
        } else {
            site.requirements.pointer_pair_positions = vec![0];
            site.requirements.param_copy_layouts = vec![list_of_string];
        }
        site.requirements.caller_encoding = Some(CanonStringEncoding::Utf8);
        site.requirements.callee_encoding = Some(CanonStringEncoding::Utf16);
        site
    }

    /// LS-F-27 (under-trip fix): a cross-encoding async `list<string>` PARAM —
    /// non-byte-granular top-level layout, byte-granular inner string the
    /// emitter raw-copies — must fail loud. Pre-fix the guard inspected only
    /// the top-level layout and silently let this through (#272 under-trip,
    /// confirmed by an adversarial Mythos pass).
    #[test]
    fn ls_f_27_async_cross_encoding_nested_list_string_param_fails_loud() {
        let site = async_xenc_nested_list_string_site(false);
        FactStyleGenerator::guard_async_cross_encoding_strings(&site)
            .expect_err("cross-encoding async list<string> param must fail loud (nested string)");
    }

    /// LS-F-27 (under-trip fix), result side.
    #[test]
    fn ls_f_27_async_cross_encoding_nested_list_string_result_fails_loud() {
        let site = async_xenc_nested_list_string_site(true);
        FactStyleGenerator::guard_async_cross_encoding_strings(&site)
            .expect_err("cross-encoding async list<string> result must fail loud (nested string)");
    }

    /// LS-F-27 negative (the recursion must not OVER-trip): a cross-encoding
    /// async `list<list<u32>>` — nested but with NO byte-granular buffer at any
    /// depth (inner `Elements{element_size: 4}`) — must still pass.
    #[test]
    fn ls_f_27_async_cross_encoding_nested_no_string_ok() {
        use crate::parser::CanonStringEncoding;
        use crate::resolver::{CopyLayout, InnerPointer};
        let list_of_list_u32 = CopyLayout::Elements {
            element_size: 8,
            inner_pointers: vec![InnerPointer::unconditional(
                0,
                CopyLayout::Elements {
                    element_size: 4,
                    inner_pointers: vec![],
                    inner_resources: vec![],
                },
            )],
            inner_resources: vec![],
        };
        let mut site = async_lift_site("[async-lift]f");
        site.crosses_memory = true;
        site.requirements.pointer_pair_positions = vec![0];
        site.requirements.param_copy_layouts = vec![list_of_list_u32];
        site.requirements.caller_encoding = Some(CanonStringEncoding::Utf8);
        site.requirements.callee_encoding = Some(CanonStringEncoding::Utf16);
        FactStyleGenerator::guard_async_cross_encoding_strings(&site)
            .expect("nested list<list<u32>> with no string must NOT trip the guard");
    }

    /// #272 inc 1: a top-level UTF-8 → UTF-16 string PARAM crossing memory is
    /// now the IMPLEMENTED async transcode case, so the guard must ALLOW it
    /// through (the emitter transcodes rather than raw-copies). Previously this
    /// case failed loud (LS-F-27); inc 1 legitimately flips it to success. The
    /// runtime differential proof that the transcode is correct (not a raw
    /// copy) lives in the `async_cross_encoding` runtime test target.
    #[test]
    fn inc1_async_utf8_to_utf16_top_level_string_param_allowed() {
        use crate::parser::CanonStringEncoding;
        let site =
            async_xenc_string_param_site(CanonStringEncoding::Utf8, CanonStringEncoding::Utf16);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&site).is_ok(),
            "#272 inc 1: a top-level UTF-8 → UTF-16 async string param must be \
             allowed through (transcoded), not fail loud"
        );
    }

    /// #272 inc 2: the REVERSE direction — a top-level UTF-16 → UTF-8 string
    /// PARAM crossing memory is now the IMPLEMENTED async transcode case, so
    /// the guard must ALLOW it through (the emitter transcodes rather than
    /// raw-copies). Previously this case failed loud (LS-F-27); inc 2
    /// legitimately flips it to success. The runtime differential proof that
    /// the transcode is correct (not a raw copy) lives in the
    /// `async_cross_encoding` runtime test target.
    #[test]
    fn inc2_async_utf16_to_utf8_top_level_string_param_allowed() {
        use crate::parser::CanonStringEncoding;
        let site =
            async_xenc_string_param_site(CanonStringEncoding::Utf16, CanonStringEncoding::Utf8);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&site).is_ok(),
            "#272 inc 2: a top-level UTF-16 → UTF-8 async string param must be \
             allowed through (transcoded), not fail loud"
        );
    }

    /// #272 inc 4a: a top-level latin1+utf16 (CompactUtf16) → UTF-16 string
    /// PARAM crossing memory is now the IMPLEMENTED async transcode case (tag
    /// dispatch in `emit_latin1_to_utf16_transcode_param`), so the guard must
    /// ALLOW it through. Previously it failed loud (LS-F-27). The runtime
    /// differential proof lives in the `async_cross_encoding` target.
    #[test]
    fn inc4a_async_latin1_to_utf16_top_level_string_param_allowed() {
        use crate::parser::CanonStringEncoding;
        let site = async_xenc_string_param_site(
            CanonStringEncoding::CompactUtf16,
            CanonStringEncoding::Utf16,
        );
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&site).is_ok(),
            "#272 inc 4a: a top-level latin1+utf16 → UTF-16 async string param \
             must be allowed through (transcoded), not fail loud"
        );
    }

    /// #272 inc 4a: a top-level latin1+utf16 (CompactUtf16) → UTF-8 string PARAM
    /// is also implemented (tag dispatch in
    /// `emit_latin1_to_utf8_transcode_param`), so the guard must ALLOW it.
    #[test]
    fn inc4a_async_latin1_to_utf8_top_level_string_param_allowed() {
        use crate::parser::CanonStringEncoding;
        let site = async_xenc_string_param_site(
            CanonStringEncoding::CompactUtf16,
            CanonStringEncoding::Utf8,
        );
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&site).is_ok(),
            "#272 inc 4a: a top-level latin1+utf16 → UTF-8 async string param \
             must be allowed through (transcoded), not fail loud"
        );
    }

    /// #272 inc 4b: the DEST-latin1 / tag-PRODUCING param directions — a UTF-8
    /// or UTF-16 CALLER to a latin1+utf16 (CompactUtf16) callee — are now the
    /// IMPLEMENTED async transcode case (the two-phase
    /// `emit_{utf8,utf16}_to_latin1_transcode_param` loops), so the guard must
    /// ALLOW them through. Previously (inc 4a) they failed loud. This completes
    /// all 6 PARAM directions. The runtime differential proof lives in the
    /// `async_cross_encoding` target.
    #[test]
    fn inc4b_async_dest_latin1_param_directions_allowed() {
        use crate::parser::CanonStringEncoding;
        let utf8_to_latin1 = async_xenc_string_param_site(
            CanonStringEncoding::Utf8,
            CanonStringEncoding::CompactUtf16,
        );
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&utf8_to_latin1).is_ok(),
            "#272 inc 4b: UTF-8 → latin1+utf16 (DEST-latin1) async string param \
             must be allowed through (transcoded), not fail loud"
        );
        let utf16_to_latin1 = async_xenc_string_param_site(
            CanonStringEncoding::Utf16,
            CanonStringEncoding::CompactUtf16,
        );
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&utf16_to_latin1).is_ok(),
            "#272 inc 4b: UTF-16 → latin1+utf16 (DEST-latin1) async string param \
             must be allowed through (transcoded), not fail loud"
        );
    }

    /// #272 inc 4c: a latin1-SOURCE (CompactUtf16) callee PRODUCING a top-level
    /// RESULT string read by a UTF-8 caller (result dir callee→caller =
    /// latin1→utf8) is now the IMPLEMENTED async transcode case — the result
    /// writeback calls `emit_latin1_to_utf8_transcode_param`. Previously this
    /// failed loud (inc 4a out of scope); inc 4c legitimately flips it to allow.
    #[test]
    fn inc4c_async_latin1_to_utf8_top_level_string_result_allowed() {
        use crate::parser::CanonStringEncoding;
        let mut site = async_lift_site("[async-lift]greet");
        site.crosses_memory = true;
        site.requirements.result_pointer_pair_offsets = vec![0];
        site.requirements.result_copy_layouts =
            vec![crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 }];
        // caller=Utf8, callee=CompactUtf16 ⇒ result dir (callee→caller) =
        // latin1→utf8, now transcoded by the result writeback.
        site.requirements.caller_encoding = Some(CanonStringEncoding::Utf8);
        site.requirements.callee_encoding = Some(CanonStringEncoding::CompactUtf16);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&site).is_ok(),
            "#272 inc 4c: a top-level latin1 → UTF-8 (callee→caller) async string \
             result must be allowed through (transcoded), not fail loud"
        );
    }

    /// #272 inc 4a (scope guard, still fail-loud): a NESTED latin1-source
    /// `list<string>` param (top-level `Elements{element_size: 8}`, byte-granular
    /// inner string) must STILL fail loud — only TOP-LEVEL latin1-source params
    /// are transcoded; the inner string is still raw-copied.
    #[test]
    fn inc4a_async_nested_latin1_source_param_still_fails_loud() {
        use crate::parser::CanonStringEncoding;
        use crate::resolver::{CopyLayout, InnerPointer};
        let list_of_string = CopyLayout::Elements {
            element_size: 8,
            inner_pointers: vec![InnerPointer::unconditional(
                0,
                CopyLayout::Bulk { byte_multiplier: 1 },
            )],
            inner_resources: vec![],
        };
        let mut site = async_lift_site("[async-lift]greet");
        site.crosses_memory = true;
        site.requirements.pointer_pair_positions = vec![0];
        site.requirements.param_copy_layouts = vec![list_of_string];
        site.requirements.caller_encoding = Some(CanonStringEncoding::CompactUtf16);
        site.requirements.callee_encoding = Some(CanonStringEncoding::Utf16);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&site).is_err(),
            "#272 inc 4a: a NESTED latin1+utf16 list<string> param must still \
             fail loud (inner string is raw-copied)"
        );
    }

    /// #272 inc 4b (scope guard, still fail-loud): a NESTED DEST-latin1
    /// `list<string>` param (UTF-8 caller, CompactUtf16 callee; top-level
    /// `Elements{element_size: 8}` with a byte-granular inner string) must STILL
    /// fail loud — only TOP-LEVEL dest-latin1 params are two-phase transcoded;
    /// the inner string is still raw-copied by `emit_patch_nested_indirections`.
    #[test]
    fn inc4b_async_nested_dest_latin1_param_still_fails_loud() {
        use crate::parser::CanonStringEncoding;
        use crate::resolver::{CopyLayout, InnerPointer};
        let list_of_string = CopyLayout::Elements {
            element_size: 8,
            inner_pointers: vec![InnerPointer::unconditional(
                0,
                CopyLayout::Bulk { byte_multiplier: 1 },
            )],
            inner_resources: vec![],
        };
        let mut site = async_lift_site("[async-lift]greet");
        site.crosses_memory = true;
        site.requirements.pointer_pair_positions = vec![0];
        site.requirements.param_copy_layouts = vec![list_of_string];
        site.requirements.caller_encoding = Some(CanonStringEncoding::Utf8);
        site.requirements.callee_encoding = Some(CanonStringEncoding::CompactUtf16);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&site).is_err(),
            "#272 inc 4b: a NESTED dest-latin1 list<string> param must still \
             fail loud (inner string is raw-copied)"
        );
    }

    /// LS-F-27 (still fail-loud): an UNIMPLEMENTED case — a NESTED latin1
    /// (CompactUtf16) `list<string>` RESULT (top-level `Elements{element_size:
    /// 8}` with a byte-granular inner string). #272 inc 4c implemented all 6
    /// TOP-LEVEL result directions, but a NESTED result's inner string is still
    /// raw-copied by `emit_patch_nested_indirections`, so this remains the
    /// canonical fail-loud case carrying the diagnostic. (Top-level latin1
    /// results now ALLOW — see `inc4c_async_*_result_allowed`.) Asserts both the
    /// error variant and the diagnostic text — the message must still explain the
    /// gap and cite #272.
    #[test]
    fn ls_f_27_async_cross_encoding_unimplemented_direction_fails_loud() {
        use crate::parser::CanonStringEncoding;
        use crate::resolver::{CopyLayout, InnerPointer};
        let nested_list_of_string = CopyLayout::Elements {
            element_size: 8,
            inner_pointers: vec![InnerPointer::unconditional(
                0,
                CopyLayout::Bulk { byte_multiplier: 1 },
            )],
            inner_resources: vec![],
        };
        let mut site = async_lift_site("[async-lift]greet");
        site.crosses_memory = true;
        site.requirements.result_pointer_pair_offsets = vec![0];
        site.requirements.result_copy_layouts = vec![nested_list_of_string];
        // caller=Utf8, callee=CompactUtf16 ⇒ a latin1 result direction, and the
        // result is NESTED, so the inner string is raw-copied → fail loud.
        site.requirements.caller_encoding = Some(CanonStringEncoding::Utf8);
        site.requirements.callee_encoding = Some(CanonStringEncoding::CompactUtf16);
        let err = FactStyleGenerator::guard_async_cross_encoding_strings(&site)
            .expect_err("a NESTED latin1 list<string> RESULT must still fail loud");
        match err {
            crate::Error::AdapterGeneration(msg) => {
                assert!(
                    msg.contains("async cross-encoding string transcoding is not yet supported")
                        && msg.contains("#272"),
                    "LS-F-27 guard message must explain the cross-encoding gap and \
                     cite #272; got: {msg}"
                );
            }
            other => panic!("LS-F-27: expected AdapterGeneration error, got {other:?}"),
        }
    }

    /// #272 inc 4c: the MIRROR latin1 RESULT direction — a UTF-16 caller reading
    /// a latin1+utf16 callee's RESULT (result dir callee→caller = latin1→utf16)
    /// — is now implemented; the result writeback calls
    /// `emit_latin1_to_utf16_transcode_param`. Previously fail-loud (inc 4b out
    /// of scope); inc 4c legitimately flips it to allow.
    #[test]
    fn inc4c_async_latin1_to_utf16_top_level_string_result_allowed() {
        use crate::parser::CanonStringEncoding;
        let mut site = async_lift_site("[async-lift]greet");
        site.crosses_memory = true;
        site.requirements.result_pointer_pair_offsets = vec![0];
        site.requirements.result_copy_layouts =
            vec![crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 }];
        site.requirements.caller_encoding = Some(CanonStringEncoding::Utf16);
        site.requirements.callee_encoding = Some(CanonStringEncoding::CompactUtf16);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&site).is_ok(),
            "#272 inc 4c: a top-level latin1 → UTF-16 (callee→caller) async string \
             result must be allowed through (transcoded), not fail loud"
        );
    }

    /// #272 inc 3: a top-level byte-granular RESULT string crossing memory in a
    /// utf8↔utf16 direction is now the IMPLEMENTED async transcode case, so the
    /// guard must ALLOW it through (the result writeback transcodes rather than
    /// raw-copies). Previously this case failed loud (LS-F-27); inc 3
    /// legitimately flips it to success.
    ///
    /// DIRECTION SUBTLETY: caller=Utf16, callee=Utf8 means the RESULT (produced
    /// by the callee, read by the caller) transcodes callee→caller = Utf8→Utf16
    /// — an implemented direction. The runtime differential proof for the
    /// transcode loop itself lives in the `async_cross_encoding` target.
    #[test]
    fn inc3_async_utf8_to_utf16_top_level_string_result_allowed() {
        use crate::parser::CanonStringEncoding;
        let mut site = async_lift_site("[async-lift]greet");
        site.crosses_memory = true;
        site.requirements.result_pointer_pair_offsets = vec![0];
        site.requirements.result_copy_layouts =
            vec![crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 }];
        // caller=Utf16, callee=Utf8 ⇒ result dir (callee→caller) = Utf8→Utf16.
        site.requirements.caller_encoding = Some(CanonStringEncoding::Utf16);
        site.requirements.callee_encoding = Some(CanonStringEncoding::Utf8);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&site).is_ok(),
            "#272 inc 3: a top-level UTF-8 → UTF-16 (callee→caller) async string \
             result must be allowed through (transcoded), not fail loud"
        );

        // The mirror result direction (callee=Utf16, caller=Utf8 ⇒ result dir
        // Utf16→Utf8) is also implemented and must be allowed.
        let mut mirror = async_lift_site("[async-lift]greet");
        mirror.crosses_memory = true;
        mirror.requirements.result_pointer_pair_offsets = vec![0];
        mirror.requirements.result_copy_layouts =
            vec![crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 }];
        mirror.requirements.caller_encoding = Some(CanonStringEncoding::Utf8);
        mirror.requirements.callee_encoding = Some(CanonStringEncoding::Utf16);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&mirror).is_ok(),
            "#272 inc 3: a top-level UTF-16 → UTF-8 (callee→caller) async string \
             result must be allowed through (transcoded), not fail loud"
        );
    }

    /// #272 inc 4c: the two DEST-latin1 RESULT directions — a CompactUtf16
    /// caller reading a UTF-8 (or UTF-16) callee's RESULT (result dir
    /// callee→caller = utf8→latin1, utf16→latin1) — are now implemented; the
    /// result writeback calls the two-phase tag-PRODUCING `emit_utf8_to_latin1`
    /// / `emit_utf16_to_latin1` loops. Previously these failed loud (inc 3);
    /// inc 4c legitimately flips both to allow. Together with the two
    /// latin1-SOURCE result tests above, all FOUR latin1 result directions (and
    /// thus all 6 result directions) are now allowed.
    #[test]
    fn inc4c_async_dest_latin1_top_level_string_result_allowed() {
        use crate::parser::CanonStringEncoding;
        // callee=Utf8, caller=CompactUtf16 ⇒ result dir = utf8→latin1.
        let mut utf8_to_latin1 = async_lift_site("[async-lift]greet");
        utf8_to_latin1.crosses_memory = true;
        utf8_to_latin1.requirements.result_pointer_pair_offsets = vec![0];
        utf8_to_latin1.requirements.result_copy_layouts =
            vec![crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 }];
        utf8_to_latin1.requirements.caller_encoding = Some(CanonStringEncoding::CompactUtf16);
        utf8_to_latin1.requirements.callee_encoding = Some(CanonStringEncoding::Utf8);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&utf8_to_latin1).is_ok(),
            "#272 inc 4c: a top-level UTF-8 → latin1 (callee→caller) async string \
             result must be allowed through (transcoded), not fail loud"
        );

        // callee=Utf16, caller=CompactUtf16 ⇒ result dir = utf16→latin1.
        let mut utf16_to_latin1 = async_lift_site("[async-lift]greet");
        utf16_to_latin1.crosses_memory = true;
        utf16_to_latin1.requirements.result_pointer_pair_offsets = vec![0];
        utf16_to_latin1.requirements.result_copy_layouts =
            vec![crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 }];
        utf16_to_latin1.requirements.caller_encoding = Some(CanonStringEncoding::CompactUtf16);
        utf16_to_latin1.requirements.callee_encoding = Some(CanonStringEncoding::Utf16);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&utf16_to_latin1).is_ok(),
            "#272 inc 4c: a top-level UTF-16 → latin1 (callee→caller) async string \
             result must be allowed through (transcoded), not fail loud"
        );
    }

    /// LS-F-27 must NOT over-trip: a SAME-encoding async string call keeps
    /// working (no transcode needed, raw copy is correct).
    #[test]
    fn ls_f_27_same_encoding_async_string_ok() {
        use crate::parser::CanonStringEncoding;
        let site =
            async_xenc_string_param_site(CanonStringEncoding::Utf8, CanonStringEncoding::Utf8);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&site).is_ok(),
            "LS-F-27: same-encoding async string must not trip the guard"
        );
    }

    /// LS-F-27 must NOT over-trip: a CROSS-encoding async call with NO string
    /// param/result (e.g. a `list<u32>`, element size 4 — encoding-independent)
    /// keeps working. Differing encodings alone must not block the call.
    #[test]
    fn ls_f_27_cross_encoding_async_no_string_ok() {
        use crate::parser::CanonStringEncoding;
        // A non-byte-element list param: element_size 4 → not a string.
        let mut site = async_lift_site("[async-lift]sum");
        site.crosses_memory = true;
        site.requirements.pointer_pair_positions = vec![0];
        site.requirements.param_copy_layouts = vec![crate::resolver::CopyLayout::Elements {
            element_size: 4,
            inner_pointers: Vec::new(),
            inner_resources: Vec::new(),
        }];
        site.requirements.caller_encoding = Some(CanonStringEncoding::Utf8);
        site.requirements.callee_encoding = Some(CanonStringEncoding::Utf16);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&site).is_ok(),
            "LS-F-27: cross-encoding async with no string must not trip the guard"
        );

        // And a cross-encoding async call with NO ptr-pairs at all.
        let mut bare = async_lift_site("[async-lift]noop");
        bare.crosses_memory = true;
        bare.requirements.caller_encoding = Some(CanonStringEncoding::Utf8);
        bare.requirements.callee_encoding = Some(CanonStringEncoding::Utf16);
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&bare).is_ok(),
            "LS-F-27: cross-encoding async with no ptr-pairs must not trip"
        );
    }

    /// LS-F-27 must NOT over-trip: a cross-encoding async string that does
    /// NOT cross memory (shared-memory mode) keeps working — there is only
    /// one memory and one encoding in play.
    #[test]
    fn ls_f_27_cross_encoding_async_same_memory_ok() {
        use crate::parser::CanonStringEncoding;
        let mut site =
            async_xenc_string_param_site(CanonStringEncoding::Utf8, CanonStringEncoding::Utf16);
        site.crosses_memory = false;
        assert!(
            FactStyleGenerator::guard_async_cross_encoding_strings(&site).is_ok(),
            "LS-F-27: non-cross-memory async string must not trip the guard"
        );
    }

    /// LS-F-27 wiring: the guard is reached through the real `generate`
    /// dispatch (not just the helper), so a graph with a STILL-unimplemented
    /// cross-encoding async string site (here UTF-8 → latin1+utf16, which
    /// neither inc 1 nor inc 2 transcodes) makes `generate` return Err before
    /// emitting a silently-corrupting adapter. (The now-implemented UTF-8 →
    /// UTF-16 and UTF-16 → UTF-8 param cases are covered by
    /// `inc1_async_utf8_to_utf16_top_level_string_param_allowed` /
    /// `inc2_async_utf16_to_utf8_top_level_string_param_allowed` and the runtime
    /// differential tests.)
    #[test]
    fn ls_f_27_generate_dispatch_rejects_cross_encoding_async_string() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let merged = empty_merged();
        let site = async_xenc_string_param_site(
            CanonStringEncoding::Utf8,
            CanonStringEncoding::CompactUtf16,
        );
        let graph = crate::resolver::DependencyGraph {
            instantiation_order: vec![0, 1],
            resolved_imports: std::collections::HashMap::new(),
            unresolved_imports: Vec::new(),
            adapter_sites: vec![site],
            resource_graph: None,
            stream_pair_graph: None,
            module_resolutions: Vec::new(),
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
        };
        let res = <FactStyleGenerator as AdapterGenerator>::generate(&gen_, &merged, &graph);
        assert!(
            res.is_err(),
            "LS-F-27: generate() must reject a cross-encoding async string site"
        );
    }

    #[test]
    fn sr32_has_callback_export_detects_companion() {
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let site = async_lift_site("[async-lift]foo");

        let mut with_cb = empty_merged();
        with_cb.exports.push(crate::merger::MergedExport {
            name: "[callback][async-lift]foo".into(),
            kind: wasm_encoder::ExportKind::Func,
            index: 0,
        });
        assert!(gen_.has_callback_export(&site, &with_cb));

        let without_cb = empty_merged();
        assert!(!gen_.has_callback_export(&site, &without_cb));
    }

    #[test]
    fn sr32_stackful_emitter_handles_no_shim_with_default_results() {
        // With no task.return shim in the empty merged module and an
        // empty caller_type (no results), the emitter should still emit
        // a valid adapter — body just ends. The path is the "no shim,
        // no results" branch (warns via log) and validates that the
        // overall emitter wiring compiles and produces an
        // AdapterFunction without panicking.
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let site = async_lift_site("[async-lift]bar");
        let mut merged = empty_merged();
        // Make resolve_target_function succeed by providing a defined
        // function the site can point at; the emitter doesn't actually
        // require the function to be well-typed for this minimal test.
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 0,
            body: wasm_encoder::Function::new([]),
            origin: (1, 0, 0),
            synthetic_kind: None,
        });
        merged.types.push(crate::merger::MergedFuncType {
            params: Vec::new(),
            results: Vec::new(),
        });
        merged.function_index_map.insert((1, 0, 0), 0);

        let adapter = gen_
            .generate_async_stackful_adapter(&site, &merged)
            .expect("stackful emitter must succeed for trivial site");
        assert_eq!(
            adapter.name, "$async_stackful_adapter_0_to_1",
            "adapter name must follow the stackful naming convention"
        );
    }

    #[test]
    fn sr32_stackful_emitter_shape_pins_call_drop_globalget() {
        // SR-32 acceptance: with a real shim wired into the merged
        // module, the stackful emitter must produce a body that
        // structurally matches the documented trampoline shape — call
        // the lift function, drop its return, read the result global,
        // end. Pin the wasm opcodes so future refactors that drift
        // away from this shape break the test loudly.
        //
        // Opcodes:
        //   local.get  = 0x20
        //   call       = 0x10
        //   drop       = 0x1A
        //   global.get = 0x23
        //   end        = 0x0B

        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let mut merged = empty_merged();

        // Type 0: () -> i32 — minimal lift signature returning one i32
        // that the stackful trampoline will drop.
        merged.types.push(crate::merger::MergedFuncType {
            params: Vec::new(),
            results: vec![wasm_encoder::ValType::I32],
        });
        // The lift function lives at merged index 0.
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 0,
            body: wasm_encoder::Function::new([]),
            origin: (1, 0, 0),
            synthetic_kind: None,
        });
        merged.function_index_map.insert((1, 0, 0), 0);

        // A result global at index 7 — the stackful trampoline must
        // emit `global.get 7` followed by the function epilogue.
        // We register it both in async_result_globals (the primary
        // lookup) and in task_return_shims (for the fallback path the
        // emitter consults to recover the result type).
        // The emitter looks up shims by `adapter_func_name`, derived
        // from `export_name.rsplit_once('#')`. When the export has no
        // '#', the lookup uses the full export name verbatim — match
        // that here.
        let lookup_name = "[async-lift]ping".to_string();
        let globals = vec![(7u32, wasm_encoder::ValType::I32)];
        merged
            .async_result_globals
            .insert((1, lookup_name.clone()), globals.clone());
        merged.task_return_shims.insert(
            0,
            crate::merger::TaskReturnShimInfo {
                shim_func: 0,
                result_globals: globals.clone(),
                component_idx: 1,
                import_name: "[task-return]0".into(),
                original_func_name: lookup_name.clone(),
                result_type: None,
            },
        );

        // Site: caller has the same result shape so we hit the
        // push-results-on-stack branch (no retptr), which is the
        // simplest readback the structural pin needs to cover.
        let mut site = async_lift_site("[async-lift]ping");
        site.import_func_type_idx = Some(0);
        site.crosses_memory = false;

        let adapter = gen_
            .generate_async_stackful_adapter(&site, &merged)
            .expect("stackful emitter must succeed");

        let body = adapter.body.into_raw_body();

        assert!(
            body.contains(&0x10),
            "stackful trampoline must emit `call` (0x10) to lift func; \
             body={body:?}",
        );
        assert!(
            body.contains(&0x1A),
            "stackful trampoline must emit `drop` (0x1A) after the lift \
             call (lift result is owned by runtime, not caller); body={body:?}",
        );
        assert!(
            body.contains(&0x23),
            "stackful trampoline must emit `global.get` (0x23) for \
             result readback; body={body:?}",
        );
        assert_eq!(
            body.last(),
            Some(&0x0B),
            "stackful trampoline body must end with `end` (0x0B); \
             body={body:?}",
        );
    }

    fn read_uleb(buf: &[u8]) -> (u64, usize) {
        let mut result: u64 = 0;
        let mut shift = 0;
        let mut consumed = 0;
        for b in buf {
            consumed += 1;
            result |= ((b & 0x7f) as u64) << shift;
            if b & 0x80 == 0 {
                break;
            }
            shift += 7;
        }
        (result, consumed)
    }

    /// #272 STEP-1 differential: confirm whether a CROSS-ENCODING async
    /// string PARAM is silently raw-copied (no transcode) by the async
    /// emitter, transcoded, or rejected. Builds a cross-memory async-lift
    /// site whose caller lowers a string param in UTF-8 while the callee
    /// lifts it in UTF-16 (`pointer_pair_positions=[0]`), then inspects
    /// the emitted body.
    ///
    /// Verdict recorded by the assertions below: the body emits
    /// `memory.copy` (0xFC 0x0A) and contains NO UTF-8↔UTF-16 transcode
    /// loop, i.e. the cross-encoding string crosses memory as raw bytes
    /// reinterpreted under the wrong encoding — verdict (a), CONFIRMED
    /// silent corruption. The post-fix guard test below
    /// (`ls_f_27_async_cross_encoding_string_param_fails_loud`) asserts
    /// this same shape is now rejected with an `AdapterGeneration` error.
    #[test]
    #[ignore = "STEP-1 evidence: pre-fix this asserted raw-copy; post-fix the \
                emitter fails loud (see ls_f_27_* gate). Kept ignored as the \
                documented confirmation record."]
    fn issue_272_step1_async_cross_encoding_param_was_raw_copied() {
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let mut merged = empty_merged();

        // Caller type: (ptr: i32, len: i32) -> () — a lowered string param.
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            results: vec![],
        });
        // Lift type: (ptr, len) -> ()
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![wasm_encoder::ValType::I32, wasm_encoder::ValType::I32],
            results: vec![],
        });
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 1,
            body: wasm_encoder::Function::new([]),
            origin: (1, 0, 0),
            synthetic_kind: None,
        });
        merged.function_index_map.insert((1, 0, 0), 0);
        // callee realloc at idx 1
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 1,
            body: wasm_encoder::Function::new([]),
            origin: (1, 0, 0),
            synthetic_kind: None,
        });
        merged.realloc_map.insert((1, 0), 1);
        merged.memory_index_map.insert((0, 0, 0), 0);
        merged.memory_index_map.insert((1, 0, 0), 1);

        let mut site = async_lift_site("[async-lift]greet");
        site.from_component = 0;
        site.to_component = 1;
        site.import_func_type_idx = Some(0);
        site.crosses_memory = true;
        // String param at flat position 0; caller UTF-8, callee UTF-16.
        site.requirements.pointer_pair_positions = vec![0];
        site.requirements.param_copy_layouts =
            vec![crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 }];
        site.requirements.caller_encoding = Some(crate::parser::CanonStringEncoding::Utf8);
        site.requirements.callee_encoding = Some(crate::parser::CanonStringEncoding::Utf16);

        let adapter = gen_
            .generate_async_stackful_adapter(&site, &merged)
            .expect("pre-fix: async emitter raw-copies cross-encoding string");
        let body = adapter.body.into_raw_body();
        let has_memcopy = body.windows(2).any(|w| w == [0xFC, 0x0A]);
        assert!(
            has_memcopy,
            "STEP-1: cross-encoding async string param raw-copied via memory.copy"
        );
    }

    /// Regression test for the cross-memory ptr-pair stackful return
    /// path. Before v0.8.1 this returned an explicit "deferred to
    /// follow-up" error rather than emit wasm. The fix routes through
    /// `emit_ptr_pair_result_writeback` (shared with the callback
    /// path) so the emitter produces the realloc + memory.copy +
    /// retptr write sequence required by SR-12 / SR-17 for cross-
    /// memory string / list<T> returns.
    ///
    /// The byte-scan asserts the body contains the marker opcodes:
    ///   call             = 0x10  (cabi_realloc + lift call)
    ///   memory.copy      = 0xFC 0x0A  (cross-memory copy of the buffer)
    ///   i32.store        = 0x36  (writing new_ptr and len to retptr)
    ///   end              = 0x0B
    #[test]
    fn stackful_ptr_pair_return_emits_realloc_memcopy_retptr_writes() {
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let mut merged = empty_merged();

        // Caller type: (retptr: i32) -> ()
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![wasm_encoder::ValType::I32],
            results: vec![],
        });
        // Lift type: () -> ()
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![],
            results: vec![],
        });

        // Lift function lives in callee (component 1) at merged idx 0.
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 1,
            body: wasm_encoder::Function::new([]),
            origin: (1, 0, 0),
            synthetic_kind: None,
        });
        merged.function_index_map.insert((1, 0, 0), 0);

        // Caller's cabi_realloc lives at merged idx 1 (defined function).
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 1,
            body: wasm_encoder::Function::new([]),
            origin: (0, 0, 0),
            synthetic_kind: None,
        });
        merged.realloc_map.insert((0, 0), 1);

        // Two memories: caller at idx 0, callee at idx 1.
        merged.memory_index_map.insert((0, 0, 0), 0);
        merged.memory_index_map.insert((1, 0, 0), 1);

        // Result globals: a (ptr, len) pair both i32, with a String
        // result_type so elem_size = 1.
        let lookup_name = "[async-lift]greet".to_string();
        let globals = vec![
            (20u32, wasm_encoder::ValType::I32),
            (21u32, wasm_encoder::ValType::I32),
        ];
        merged
            .async_result_globals
            .insert((1, lookup_name.clone()), globals.clone());
        merged.task_return_shims.insert(
            0,
            crate::merger::TaskReturnShimInfo {
                shim_func: 0,
                result_globals: globals.clone(),
                component_idx: 1,
                import_name: "[task-return]0".into(),
                original_func_name: lookup_name.clone(),
                result_type: Some(crate::parser::ComponentValType::String),
            },
        );

        // Site: from=0 (caller), to=1 (callee), crosses_memory=true.
        let mut site = async_lift_site("[async-lift]greet");
        site.from_component = 0;
        site.to_component = 1;
        site.import_func_type_idx = Some(0);
        site.crosses_memory = true;

        let adapter = gen_
            .generate_async_stackful_adapter(&site, &merged)
            .expect("stackful emitter must succeed for ptr-pair return");

        let body = adapter.body.into_raw_body();

        // memory.copy is encoded as 0xFC 0x0A followed by dst-mem and
        // src-mem indices. The 2-byte prefix is the deterministic marker.
        let has_memcopy = body.windows(2).any(|w| w == [0xFC, 0x0A]);
        assert!(
            has_memcopy,
            "stackful ptr-pair return must emit memory.copy (0xFC 0x0A) \
             for cross-memory buffer copy; body={body:?}",
        );

        // i32.store is opcode 0x36 — must appear at least twice for
        // the retptr (new_ptr at offset 0, len at offset 4).
        let i32_store_count = body.iter().filter(|&&b| b == 0x36).count();
        assert!(
            i32_store_count >= 2,
            "stackful ptr-pair return must emit >=2 i32.store (0x36) \
             for retptr (new_ptr, len); found {i32_store_count} in body \
             ={body:?}",
        );

        // The body must include a call (0x10) — at minimum the
        // cabi_realloc call inside emit_checked_realloc plus the lift
        // call. >=2 is the spec-required minimum.
        let call_count = body.iter().filter(|&&b| b == 0x10).count();
        assert!(
            call_count >= 2,
            "stackful ptr-pair return must emit >=2 call (0x10) — at \
             least cabi_realloc + lift; found {call_count} in body={body:?}",
        );

        assert_eq!(
            body.last(),
            Some(&0x0B),
            "body must end with `end` (0x0B); body={body:?}",
        );
    }

    /// Build a merged module + async-lift site for a SINGLE top-level
    /// `(ptr, len)` STRING RESULT crossing memory (caller has a retptr param,
    /// the lift returns void and writes the result via task.return globals),
    /// with the given caller/callee canon string encodings — for the #272 inc-3
    /// result-side local-bounds integration tests. The caller type (merged type
    /// 0) has one i32 retptr param, so `caller_param_count == 1`. A
    /// `[callback]` companion export is registered so the CALLBACK emitter
    /// dispatches; the stackful test renames it.
    fn xenc_string_result_merged_and_site(
        caller_enc: crate::parser::CanonStringEncoding,
        callee_enc: crate::parser::CanonStringEncoding,
    ) -> (crate::merger::MergedModule, crate::resolver::AdapterSite) {
        use wasm_encoder::{EntityType, ExportKind, Function, ValType};
        let mut merged = empty_merged();
        // type 0: (retptr: i32) -> () — caller type; one retptr param, void.
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![ValType::I32],
            results: Vec::new(),
        });
        // type 1: () -> i32 — lift (callback-mode packed return).
        merged.types.push(crate::merger::MergedFuncType {
            params: Vec::new(),
            results: vec![ValType::I32],
        });
        // type 2: (i32,i32,i32,i32) -> i32 — cabi_realloc.
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![ValType::I32; 4],
            results: vec![ValType::I32],
        });
        // lift func @ merged 0 (callee component 1).
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 1,
            body: Function::new([]),
            origin: (1, 0, 0),
            synthetic_kind: None,
        });
        merged.function_index_map.insert((1, 0, 0), 0);
        // caller's cabi_realloc @ merged 1 (caller component 0) — the result
        // writeback reallocs in CALLER memory.
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 2,
            body: Function::new([]),
            origin: (0, 0, 0),
            synthetic_kind: None,
        });
        merged.realloc_map.insert((0, 0), 1);
        // caller memory = component 0, callee memory = component 1.
        merged.memory_index_map.insert((0, 0, 0), 0);
        merged.memory_index_map.insert((1, 0, 0), 1);

        // Result globals: a (ptr, len) i32 pair with a String result_type so
        // elem_size == 1 (a top-level string result).
        let lookup_name = "[async-lift]greet".to_string();
        let globals = vec![
            (20u32, wasm_encoder::ValType::I32),
            (21u32, wasm_encoder::ValType::I32),
        ];
        merged
            .async_result_globals
            .insert((1, lookup_name.clone()), globals.clone());
        merged.task_return_shims.insert(
            0,
            crate::merger::TaskReturnShimInfo {
                shim_func: 0,
                result_globals: globals.clone(),
                component_idx: 1,
                import_name: "[task-return]0".into(),
                original_func_name: lookup_name.clone(),
                result_type: Some(crate::parser::ComponentValType::String),
            },
        );

        let export_name = "[async-lift]greet";
        merged.exports.push(crate::merger::MergedExport {
            name: format!("[callback]{export_name}"),
            kind: ExportKind::Func,
            index: 0,
        });
        merged.imports.push(crate::merger::MergedImport {
            module: "$root".into(),
            name: "[waitable-set-poll]".into(),
            entity_type: EntityType::Function(0),
            component_idx: None,
        });

        let mut site = async_lift_site(export_name);
        site.from_component = 0;
        site.to_component = 1;
        site.import_func_type_idx = Some(0); // caller type (retptr) → 1 param
        site.crosses_memory = true;
        site.requirements.result_pointer_pair_offsets = vec![0];
        site.requirements.result_copy_layouts =
            vec![crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 }];
        site.requirements.caller_encoding = Some(caller_enc);
        site.requirements.callee_encoding = Some(callee_enc);
        (merged, site)
    }

    /// #272 inc-3 (integration, callback): the CALLBACK async adapter's
    /// top-level STRING RESULT transcode path must not reference a local past
    /// its declared budget. caller=Utf16, callee=Utf8 ⇒ the RESULT transcode
    /// direction (callee→caller) is Utf8→Utf16, an implemented direction. The
    /// result transcode reuses the param-transcode local block (`l_p2 + 16 ..=
    /// l_p2 + 20`, declared by the budget of 26); this proves it for the REAL
    /// adapter — the budget-bug class inc-1 shipped.
    #[test]
    fn inc3_callback_adapter_result_string_locals_within_budget() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let (merged, site) = xenc_string_result_merged_and_site(
            CanonStringEncoding::Utf16,
            CanonStringEncoding::Utf8,
        );
        let adapter = gen_
            .generate_async_callback_adapter(&site, &merged)
            .expect("callback emitter must succeed for the inc-3 result-string site");
        let cpc = site_caller_param_count(&site, &merged);
        assert_locals_within_budget(adapter.body, cpc, "#272 inc-3 callback result");
    }

    /// #272 inc-3 (integration, stackful): the STACKFUL async adapter's
    /// top-level STRING RESULT transcode path must likewise stay within its
    /// declared budget (18); the result transcode reuses the param-transcode
    /// block `l_scratch + 12 ..= l_scratch + 16`.
    #[test]
    fn inc3_stackful_adapter_result_string_locals_within_budget() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let (mut merged, site) = xenc_string_result_merged_and_site(
            CanonStringEncoding::Utf16,
            CanonStringEncoding::Utf8,
        );
        // The stackful path dispatches on a non-`[callback]` export; rename the
        // companion so `generate_async_stackful_adapter` is under test.
        merged.exports[0].name = site.export_name.clone();
        let adapter = gen_
            .generate_async_stackful_adapter(&site, &merged)
            .expect("stackful emitter must succeed for the inc-3 result-string site");
        let cpc = site_caller_param_count(&site, &merged);
        assert_locals_within_budget(adapter.body, cpc, "#272 inc-3 stackful result");
    }

    /// #272 inc-4c (integration, callback): the CALLBACK async adapter's
    /// top-level latin1 STRING RESULT transcode path must not reference a local
    /// past its declared budget (27). The latin1 result loops reuse the
    /// param-transcode block `transcode_base = l_p2 + 16` with ≤ 6 scratch
    /// (`l_p2 + 16 ..= l_p2 + 21`, offsets 21..=26 — top index offset 26 < 27),
    /// the SAME six the inc-4a/4b PARAM loops occupy, never colliding with the
    /// result-writeback live locals (`l_p2 + 1 ..= l_p2 + 10`). Covers BOTH the
    /// source-latin1 result case (callee=CompactUtf16, caller=Utf16 ⇒ result dir
    /// latin1→utf16, the 4-scratch loop) AND the dest-latin1 result case
    /// (callee=Utf8, caller=CompactUtf16 ⇒ result dir utf8→latin1, the 6-scratch
    /// two-phase loop — the worst case for the budget). Generates the REAL
    /// adapters — the budget-bug class inc-1 shipped.
    #[test]
    fn inc4c_callback_adapter_latin1_result_locals_within_budget() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());

        // Source-latin1 result: callee=CompactUtf16 → caller=Utf16 (4 scratch).
        let (merged_src, site_src) = xenc_string_result_merged_and_site(
            CanonStringEncoding::Utf16,
            CanonStringEncoding::CompactUtf16,
        );
        let adapter_src = gen_
            .generate_async_callback_adapter(&site_src, &merged_src)
            .expect("callback emitter must succeed for the inc-4c latin1-source result site");
        let cpc_src = site_caller_param_count(&site_src, &merged_src);
        assert_locals_within_budget(
            adapter_src.body,
            cpc_src,
            "#272 inc-4c callback latin1-source result",
        );

        // Dest-latin1 result: callee=Utf8 → caller=CompactUtf16 (6 scratch, the
        // two-phase tag-producing loop — the budget worst case).
        let (merged_dst, site_dst) = xenc_string_result_merged_and_site(
            CanonStringEncoding::CompactUtf16,
            CanonStringEncoding::Utf8,
        );
        let adapter_dst = gen_
            .generate_async_callback_adapter(&site_dst, &merged_dst)
            .expect("callback emitter must succeed for the inc-4c dest-latin1 result site");
        let cpc_dst = site_caller_param_count(&site_dst, &merged_dst);
        assert_locals_within_budget(
            adapter_dst.body,
            cpc_dst,
            "#272 inc-4c callback dest-latin1 result",
        );
    }

    /// #272 inc-4c (integration, stackful): the STACKFUL async adapter's
    /// top-level latin1 STRING RESULT transcode path must likewise stay within
    /// its declared budget (18). The latin1 result loops reuse `transcode_base =
    /// l_scratch + 12` with ≤ 6 scratch (offsets 12..=17 — top index < 18),
    /// never colliding with the writeback region `l_scratch + 1 ..= l_scratch +
    /// 10`. Covers both the source-latin1 and dest-latin1 result cases.
    #[test]
    fn inc4c_stackful_adapter_latin1_result_locals_within_budget() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());

        // Source-latin1 result: callee=CompactUtf16 → caller=Utf16 (4 scratch).
        let (mut merged_src, site_src) = xenc_string_result_merged_and_site(
            CanonStringEncoding::Utf16,
            CanonStringEncoding::CompactUtf16,
        );
        merged_src.exports[0].name = site_src.export_name.clone();
        let adapter_src = gen_
            .generate_async_stackful_adapter(&site_src, &merged_src)
            .expect("stackful emitter must succeed for the inc-4c latin1-source result site");
        let cpc_src = site_caller_param_count(&site_src, &merged_src);
        assert_locals_within_budget(
            adapter_src.body,
            cpc_src,
            "#272 inc-4c stackful latin1-source result",
        );

        // Dest-latin1 result: callee=Utf8 → caller=CompactUtf16 (6 scratch).
        let (mut merged_dst, site_dst) = xenc_string_result_merged_and_site(
            CanonStringEncoding::CompactUtf16,
            CanonStringEncoding::Utf8,
        );
        merged_dst.exports[0].name = site_dst.export_name.clone();
        let adapter_dst = gen_
            .generate_async_stackful_adapter(&site_dst, &merged_dst)
            .expect("stackful emitter must succeed for the inc-4c dest-latin1 result site");
        let cpc_dst = site_caller_param_count(&site_dst, &merged_dst);
        assert_locals_within_budget(
            adapter_dst.body,
            cpc_dst,
            "#272 inc-4c stackful dest-latin1 result",
        );
    }

    /// Build a merged module + async-lift site for a NESTED `list<string>`
    /// RESULT crossing memory (caller has a retptr param, the lift returns void
    /// and writes the result via task.return globals), with the given
    /// caller/callee canon string encodings — for the #272 inc-5a result-side
    /// local-bounds integration tests. Mirrors `xenc_string_result_merged_and_site`
    /// but the result is `list<string>` (`result_type = List(String)`,
    /// `Elements{8, [Bulk{1}]}` layout) so the nested-indirection walk (and, in
    /// the Utf8→Utf16 direction, the inner transcode that runs INSIDE the nested
    /// per-element loop) is exercised on the REAL adapter — the highest-risk
    /// simultaneous-liveness budget case.
    fn xenc_list_string_result_merged_and_site(
        caller_enc: crate::parser::CanonStringEncoding,
        callee_enc: crate::parser::CanonStringEncoding,
    ) -> (crate::merger::MergedModule, crate::resolver::AdapterSite) {
        use wasm_encoder::{EntityType, ExportKind, Function, ValType};
        let mut merged = empty_merged();
        // type 0: (retptr: i32) -> () — caller type; one retptr param, void.
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![ValType::I32],
            results: Vec::new(),
        });
        // type 1: () -> i32 — lift (callback-mode packed return).
        merged.types.push(crate::merger::MergedFuncType {
            params: Vec::new(),
            results: vec![ValType::I32],
        });
        // type 2: (i32,i32,i32,i32) -> i32 — cabi_realloc.
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![ValType::I32; 4],
            results: vec![ValType::I32],
        });
        // lift func @ merged 0 (callee component 1).
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 1,
            body: Function::new([]),
            origin: (1, 0, 0),
            synthetic_kind: None,
        });
        merged.function_index_map.insert((1, 0, 0), 0);
        // caller's cabi_realloc @ merged 1 (caller component 0).
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 2,
            body: Function::new([]),
            origin: (0, 0, 0),
            synthetic_kind: None,
        });
        merged.realloc_map.insert((0, 0), 1);
        // caller memory = component 0, callee memory = component 1.
        merged.memory_index_map.insert((0, 0, 0), 0);
        merged.memory_index_map.insert((1, 0, 0), 1);

        // The nested-result element type: `string` (so the outer result is
        // `list<string>`).
        let list_string = crate::parser::ComponentValType::List(Box::new(
            crate::parser::ComponentValType::String,
        ));

        // Result globals: a (ptr, len) i32 pair with a `list<string>`
        // result_type so the writeback walks nested indirections.
        let lookup_name = "[async-lift]greet".to_string();
        let globals = vec![
            (20u32, wasm_encoder::ValType::I32),
            (21u32, wasm_encoder::ValType::I32),
        ];
        merged
            .async_result_globals
            .insert((1, lookup_name.clone()), globals.clone());
        merged.task_return_shims.insert(
            0,
            crate::merger::TaskReturnShimInfo {
                shim_func: 0,
                result_globals: globals.clone(),
                component_idx: 1,
                import_name: "[task-return]0".into(),
                original_func_name: lookup_name.clone(),
                result_type: Some(list_string.clone()),
            },
        );

        let export_name = "[async-lift]greet";
        merged.exports.push(crate::merger::MergedExport {
            name: format!("[callback]{export_name}"),
            kind: ExportKind::Func,
            index: 0,
        });
        merged.imports.push(crate::merger::MergedImport {
            module: "$root".into(),
            name: "[waitable-set-poll]".into(),
            entity_type: EntityType::Function(0),
            component_idx: None,
        });

        let mut site = async_lift_site(export_name);
        site.from_component = 0;
        site.to_component = 1;
        site.import_func_type_idx = Some(0); // caller type (retptr) → 1 param
        site.crosses_memory = true;
        site.requirements.result_pointer_pair_offsets = vec![0];
        // `list<string>` lowers to `Elements{element_size: 8, inner: [Bulk{1}]}`.
        site.requirements.result_copy_layouts = vec![crate::resolver::CopyLayout::Elements {
            element_size: 8,
            inner_pointers: vec![crate::resolver::InnerPointer::unconditional(
                0,
                crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 },
            )],
            inner_resources: Vec::new(),
        }];
        site.requirements.result_wit_types = vec![list_string];
        site.requirements.caller_encoding = Some(caller_enc);
        site.requirements.callee_encoding = Some(callee_enc);
        (merged, site)
    }

    /// #272 inc-5a (integration, callback): the CALLBACK async adapter's NESTED
    /// `list<string>` RESULT transcode path (callee=Utf8 → caller=Utf16) must not
    /// reference a local past its declared budget (27) under SIMULTANEOUS
    /// liveness — the inner transcode runs INSIDE the nested per-element loop, so
    /// the nested-loop locals (`l_p2 + 5 ..= l_p2 + 10`, offsets 10..=15) AND the
    /// transcode-loop locals (`l_p2 + 16 ..= l_p2 + 20`, offsets 21..=25) are live
    /// at once. They are DISJOINT and the top index (offset 25) < 27. Generates
    /// the REAL adapter for a `list<string>` result site — the budget-bug class
    /// inc-1 shipped, now under the worst-case simultaneous-liveness shape.
    #[test]
    fn inc5a_callback_adapter_nested_result_locals_within_budget() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        // callee=Utf8 → caller=Utf16 ⇒ the RESULT direction transcodes the inner
        // strings (the implemented inc-5a direction).
        let (merged, site) = xenc_list_string_result_merged_and_site(
            CanonStringEncoding::Utf16,
            CanonStringEncoding::Utf8,
        );
        let adapter = gen_
            .generate_async_callback_adapter(&site, &merged)
            .expect("callback emitter must succeed for the inc-5a list<string> result site");
        let cpc = site_caller_param_count(&site, &merged);
        assert_locals_within_budget(adapter.body, cpc, "#272 inc-5a callback nested result");
    }

    /// #272 inc-5a (integration, stackful): the STACKFUL async adapter's NESTED
    /// `list<string>` RESULT transcode path must likewise stay within its declared
    /// budget (18) under simultaneous liveness — nested loop `l_scratch + 5 ..=
    /// l_scratch + 10` (offsets 5..=10) vs transcode `l_scratch + 12 ..= l_scratch
    /// + 16` (offsets 12..=16), DISJOINT, top index (offset 16) < 18.
    #[test]
    fn inc5a_stackful_adapter_nested_result_locals_within_budget() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let (mut merged, site) = xenc_list_string_result_merged_and_site(
            CanonStringEncoding::Utf16,
            CanonStringEncoding::Utf8,
        );
        // The stackful path dispatches on a non-`[callback]` export; rename the
        // companion so `generate_async_stackful_adapter` is under test.
        merged.exports[0].name = site.export_name.clone();
        let adapter = gen_
            .generate_async_stackful_adapter(&site, &merged)
            .expect("stackful emitter must succeed for the inc-5a list<string> result site");
        let cpc = site_caller_param_count(&site, &merged);
        assert_locals_within_budget(adapter.body, cpc, "#272 inc-5a stackful nested result");
    }

    /// #272 inc-5a guard: a NESTED `list<string>` RESULT in the callee=Utf8 →
    /// caller=Utf16 direction is now ALLOWED (the emitter transcodes its inner
    /// strings). The guard must NOT fail loud.
    #[test]
    fn inc5a_async_nested_list_string_result_utf8_to_utf16_allowed() {
        use crate::parser::CanonStringEncoding;
        let (_merged, site) = xenc_list_string_result_merged_and_site(
            CanonStringEncoding::Utf16, // caller READS Utf16
            CanonStringEncoding::Utf8,  // callee PRODUCES Utf8
        );
        FactStyleGenerator::guard_async_cross_encoding_strings(&site).expect(
            "#272 inc-5a: a nested list<string> result in callee=Utf8 → caller=Utf16 \
             must be ALLOWED (the emitter transcodes the inner strings)",
        );
    }

    /// #272 inc-5a guard (NEGATIVE — blocker): a NESTED `list<u8>` RESULT (here a
    /// `list<list<u8>>`) must stay FAIL-LOUD even in the Utf8 → Utf16 direction:
    /// a nested `list<u8>` is `is_string == false`, so it is raw-copied, NOT
    /// transcoded — the guard's allow-set must not widen to it (no allow-but-raw-
    /// copy gap). The guard consults the SAME `collect_indirections` string-ness
    /// signal as the emitter, so it correctly rejects this.
    #[test]
    fn inc5a_async_nested_list_u8_result_not_transcoded() {
        use crate::parser::{CanonStringEncoding, ComponentValType, PrimitiveValType};
        let (_merged, mut site) = xenc_list_string_result_merged_and_site(
            CanonStringEncoding::Utf16,
            CanonStringEncoding::Utf8,
        );
        // Replace the result with `list<list<u8>>` — the inner element is
        // `list<u8>` (is_string == false). The lowered layout is identical to a
        // `list<string>` outer shape's at the descriptor level (Elements with an
        // inner byte-granular pointer), proving the guard cannot rely on layout
        // alone and must consult the WIT string-ness signal.
        let list_list_u8 = ComponentValType::List(Box::new(ComponentValType::List(Box::new(
            ComponentValType::Primitive(PrimitiveValType::U8),
        ))));
        site.requirements.result_wit_types = vec![list_list_u8];
        // Outer element is `list<u8>` ⇒ element_size 4 (a (ptr,len) pair lowering
        // is still Elements with an inner Bulk{1}); the descriptor is byte-granular
        // at the inner level exactly like list<string>.
        site.requirements.result_copy_layouts = vec![crate::resolver::CopyLayout::Elements {
            element_size: 8,
            inner_pointers: vec![crate::resolver::InnerPointer::unconditional(
                0,
                crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 },
            )],
            inner_resources: Vec::new(),
        }];
        let err = FactStyleGenerator::guard_async_cross_encoding_strings(&site)
            .expect_err("#272 inc-5a: a nested list<u8> result must stay FAIL-LOUD");
        assert!(
            matches!(err, crate::Error::AdapterGeneration(_)),
            "expected AdapterGeneration fail-loud for nested list<u8>, got {err:?}"
        );
    }

    /// #272 inc-5a guard (NEGATIVE — other direction): a nested `list<string>`
    /// RESULT in a direction OTHER than callee=Utf8 → caller=Utf16 (here
    /// callee=Utf16 → caller=Utf8) stays FAIL-LOUD — inc-5a implements ONLY the
    /// single utf8→utf16 result direction for nested strings.
    #[test]
    fn inc5a_async_nested_list_string_result_other_direction_fails_loud() {
        use crate::parser::CanonStringEncoding;
        let (_merged, site) = xenc_list_string_result_merged_and_site(
            CanonStringEncoding::Utf8,  // caller READS Utf8
            CanonStringEncoding::Utf16, // callee PRODUCES Utf16
        );
        let err = FactStyleGenerator::guard_async_cross_encoding_strings(&site).expect_err(
            "#272 inc-5a: a nested list<string> result in callee=Utf16 → caller=Utf8 \
             must stay FAIL-LOUD (only utf8→utf16 nested is implemented)",
        );
        assert!(
            matches!(err, crate::Error::AdapterGeneration(_)),
            "expected AdapterGeneration fail-loud, got {err:?}"
        );
    }

    /// #272 inc-5a guard (NEGATIVE — nested PARAM): a nested `list<string>` PARAM
    /// (as opposed to a result) stays FAIL-LOUD — inc-5a only extends the RESULT
    /// side; nested params remain raw-copied / fail-loud.
    #[test]
    fn inc5a_async_nested_list_string_param_still_fails_loud() {
        use crate::parser::CanonStringEncoding;
        let mut site = async_lift_site("[async-lift]take");
        site.from_component = 0;
        site.to_component = 1;
        site.crosses_memory = true;
        // A nested `list<string>` PARAM: top-level Elements{8} with an inner
        // Bulk{1} string. Param direction utf8→utf16 (an implemented TOP-LEVEL
        // direction) — but NESTED params are not implemented, so it must fail.
        site.requirements.pointer_pair_positions = vec![0];
        site.requirements.param_copy_layouts = vec![crate::resolver::CopyLayout::Elements {
            element_size: 8,
            inner_pointers: vec![crate::resolver::InnerPointer::unconditional(
                0,
                crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 },
            )],
            inner_resources: Vec::new(),
        }];
        site.requirements.caller_encoding = Some(CanonStringEncoding::Utf8);
        site.requirements.callee_encoding = Some(CanonStringEncoding::Utf16);
        let err = FactStyleGenerator::guard_async_cross_encoding_strings(&site).expect_err(
            "#272 inc-5a: a nested list<string> PARAM must stay FAIL-LOUD (inc-5a \
             extends only the RESULT side)",
        );
        assert!(
            matches!(err, crate::Error::AdapterGeneration(_)),
            "expected AdapterGeneration fail-loud for nested param, got {err:?}"
        );
    }

    /// Regression test for the alignment-padding bug surfaced by the
    /// v0.8.0 pre-release Mythos delta-pass on adapter/fact.rs.
    ///
    /// The stackful and callback emitters both advance the retptr
    /// write offset by only the flat size of each result global (4 or
    /// 8 bytes) without aligning up to the next field's natural
    /// alignment. For a result whose flat lowering contains
    /// `[I32, I64]` (record `{u32, u64}`, tuple `(s32, s64)`,
    /// `result<u64, u32>`, etc.), the canonical-ABI offset of the i64
    /// is 8 (i32 at 0, 4 bytes padding, i64 at 8 — record size 16).
    /// The emitter produced 4. Callers reading the retptr per CABI
    /// see stale/zero bytes for the high-order field.
    ///
    /// Hazard: H-4 (canonical ABI lowering mismatch). Maps to UCA-A-13
    /// generically — the stated context is "variants with i64/f64
    /// payload" but any aggregate whose flat lowering interleaves
    /// 4-byte and 8-byte fields realises the same defect.
    ///
    /// Engines treat MemArg `align` as a hint, so this is silent data
    /// corruption with no trap.
    #[test]
    fn cabi_alignment_stackful_retptr_writes_i64_at_offset_8() {
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let mut merged = empty_merged();

        // Caller type: (retptr: i32) -> ()
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![wasm_encoder::ValType::I32],
            results: vec![],
        });
        // Lift type: () -> ()
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![],
            results: vec![],
        });
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 1,
            body: wasm_encoder::Function::new([]),
            origin: (1, 0, 0),
            synthetic_kind: None,
        });
        merged.function_index_map.insert((1, 0, 0), 0);

        let lookup_name = "[async-lift]mixed".to_string();
        let globals = vec![
            (10u32, wasm_encoder::ValType::I32),
            (11u32, wasm_encoder::ValType::I64),
        ];
        merged
            .async_result_globals
            .insert((1, lookup_name.clone()), globals.clone());
        merged.task_return_shims.insert(
            0,
            crate::merger::TaskReturnShimInfo {
                shim_func: 0,
                result_globals: globals.clone(),
                component_idx: 1,
                import_name: "[task-return]0".into(),
                original_func_name: lookup_name.clone(),
                result_type: None,
            },
        );

        let mut site = async_lift_site("[async-lift]mixed");
        site.import_func_type_idx = Some(0);
        site.crosses_memory = false;

        let adapter = gen_
            .generate_async_stackful_adapter(&site, &merged)
            .expect("stackful emitter must succeed");

        let raw = adapter.body.into_raw_body();

        // i64.store opcode is 0x37 followed by LEB align then LEB offset.
        let mut i = 0;
        let mut found_offset: Option<u64> = None;
        while i < raw.len() {
            if raw[i] == 0x37 {
                let (_align, n1) = read_uleb(&raw[i + 1..]);
                let (offset, _n2) = read_uleb(&raw[i + 1 + n1..]);
                found_offset = Some(offset);
                break;
            }
            i += 1;
        }

        let offset = found_offset.expect("body must contain i64.store");
        assert_eq!(
            offset, 8,
            "i64 result must store at CABI-aligned offset 8 for record \
             {{i32, i64}} (i32 at 0, 4 bytes padding, i64 at 8); emitter \
             produced offset {offset} — callers reading retptr per CABI \
             would see stale bytes",
        );
    }

    /// LS-N verification gate convention alias. Pins LS-A-10
    /// (async-lift retptr writeback skips CABI alignment padding)
    /// via the discoverable `ls_a_10_*` name. Same body as the
    /// pre-existing `cabi_alignment_stackful_retptr_writes_i64_at_offset_8`
    /// regression test.
    #[test]
    fn ls_a_10_cabi_align_retptr_writeback() {
        cabi_alignment_stackful_retptr_writes_i64_at_offset_8();
    }

    /// LS-A-9: `generate_async_callback_adapter` must dispatch
    /// `[waitable-set-poll]` on **both** `WAIT (2)` and `POLL (3)`.
    /// The pre-fix `if code == WAIT` branch let POLL fall through to
    /// the YIELD path, which sent `(EVENT_NONE, 0, 0)` to `[callback]`
    /// and dropped any event the host had ready — silent semantic
    /// drift between fused and composed modules with no host trap.
    ///
    /// Asserts the WAIT/POLL OR-pattern is present in the emitted
    /// adapter body: the byte sequence
    ///
    ///     local.get l_code (0x20 <leb128>)
    ///     i32.const WAIT=2 (0x41 0x02)
    ///     i32.eq           (0x46)
    ///     local.get l_code (0x20 <leb128>)
    ///     i32.const POLL=3 (0x41 0x03)
    ///     i32.eq           (0x46)
    ///     i32.or           (0x72)
    ///
    /// Pin-by-substring is robust against unrelated body changes
    /// (locals layout, surrounding control flow) — what we care about
    /// is that `i32.const 2 / i32.eq / i32.const 3 / i32.eq / i32.or`
    /// appears in that order somewhere in the loop body.
    /// Regression for #272 inc-1 (integration, not just loop logic): the
    /// callback async adapter's UTF-8→UTF-16 string-param transcode path must
    /// not reference a local past its declared budget. As shipped, the budget
    /// was 22 (top addressable local `caller_params + 21`) but the transcode
    /// loop reaches `caller_params + 25`, so the generated callback adapter
    /// failed wasm validation ("unknown local 24") for exactly the inc-1 case.
    /// An adversarial Mythos pass found this: the runtime oracle drives the
    /// transcode *emitter* via a synthetic module with a large-enough local
    /// block, so it never exercised the real callback adapter's budget. This
    /// generates the REAL callback adapter for the inc-1 site and asserts every
    /// referenced local is addressable (params + declared locals).
    #[test]
    fn inc1_callback_adapter_transcode_locals_within_budget() {
        use wasm_encoder::{EntityType, ExportKind, Function, ValType};
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let mut merged = empty_merged();
        // type 0: () -> i32 (lift, callback-mode packed return).
        merged.types.push(crate::merger::MergedFuncType {
            params: Vec::new(),
            results: vec![ValType::I32],
        });
        // type 1: (i32, i32) -> () — caller type, one (ptr,len) string param.
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![ValType::I32, ValType::I32],
            results: Vec::new(),
        });
        // type 2: (i32,i32,i32,i32) -> i32 — cabi_realloc.
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![ValType::I32; 4],
            results: vec![ValType::I32],
        });
        // lift func @ merged 0, realloc func @ merged 1.
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 0,
            body: Function::new([]),
            origin: (1, 0, 0),
            synthetic_kind: None,
        });
        merged.function_index_map.insert((1, 0, 0), 0);
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 2,
            body: Function::new([]),
            origin: (1, 0, 1),
            synthetic_kind: None,
        });
        merged.realloc_map.insert((1, 0), 1);
        // caller memory = component 0, callee memory = component 1.
        merged.memory_index_map.insert((0, 0, 0), 0);
        merged.memory_index_map.insert((1, 0, 0), 1);
        let export_name = "[async-lift]greet";
        merged.exports.push(crate::merger::MergedExport {
            name: format!("[callback]{export_name}"),
            kind: ExportKind::Func,
            index: 0,
        });
        merged.imports.push(crate::merger::MergedImport {
            module: "$root".into(),
            name: "[waitable-set-poll]".into(),
            entity_type: EntityType::Function(0),
            component_idx: None,
        });

        let mut site = async_lift_site(export_name);
        site.from_component = 0;
        site.to_component = 1;
        site.import_func_type_idx = Some(1); // caller type (i32,i32) → 2 params
        site.crosses_memory = true;
        site.requirements.pointer_pair_positions = vec![0];
        site.requirements.param_copy_layouts =
            vec![crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 }];
        site.requirements.caller_encoding = Some(crate::parser::CanonStringEncoding::Utf8);
        site.requirements.callee_encoding = Some(crate::parser::CanonStringEncoding::Utf16);

        let adapter = gen_
            .generate_async_callback_adapter(&site, &merged)
            .expect("callback emitter must succeed for the inc-1 utf8→utf16 string-param site");

        let caller_param_count = 2u32; // type 1 has two i32 params
        let raw = adapter.body.into_raw_body();
        let fb = wasmparser::FunctionBody::new(wasmparser::BinaryReader::new(&raw, 0));
        let mut declared = 0u32;
        for lp in fb.get_locals_reader().expect("locals reader") {
            let (count, _ty) = lp.expect("local pair");
            declared += count;
        }
        let total_locals = caller_param_count + declared;
        let mut max_idx = 0u32;
        let mut found = false;
        for op in fb.get_operators_reader().expect("ops reader") {
            match op.expect("operator") {
                wasmparser::Operator::LocalGet { local_index }
                | wasmparser::Operator::LocalSet { local_index }
                | wasmparser::Operator::LocalTee { local_index } => {
                    found = true;
                    max_idx = max_idx.max(local_index);
                }
                _ => {}
            }
        }
        assert!(found, "adapter body should reference locals");
        assert!(
            max_idx < total_locals,
            "#272 inc-1: callback adapter references local {max_idx} but only \
             {total_locals} are addressable ({caller_param_count} params + \
             {declared} declared) — transcode locals overflow the budget",
        );
    }

    /// Build a merged module + async-lift site for a SINGLE top-level
    /// `(ptr, len)` string param crossing memory, with the given caller/callee
    /// canon string encodings, for the inc-2 local-bounds integration tests.
    /// The caller type (merged type 1) has two i32 params, so
    /// `caller_param_count == 2`.
    fn xenc_string_param_merged_and_site(
        caller_enc: crate::parser::CanonStringEncoding,
        callee_enc: crate::parser::CanonStringEncoding,
    ) -> (crate::merger::MergedModule, crate::resolver::AdapterSite) {
        use wasm_encoder::{EntityType, ExportKind, Function, ValType};
        let mut merged = empty_merged();
        // type 0: () -> i32 (lift, callback-mode packed return).
        merged.types.push(crate::merger::MergedFuncType {
            params: Vec::new(),
            results: vec![ValType::I32],
        });
        // type 1: (i32, i32) -> () — caller type, one (ptr,len) string param.
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![ValType::I32, ValType::I32],
            results: Vec::new(),
        });
        // type 2: (i32,i32,i32,i32) -> i32 — cabi_realloc.
        merged.types.push(crate::merger::MergedFuncType {
            params: vec![ValType::I32; 4],
            results: vec![ValType::I32],
        });
        // lift func @ merged 0, realloc func @ merged 1.
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 0,
            body: Function::new([]),
            origin: (1, 0, 0),
            synthetic_kind: None,
        });
        merged.function_index_map.insert((1, 0, 0), 0);
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 2,
            body: Function::new([]),
            origin: (1, 0, 1),
            synthetic_kind: None,
        });
        merged.realloc_map.insert((1, 0), 1);
        // caller memory = component 0, callee memory = component 1.
        merged.memory_index_map.insert((0, 0, 0), 0);
        merged.memory_index_map.insert((1, 0, 0), 1);
        let export_name = "[async-lift]greet";
        merged.exports.push(crate::merger::MergedExport {
            name: format!("[callback]{export_name}"),
            kind: ExportKind::Func,
            index: 0,
        });
        merged.imports.push(crate::merger::MergedImport {
            module: "$root".into(),
            name: "[waitable-set-poll]".into(),
            entity_type: EntityType::Function(0),
            component_idx: None,
        });

        let mut site = async_lift_site(export_name);
        site.from_component = 0;
        site.to_component = 1;
        site.import_func_type_idx = Some(1); // caller type (i32,i32) → 2 params
        site.crosses_memory = true;
        site.requirements.pointer_pair_positions = vec![0];
        site.requirements.param_copy_layouts =
            vec![crate::resolver::CopyLayout::Bulk { byte_multiplier: 1 }];
        site.requirements.caller_encoding = Some(caller_enc);
        site.requirements.callee_encoding = Some(callee_enc);
        (merged, site)
    }

    /// Derive the REAL caller param count for an async-lift site, exactly as
    /// the callback/stackful emitters do: resolve `site.import_func_type_idx`
    /// (the caller's local type index) through `merged.type_index_map` to the
    /// merged func type, and take its param count. This is the same value
    /// `generate_async_{callback,stackful}_adapter` use to lay out the local
    /// block, so the local-bounds assertion below is tight for ALL increments
    /// rather than assuming a fixed `2` (the inc-4a Mythos accuracy flag).
    fn site_caller_param_count(
        site: &crate::resolver::AdapterSite,
        merged: &crate::merger::MergedModule,
    ) -> u32 {
        let caller_type_idx = site
            .import_func_type_idx
            .and_then(|local_ti| {
                merged
                    .type_index_map
                    .get(&(site.from_component, site.from_module, local_ti))
                    .copied()
            })
            .unwrap_or(0);
        merged
            .types
            .get(caller_type_idx as usize)
            .map(|t| t.params.len() as u32)
            .unwrap_or(0)
    }

    /// Assert that every local referenced in `adapter_body` is addressable
    /// given `caller_param_count` params plus the declared local count.
    fn assert_locals_within_budget(
        adapter_body: wasm_encoder::Function,
        caller_param_count: u32,
        label: &str,
    ) {
        let raw = adapter_body.into_raw_body();
        let fb = wasmparser::FunctionBody::new(wasmparser::BinaryReader::new(&raw, 0));
        let mut declared = 0u32;
        for lp in fb.get_locals_reader().expect("locals reader") {
            let (count, _ty) = lp.expect("local pair");
            declared += count;
        }
        let total_locals = caller_param_count + declared;
        let mut max_idx = 0u32;
        let mut found = false;
        for op in fb.get_operators_reader().expect("ops reader") {
            match op.expect("operator") {
                wasmparser::Operator::LocalGet { local_index }
                | wasmparser::Operator::LocalSet { local_index }
                | wasmparser::Operator::LocalTee { local_index } => {
                    found = true;
                    max_idx = max_idx.max(local_index);
                }
                _ => {}
            }
        }
        assert!(found, "{label}: adapter body should reference locals");
        assert!(
            max_idx < total_locals,
            "{label}: adapter references local {max_idx} but only {total_locals} \
             are addressable ({caller_param_count} params + {declared} declared) \
             — transcode locals overflow the budget",
        );
    }

    /// #272 inc-2 (integration, callback): the CALLBACK async adapter's
    /// UTF-16→UTF-8 string-param transcode path must not reference a local past
    /// its declared budget. The inc-2 transcode loop uses the SAME number of
    /// scratch locals (5: src_idx, dst_idx, cp, cu, cu2) as inc-1, so the
    /// callback budget of 26 (top addressable `caller_params + 25`; transcode
    /// top `caller_params + 25`) already suffices — but the runtime oracle (a
    /// synthetic module with a large local block) can't prove that for the REAL
    /// adapter, so this generates it and asserts every referenced local is
    /// addressable. This is the integration check that caught the inc-1
    /// "unknown local 24" bug.
    #[test]
    fn inc2_callback_adapter_utf16_to_utf8_locals_within_budget() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let (merged, site) = xenc_string_param_merged_and_site(
            CanonStringEncoding::Utf16,
            CanonStringEncoding::Utf8,
        );
        let adapter = gen_
            .generate_async_callback_adapter(&site, &merged)
            .expect("callback emitter must succeed for the inc-2 utf16→utf8 string-param site");
        let cpc = site_caller_param_count(&site, &merged);
        assert_locals_within_budget(adapter.body, cpc, "#272 inc-2 callback");
    }

    /// #272 inc-2 (integration, stackful): the STACKFUL async adapter's
    /// UTF-16→UTF-8 string-param transcode path must likewise stay within its
    /// declared budget (18; `transcode_base = l_scratch + 12`, top
    /// `caller_params + 16` ≤ `caller_params + 17`). Inc 1 added only the
    /// callback bounds test; this adds the stackful variant so BOTH async
    /// emitters are integration-checked for the implemented transcode site.
    #[test]
    fn inc2_stackful_adapter_utf16_to_utf8_locals_within_budget() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let (mut merged, mut site) = xenc_string_param_merged_and_site(
            CanonStringEncoding::Utf16,
            CanonStringEncoding::Utf8,
        );
        // The stackful path dispatches on a non-`[callback]` export; rename the
        // export so `generate_async_stackful_adapter` is the one under test.
        merged.exports[0].name = site.export_name.clone();
        site.requirements.caller_encoding = Some(CanonStringEncoding::Utf16);
        site.requirements.callee_encoding = Some(CanonStringEncoding::Utf8);
        let adapter = gen_
            .generate_async_stackful_adapter(&site, &merged)
            .expect("stackful emitter must succeed for the inc-2 utf16→utf8 string-param site");
        let cpc = site_caller_param_count(&site, &merged);
        assert_locals_within_budget(adapter.body, cpc, "#272 inc-2 stackful");
    }

    /// #272 inc-4a (integration, callback): the CALLBACK async adapter's
    /// latin1-SOURCE string-param transcode path must not reference a local past
    /// its declared budget. The `Latin1 → UTF-8` tag-dispatch loop uses 6
    /// scratch locals (tag, src_idx, dst_idx, cp, cu, cu2) at
    /// `transcode_base = l_p2 + 16`, i.e. offsets 21..=26 — top
    /// `caller_params + 26`, which required GROWING the callback budget 26 → 27.
    /// This generates the REAL adapter for both latin1-source sites (callee=Utf8
    /// AND callee=Utf16) and asserts every referenced local is addressable — the
    /// integration check the loop-only runtime oracle cannot reach (the same
    /// budget-bug class inc-1 shipped).
    #[test]
    fn inc4a_callback_adapter_latin1_source_locals_within_budget() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        // callee=Utf8 is the wider (6-scratch) loop — the one that grew the budget.
        let (merged8, site8) = xenc_string_param_merged_and_site(
            CanonStringEncoding::CompactUtf16,
            CanonStringEncoding::Utf8,
        );
        let adapter8 = gen_
            .generate_async_callback_adapter(&site8, &merged8)
            .expect("callback emitter must succeed for the inc-4a latin1→utf8 string-param site");
        let cpc8 = site_caller_param_count(&site8, &merged8);
        assert_locals_within_budget(adapter8.body, cpc8, "#272 inc-4a callback latin1→utf8");

        let (merged16, site16) = xenc_string_param_merged_and_site(
            CanonStringEncoding::CompactUtf16,
            CanonStringEncoding::Utf16,
        );
        let adapter16 = gen_
            .generate_async_callback_adapter(&site16, &merged16)
            .expect("callback emitter must succeed for the inc-4a latin1→utf16 string-param site");
        let cpc16 = site_caller_param_count(&site16, &merged16);
        assert_locals_within_budget(adapter16.body, cpc16, "#272 inc-4a callback latin1→utf16");
    }

    /// #272 inc-4a (integration, stackful): the STACKFUL async adapter's
    /// latin1-SOURCE string-param transcode path must stay within its declared
    /// budget (18). The `Latin1 → UTF-8` loop uses 6 scratch at
    /// `transcode_base = l_scratch + 12`, i.e. offsets 12..=17 — top
    /// `caller_params + 17` < 18, so the stackful variant fits WITHOUT growing
    /// (only the callback variant grew). Generates the REAL adapter for both
    /// latin1-source sites (callee=Utf8 AND callee=Utf16).
    #[test]
    fn inc4a_stackful_adapter_latin1_source_locals_within_budget() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let (mut merged8, site8) = xenc_string_param_merged_and_site(
            CanonStringEncoding::CompactUtf16,
            CanonStringEncoding::Utf8,
        );
        // Stackful dispatches on a non-`[callback]` export; rename the companion.
        merged8.exports[0].name = site8.export_name.clone();
        let adapter8 = gen_
            .generate_async_stackful_adapter(&site8, &merged8)
            .expect("stackful emitter must succeed for the inc-4a latin1→utf8 string-param site");
        let cpc8 = site_caller_param_count(&site8, &merged8);
        assert_locals_within_budget(adapter8.body, cpc8, "#272 inc-4a stackful latin1→utf8");

        let (mut merged16, site16) = xenc_string_param_merged_and_site(
            CanonStringEncoding::CompactUtf16,
            CanonStringEncoding::Utf16,
        );
        merged16.exports[0].name = site16.export_name.clone();
        let adapter16 = gen_
            .generate_async_stackful_adapter(&site16, &merged16)
            .expect("stackful emitter must succeed for the inc-4a latin1→utf16 string-param site");
        let cpc16 = site_caller_param_count(&site16, &merged16);
        assert_locals_within_budget(adapter16.body, cpc16, "#272 inc-4a stackful latin1→utf16");
    }

    /// #272 inc-4b (integration, callback): the CALLBACK async adapter's
    /// DEST-latin1 string-param transcode path (UTF-8/UTF-16 → latin1+utf16)
    /// must not reference a local past its declared budget. Each two-phase loop
    /// uses 6 scratch locals at `transcode_base = l_p2 + 16` (offsets 21..=26 —
    /// the same six the inc-4a `Latin1 → UTF-8` loop occupies, reused across the
    /// scan + write phases), so the inc-4a budget of 27 already fits with NO
    /// growth. Generates the REAL adapter for BOTH dest-latin1 sites (caller=Utf8
    /// AND caller=Utf16) and asserts every referenced local is addressable, with
    /// the NOW-ACCURATE caller-param-count derivation.
    #[test]
    fn inc4b_callback_adapter_dest_latin1_locals_within_budget() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        // caller=Utf8 → latin1+utf16 (the UTF-8 two-phase encoder).
        let (merged8, site8) = xenc_string_param_merged_and_site(
            CanonStringEncoding::Utf8,
            CanonStringEncoding::CompactUtf16,
        );
        let adapter8 = gen_
            .generate_async_callback_adapter(&site8, &merged8)
            .expect("callback emitter must succeed for the inc-4b utf8→latin1 string-param site");
        let cpc8 = site_caller_param_count(&site8, &merged8);
        assert_locals_within_budget(adapter8.body, cpc8, "#272 inc-4b callback utf8→latin1");

        // caller=Utf16 → latin1+utf16 (the UTF-16 two-phase encoder).
        let (merged16, site16) = xenc_string_param_merged_and_site(
            CanonStringEncoding::Utf16,
            CanonStringEncoding::CompactUtf16,
        );
        let adapter16 = gen_
            .generate_async_callback_adapter(&site16, &merged16)
            .expect("callback emitter must succeed for the inc-4b utf16→latin1 string-param site");
        let cpc16 = site_caller_param_count(&site16, &merged16);
        assert_locals_within_budget(adapter16.body, cpc16, "#272 inc-4b callback utf16→latin1");
    }

    /// #272 inc-4b (integration, stackful): the STACKFUL async adapter's
    /// DEST-latin1 string-param transcode path must stay within its declared
    /// budget (18). Each two-phase loop uses 6 scratch at
    /// `transcode_base = l_scratch + 12`, i.e. offsets 12..=17 — top
    /// `caller_params + 17` < 18, so the stackful variant fits WITHOUT growing.
    /// Generates the REAL adapter for both dest-latin1 sites.
    #[test]
    fn inc4b_stackful_adapter_dest_latin1_locals_within_budget() {
        use crate::parser::CanonStringEncoding;
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let (mut merged8, site8) = xenc_string_param_merged_and_site(
            CanonStringEncoding::Utf8,
            CanonStringEncoding::CompactUtf16,
        );
        // Stackful dispatches on a non-`[callback]` export; rename the companion.
        merged8.exports[0].name = site8.export_name.clone();
        let adapter8 = gen_
            .generate_async_stackful_adapter(&site8, &merged8)
            .expect("stackful emitter must succeed for the inc-4b utf8→latin1 string-param site");
        let cpc8 = site_caller_param_count(&site8, &merged8);
        assert_locals_within_budget(adapter8.body, cpc8, "#272 inc-4b stackful utf8→latin1");

        let (mut merged16, site16) = xenc_string_param_merged_and_site(
            CanonStringEncoding::Utf16,
            CanonStringEncoding::CompactUtf16,
        );
        merged16.exports[0].name = site16.export_name.clone();
        let adapter16 = gen_
            .generate_async_stackful_adapter(&site16, &merged16)
            .expect("stackful emitter must succeed for the inc-4b utf16→latin1 string-param site");
        let cpc16 = site_caller_param_count(&site16, &merged16);
        assert_locals_within_budget(adapter16.body, cpc16, "#272 inc-4b stackful utf16→latin1");
    }

    #[test]
    fn ls_a_9_callback_adapter_dispatches_both_wait_and_poll() {
        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let mut merged = empty_merged();

        // Type 0: () -> i32 — minimal lift signature matching the
        // callback-mode return convention (packed callback code i32).
        merged.types.push(crate::merger::MergedFuncType {
            params: Vec::new(),
            results: vec![wasm_encoder::ValType::I32],
        });

        // The lift function lives at merged index 0.
        merged.functions.push(crate::merger::MergedFunction {
            type_idx: 0,
            body: wasm_encoder::Function::new([]),
            origin: (1, 0, 0),
            synthetic_kind: None,
        });
        merged.function_index_map.insert((1, 0, 0), 0);

        // The [callback] companion export — the callback adapter
        // resolves this by name (`[callback]<export_name>`).
        let export_name = "[async-lift]async_export";
        merged.exports.push(crate::merger::MergedExport {
            name: format!("[callback]{export_name}"),
            kind: wasm_encoder::ExportKind::Func,
            index: 0,
        });

        // Required host import — the adapter looks up
        // [waitable-set-poll] by name prefix.
        merged.imports.push(crate::merger::MergedImport {
            module: "$root".into(),
            name: "[waitable-set-poll]".into(),
            entity_type: wasm_encoder::EntityType::Function(0),
            component_idx: None,
        });

        let mut site = async_lift_site(export_name);
        site.import_func_type_idx = Some(0);
        site.crosses_memory = false;

        let adapter = gen_
            .generate_async_callback_adapter(&site, &merged)
            .expect("callback emitter must succeed with [callback] + [waitable-set-poll] wired");

        let body = adapter.body.into_raw_body();

        // The WAIT/POLL OR-pattern as raw bytes. WAIT=2 / POLL=3 both
        // fit in single-byte sleb128. We omit the `local.get l_code`
        // bytes from the pattern (their leb128 encoding depends on
        // local index) and assert the constant+compare+or skeleton
        // appears in order.
        const WAIT_POLL_OR_TAIL: &[u8] = &[
            0x41, 0x02, // i32.const WAIT (2)
            0x46, // i32.eq
            0x20, // local.get … (l_code; one-byte leb when index<128)
        ];
        const POLL_OR: &[u8] = &[
            0x41, 0x03, // i32.const POLL (3)
            0x46, // i32.eq
            0x72, // i32.or
        ];

        let wait_idx = body
            .windows(WAIT_POLL_OR_TAIL.len())
            .position(|w| w == WAIT_POLL_OR_TAIL)
            .unwrap_or_else(|| {
                panic!(
                    "callback adapter body must contain WAIT(2)/eq/local.get \
                     prefix of the OR-pattern; body={body:?}"
                )
            });
        let poll_idx = body[wait_idx..]
            .windows(POLL_OR.len())
            .position(|w| w == POLL_OR)
            .unwrap_or_else(|| {
                panic!(
                    "callback adapter body must contain POLL(3)/eq/or \
                     tail of the OR-pattern AFTER the WAIT match at \
                     offset {wait_idx}; body={body:?}"
                )
            });
        assert!(
            poll_idx > 0,
            "POLL_OR pattern must come after WAIT pattern in body \
             (locals interleave between them); poll_idx={poll_idx}"
        );
    }

    /// LS-A-8: For a `list<record { x: borrow<A>, y: borrow<B> }>` (or
    /// any list whose elements carry borrows to multiple distinct
    /// resource types), `analyze_call_site` must select the **correct
    /// per-type** `[resource-rep]` import for each inner-resource
    /// slot. A previous version did `resource_rep_imports.values()
    /// .next()` — HashMap iteration order, so the rep_func picked for
    /// each slot was effectively random, routing borrow handles of
    /// resource A through resource B's rep_func and vice versa
    /// (silent rep-vs-handle confusion across the cross-component
    /// handle boundary, H-4/H-4.2, UCA-A-7).
    ///
    /// The fix threads a pre-resolved `rep_import: Option<(String,
    /// String)>` through `InnerResource`, populated at site-
    /// requirements time; fact.rs looks the rep_func up per-type
    /// rather than via `.values().next()`.
    ///
    /// This test pins the per-type lookup. It builds adversarial
    /// inputs: two `InnerResource`s pointing at distinct rep_import
    /// keys, a `resource_rep_imports` map binding each key to a
    /// distinct func index, and asserts the resulting
    /// `options.inner_resource_fixups` pair each byte_offset with
    /// the **correct** func — never crossed.
    #[test]
    fn ls_a_8_inner_list_rep_func_selected_by_type_not_iteration_order() {
        use crate::resolver::{AdapterRequirements, CopyLayout, InnerResource};

        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let merged = empty_merged();

        // Adversarial inner-resources: borrow<A> at offset 0 and
        // borrow<B> at offset 4 (two i32 handles in the record).
        let rep_a_key = ("$root".to_string(), "[resource-rep]res_a".to_string());
        let rep_b_key = ("$root".to_string(), "[resource-rep]res_b".to_string());
        let inner_a = InnerResource {
            byte_offset: 0,
            resource_type_id: 100,
            is_owned: false,
            rep_import: Some(rep_a_key.clone()),
            guards: Vec::new(),
        };
        let inner_b = InnerResource {
            byte_offset: 4,
            resource_type_id: 200,
            is_owned: false,
            rep_import: Some(rep_b_key.clone()),
            guards: Vec::new(),
        };

        // Build a single Elements layout carrying both inner-
        // resources. The element_size + inner_pointers fields don't
        // matter for this assertion — `analyze_call_site` only walks
        // `inner_resources`.
        let layout = CopyLayout::Elements {
            element_size: 8,
            inner_pointers: Vec::new(),
            inner_resources: vec![inner_a, inner_b],
        };

        let requirements = AdapterRequirements {
            param_copy_layouts: vec![layout],
            ..Default::default()
        };

        let mut site = async_lift_site("[lift]list_of_borrows");
        site.requirements = requirements;
        site.is_async_lift = false;

        // Two distinct rep_func indices, deliberately chosen so a
        // HashMap-iteration `.values().next()` would pick wrongly
        // for at least one of them.
        let mut rep_imports = std::collections::HashMap::new();
        rep_imports.insert(rep_a_key.clone(), 100u32);
        rep_imports.insert(rep_b_key.clone(), 200u32);
        let new_imports = std::collections::HashMap::new();

        // Sample many times to make non-determinism observable. If the
        // impl picked `.values().next()`, hash-seed-randomised
        // iteration order would yield the wrong pairing under at
        // least some seeds; with the type-pinned lookup the result is
        // identical every run.
        for _ in 0..32 {
            let options = gen_.analyze_call_site(&site, &merged, &rep_imports, &new_imports);
            assert_eq!(
                options.inner_resource_fixups.len(),
                2,
                "both inner-resources must produce fixups; got {options:?}",
            );
            // Find the fixup tagged at offset 0 and 4 — they MUST map
            // to rep_func 100 and 200 respectively (i.e., the
            // resource type's own rep_func, not the other one).
            let off_0 = options
                .inner_resource_fixups
                .iter()
                .find(|f| f.byte_offset == 0)
                .expect("must have fixup at offset 0");
            let off_4 = options
                .inner_resource_fixups
                .iter()
                .find(|f| f.byte_offset == 4)
                .expect("must have fixup at offset 4");
            assert_eq!(
                off_0.rep_func, 100,
                "borrow<A> at offset 0 must select rep_a's func (100); got {off_0:?}",
            );
            assert_eq!(
                off_4.rep_func, 200,
                "borrow<B> at offset 4 must select rep_b's func (200); got {off_4:?}",
            );
        }
    }

    /// LS-A-8 sibling case: when an `InnerResource` has no
    /// `rep_import` (i.e., the resolver couldn't map the type id to
    /// an import), the fixup must be **skipped** with a warning —
    /// NOT fall back to an arbitrary HashMap entry, which was the
    /// pre-fix behavior.
    #[test]
    fn ls_a_8_no_rep_import_skips_fixup_rather_than_picking_arbitrary() {
        use crate::resolver::{AdapterRequirements, CopyLayout, InnerResource};

        let gen_ = FactStyleGenerator::new(AdapterConfig::default());
        let merged = empty_merged();

        let inner = InnerResource {
            byte_offset: 0,
            resource_type_id: 999,
            is_owned: false,
            rep_import: None, // resolver failed to map; pre-fix would `.values().next()`
            guards: Vec::new(),
        };

        let requirements = AdapterRequirements {
            param_copy_layouts: vec![CopyLayout::Elements {
                element_size: 4,
                inner_pointers: Vec::new(),
                inner_resources: vec![inner],
            }],
            ..Default::default()
        };

        let mut site = async_lift_site("[lift]list_borrow_unmapped");
        site.requirements = requirements;
        site.is_async_lift = false;

        // Even though imports are present, the lookup must skip when
        // rep_import is None — not silently fall back.
        let mut rep_imports = std::collections::HashMap::new();
        rep_imports.insert(
            ("$root".to_string(), "[resource-rep]res_other".to_string()),
            777u32,
        );
        let new_imports = std::collections::HashMap::new();

        let options = gen_.analyze_call_site(&site, &merged, &rep_imports, &new_imports);
        assert!(
            options.inner_resource_fixups.is_empty(),
            "InnerResource with rep_import=None must NOT produce a \
             fixup (pre-fix bug fell back to HashMap.values().next() \
             yielding 777 arbitrarily); got {options:?}",
        );
    }
}
