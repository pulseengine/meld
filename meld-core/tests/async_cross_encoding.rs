//! Runtime-differential oracle for #272 inc 1 — async cross-encoding string
//! transcoding (UTF-8 → UTF-16 top-level param).
//!
//! ## Why this shape (honest construction note)
//!
//! The original #272 scoping asked for an async-lift callee fused + run via
//! the async fuse+run harness (mirroring the sync
//! `test_sr17_utf8_to_utf16_string_transcoding`). That is **not expressible**
//! under bare `wasmtime`: meld's async-lift execution model is the callback /
//! stackful trampoline driven by a real async runtime (kiln), and the repo's
//! own async-lift e2e tests are explicitly fuse-only / structural —
//! `p3_async_lowering.rs` notes "A runtime stub against kiln is OUT OF SCOPE"
//! and that the `wat` crate does not even parse `canon lift ... async`. The
//! existing stream `p3_bridge_runtime.rs` harness hand-stubs the
//! `pulseengine:async` stream intrinsics; there is no harness for a
//! string-param async-lift call.
//!
//! So this oracle drives the **exact production transcode emitter**
//! (`emit_utf8_to_utf16_transcode_param`, the free function
//! `emit_param_copy_step` calls on the UTF-8 → UTF-16 async param path,
//! composed from the shared `emit_utf8_decode_codepoint` /
//! `emit_utf16_encode_codepoint` codepoint helpers) inside a two-memory wasm
//! module built by `meld_core::adapter::build_utf8_to_utf16_transcode_test_module`.
//! The caller's UTF-8 bytes live in memory 0; the emitter transcodes them into
//! a freshly `cabi_realloc`'d buffer in memory 1; the module then sums the
//! UTF-16 code units the way a UTF-16-lifting callee would read them. A raw
//! byte-copy (the pre-inc-1 behaviour the LS-F-27 guard failed loud on) cannot
//! produce the correct code-unit sum, so a passing assertion proves
//! transcoding, not copying.
//!
//! The NEGATIVE side (result strings, nested `list<string>` params, and the
//! UTF-16 → UTF-8 direction still fail loud — the guard is not over-narrowed)
//! is covered by the `ls_f_27_*` unit tests in
//! `meld-core/src/adapter/fact.rs`, which assert
//! `guard_async_cross_encoding_strings` (a private fn) directly.

use meld_core::adapter::{
    build_latin1_to_utf8_transcode_test_module, build_latin1_to_utf16_transcode_test_module,
    build_nested_list_string_result_test_module, build_utf8_to_latin1_transcode_test_module,
    build_utf8_to_utf16_transcode_test_module, build_utf16_to_latin1_transcode_test_module,
    build_utf16_to_utf8_transcode_test_module,
};
use meld_core::parser::CanonStringEncoding;
use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};

/// The canonical-ABI `latin1+utf16` length-operand tag bit, mirrored from
/// `meld_core::adapter::fact::UTF16_TAG` (a crate-private const). A tag-SET
/// length means the source bytes are UTF-16 (code-unit count = `len & !TAG`);
/// tag-CLEAR means pure Latin-1 (byte count = `len`).
const UTF16_TAG: i32 = 1 << 31;

/// Build the oracle module, write `src_bytes` into caller memory 0 at offset
/// 0, call `transcode_and_sum(0, src_bytes.len())`, and return the summed
/// UTF-16 code units the transcode produced in callee memory 1.
fn transcode_and_sum(src_bytes: &[u8]) -> i32 {
    let wasm = build_utf8_to_utf16_transcode_test_module();

    // Sanity: the emitted module must be valid wasm.
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&wasm)
        .expect("#272 inc1 oracle module should validate");

    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let module = RuntimeModule::new(&engine, &wasm).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // Write the UTF-8 source into caller memory 0.
    let caller_mem = instance
        .get_memory(&mut store, "caller_memory")
        .expect("oracle module exports caller_memory");
    caller_mem
        .write(&mut store, 0, src_bytes)
        .expect("write src bytes into caller memory");

    let f = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "transcode_and_sum")
        .expect("oracle module exports transcode_and_sum");
    f.call(&mut store, (0, src_bytes.len() as i32))
        .expect("transcode_and_sum runs")
}

/// #272 inc 1 (positive, ASCII): "Hello" UTF-8 → UTF-16 yields code units
/// [0x48,0x65,0x6C,0x6C,0x6F] summing to 500 — identical to the sync SR-17
/// oracle (`test_sr17_utf8_to_utf16_string_transcoding`) but exercising the
/// ASYNC-path transcode emitter. A raw copy would instead leave 5 UTF-8 bytes
/// the callee reads as 16-bit units, producing a different sum.
#[test]
fn inc1_async_utf8_to_utf16_param_transcodes_hello() {
    assert_eq!(
        transcode_and_sum(b"Hello"),
        500,
        "#272 inc1: async UTF-8 → UTF-16 transcode of \"Hello\" must sum to 500 \
         (proves transcoding, not raw copy)"
    );
}

/// #272 inc 1 (positive, supplementary plane): "A😀" — 'A' (U+0041, 1 BMP code
/// unit) then U+1F600 (UTF-8 `F0 9F 98 80`, encoded as the surrogate PAIR
/// D83D DE00). Sum = 0x0041 + 0xD83D + 0xDE00 = 65 + 55357 + 56832 = 112254.
/// This exercises the encoder's surrogate-pair branch and the dst-cursor
/// advancing by 1 then 2 on the async path; mirrors the sync
/// `test_sr17_utf8_to_utf16_supplementary_plane_transcoding`.
#[test]
fn inc1_async_utf8_to_utf16_param_transcodes_supplementary_plane() {
    assert_eq!(
        transcode_and_sum(&[0x41, 0xF0, 0x9F, 0x98, 0x80]),
        112254,
        "#272 inc1: async UTF-8 → UTF-16 transcode of \"A😀\" must sum to 112254 \
         (surrogate pair D83D DE00 + 'A')"
    );
}

/// #272 inc 1 (positive, malformed UTF-8 → U+FFFD): a lone continuation byte
/// 0x80 must decode to one U+FFFD code unit (Canonical-ABI lossy replacement),
/// not be raw-copied. "A" + 0x80 + "B" → [0x0041, 0xFFFD, 0x0042], sum =
/// 65 + 65533 + 66 = 65664. Confirms the async path uses the hardened shared
/// decoder rather than a verbatim copy.
#[test]
fn inc1_async_utf8_to_utf16_param_replaces_malformed_with_fffd() {
    assert_eq!(
        transcode_and_sum(&[0x41, 0x80, 0x42]),
        65664,
        "#272 inc1: malformed lead 0x80 must become U+FFFD (sum 65664)"
    );
}

/// #272 inc 1 (positive, empty string): zero-length source transcodes to zero
/// code units, sum 0 — the realloc/loop must handle len==0 without trapping.
#[test]
fn inc1_async_utf8_to_utf16_param_empty_string() {
    assert_eq!(
        transcode_and_sum(b""),
        0,
        "#272 inc1: empty UTF-8 source must transcode to 0 code units (sum 0)"
    );
}

// ----------------------------------------------------------------------------
// #272 inc 2 — the REVERSE direction: UTF-16 → UTF-8 top-level param transcode.
//
// Same oracle shape, driving the production `emit_utf16_to_utf8_transcode_param`
// emitter inside the two-memory module built by
// `build_utf16_to_utf8_transcode_test_module`: caller UTF-16 code units (LE) in
// memory 0, transcoded to a `cabi_realloc`'d UTF-8 buffer in memory 1, then the
// module sums the resulting UTF-8 BYTES the way a UTF-8-lifting callee would
// read them. A raw byte-copy (the pre-inc-2 behaviour the LS-F-27 guard failed
// loud on) leaves the callee reading UTF-16 LE bytes as UTF-8, producing a
// different sum, so a passing assertion proves transcoding, not copying.
// ----------------------------------------------------------------------------

/// Write `src_units` (UTF-16 code units) as little-endian bytes into caller
/// memory 0 at offset 0, call `transcode_and_sum(0, src_units.len())`, and
/// return the summed UTF-8 output bytes the transcode produced in memory 1.
fn transcode_utf16_to_utf8_and_sum(src_units: &[u16]) -> i32 {
    let wasm = build_utf16_to_utf8_transcode_test_module();

    // Sanity: the emitted module must be valid wasm.
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&wasm)
        .expect("#272 inc2 oracle module should validate");

    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let module = RuntimeModule::new(&engine, &wasm).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    // Write the UTF-16 source (little-endian) into caller memory 0.
    let mut src_bytes = Vec::with_capacity(src_units.len() * 2);
    for u in src_units {
        src_bytes.extend_from_slice(&u.to_le_bytes());
    }
    let caller_mem = instance
        .get_memory(&mut store, "caller_memory")
        .expect("oracle module exports caller_memory");
    caller_mem
        .write(&mut store, 0, &src_bytes)
        .expect("write src code units into caller memory");

    let f = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "transcode_and_sum")
        .expect("oracle module exports transcode_and_sum");
    // The second arg is the source CODE-UNIT count (not a byte count).
    f.call(&mut store, (0, src_units.len() as i32))
        .expect("transcode_and_sum runs")
}

/// #272 inc 2 (positive, ASCII): "Hello" UTF-16 → UTF-8 yields the bytes
/// [0x48,0x65,0x6C,0x6C,0x6F] summing to 500 — each BMP-ASCII unit becomes one
/// 1-byte UTF-8 sequence. A raw copy would instead emit 10 UTF-16 LE bytes
/// (with interleaved zeros), a different sum.
#[test]
fn inc2_async_utf16_to_utf8_param_transcodes_hello() {
    let units: Vec<u16> = "Hello".encode_utf16().collect();
    assert_eq!(
        transcode_utf16_to_utf8_and_sum(&units),
        500,
        "#272 inc2: async UTF-16 → UTF-8 transcode of \"Hello\" must sum to 500 \
         (proves transcoding, not raw copy)"
    );
}

/// #272 inc 2 (positive, BMP multi-byte): é = U+00E9 → UTF-8 `C3 A9`, the
/// 2-byte encoder branch. Sum = 0xC3 + 0xA9 = 195 + 169 = 364.
#[test]
fn inc2_async_utf16_to_utf8_param_transcodes_bmp_two_byte() {
    assert_eq!(
        transcode_utf16_to_utf8_and_sum(&[0x00E9]),
        364,
        "#272 inc2: é (U+00E9) must transcode to UTF-8 C3 A9 (sum 364)"
    );
}

/// #272 inc 2 (positive, supplementary plane): 😀 = U+1F600, the surrogate
/// PAIR D83D DE00 (2 source code units) → UTF-8 `F0 9F 98 80`, the 4-byte
/// encoder branch fed by the decoder's surrogate-pair path. Sum =
/// 0xF0 + 0x9F + 0x98 + 0x80 = 240 + 159 + 152 + 128 = 679.
#[test]
fn inc2_async_utf16_to_utf8_param_transcodes_supplementary_plane() {
    let units: Vec<u16> = "😀".encode_utf16().collect();
    assert_eq!(
        units,
        vec![0xD83D, 0xDE00],
        "sanity: 😀 is the pair D83D DE00"
    );
    assert_eq!(
        transcode_utf16_to_utf8_and_sum(&units),
        679,
        "#272 inc2: 😀 (surrogate pair D83D DE00) must transcode to UTF-8 \
         F0 9F 98 80 (sum 679)"
    );
}

/// #272 inc 2 (positive, lone surrogate → U+FFFD): a lone high surrogate
/// 0xD800 with no following low surrogate must be replaced with U+FFFD
/// (Canonical-ABI lossy replacement) → UTF-8 `EF BF BD`, not raw-copied. Sum =
/// 0xEF + 0xBF + 0xBD = 239 + 191 + 189 = 619. Confirms the async path uses the
/// hardened shared UTF-16 decoder.
#[test]
fn inc2_async_utf16_to_utf8_param_replaces_lone_surrogate_with_fffd() {
    assert_eq!(
        transcode_utf16_to_utf8_and_sum(&[0xD800]),
        619,
        "#272 inc2: lone high surrogate 0xD800 must become U+FFFD UTF-8 \
         EF BF BD (sum 619)"
    );
}

/// #272 inc 2 (positive, empty string): zero-length source transcodes to zero
/// bytes, sum 0 — the realloc/loop must handle len==0 without trapping.
#[test]
fn inc2_async_utf16_to_utf8_param_empty_string() {
    assert_eq!(
        transcode_utf16_to_utf8_and_sum(&[]),
        0,
        "#272 inc2: empty UTF-16 source must transcode to 0 bytes (sum 0)"
    );
}

// ----------------------------------------------------------------------------
// #272 inc 4a — latin1-SOURCE param transcode: `latin1+utf16` (CompactUTF16)
// CALLER → UTF-16 or UTF-8 callee. The CALLER length operand is tag-encoded
// (UTF16_TAG): tag-CLEAR → pure Latin-1 source (1 byte/char), tag-SET → UTF-16
// source (code-unit count = len & !TAG). Each oracle writes the raw caller
// bytes into memory 0 and passes the TAGGED length; the production tag-dispatch
// emitter (`emit_latin1_to_{utf16,utf8}_transcode_param`) picks the arm, runs
// the transcode into a `cabi_realloc`'d buffer in memory 1, and the module sums
// the output the way the callee would read it. A raw copy of the tagged operand
// + tag-set bytes cannot produce the correct sum, so a pass proves transcoding.
// ----------------------------------------------------------------------------

/// Write `src_bytes` (raw CALLER bytes — Latin-1 bytes when `tag_set` is false,
/// UTF-16 LE bytes when true) into caller memory 0, call
/// `transcode_and_sum(0, tagged_len)`, and return the summed UTF-16 code units
/// the latin1+utf16 → UTF-16 transcode produced in callee memory 1. `count` is
/// the untagged code/byte count (Latin-1 byte count, or UTF-16 code-unit count).
fn latin1_to_utf16_transcode_and_sum(src_bytes: &[u8], count: i32, tag_set: bool) -> i32 {
    let wasm = build_latin1_to_utf16_transcode_test_module();
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&wasm)
        .expect("#272 inc4a latin1→utf16 oracle module should validate");

    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let module = RuntimeModule::new(&engine, &wasm).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let caller_mem = instance
        .get_memory(&mut store, "caller_memory")
        .expect("oracle module exports caller_memory");
    caller_mem
        .write(&mut store, 0, src_bytes)
        .expect("write src bytes into caller memory");

    let f = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "transcode_and_sum")
        .expect("oracle module exports transcode_and_sum");
    let tagged_len = if tag_set { count | UTF16_TAG } else { count };
    f.call(&mut store, (0, tagged_len))
        .expect("transcode_and_sum runs")
}

/// Same as above for the latin1+utf16 → UTF-8 direction; returns the summed
/// UTF-8 output bytes.
fn latin1_to_utf8_transcode_and_sum(src_bytes: &[u8], count: i32, tag_set: bool) -> i32 {
    let wasm = build_latin1_to_utf8_transcode_test_module();
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&wasm)
        .expect("#272 inc4a latin1→utf8 oracle module should validate");

    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let module = RuntimeModule::new(&engine, &wasm).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let caller_mem = instance
        .get_memory(&mut store, "caller_memory")
        .expect("oracle module exports caller_memory");
    caller_mem
        .write(&mut store, 0, src_bytes)
        .expect("write src bytes into caller memory");

    let f = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "transcode_and_sum")
        .expect("oracle module exports transcode_and_sum");
    let tagged_len = if tag_set { count | UTF16_TAG } else { count };
    f.call(&mut store, (0, tagged_len))
        .expect("transcode_and_sum runs")
}

/// Encode a `&str` as UTF-16 LE bytes (the tag-set CALLER payload shape).
fn utf16_le_bytes(s: &str) -> Vec<u8> {
    let mut v = Vec::new();
    for u in s.encode_utf16() {
        v.extend_from_slice(&u.to_le_bytes());
    }
    v
}

// --- latin1+utf16 → UTF-16 ---------------------------------------------------

/// #272 inc 4a (latin1→utf16, tag CLEAR): a pure Latin-1 "café" =
/// [0x63,0x61,0x66,0xE9] (tag clear, count 4) → UTF-16 code units
/// [0x0063,0x0061,0x0066,0x00E9] by zero-extension, summing to
/// 99+97+102+233 = 531. A raw copy would leave 4 bytes the callee reads as
/// 16-bit units, a different sum.
#[test]
fn inc4a_async_latin1_to_utf16_tag_clear_cafe() {
    assert_eq!(
        latin1_to_utf16_transcode_and_sum(&[0x63, 0x61, 0x66, 0xE9], 4, false),
        531,
        "#272 inc4a: tag-clear Latin-1 \"café\" → UTF-16 must sum to 531"
    );
}

/// #272 inc 4a (latin1→utf16, tag SET): a UTF-16 source "日本" = units
/// [0x65E5,0x672C] (tag set, count 2) is copied VERBATIM as 2 code units,
/// summing to 0x65E5 + 0x672C = 52497.
#[test]
fn inc4a_async_latin1_to_utf16_tag_set_nihon() {
    assert_eq!(
        latin1_to_utf16_transcode_and_sum(&utf16_le_bytes("日本"), 2, true),
        52497,
        "#272 inc4a: tag-set UTF-16 \"日本\" → UTF-16 verbatim copy must sum to 52497"
    );
}

/// #272 inc 4a (latin1→utf16, empty): zero-length source (tag clear) → 0 code
/// units, sum 0 — the realloc/loop must handle count==0 without trapping.
#[test]
fn inc4a_async_latin1_to_utf16_empty() {
    assert_eq!(
        latin1_to_utf16_transcode_and_sum(&[], 0, false),
        0,
        "#272 inc4a: empty latin1+utf16 source → 0 UTF-16 code units (sum 0)"
    );
}

// --- latin1+utf16 → UTF-8 ----------------------------------------------------

/// #272 inc 4a (latin1→utf8, tag CLEAR): pure Latin-1 "café" =
/// [0x63,0x61,0x66,0xE9] (count 4) → UTF-8 [0x63,0x61,0x66,0xC3,0xA9] (0xE9 is
/// the 2-byte branch), summing to 99+97+102+195+169 = 662.
#[test]
fn inc4a_async_latin1_to_utf8_tag_clear_cafe() {
    assert_eq!(
        latin1_to_utf8_transcode_and_sum(&[0x63, 0x61, 0x66, 0xE9], 4, false),
        662,
        "#272 inc4a: tag-clear Latin-1 \"café\" → UTF-8 must sum to 662"
    );
}

/// #272 inc 4a (latin1→utf8, tag SET): UTF-16 source "日本" = units
/// [0x65E5,0x672C] (count 2) → UTF-8 [0xE6,0x97,0xA5, 0xE6,0x9C,0xAC] (each a
/// BMP 3-byte sequence via the shared UTF-16 decoder + UTF-8 encoder), summing
/// to 230+151+165 + 230+156+172 = 1104.
#[test]
fn inc4a_async_latin1_to_utf8_tag_set_nihon() {
    assert_eq!(
        latin1_to_utf8_transcode_and_sum(&utf16_le_bytes("日本"), 2, true),
        1104,
        "#272 inc4a: tag-set UTF-16 \"日本\" → UTF-8 must sum to 1104"
    );
}

/// #272 inc 4a (latin1→utf8, empty): zero-length source (tag clear) → 0 bytes,
/// sum 0.
#[test]
fn inc4a_async_latin1_to_utf8_empty() {
    assert_eq!(
        latin1_to_utf8_transcode_and_sum(&[], 0, false),
        0,
        "#272 inc4a: empty latin1+utf16 source → 0 UTF-8 bytes (sum 0)"
    );
}

// ----------------------------------------------------------------------------
// #272 inc 4b — DEST-latin1 / tag-PRODUCING param transcode: UTF-8 or UTF-16
// CALLER → `latin1+utf16` (CompactUTF16) callee. These are the two-phase
// encoders: phase 1 scans the source code points (any cp > 0xFF ⇒ UTF-16),
// phase 2 writes either Latin-1 (1 byte/char, tag CLEAR) or UTF-16 (code units,
// possibly surrogate pairs, length | UTF16_TAG). The oracle returns the TAGGED
// output length and exposes the output pointer (global `out_ptr`) so the test
// asserts BOTH the tag bit and the exact output bytes a `latin1+utf16` lifting
// callee would read. A raw copy could not produce the correct tagged length +
// representation, so a pass proves two-phase transcoding.
// ----------------------------------------------------------------------------

/// Run a DEST-latin1 oracle: write `src_bytes` into caller memory 0, call
/// `transcode(0, src_count)`, and return `(tagged_len, output_bytes)` — the
/// raw bytes of the produced `latin1+utf16` buffer in callee memory 1, sized by
/// the untagged output length (Latin-1: `len` bytes; UTF-16: `2 * (len & !TAG)`
/// bytes). `utf16_source` selects which oracle module to build.
fn dest_latin1_transcode(src_bytes: &[u8], src_count: i32, utf16_source: bool) -> (i32, Vec<u8>) {
    let wasm = if utf16_source {
        build_utf16_to_latin1_transcode_test_module()
    } else {
        build_utf8_to_latin1_transcode_test_module()
    };
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&wasm)
        .expect("#272 inc4b dest-latin1 oracle module should validate");

    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let module = RuntimeModule::new(&engine, &wasm).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let caller_mem = instance
        .get_memory(&mut store, "caller_memory")
        .expect("oracle module exports caller_memory");
    caller_mem
        .write(&mut store, 0, src_bytes)
        .expect("write src bytes into caller memory");

    let f = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "transcode")
        .expect("oracle module exports transcode");
    let tagged_len = f.call(&mut store, (0, src_count)).expect("transcode runs");

    let out_ptr = instance
        .get_global(&mut store, "out_ptr")
        .expect("oracle module exports out_ptr")
        .get(&mut store)
        .i32()
        .expect("out_ptr is i32") as usize;
    let count = (tagged_len & !UTF16_TAG) as usize;
    let byte_len = if tagged_len & UTF16_TAG != 0 {
        count * 2 // UTF-16 code units
    } else {
        count // Latin-1 bytes
    };
    let callee_mem = instance
        .get_memory(&mut store, "callee_memory")
        .expect("oracle module exports callee_memory");
    let mut out = vec![0u8; byte_len];
    callee_mem
        .read(&store, out_ptr, &mut out)
        .expect("read output bytes from callee memory");
    (tagged_len, out)
}

/// Encode a `&str` as UTF-16 LE bytes (the UTF-16-source CALLER payload shape).
fn inc4b_utf16_le_bytes(s: &str) -> Vec<u8> {
    let mut v = Vec::new();
    for u in s.encode_utf16() {
        v.extend_from_slice(&u.to_le_bytes());
    }
    v
}

// --- UTF-8 → latin1+utf16 ----------------------------------------------------

/// #272 inc 4b (utf8→latin1, latin1-FITS): UTF-8 "café" = [0x63,0x61,0x66,
/// 0xC3,0xA9] (5 bytes, all cp ≤ 0xFF) → Latin-1 output [0x63,0x61,0x66,0xE9],
/// tag CLEAR, length 4.
#[test]
fn inc4b_async_utf8_to_latin1_fits_cafe() {
    let (tagged, out) = dest_latin1_transcode(&[0x63, 0x61, 0x66, 0xC3, 0xA9], 5, false);
    assert_eq!(tagged & UTF16_TAG, 0, "café must pick Latin-1 (tag CLEAR)");
    assert_eq!(tagged, 4, "café Latin-1 output length must be 4");
    assert_eq!(out, vec![0x63, 0x61, 0x66, 0xE9], "café Latin-1 bytes");
}

/// #272 inc 4b (utf8→latin1, NON-latin1): UTF-8 "日本" (cp 0x65E5,0x672C > 0xFF)
/// → UTF-16 output units [0x65E5,0x672C], tag SET, length 2.
#[test]
fn inc4b_async_utf8_to_latin1_nihon_utf16() {
    let src = "日本".as_bytes();
    let (tagged, out) = dest_latin1_transcode(src, src.len() as i32, false);
    assert_ne!(tagged & UTF16_TAG, 0, "日本 must pick UTF-16 (tag SET)");
    assert_eq!(tagged & !UTF16_TAG, 2, "日本 UTF-16 output is 2 code units");
    assert_eq!(
        out,
        vec![0xE5, 0x65, 0x2C, 0x67],
        "日本 UTF-16 LE bytes [0x65E5, 0x672C]"
    );
}

/// #272 inc 4b (utf8→latin1, supplementary): UTF-8 "😀" (U+1F600, supplementary)
/// forces UTF-16 with a surrogate PAIR [0xD83D,0xDE00], tag SET, length 2.
#[test]
fn inc4b_async_utf8_to_latin1_emoji_surrogate_pair() {
    let src = "😀".as_bytes(); // 4 UTF-8 bytes
    let (tagged, out) = dest_latin1_transcode(src, src.len() as i32, false);
    assert_ne!(tagged & UTF16_TAG, 0, "😀 must pick UTF-16 (tag SET)");
    assert_eq!(
        tagged & !UTF16_TAG,
        2,
        "😀 UTF-16 output is a 2-unit surrogate pair"
    );
    assert_eq!(
        out,
        vec![0x3D, 0xD8, 0x00, 0xDE],
        "😀 surrogate pair LE bytes [0xD83D, 0xDE00]"
    );
}

/// #272 inc 4b (utf8→latin1, empty): zero-length source → Latin-1, tag CLEAR,
/// length 0 — the scan/realloc/write must handle count==0 without trapping.
#[test]
fn inc4b_async_utf8_to_latin1_empty() {
    let (tagged, out) = dest_latin1_transcode(&[], 0, false);
    assert_eq!(tagged, 0, "empty UTF-8 source → tag-clear length 0");
    assert!(out.is_empty(), "empty output buffer");
}

// --- UTF-16 → latin1+utf16 ---------------------------------------------------

/// #272 inc 4b (utf16→latin1, latin1-FITS): UTF-16 "café" (units all ≤ 0xFF) →
/// Latin-1 output [0x63,0x61,0x66,0xE9], tag CLEAR, length 4.
#[test]
fn inc4b_async_utf16_to_latin1_fits_cafe() {
    let src = inc4b_utf16_le_bytes("café");
    let (tagged, out) = dest_latin1_transcode(&src, 4, true);
    assert_eq!(tagged & UTF16_TAG, 0, "café must pick Latin-1 (tag CLEAR)");
    assert_eq!(tagged, 4, "café Latin-1 output length must be 4");
    assert_eq!(out, vec![0x63, 0x61, 0x66, 0xE9], "café Latin-1 bytes");
}

/// #272 inc 4b (utf16→latin1, NON-latin1): UTF-16 "日本" → UTF-16 output
/// [0x65E5,0x672C], tag SET, length 2 (re-encoded verbatim through the decoder).
#[test]
fn inc4b_async_utf16_to_latin1_nihon_utf16() {
    let src = inc4b_utf16_le_bytes("日本");
    let (tagged, out) = dest_latin1_transcode(&src, 2, true);
    assert_ne!(tagged & UTF16_TAG, 0, "日本 must pick UTF-16 (tag SET)");
    assert_eq!(tagged & !UTF16_TAG, 2, "日本 UTF-16 output is 2 code units");
    assert_eq!(
        out,
        vec![0xE5, 0x65, 0x2C, 0x67],
        "日本 UTF-16 LE bytes [0x65E5, 0x672C]"
    );
}

/// #272 inc 4b (utf16→latin1, supplementary): UTF-16 "😀" (a surrogate pair on
/// input, 2 code units) → UTF-16 surrogate pair output [0xD83D,0xDE00], tag SET,
/// length 2 (decoded to U+1F600 then re-encoded).
#[test]
fn inc4b_async_utf16_to_latin1_emoji_surrogate_pair() {
    let src = inc4b_utf16_le_bytes("😀"); // 2 code units (surrogate pair)
    let (tagged, out) = dest_latin1_transcode(&src, 2, true);
    assert_ne!(tagged & UTF16_TAG, 0, "😀 must pick UTF-16 (tag SET)");
    assert_eq!(tagged & !UTF16_TAG, 2, "😀 UTF-16 output is a 2-unit pair");
    assert_eq!(
        out,
        vec![0x3D, 0xD8, 0x00, 0xDE],
        "😀 surrogate pair LE bytes [0xD83D, 0xDE00]"
    );
}

/// #272 inc 4b (utf16→latin1, empty): zero-length UTF-16 source → Latin-1, tag
/// CLEAR, length 0.
#[test]
fn inc4b_async_utf16_to_latin1_empty() {
    let (tagged, out) = dest_latin1_transcode(&[], 0, true);
    assert_eq!(tagged, 0, "empty UTF-16 source → tag-clear length 0");
    assert!(out.is_empty(), "empty output buffer");
}

// ----------------------------------------------------------------------------
// #272 inc 5a — NESTED `list<string>` RESULT transcode (UTF-8 → UTF-16), the
// first real nested cross-encoding delivery, plus the negative `list<u8>` case
// proving the string-ness blocker is resolved (a nested `list<u8>` is RAW-COPIED
// verbatim, never transcoded, so its arbitrary binary bytes are not corrupted).
//
// Both drive the EXACT production `emit_patch_nested_indirections` emitter via
// the two-memory modules built by
// `build_nested_list_string_utf8_to_utf16_result_test_module` /
// `build_nested_list_u8_result_not_transcoded_test_module`. This is the RESULT
// direction (callee PRODUCES, caller READS): the host writes the inner buffers +
// the outer `(ptr, len)` records into CALLEE memory 1, and a verbatim copy of
// the outer records into CALLER memory 0 (the post-outer-bulk-copy state). The
// emitter transcodes (or raw-copies) each inner buffer into caller memory 0,
// rewrites the caller-side inner `(ptr, len)` header, and the module then sums
// the inner units by re-reading the PATCHED headers.
// ----------------------------------------------------------------------------

const INNER_A_OFF: i32 = 100; // callee-memory offset of inner buffer 0
const INNER_B_OFF: i32 = 140; // callee-memory offset of inner buffer 1
const OUTER_OFF: i32 = 200; // outer list offset (BOTH memories)

/// Instantiate `wasm`, write the two inner byte buffers into CALLEE memory 1 at
/// `INNER_A_OFF`/`INNER_B_OFF`, lay out a 2-record outer list `(ptr, len)` at
/// `OUTER_OFF` in BOTH memories (callee = source, caller = the stale post-bulk-
/// copy duplicate), run `patch_and_sum(OUTER_OFF, OUTER_OFF, 2)`, and return its
/// sum.
fn nested_patch_and_sum(wasm: &[u8], inner_a: &[u8], inner_b: &[u8]) -> i32 {
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(wasm)
        .expect("#272 inc5a oracle module should validate");

    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let module = RuntimeModule::new(&engine, wasm).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let caller_mem = instance
        .get_memory(&mut store, "caller_memory")
        .expect("oracle module exports caller_memory");
    let callee_mem = instance
        .get_memory(&mut store, "callee_memory")
        .expect("oracle module exports callee_memory");

    // Inner buffers live ONLY in callee memory 1 (the source).
    callee_mem
        .write(&mut store, INNER_A_OFF as usize, inner_a)
        .expect("write inner buffer 0 into callee memory");
    callee_mem
        .write(&mut store, INNER_B_OFF as usize, inner_b)
        .expect("write inner buffer 1 into callee memory");

    // Outer list: rec0 = (INNER_A_OFF, len_a), rec1 = (INNER_B_OFF, len_b),
    // 8 bytes each. The same bytes go into BOTH memories — caller memory 0 is
    // the verbatim outer bulk-copy the production writeback already performed.
    let mut outer = Vec::new();
    outer.extend_from_slice(&INNER_A_OFF.to_le_bytes());
    outer.extend_from_slice(&(inner_a.len() as i32).to_le_bytes());
    outer.extend_from_slice(&INNER_B_OFF.to_le_bytes());
    outer.extend_from_slice(&(inner_b.len() as i32).to_le_bytes());
    callee_mem
        .write(&mut store, OUTER_OFF as usize, &outer)
        .expect("write outer records into callee memory");
    caller_mem
        .write(&mut store, OUTER_OFF as usize, &outer)
        .expect("write outer records into caller memory (stale duplicate)");

    let f = instance
        .get_typed_func::<(i32, i32, i32), i32>(&mut store, "patch_and_sum")
        .expect("oracle module exports patch_and_sum");
    f.call(&mut store, (OUTER_OFF, OUTER_OFF, 2))
        .expect("patch_and_sum runs")
}

/// #272 inc 5a (positive): a 2-element `list<string>` result `["Hi", "yo"]`
/// (UTF-8 bytes) transcoded UTF-8 → UTF-16 sums the inner UTF-16 CODE UNITS to
/// 'H'+'i'+'y'+'o' = 0x48+0x69+0x79+0x6F = 409. The module sums by re-reading
/// the PATCHED caller-side `(ptr, len)` headers, so a correct sum proves BOTH
/// the inner transcode AND the NEW header-len rewrite (the rewritten len must be
/// the UTF-16 code-unit count = 2 per string, not the UTF-8 byte count — they
/// happen to coincide for ASCII, but the patched PTR must point into caller
/// memory, which a raw copy would not produce correctly for the summing loop).
#[test]
fn inc5a_async_nested_list_string_utf8_to_utf16_transcodes() {
    let wasm = meld_core::adapter::build_nested_list_string_utf8_to_utf16_result_test_module();
    // "Hi" = [0x48, 0x69], "yo" = [0x79, 0x6F].
    let sum = nested_patch_and_sum(&wasm, b"Hi", b"yo");
    assert_eq!(
        sum, 409,
        "#272 inc5a: nested list<string> [\"Hi\",\"yo\"] UTF-8 → UTF-16 must sum \
         the transcoded inner code units to 409 (proves real nested transcode + \
         header-len rewrite, not raw copy)"
    );
}

/// #272 inc 5a (positive, non-ASCII): a `list<string>` result `["é", "Hi"]`
/// where "é" is UTF-8 `0xC3 0xA9` (2 bytes) → ONE UTF-16 code unit 0x00E9. The
/// inner len header MUST be rewritten from the 2-byte UTF-8 length to the 1-unit
/// UTF-16 length, else the summing loop would read a phantom second unit. Sum =
/// 0x00E9 (é) + 0x48 ('H') + 0x69 ('i') = 233 + 72 + 105 = 410.
#[test]
fn inc5a_async_nested_list_string_non_ascii_rewrites_len() {
    let wasm = meld_core::adapter::build_nested_list_string_utf8_to_utf16_result_test_module();
    let sum = nested_patch_and_sum(&wasm, &[0xC3, 0xA9], b"Hi");
    assert_eq!(
        sum, 410,
        "#272 inc5a: nested list<string> [\"é\",\"Hi\"] must transcode 'é' to one \
         UTF-16 unit 0x00E9 and REWRITE its inner len to 1 (sum 410); a stale \
         2-byte len would over-read"
    );
}

/// #272 inc 5a (NEGATIVE — the blocker resolution): a 2-element `list<list<u8>>`
/// result must be RAW-COPIED, never transcoded. A nested `list<u8>`
/// (`is_string == false` from `collect_indirections`) is arbitrary binary;
/// transcoding it as UTF-8 would corrupt it. Inner buffers `[0xC3, 0xA9]` and
/// `[0x01, 0x80]`: a raw copy preserves all 4 bytes (lengths stay 2 each), so
/// the byte-sum is 0xC3+0xA9+0x01+0x80 = 195+169+1+128 = 493. A (WRONG)
/// UTF-8→UTF-16 transcode would collapse `0xC3 0xA9` to one unit 0x00E9 and
/// replace the lone `0x80` with U+FFFD, changing both the bytes AND the lengths
/// — a different sum. The correct 493 proves the `list<u8>` is NOT transcoded.
#[test]
fn inc5a_async_nested_list_u8_result_not_transcoded() {
    let wasm = meld_core::adapter::build_nested_list_u8_result_not_transcoded_test_module();
    let sum = nested_patch_and_sum(&wasm, &[0xC3, 0xA9], &[0x01, 0x80]);
    assert_eq!(
        sum, 493,
        "#272 inc5a: nested list<u8> must be RAW-COPIED verbatim (byte-sum 493), \
         NOT transcoded — proves the string-ness blocker is resolved and \
         arbitrary binary is not corrupted"
    );
}

// ----------------------------------------------------------------------------
// #272 inc 5b — NESTED `list<string>` RESULT transcode, the FIVE remaining
// result directions (everything except inc-5a's callee=Utf8 → caller=Utf16).
// Drives the production `emit_patch_nested_indirections` via the parametrized
// `build_nested_list_string_result_test_module(caller_enc, callee_enc)` module,
// which patches but does NOT sum in wasm; the host reads back the PATCHED
// caller-memory inner `(ptr, len)` headers + transcoded buffers and asserts
// directly (so dest-latin1 TAGGED lengths are observable in Rust).
// ----------------------------------------------------------------------------

const N_INNER_A_OFF: i32 = 100; // callee-memory offset of inner buffer 0
const N_INNER_B_OFF: i32 = 160; // callee-memory offset of inner buffer 1
const N_OUTER_OFF: i32 = 240; // outer list offset (BOTH memories)

/// A patched inner record as the host reads it back from CALLER memory after
/// `patch`: `(inner_ptr, inner_len_raw, bytes)` — `inner_len_raw` is the
/// possibly-UTF16_TAG-tagged length the emitter wrote; `bytes` is the
/// transcoded output buffer read at `inner_ptr` for the UNTAGGED unit/byte
/// count (read as raw bytes; the caller asserts shape per direction).
struct PatchedInner {
    len_raw: i32,
    bytes: Vec<u8>,
}

/// Instantiate the inc-5b module for `(caller_enc, callee_enc)`, write the two
/// inner source buffers into CALLEE memory 1 with the given (possibly tagged)
/// source lengths, lay out the 2-record outer list in BOTH memories, run
/// `patch`, and return the two PATCHED inner records read back from CALLER
/// memory. `read_unit_bytes` is how many bytes per output unit to read for the
/// UNTAGGED length (1 for UTF-8/Latin-1 output, 2 for UTF-16 output) — for
/// dest-latin1 the caller decides per-record from the tag.
/// `out_unit_width`: how many output bytes per UNTAGGED unit. `Some(2)` for a
/// UTF-16 caller, `Some(1)` for a UTF-8 caller; `None` for a CompactUtf16
/// (dest-latin1) caller, where the width is derived per-record from the output
/// tag (tag-set → 2-byte UTF-16, tag-clear → 1-byte Latin-1).
fn nested_patch_readback(
    caller_enc: CanonStringEncoding,
    callee_enc: CanonStringEncoding,
    out_unit_width: Option<usize>,
    inner_a: (&[u8], i32),
    inner_b: (&[u8], i32),
) -> Vec<PatchedInner> {
    let wasm = build_nested_list_string_result_test_module(caller_enc, callee_enc);

    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&wasm)
        .expect("#272 inc5b oracle module should validate");

    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let module = RuntimeModule::new(&engine, &wasm).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let caller_mem = instance
        .get_memory(&mut store, "caller_memory")
        .expect("oracle module exports caller_memory");
    let callee_mem = instance
        .get_memory(&mut store, "callee_memory")
        .expect("oracle module exports callee_memory");

    // Inner SOURCE buffers live only in callee memory 1.
    callee_mem
        .write(&mut store, N_INNER_A_OFF as usize, inner_a.0)
        .expect("write inner buffer 0");
    callee_mem
        .write(&mut store, N_INNER_B_OFF as usize, inner_b.0)
        .expect("write inner buffer 1");

    // Outer list: (ptr, len) per record, the SAME bytes in both memories
    // (caller = the stale post-outer-bulk-copy duplicate the emitter overwrites).
    let mut outer = Vec::new();
    outer.extend_from_slice(&N_INNER_A_OFF.to_le_bytes());
    outer.extend_from_slice(&inner_a.1.to_le_bytes());
    outer.extend_from_slice(&N_INNER_B_OFF.to_le_bytes());
    outer.extend_from_slice(&inner_b.1.to_le_bytes());
    callee_mem
        .write(&mut store, N_OUTER_OFF as usize, &outer)
        .expect("write outer records (callee)");
    caller_mem
        .write(&mut store, N_OUTER_OFF as usize, &outer)
        .expect("write outer records (caller stale)");

    let f = instance
        .get_typed_func::<(i32, i32, i32), ()>(&mut store, "patch")
        .expect("oracle module exports patch");
    f.call(&mut store, (N_OUTER_OFF, N_OUTER_OFF, 2))
        .expect("patch runs");

    // Read back the two PATCHED caller-side records.
    let mut out = Vec::new();
    for i in 0..2i32 {
        let rec = (N_OUTER_OFF + i * 8) as usize;
        let mut hdr = [0u8; 8];
        caller_mem
            .read(&mut store, rec, &mut hdr)
            .expect("read hdr");
        let ptr = i32::from_le_bytes(hdr[0..4].try_into().unwrap());
        let len_raw = i32::from_le_bytes(hdr[4..8].try_into().unwrap());
        // Untagged unit count; output unit width depends on whether the tag is
        // set (UTF-16, 2 bytes) or clear (1 byte) — for non-dest-latin1 the tag
        // is never set so this collapses to the natural width.
        let units = (len_raw & !UTF16_TAG) as usize;
        // Output unit width: fixed for utf8/utf16 callers; tag-derived for the
        // dest-latin1 (CompactUtf16) caller.
        let unit_w = out_unit_width.unwrap_or(if (len_raw & UTF16_TAG) != 0 { 2 } else { 1 });
        let mut bytes = vec![0u8; units * unit_w];
        caller_mem
            .read(&mut store, ptr as usize, &mut bytes)
            .expect("read inner buffer");
        out.push(PatchedInner { len_raw, bytes });
    }
    out
}

/// #272 inc 5b (callee=Utf16 → caller=Utf8): a nested `list<string>` result with
/// a latin1-fitting "Hi" (UTF-16 [H,i]) and a non-latin1 "é" (UTF-16 [0x00E9])
/// must transcode the inner UTF-16 to UTF-8. "Hi" → [0x48,0x69] (len 2); "é" →
/// the 2-byte UTF-8 sequence [0xC3,0xA9] (len 2 — the direction's multi-byte
/// representation matters: a raw copy would leave 2 UTF-16 code units = 4 bytes).
#[test]
fn inc5b_nested_list_string_utf16_to_utf8() {
    // "Hi" UTF-16 LE, len 2 code units; "é" = U+00E9 UTF-16 LE, len 1.
    let recs = nested_patch_readback(
        CanonStringEncoding::Utf8,
        CanonStringEncoding::Utf16,
        Some(1), // UTF-8 caller output: 1 byte/unit
        (&[0x48, 0x00, 0x69, 0x00], 2),
        (&[0xE9, 0x00], 1),
    );
    assert_eq!(recs[0].len_raw, 2, "\"Hi\" → UTF-8 byte len 2");
    assert_eq!(recs[0].bytes, vec![0x48, 0x69]);
    assert_eq!(recs[1].len_raw, 2, "\"é\" → 2-byte UTF-8 len 2");
    assert_eq!(recs[1].bytes, vec![0xC3, 0xA9]);
}

/// #272 inc 5b (callee=CompactUtf16 → caller=Utf16): a nested `list<string>`
/// result. Record 0 is a tag-CLEAR Latin-1 "Hi" (bytes [0x48,0x69], len 2);
/// record 1 DRIVES A TAG-SET inner (source already UTF-16): "中" = U+4E2D,
/// stored verbatim as UTF-16 [0x2D,0x4E], len = 1 | UTF16_TAG. Both transcode to
/// UTF-16 output: "Hi" → [H,0,i,0] len 2; "中" → [0x2D,0x4E] len 1.
#[test]
fn inc5b_nested_list_string_latin1_to_utf16() {
    let recs = nested_patch_readback(
        CanonStringEncoding::Utf16,
        CanonStringEncoding::CompactUtf16,
        Some(2),                        // UTF-16 caller output: 2 bytes/unit
        (&[0x48, 0x69], 2),             // tag-clear Latin-1 "Hi"
        (&[0x2D, 0x4E], 1 | UTF16_TAG), // tag-SET UTF-16 "中"
    );
    assert_eq!(recs[0].len_raw, 2, "latin1 \"Hi\" → UTF-16 code-unit len 2");
    assert_eq!(recs[0].bytes, vec![0x48, 0x00, 0x69, 0x00]);
    assert_eq!(
        recs[1].len_raw, 1,
        "tag-set \"中\" → UTF-16 code-unit len 1"
    );
    assert_eq!(recs[1].bytes, vec![0x2D, 0x4E]);
}

/// #272 inc 5b (callee=CompactUtf16 → caller=Utf8): record 0 tag-CLEAR Latin-1
/// "Hi" → UTF-8 "Hi" (len 2); record 1 DRIVES A TAG-SET inner "中" (UTF-16
/// [0x2D,0x4E], len 1|TAG) → 3-byte UTF-8 [0xE4,0xB8,0xAD] (len 3).
#[test]
fn inc5b_nested_list_string_latin1_to_utf8() {
    let recs = nested_patch_readback(
        CanonStringEncoding::Utf8,
        CanonStringEncoding::CompactUtf16,
        Some(1), // UTF-8 caller output: 1 byte/unit
        (&[0x48, 0x69], 2),
        (&[0x2D, 0x4E], 1 | UTF16_TAG),
    );
    assert_eq!(recs[0].len_raw, 2, "latin1 \"Hi\" → UTF-8 len 2");
    assert_eq!(recs[0].bytes, vec![0x48, 0x69]);
    assert_eq!(recs[1].len_raw, 3, "tag-set \"中\" → 3-byte UTF-8 len 3");
    assert_eq!(recs[1].bytes, vec![0xE4, 0xB8, 0xAD]);
}

/// #272 inc 5b (callee=Utf8 → caller=CompactUtf16, DEST-LATIN1): record 0 a
/// latin1-FITTING "é" (UTF-8 [0xC3,0xA9]) collapses to a single Latin-1 byte
/// [0xE9] with a tag-CLEAR len 1; record 1 a NON-LATIN1 "中" (UTF-8
/// [0xE4,0xB8,0xAD]) must use the UTF-16 representation [0x2D,0x4E] with the
/// TAGGED len (1 | UTF16_TAG). Asserting the tagged len on the non-latin1 record
/// proves the dest-latin1 tag-producing path runs inside the nested loop.
#[test]
fn inc5b_nested_list_string_utf8_to_latin1() {
    let recs = nested_patch_readback(
        CanonStringEncoding::CompactUtf16,
        CanonStringEncoding::Utf8,
        None,                     // dest-latin1: output width tag-derived per record
        (&[0xC3, 0xA9], 2),       // "é" UTF-8, fits Latin-1
        (&[0xE4, 0xB8, 0xAD], 3), // "中" UTF-8, needs UTF-16
    );
    assert_eq!(recs[0].len_raw, 1, "latin1-fitting \"é\" → tag-CLEAR len 1");
    assert_eq!(recs[0].bytes, vec![0xE9]);
    assert_eq!(
        recs[1].len_raw,
        1 | UTF16_TAG,
        "non-latin1 \"中\" → TAGGED len (1 | UTF16_TAG)"
    );
    assert_eq!(recs[1].bytes, vec![0x2D, 0x4E]);
}

/// #272 inc 5b (callee=Utf16 → caller=CompactUtf16, DEST-LATIN1): record 0 a
/// latin1-FITTING "é" (UTF-16 [0xE9,0x00]) → Latin-1 byte [0xE9], tag-CLEAR len
/// 1; record 1 a NON-LATIN1 "中" (UTF-16 [0x2D,0x4E]) → UTF-16 [0x2D,0x4E] with
/// TAGGED len (1 | UTF16_TAG).
#[test]
fn inc5b_nested_list_string_utf16_to_latin1() {
    let recs = nested_patch_readback(
        CanonStringEncoding::CompactUtf16,
        CanonStringEncoding::Utf16,
        None,               // dest-latin1: output width tag-derived per record
        (&[0xE9, 0x00], 1), // "é" UTF-16, fits Latin-1
        (&[0x2D, 0x4E], 1), // "中" UTF-16, needs UTF-16 rep
    );
    assert_eq!(recs[0].len_raw, 1, "latin1-fitting \"é\" → tag-CLEAR len 1");
    assert_eq!(recs[0].bytes, vec![0xE9]);
    assert_eq!(
        recs[1].len_raw,
        1 | UTF16_TAG,
        "non-latin1 \"中\" → TAGGED len (1 | UTF16_TAG)"
    );
    assert_eq!(recs[1].bytes, vec![0x2D, 0x4E]);
}

// ----------------------------------------------------------------------------
// #272 inc 5c-a — NESTED `list<string>` PARAM nested-copy (UTF-8 → UTF-16), the
// FIRST real nested-PARAM transcoding, plus the negative `list<u8>` case proving
// the #281 same-encoding/deep-copy gap is CLOSED (a nested `list<u8>` PARAM is
// DEEP-COPIED VERBATIM into callee memory + re-pointed, never transcoded).
//
// Both drive the EXACT production `emit_param_nested_indirections` emitter via
// the two-memory modules built by
// `build_nested_list_string_utf8_to_utf16_param_test_module` /
// `build_nested_list_u8_param_deep_copied_test_module`. This is the PARAM
// direction (caller PROVIDES, callee READS): the host writes the inner SOURCE
// buffers into CALLER memory 0, and the SHALLOW outer `(ptr, len)` records (inner
// ptr still pointing into CALLER memory) into CALLEE memory 1 — the post-outer-
// bulk-copy state. The emitter transcodes (or deep-copies) each inner buffer into
// callee memory 1, rewrites the callee-side inner header, and the module then
// sums the inner units by re-reading the PATCHED CALLEE-memory headers.
// ----------------------------------------------------------------------------

const P_INNER_A_OFF: i32 = 100; // CALLER-memory offset of inner source buffer 0
const P_INNER_B_OFF: i32 = 140; // CALLER-memory offset of inner source buffer 1
const P_OUTER_OFF: i32 = 200; // shallow outer record array offset (CALLEE memory)

/// Instantiate `wasm`, write the two inner SOURCE buffers into CALLER memory 0,
/// lay out the SHALLOW 2-record outer list `(inner_caller_ptr, len)` at
/// `P_OUTER_OFF` in CALLEE memory 1 (the inner ptr still points into CALLER
/// memory — the post-bulk-copy state), run `patch_and_sum(P_OUTER_OFF, 2)`, and
/// return its sum.
fn nested_param_patch_and_sum(wasm: &[u8], inner_a: &[u8], inner_b: &[u8]) -> i32 {
    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(wasm)
        .expect("#272 inc5c-a oracle module should validate");

    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let module = RuntimeModule::new(&engine, wasm).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let caller_mem = instance
        .get_memory(&mut store, "caller_memory")
        .expect("oracle module exports caller_memory");
    let callee_mem = instance
        .get_memory(&mut store, "callee_memory")
        .expect("oracle module exports callee_memory");

    // Inner SOURCE buffers live ONLY in CALLER memory 0 (the param source).
    caller_mem
        .write(&mut store, P_INNER_A_OFF as usize, inner_a)
        .expect("write inner buffer 0 into caller memory");
    caller_mem
        .write(&mut store, P_INNER_B_OFF as usize, inner_b)
        .expect("write inner buffer 1 into caller memory");

    // SHALLOW outer record array in CALLEE memory 1: rec0 = (P_INNER_A_OFF,
    // len_a), rec1 = (P_INNER_B_OFF, len_b). The inner ptr points into CALLER
    // memory — exactly what the outer bulk `memory.copy` leaves (gap #281).
    let mut outer = Vec::new();
    outer.extend_from_slice(&P_INNER_A_OFF.to_le_bytes());
    outer.extend_from_slice(&(inner_a.len() as i32).to_le_bytes());
    outer.extend_from_slice(&P_INNER_B_OFF.to_le_bytes());
    outer.extend_from_slice(&(inner_b.len() as i32).to_le_bytes());
    callee_mem
        .write(&mut store, P_OUTER_OFF as usize, &outer)
        .expect("write shallow outer records into callee memory");

    let f = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "patch_and_sum")
        .expect("oracle module exports patch_and_sum");
    f.call(&mut store, (P_OUTER_OFF, 2))
        .expect("patch_and_sum runs")
}

/// #272 inc 5c-a (positive): a 2-element `list<string>` PARAM `["Hi", "yo"]`
/// (UTF-8) transcoded UTF-8 → UTF-16 sums the inner UTF-16 CODE UNITS to
/// 'H'+'i'+'y'+'o' = 0x48+0x69+0x79+0x6F = 409, read back from the PATCHED
/// CALLEE-memory headers. A correct sum proves the inner strings are TRANSCODED,
/// their headers re-pointed INTO CALLEE memory, and the len set to the UTF-16
/// code-unit count.
#[test]
fn inc5c_a_async_nested_list_string_param_utf8_to_utf16_transcodes() {
    let wasm = meld_core::adapter::build_nested_list_string_utf8_to_utf16_param_test_module();
    let sum = nested_param_patch_and_sum(&wasm, b"Hi", b"yo");
    assert_eq!(
        sum, 409,
        "#272 inc5c-a: nested list<string> [\"Hi\",\"yo\"] PARAM UTF-8 → UTF-16 must \
         sum the transcoded inner code units to 409 (proves real nested PARAM \
         transcode + re-point into callee memory, not a shallow copy)"
    );
}

/// #272 inc 5c-a (positive, non-ASCII): a `list<string>` PARAM `["é", "Hi"]`
/// where "é" is UTF-8 `0xC3 0xA9` (2 bytes) → ONE UTF-16 code unit 0x00E9. The
/// inner len header MUST be rewritten from the 2-byte UTF-8 length to the 1-unit
/// UTF-16 length, else the summing loop would read a phantom second unit. Sum =
/// 0x00E9 + 0x48 + 0x69 = 233 + 72 + 105 = 410.
#[test]
fn inc5c_a_async_nested_list_string_param_non_ascii_rewrites_len() {
    let wasm = meld_core::adapter::build_nested_list_string_utf8_to_utf16_param_test_module();
    let sum = nested_param_patch_and_sum(&wasm, &[0xC3, 0xA9], b"Hi");
    assert_eq!(
        sum, 410,
        "#272 inc5c-a: nested list<string> [\"é\",\"Hi\"] PARAM must transcode 'é' to \
         one UTF-16 unit 0x00E9 and REWRITE its inner len to 1 (sum 410)"
    );
}

/// #272 inc 5c-a (NEGATIVE — the #281 close): a 2-element `list<list<u8>>` PARAM
/// must be DEEP-COPIED VERBATIM into callee memory and re-pointed, NEVER
/// transcoded. A nested `list<u8>` (`is_string == false`) is arbitrary binary.
/// Inner buffers `[0xC3, 0xA9]` and `[0x01, 0x80]`: a verbatim deep-copy
/// preserves all 4 bytes (lengths stay 2 each), so the byte-sum is
/// 0xC3+0xA9+0x01+0x80 = 195+169+1+128 = 493. A (wrong) UTF-8→UTF-16 transcode
/// would collapse `0xC3 0xA9` to one unit 0x00E9 and replace the lone `0x80`
/// with U+FFFD — a different sum. The correct 493 (re-read from the PATCHED
/// CALLEE-memory header) proves the inner buffer is deep-copied + re-pointed
/// (NOT left dangling into caller memory — #281 closed — and NOT transcoded).
#[test]
fn inc5c_a_async_nested_list_u8_param_deep_copied_verbatim() {
    let wasm = meld_core::adapter::build_nested_list_u8_param_deep_copied_test_module();
    let sum = nested_param_patch_and_sum(&wasm, &[0xC3, 0xA9], &[0x01, 0x80]);
    assert_eq!(
        sum, 493,
        "#272 inc5c-a: nested list<u8> PARAM must be DEEP-COPIED verbatim into \
         callee memory + re-pointed (byte-sum 493), NOT transcoded — proves #281 \
         closed and arbitrary binary is not corrupted"
    );
}

// ----------------------------------------------------------------------------
// #272 inc 5c-b — NESTED `list<string>` PARAM nested-copy for the REMAINING 5
// directions, completing ALL 6 nested-PARAM directions (mirroring how inc 5b
// completed the result side). Each drives the EXACT production
// `emit_param_nested_indirections` 6-way dispatch via
// `build_nested_list_string_param_test_module(caller_enc, callee_enc)`.
//
// PARAM direction (caller PROVIDES, callee READS): SRC = CALLER memory 0 (inner
// SOURCE strings), DST = CALLEE memory 1 (transcoded buffers + patched records +
// realloc arena). The host writes the inner SOURCE buffers into CALLER memory 0
// and the SHALLOW outer `(ptr, len)` records (inner ptr → CALLER memory) into
// CALLEE memory 1, runs `patch`, then reads the PATCHED records + transcoded
// buffers back from CALLEE memory 1 and asserts directly in Rust (incl. the
// TAGGED inner len for the dest-latin1 directions).
// ----------------------------------------------------------------------------

/// A patched inner record as the host reads it back from CALLEE memory after
/// `patch`: `(len_raw, bytes)` — `len_raw` is the possibly-UTF16_TAG-tagged
/// length the emitter wrote; `bytes` is the transcoded output read at the
/// re-pointed inner ptr for the UNTAGGED unit/byte count.
struct PatchedParamInner {
    len_raw: i32,
    bytes: Vec<u8>,
}

/// Instantiate the inc-5c-b PARAM module for `(caller_enc, callee_enc)`, write
/// the two inner SOURCE buffers into CALLER memory 0, lay out the SHALLOW
/// 2-record outer list `(inner_caller_ptr, src_len)` in CALLEE memory 1, run
/// `patch`, and return the two PATCHED inner records read back from CALLEE
/// memory 1. `out_unit_width`: bytes per UNTAGGED output unit — `Some(2)` UTF-16
/// callee, `Some(1)` UTF-8 callee, `None` for a CompactUtf16 (dest-latin1)
/// callee where the width is derived per-record from the output tag.
fn nested_param_patch_readback(
    caller_enc: CanonStringEncoding,
    callee_enc: CanonStringEncoding,
    out_unit_width: Option<usize>,
    inner_a: (&[u8], i32),
    inner_b: (&[u8], i32),
) -> Vec<PatchedParamInner> {
    let wasm =
        meld_core::adapter::build_nested_list_string_param_test_module(caller_enc, callee_enc);

    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&wasm)
        .expect("#272 inc5c-b oracle module should validate");

    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let module = RuntimeModule::new(&engine, &wasm).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let caller_mem = instance
        .get_memory(&mut store, "caller_memory")
        .expect("oracle module exports caller_memory");
    let callee_mem = instance
        .get_memory(&mut store, "callee_memory")
        .expect("oracle module exports callee_memory");

    // Inner SOURCE buffers live ONLY in CALLER memory 0 (the param source).
    caller_mem
        .write(&mut store, P_INNER_A_OFF as usize, inner_a.0)
        .expect("write inner buffer 0 into caller memory");
    caller_mem
        .write(&mut store, P_INNER_B_OFF as usize, inner_b.0)
        .expect("write inner buffer 1 into caller memory");

    // SHALLOW outer record array in CALLEE memory 1: the inner ptr points into
    // CALLER memory, with the (possibly tagged) SOURCE length — exactly the
    // post-outer-bulk-copy state (gap #281).
    let mut outer = Vec::new();
    outer.extend_from_slice(&P_INNER_A_OFF.to_le_bytes());
    outer.extend_from_slice(&inner_a.1.to_le_bytes());
    outer.extend_from_slice(&P_INNER_B_OFF.to_le_bytes());
    outer.extend_from_slice(&inner_b.1.to_le_bytes());
    callee_mem
        .write(&mut store, P_OUTER_OFF as usize, &outer)
        .expect("write shallow outer records into callee memory");

    let f = instance
        .get_typed_func::<(i32, i32), ()>(&mut store, "patch")
        .expect("oracle module exports patch");
    f.call(&mut store, (P_OUTER_OFF, 2)).expect("patch runs");

    // Read back the two PATCHED CALLEE-side records (re-pointed into callee mem).
    let mut out = Vec::new();
    for i in 0..2i32 {
        let rec = (P_OUTER_OFF + i * 8) as usize;
        let mut hdr = [0u8; 8];
        callee_mem
            .read(&mut store, rec, &mut hdr)
            .expect("read hdr");
        let ptr = i32::from_le_bytes(hdr[0..4].try_into().unwrap());
        let len_raw = i32::from_le_bytes(hdr[4..8].try_into().unwrap());
        let units = (len_raw & !UTF16_TAG) as usize;
        let unit_w = out_unit_width.unwrap_or(if (len_raw & UTF16_TAG) != 0 { 2 } else { 1 });
        let mut bytes = vec![0u8; units * unit_w];
        callee_mem
            .read(&mut store, ptr as usize, &mut bytes)
            .expect("read inner buffer");
        out.push(PatchedParamInner { len_raw, bytes });
    }
    out
}

/// #272 inc 5c-b (caller=Utf16 → callee=Utf8): a nested `list<string>` PARAM
/// with a latin1-fitting "Hi" (UTF-16 [H,i], 2 units) and a non-latin1 "é"
/// (UTF-16 [0x00E9], 1 unit) must transcode the inner UTF-16 to UTF-8. "Hi" →
/// [0x48,0x69] len 2; "é" → 2-byte UTF-8 [0xC3,0xA9] len 2 (a raw copy would
/// leave 2 UTF-16 units = wrong).
#[test]
fn inc5c_b_async_nested_list_string_param_utf16_to_utf8() {
    let recs = nested_param_patch_readback(
        CanonStringEncoding::Utf16,
        CanonStringEncoding::Utf8,
        Some(1),
        (&[0x48, 0x00, 0x69, 0x00], 2),
        (&[0xE9, 0x00], 1),
    );
    assert_eq!(recs[0].len_raw, 2, "\"Hi\" → UTF-8 byte len 2");
    assert_eq!(recs[0].bytes, vec![0x48, 0x69]);
    assert_eq!(recs[1].len_raw, 2, "\"é\" → 2-byte UTF-8 len 2");
    assert_eq!(recs[1].bytes, vec![0xC3, 0xA9]);
}

/// #272 inc 5c-b (caller=CompactUtf16 → callee=Utf16): record 0 a tag-CLEAR
/// Latin-1 "Hi" (bytes [0x48,0x69], len 2); record 1 DRIVES A TAG-SET inner
/// (source already UTF-16) "中" = U+4E2D, stored verbatim as UTF-16 [0x2D,0x4E],
/// len = 1 | UTF16_TAG. Both → UTF-16 output: "Hi" → [H,0,i,0] len 2; "中" →
/// [0x2D,0x4E] len 1. Drives the source-latin1 tag dispatch inside the loop.
#[test]
fn inc5c_b_async_nested_list_string_param_latin1_to_utf16() {
    let recs = nested_param_patch_readback(
        CanonStringEncoding::CompactUtf16,
        CanonStringEncoding::Utf16,
        Some(2),
        (&[0x48, 0x69], 2),             // tag-clear Latin-1 "Hi"
        (&[0x2D, 0x4E], 1 | UTF16_TAG), // tag-SET UTF-16 "中"
    );
    assert_eq!(recs[0].len_raw, 2, "latin1 \"Hi\" → UTF-16 unit len 2");
    assert_eq!(recs[0].bytes, vec![0x48, 0x00, 0x69, 0x00]);
    assert_eq!(recs[1].len_raw, 1, "tag-set \"中\" → UTF-16 unit len 1");
    assert_eq!(recs[1].bytes, vec![0x2D, 0x4E]);
}

/// #272 inc 5c-b (caller=CompactUtf16 → callee=Utf8): record 0 tag-CLEAR Latin-1
/// "Hi" → UTF-8 "Hi" (len 2); record 1 DRIVES A TAG-SET inner "中" (UTF-16
/// [0x2D,0x4E], len 1|TAG) → 3-byte UTF-8 [0xE4,0xB8,0xAD] (len 3).
#[test]
fn inc5c_b_async_nested_list_string_param_latin1_to_utf8() {
    let recs = nested_param_patch_readback(
        CanonStringEncoding::CompactUtf16,
        CanonStringEncoding::Utf8,
        Some(1),
        (&[0x48, 0x69], 2),
        (&[0x2D, 0x4E], 1 | UTF16_TAG),
    );
    assert_eq!(recs[0].len_raw, 2, "latin1 \"Hi\" → UTF-8 len 2");
    assert_eq!(recs[0].bytes, vec![0x48, 0x69]);
    assert_eq!(recs[1].len_raw, 3, "tag-set \"中\" → 3-byte UTF-8 len 3");
    assert_eq!(recs[1].bytes, vec![0xE4, 0xB8, 0xAD]);
}

/// #272 inc 5c-b (caller=Utf8 → callee=CompactUtf16, DEST-LATIN1): record 0 a
/// latin1-FITTING "é" (UTF-8 [0xC3,0xA9]) collapses to a single Latin-1 byte
/// [0xE9] with a tag-CLEAR len 1; record 1 a NON-LATIN1 "中" (UTF-8
/// [0xE4,0xB8,0xAD]) must use the UTF-16 representation [0x2D,0x4E] with the
/// TAGGED inner len (1 | UTF16_TAG). Asserting the TAGGED len on the non-latin1
/// record proves the dest-latin1 tag-producing path runs inside the nested loop
/// AND that the inner header gets the tagged length (the inc-4b flat-path rule).
#[test]
fn inc5c_b_async_nested_list_string_param_utf8_to_latin1() {
    let recs = nested_param_patch_readback(
        CanonStringEncoding::Utf8,
        CanonStringEncoding::CompactUtf16,
        None, // dest-latin1: output width tag-derived per record
        (&[0xC3, 0xA9], 2),
        (&[0xE4, 0xB8, 0xAD], 3),
    );
    assert_eq!(recs[0].len_raw, 1, "latin1-fitting \"é\" → tag-CLEAR len 1");
    assert_eq!(recs[0].bytes, vec![0xE9]);
    assert_eq!(
        recs[1].len_raw,
        1 | UTF16_TAG,
        "non-latin1 \"中\" → TAGGED inner len (1 | UTF16_TAG)"
    );
    assert_eq!(recs[1].bytes, vec![0x2D, 0x4E]);
}

/// #272 inc 5c-b (caller=Utf16 → callee=CompactUtf16, DEST-LATIN1): record 0 a
/// latin1-FITTING "é" (UTF-16 [0xE9,0x00]) → Latin-1 byte [0xE9], tag-CLEAR len
/// 1; record 1 a NON-LATIN1 "中" (UTF-16 [0x2D,0x4E]) → UTF-16 [0x2D,0x4E] with
/// the TAGGED inner len (1 | UTF16_TAG).
#[test]
fn inc5c_b_async_nested_list_string_param_utf16_to_latin1() {
    let recs = nested_param_patch_readback(
        CanonStringEncoding::Utf16,
        CanonStringEncoding::CompactUtf16,
        None,
        (&[0xE9, 0x00], 1),
        (&[0x2D, 0x4E], 1),
    );
    assert_eq!(recs[0].len_raw, 1, "latin1-fitting \"é\" → tag-CLEAR len 1");
    assert_eq!(recs[0].bytes, vec![0xE9]);
    assert_eq!(
        recs[1].len_raw,
        1 | UTF16_TAG,
        "non-latin1 \"中\" → TAGGED inner len (1 | UTF16_TAG)"
    );
    assert_eq!(recs[1].bytes, vec![0x2D, 0x4E]);
}

/// #272 inc 5c-b (NEGATIVE — nested `list<u8>` deep-copied, NOT transcoded, in a
/// transcoding direction): the #281-close verbatim deep-copy of a nested
/// `list<u8>` param must hold regardless of the encoding direction (the
/// is_string == false gate suppresses transcode in EVERY direction). Reuses the
/// 5c-a `list<u8>` deep-copy oracle (caller=Utf8 → callee=Utf16): inner buffers
/// `[0xC3,0xA9]` and `[0x01,0x80]` are copied verbatim (byte-sum 493), NOT
/// transcoded (a transcode would collapse `0xC3 0xA9` → one unit + map `0x80` →
/// U+FFFD, a different sum). The guard test
/// `inc5c_b_async_nested_list_u8_param_fails_loud_all_directions` separately
/// pins that the GUARD refuses to widen the allow-set for a `list<u8>` in all 6
/// directions; this confirms the EMITTER's deep-copy semantics at runtime.
#[test]
fn inc5c_b_async_nested_list_u8_param_deep_copied_not_transcoded() {
    let wasm = meld_core::adapter::build_nested_list_u8_param_deep_copied_test_module();
    let sum = nested_param_patch_and_sum(&wasm, &[0xC3, 0xA9], &[0x01, 0x80]);
    assert_eq!(
        sum, 493,
        "#272 inc5c-b: a nested list<u8> PARAM is DEEP-COPIED verbatim (byte-sum \
         493), NEVER transcoded — the is_string==false gate holds in every direction"
    );
}

// ----------------------------------------------------------------------------
// #272 inc 5c-b — SAME-ENCODING nested `list<string>` PARAM deep-copy (the #281
// completeness gap). A same-encoding direction (caller_enc == callee_enc) is
// NOT transcoded; it falls through to the verbatim deep-copy. The inner `len`
// header is a CODE-UNIT count (UTF-16) or a tagged count (CompactUtf16), NOT a
// byte count, so the deep-copy byte count MUST account for the encoding width —
// mirroring the result-side `emit_patch_nested_indirections`. Pre-fix these
// fail: a UTF-16 same-encoding inner copies `len*1` bytes (half the buffer,
// bleeding adjacent data) and a CompactUtf16 tag-set inner inflates the bounds
// guard so the re-point is skipped (dangling pointer).
// ----------------------------------------------------------------------------

/// Like `nested_param_patch_readback` but for the SAME-ENCODING deep-copy path:
/// the inner header `len` is PRESERVED verbatim (the deep-copy keeps the
/// original len), so the host supplies the read-back width and the explicit
/// caller-side source ptr. Returns each patched `(ptr, len_raw, bytes)` so a
/// test can assert BOTH the re-point happened (ptr moved out of caller memory)
/// and the full code units landed in callee memory.
fn nested_param_deepcopy_readback(
    caller_enc: CanonStringEncoding,
    callee_enc: CanonStringEncoding,
    unit_width: usize,
    inner_a: (&[u8], i32),
    inner_b: (&[u8], i32),
) -> Vec<(i32, i32, Vec<u8>)> {
    let wasm =
        meld_core::adapter::build_nested_list_string_param_test_module(caller_enc, callee_enc);

    let mut validator = wasmparser::Validator::new();
    validator
        .validate_all(&wasm)
        .expect("#272 inc5c-b same-encoding oracle module should validate");

    let mut config = Config::new();
    config.wasm_multi_memory(true);
    let engine = Engine::new(&config).unwrap();
    let module = RuntimeModule::new(&engine, &wasm).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let caller_mem = instance
        .get_memory(&mut store, "caller_memory")
        .expect("oracle module exports caller_memory");
    let callee_mem = instance
        .get_memory(&mut store, "callee_memory")
        .expect("oracle module exports callee_memory");

    // Inner SOURCE buffers live ONLY in CALLER memory 0 (the param source).
    caller_mem
        .write(&mut store, P_INNER_A_OFF as usize, inner_a.0)
        .expect("write inner buffer 0 into caller memory");
    caller_mem
        .write(&mut store, P_INNER_B_OFF as usize, inner_b.0)
        .expect("write inner buffer 1 into caller memory");

    // SHALLOW outer record array in CALLEE memory 1 (post-bulk-copy state, #281):
    // inner ptr → CALLER memory, with the (possibly tagged) SOURCE length.
    let mut outer = Vec::new();
    outer.extend_from_slice(&P_INNER_A_OFF.to_le_bytes());
    outer.extend_from_slice(&inner_a.1.to_le_bytes());
    outer.extend_from_slice(&P_INNER_B_OFF.to_le_bytes());
    outer.extend_from_slice(&inner_b.1.to_le_bytes());
    callee_mem
        .write(&mut store, P_OUTER_OFF as usize, &outer)
        .expect("write shallow outer records into callee memory");

    let f = instance
        .get_typed_func::<(i32, i32), ()>(&mut store, "patch")
        .expect("oracle module exports patch");
    f.call(&mut store, (P_OUTER_OFF, 2)).expect("patch runs");

    let mut out = Vec::new();
    for i in 0..2i32 {
        let rec = (P_OUTER_OFF + i * 8) as usize;
        let mut hdr = [0u8; 8];
        callee_mem
            .read(&mut store, rec, &mut hdr)
            .expect("read hdr");
        let ptr = i32::from_le_bytes(hdr[0..4].try_into().unwrap());
        let len_raw = i32::from_le_bytes(hdr[4..8].try_into().unwrap());
        let units = (len_raw & !UTF16_TAG) as usize;
        let mut bytes = vec![0u8; units * unit_width];
        callee_mem
            .read(&mut store, ptr as usize, &mut bytes)
            .expect("read inner buffer");
        out.push((ptr, len_raw, bytes));
    }
    out
}

/// #272 inc 5c-b (SAME-ENCODING Utf16 → Utf16, #281 completeness): a nested
/// `list<string>` PARAM over `["é","Hi"]` in UTF-16. "é" = U+00E9 → 1 code unit
/// [0xE9,0x00]; "Hi" = 2 code units [0x48,0x00,0x69,0x00]. Same-encoding ⇒ NOT
/// transcoded ⇒ verbatim deep-copy. Each re-pointed callee buffer MUST hold the
/// FULL code units (é = [0xE9,0x00], i.e. `len*2` bytes). Pre-fix the deep-copy
/// copies `len*1` bytes — é lands as [0xE9, 0x48] (the trailing 0x00 dropped, the
/// 0x48 bled in from the adjacent "Hi" buffer) — so this FAILS; post-fix the
/// UTF-16 width (`len*2`, align 2) copies the whole buffer and it PASSES.
#[test]
fn inc5c_b_same_encoding_utf16_nested_param_deep_copies_full_codeunits() {
    let recs = nested_param_deepcopy_readback(
        CanonStringEncoding::Utf16,
        CanonStringEncoding::Utf16,
        2,                              // UTF-16: 2 bytes per code unit
        (&[0xE9, 0x00], 1),             // "é" — 1 code unit
        (&[0x48, 0x00, 0x69, 0x00], 2), // "Hi" — 2 code units
    );
    // re-pointed out of CALLER memory into the CALLEE realloc arena (>= 1024).
    assert!(
        recs[0].0 >= 1024 && recs[1].0 >= 1024,
        "same-encoding UTF-16 inner buffers must be re-pointed into callee memory"
    );
    assert_eq!(recs[0].1, 1, "\"é\" inner len preserved (1 code unit)");
    assert_eq!(
        recs[0].2,
        vec![0xE9, 0x00],
        "#272 inc5c-b: same-encoding UTF-16 deep-copy must hold the FULL code \
         units (é = [0xE9,0x00], not [0xE9,0x48]) — len*2, not len*1"
    );
    assert_eq!(recs[1].1, 2, "\"Hi\" inner len preserved (2 code units)");
    assert_eq!(recs[1].2, vec![0x48, 0x00, 0x69, 0x00]);
}

/// #272 inc 5c-b (SAME-ENCODING CompactUtf16, tag-SET inner, #281 completeness):
/// a nested `list<string>` PARAM where record 1 is a TAG-SET inner — "中" =
/// U+4E2D stored as UTF-16 [0x2D,0x4E], len = 1 | UTF16_TAG. Same-encoding ⇒ NOT
/// transcoded ⇒ verbatim deep-copy. Pre-fix the raw tagged `len` (a huge value)
/// inflates the in-bounds guard so the re-point is SKIPPED — the callee record
/// keeps the stale CALLER ptr (dangling). Post-fix the tag-aware byte count
/// (`(len & !TAG)*2 = 2` bytes, align 2) un-inflates the guard, the buffer is
/// re-pointed into callee memory, and the 2 UTF-16 bytes land correctly.
#[test]
fn inc5c_b_same_encoding_compact_utf16_nested_param_tagset_deep_copies() {
    let recs = nested_param_deepcopy_readback(
        CanonStringEncoding::CompactUtf16,
        CanonStringEncoding::CompactUtf16,
        2,                              // tag-set record reads 2 bytes per (UTF-16) code unit
        (&[0x2D, 0x4E], 1 | UTF16_TAG), // tag-SET UTF-16 "中"
        (&[0x2D, 0x4E], 1 | UTF16_TAG),
    );
    // The re-point MUST happen — the buffer moves into the callee realloc arena
    // (>= 1024), NOT left at the stale caller ptr P_INNER_*_OFF (100 / 140).
    assert!(
        recs[0].0 >= 1024,
        "#272 inc5c-b: tag-set CompactUtf16 inner must be re-pointed (not skipped \
         by the inflated tagged-len guard) — ptr {} should be in the callee arena",
        recs[0].0
    );
    assert!(recs[1].0 >= 1024, "second tag-set inner must also re-point");
    assert_eq!(
        recs[0].1,
        1 | UTF16_TAG,
        "tagged inner len preserved verbatim"
    );
    assert_eq!(
        recs[0].2,
        vec![0x2D, 0x4E],
        "#272 inc5c-b: tag-set CompactUtf16 deep-copy must hold the full UTF-16 \
         code unit [0x2D,0x4E]"
    );
    assert_eq!(recs[1].2, vec![0x2D, 0x4E]);
}

/// #272 inc 5c-b (SAME-ENCODING Utf8 → Utf8, UNCHANGED correct behavior): a
/// nested `list<string>` PARAM over `["é","Hi"]` in UTF-8. "é" = [0xC3,0xA9]
/// (2 bytes, len 2); "Hi" = [0x48,0x69] (2 bytes, len 2). Same-encoding UTF-8 ⇒
/// deep-copy with byte count `len*1` — the path the fix MUST leave untouched.
#[test]
fn inc5c_b_same_encoding_utf8_nested_param_deep_copies_verbatim() {
    let recs = nested_param_deepcopy_readback(
        CanonStringEncoding::Utf8,
        CanonStringEncoding::Utf8,
        1, // UTF-8: 1 byte per unit (len is a byte count)
        (&[0xC3, 0xA9], 2),
        (&[0x48, 0x69], 2),
    );
    assert!(
        recs[0].0 >= 1024 && recs[1].0 >= 1024,
        "same-encoding UTF-8 inner buffers must be re-pointed into callee memory"
    );
    assert_eq!(recs[0].1, 2, "\"é\" UTF-8 byte len preserved (2)");
    assert_eq!(
        recs[0].2,
        vec![0xC3, 0xA9],
        "#272 inc5c-b: same-encoding UTF-8 deep-copy is byte-for-byte (len*1) — \
         UNCHANGED by the fix"
    );
    assert_eq!(recs[1].1, 2);
    assert_eq!(recs[1].2, vec![0x48, 0x69]);
}

/// #272 inc 5c-b (nested `list<u8>` param, UNCHANGED verbatim deep-copy): the
/// `is_string == false` path keeps `len * sub_elem_size` and must be untouched
/// by the string-width fix. Inner buffers `[0xC3,0xA9]` (sum 365) and
/// `[0x01,0x80]` (sum 129) → byte-sum 493, copied verbatim.
#[test]
fn inc5c_b_nested_list_u8_param_deep_copy_unchanged() {
    let wasm = meld_core::adapter::build_nested_list_u8_param_deep_copied_test_module();
    let sum = nested_param_patch_and_sum(&wasm, &[0xC3, 0xA9], &[0x01, 0x80]);
    assert_eq!(
        sum, 493,
        "#272 inc5c-b: nested list<u8> param deep-copy (len*sub_elem_size) is \
         UNCHANGED by the same-encoding string-width fix"
    );
}
