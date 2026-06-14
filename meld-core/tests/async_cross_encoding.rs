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
    build_utf8_to_latin1_transcode_test_module, build_utf8_to_utf16_transcode_test_module,
    build_utf16_to_latin1_transcode_test_module, build_utf16_to_utf8_transcode_test_module,
};
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
