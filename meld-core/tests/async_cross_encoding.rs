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
    build_utf8_to_utf16_transcode_test_module, build_utf16_to_utf8_transcode_test_module,
};
use wasmtime::{Config, Engine, Instance, Module as RuntimeModule, Store};

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
