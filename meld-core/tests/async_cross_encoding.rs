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

use meld_core::adapter::build_utf8_to_utf16_transcode_test_module;
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
