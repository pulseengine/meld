//! `component-provenance` custom section — issue #192 / scry DD-002.
//!
//! Maps every function in the fused Core Wasm module back to the
//! component + originating function index it came from, so downstream
//! consumers (notably `pulseengine/scry`'s sound abstract interpreter)
//! can project Component-Model invariants computed on the original
//! component sources onto fused-module locations.
//!
//! The data has been in-memory all along — [`crate::merger::MergedFunction::origin`]
//! is a `(component_idx, module_idx, function_idx)` triple built during
//! fusion. Prior to v0.14.0 it was discarded at emit time; this module
//! preserves it as a JSON-encoded custom section named
//! `component-provenance`.
//!
//! ## Boundary
//!
//! meld owns Core Wasm fusion correctness. scry owns Component-Model
//! semantics. The custom section is the typed contract between them.
//! This module deliberately does NOT carry:
//!
//! - Resource type names, handle shapes, capability-flow metadata
//! - WIT refinement predicates
//! - Adapter provenance (a future v2 ask)
//!
//! scry derives all of those from the original component sources
//! directly; meld only needs to provide the back-pointer.
//!
//! ## Self-referential hash
//!
//! Each provenance section carries `fused_module_sha256` to bind it to
//! a specific fused module. Because the section is itself part of the
//! module bytes, the hash is computed over the module WITHOUT the
//! provenance section (and without `wsc.transformation.attestation`).
//! Consumers verify by stripping both custom sections, hashing the
//! result, and comparing to `fused_module_sha256`. Same pattern
//! [`crate::attestation`] uses.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Custom-section name for the provenance payload. Wasm spec allows
/// arbitrary custom-section names; consumers identify by this string.
pub const SECTION_NAME: &str = "component-provenance";

/// Current section format version.
///
/// - **v1**: `{ fused_func_idx, component_id, originating_func_idx }`
///   per entry (issue #192).
/// - **v2** (DWARF Phase 2, issue #143): adds an optional
///   [`Entry::code_range`].
/// - **v3** (#313 / scry#63): the canonical **binary `SCPV`** wire
///   format (replacing the JSON encoding, which never decoded against
///   scry's binary `scry-provenance` reader — the boundary was dead).
///   Adds a fixed header carrying the **fusion premises**
///   ([`ComponentProvenance::bounded_memory`],
///   [`ComponentProvenance::closed_world`]) that tighten scry's
///   abstract-interpretation fixpoint. The byte layout is the
///   converged spec in scry#63; see [`ComponentProvenance::to_bytes`].
///   meld is the producer; scry's `scry-provenance` is the consumer
///   and owns the format (DD-002).
///
/// Consumers MUST check the `SCPV` magic + `version` before decoding.
pub const VERSION: u32 = 3;

/// Magic prefixing the binary `SCPV` payload — lets a consumer reject a
/// non-provenance / wrong-format section before decoding (scry#63).
pub const MAGIC: &[u8; 4] = b"SCPV";

/// Byte span of a function body in the fused module's code section.
///
/// Offsets are **relative to the start of the code section's
/// contents** (the byte immediately after the code section's
/// size/count header — `wasmparser::Payload::CodeSectionStart.range.start`),
/// matching the WebAssembly-DWARF "code section relative" address
/// convention. `start` is the first byte of the function body
/// (its locals-declaration vector), `end` is one past its last
/// instruction byte — i.e. the half-open span `[start, end)` that
/// `wasmparser::FunctionBody::range()` reports, rebased to the
/// section content start.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodeRange {
    pub start: u32,
    pub end: u32,
}

/// One entry per defined function in the fused Core Wasm module.
///
/// Imported functions are *not* covered — their definition lives
/// outside meld's authorship, and there is no origin to attribute.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Entry {
    /// Absolute wasm function index in the fused output (including
    /// the leading imported-function slots; see
    /// [`crate::merger::MergedModule::defined_func`] for the
    /// imports-vs-defined arithmetic).
    pub fused_func_idx: u32,
    /// Stable component identifier — meld uses `comp.name` from the
    /// component's binary, falling back to a positional default of
    /// `component-<idx>` for nameless components.
    pub component_id: String,
    /// Function index within the originating component's flattened
    /// view (the `function_idx` field of
    /// `MergedFunction.origin: (comp_idx, mod_idx, func_idx)`).
    pub originating_func_idx: u32,
    /// v2: byte span of this function's body in the fused code
    /// section (see [`CodeRange`]). `None` when the code-offset map
    /// could not be built (e.g. the output had no code section).
    /// Serialized only when present so v1-shaped entries round-trip
    /// unchanged.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub code_range: Option<CodeRange>,
}

/// Decoded provenance section. Constructed by [`build`] at fusion
/// time; consumers should round-trip from the section bytes via
/// [`from_bytes`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComponentProvenance {
    pub version: u32,
    /// **Fusion premise (#313):** the fused core uses no `memory.grow`,
    /// so its linear memory is fixed-size. Lets scry assume a bounded
    /// memory and drop grow-reachability widening. Sound, varies per
    /// input (computed by [`crate::memory_probe::module_uses_memory_grow`]).
    pub bounded_memory: bool,
    /// **Fusion premise (#313):** every cross-component import edge has
    /// been internalised — the fused module has no residual import in a
    /// non-host namespace. Lets scry tighten `reachable_from_exports`
    /// and assume no inter-component call escapes through an import.
    /// Conservative: an unrecognised import namespace yields `false`.
    pub closed_world: bool,
    pub fused_module_sha256: String,
    pub entries: Vec<Entry>,
}

impl ComponentProvenance {
    /// Encode the canonical **binary `SCPV` v3** section payload
    /// (scry#63). Little-endian; entries are length-prefixed so a
    /// `no_std`/no-alloc consumer can bound-check without allocating.
    ///
    /// ```text
    /// "SCPV" | u8 ver=3 | u8 bounded_memory | u8 closed_world
    ///        | sha256[32 raw] | u32 count
    ///        | { fused_idx:u32, id_len:u32, id:[u8;len], orig_idx:u32,
    ///            has_code_range:u8, [start:u32, end:u32] } * count
    /// ```
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(43 + self.entries.len() * 24);
        b.extend_from_slice(MAGIC);
        b.push(VERSION as u8);
        b.push(self.bounded_memory as u8);
        b.push(self.closed_world as u8);
        // sha256 hex string -> 32 raw bytes (zero-padded if malformed,
        // which build() never produces).
        let mut sha32 = [0u8; 32];
        if let Ok(raw) = hex::decode(&self.fused_module_sha256) {
            let n = raw.len().min(32);
            sha32[..n].copy_from_slice(&raw[..n]);
        }
        b.extend_from_slice(&sha32);
        b.extend_from_slice(&(self.entries.len() as u32).to_le_bytes());
        for e in &self.entries {
            b.extend_from_slice(&e.fused_func_idx.to_le_bytes());
            let id = e.component_id.as_bytes();
            b.extend_from_slice(&(id.len() as u32).to_le_bytes());
            b.extend_from_slice(id);
            b.extend_from_slice(&e.originating_func_idx.to_le_bytes());
            match e.code_range {
                Some(cr) => {
                    b.push(1);
                    b.extend_from_slice(&cr.start.to_le_bytes());
                    b.extend_from_slice(&cr.end.to_le_bytes());
                }
                None => b.push(0),
            }
        }
        b
    }

    /// Inverse of [`to_bytes`] — decode a binary `SCPV` v3 payload.
    /// `Err` on bad magic, unsupported version, truncation, or invalid
    /// UTF-8 in a `component_id`.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut p = 0usize;
        let take = |b: &[u8], p: &mut usize, n: usize| -> Result<Vec<u8>, String> {
            if *p + n > b.len() {
                return Err(format!("SCPV truncated: need {n} at {p}, have {}", b.len()));
            }
            let s = b[*p..*p + n].to_vec();
            *p += n;
            Ok(s)
        };
        let u32le = |b: &[u8], p: &mut usize| -> Result<u32, String> {
            let s = take(b, p, 4)?;
            Ok(u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
        };
        if take(bytes, &mut p, 4)? != MAGIC {
            return Err("SCPV bad magic".into());
        }
        let ver = take(bytes, &mut p, 1)?[0] as u32;
        if ver != VERSION {
            return Err(format!(
                "SCPV unsupported version {ver} (expected {VERSION})"
            ));
        }
        let bounded_memory = take(bytes, &mut p, 1)?[0] != 0;
        let closed_world = take(bytes, &mut p, 1)?[0] != 0;
        let fused_module_sha256 = hex::encode(take(bytes, &mut p, 32)?);
        let count = u32le(bytes, &mut p)? as usize;
        // Bound the pre-allocation by the bytes actually remaining: the
        // count is an untrusted wire u32, so a crafted section with
        // count = u32::MAX must NOT trigger a ~190 GiB `with_capacity`
        // and abort the process (DoS on memory-constrained hosts).
        // Smallest possible entry is 13 bytes (fused_idx 4 + id_len 4 +
        // id 0 + orig_idx 4 + has_code_range 1); the loop's bounded
        // `take` still errors on genuine truncation.
        const MIN_ENTRY_BYTES: usize = 13;
        let max_possible = bytes.len().saturating_sub(p) / MIN_ENTRY_BYTES;
        let mut entries = Vec::with_capacity(count.min(max_possible));
        for _ in 0..count {
            let fused_func_idx = u32le(bytes, &mut p)?;
            let id_len = u32le(bytes, &mut p)? as usize;
            let component_id =
                String::from_utf8(take(bytes, &mut p, id_len)?).map_err(|_| "SCPV bad utf8")?;
            let originating_func_idx = u32le(bytes, &mut p)?;
            let code_range = if take(bytes, &mut p, 1)?[0] != 0 {
                Some(CodeRange {
                    start: u32le(bytes, &mut p)?,
                    end: u32le(bytes, &mut p)?,
                })
            } else {
                None
            };
            entries.push(Entry {
                fused_func_idx,
                component_id,
                originating_func_idx,
                code_range,
            });
        }
        Ok(ComponentProvenance {
            version: ver,
            bounded_memory,
            closed_world,
            fused_module_sha256,
            entries,
        })
    }
}

/// Host import namespaces — residual imports in these are the external
/// boundary, not unresolved inter-component edges, so they don't break
/// `closed_world`. Anything else is treated conservatively as a
/// surviving cross-component import (`closed_world = false`).
fn is_host_import_namespace(module: &str) -> bool {
    module.starts_with("wasi")
        || module == "env"
        || module.starts_with("pulseengine:")
        || module.starts_with("__")
}

/// `closed_world` premise: every import in `module_bytes` is in a host
/// namespace (no surviving inter-component import edge). A module with
/// no imports is trivially closed. Conservative on unrecognised
/// namespaces (returns `false`) so the premise is never over-asserted.
pub fn fused_is_closed_world(module_bytes: &[u8]) -> bool {
    for payload in wasmparser::Parser::new(0).parse_all(module_bytes) {
        if let Ok(wasmparser::Payload::ImportSection(reader)) = payload {
            for imp in reader.into_imports() {
                match imp {
                    Ok(import) if !is_host_import_namespace(import.module) => return false,
                    Ok(_) => {}
                    Err(_) => return false,
                }
            }
        }
    }
    true
}

/// Compute the SHA-256 hex digest of the given bytes. Lower-case hex,
/// no leading `0x`, 64 chars — same format as
/// [`crate::attestation::build_wsc_attestation`].
pub fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let out = hasher.finalize();
    hex::encode(out)
}

/// Extract the code-section-relative byte span of every defined
/// function body in `module_bytes`, in code-section order.
///
/// Returns `[(start, end); n_defined_functions]` with offsets
/// rebased to the code section content start (see [`CodeRange`]).
/// Empty if the module has no code section. The i-th entry
/// corresponds to the i-th defined function in code-section order:
/// meld writes `merged.functions` first, then adapter trampolines
/// (`meld-core/src/lib.rs` `encode_output`), so index `i` aligns
/// with `merged.functions[i]` for `i < merged.functions.len()`.
pub fn code_section_function_ranges(module_bytes: &[u8]) -> Vec<CodeRange> {
    let mut ranges = Vec::new();
    let mut content_start: Option<usize> = None;
    let parser = wasmparser::Parser::new(0);
    for payload in parser.parse_all(module_bytes) {
        match payload {
            Ok(wasmparser::Payload::CodeSectionStart { range, .. }) => {
                content_start = Some(range.start);
            }
            Ok(wasmparser::Payload::CodeSectionEntry(body)) => {
                let base = content_start.unwrap_or(0);
                let r = body.range();
                ranges.push(CodeRange {
                    start: (r.start - base) as u32,
                    end: (r.end - base) as u32,
                });
            }
            Ok(_) => {}
            Err(_) => break,
        }
    }
    ranges
}

/// Build a [`ComponentProvenance`] from the merged module + the
/// component slice. The hash binds the section to the fused module
/// without the section (call this with bytes that don't yet include
/// the `component-provenance` or `wsc.transformation.attestation`
/// custom sections — see the module-level note).
///
/// v2 (#143): each entry's [`Entry::code_range`] is populated from
/// the code section of `fused_bytes_without_extras` by index-order
/// alignment with `merged.functions`. If the parsed code section has
/// fewer bodies than `merged.functions` (should not happen for a
/// well-formed output), the missing entries get `code_range: None`
/// rather than a wrong span.
pub fn build(
    merged: &crate::merger::MergedModule,
    components: &[crate::parser::ParsedComponent],
    fused_bytes_without_extras: &[u8],
) -> ComponentProvenance {
    let import_count = merged.import_counts.func;
    let ranges = code_section_function_ranges(fused_bytes_without_extras);
    let entries: Vec<Entry> = merged
        .functions
        .iter()
        .enumerate()
        .map(|(defined_idx, mf)| {
            let (comp_idx, _mod_idx, func_idx) = mf.origin;
            let component_id = components
                .get(comp_idx)
                .and_then(|c| c.name.clone())
                .unwrap_or_else(|| format!("component-{comp_idx}"));
            Entry {
                fused_func_idx: import_count + defined_idx as u32,
                component_id,
                originating_func_idx: func_idx,
                code_range: ranges.get(defined_idx).copied(),
            }
        })
        .collect();

    ComponentProvenance {
        version: VERSION,
        // Fusion premises (#313): both sound, computed from the fused
        // bytes meld just produced. `bounded_memory` varies per input;
        // `closed_world` is conservative (false on any non-host import).
        bounded_memory: !crate::memory_probe::module_uses_memory_grow(fused_bytes_without_extras),
        closed_world: fused_is_closed_world(fused_bytes_without_extras),
        fused_module_sha256: sha256_hex(fused_bytes_without_extras),
        entries,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample(bounded: bool, closed: bool) -> ComponentProvenance {
        ComponentProvenance {
            version: VERSION,
            bounded_memory: bounded,
            closed_world: closed,
            fused_module_sha256: "deadbeef".repeat(8),
            entries: vec![
                Entry {
                    fused_func_idx: 0,
                    component_id: "auth".into(),
                    originating_func_idx: 3,
                    code_range: Some(CodeRange { start: 0, end: 42 }),
                },
                Entry {
                    fused_func_idx: 1,
                    component_id: "db".into(),
                    originating_func_idx: 7,
                    code_range: None,
                },
            ],
        }
    }

    #[test]
    fn scpv_v3_round_trip_preserves_payload() {
        for (b, c) in [(true, true), (true, false), (false, true), (false, false)] {
            let original = sample(b, c);
            let decoded = ComponentProvenance::from_bytes(&original.to_bytes()).expect("decode");
            assert_eq!(original, decoded, "premises ({b},{c}) must round-trip");
        }
    }

    #[test]
    fn scpv_v3_header_layout_pinned() {
        // Pin the converged scry#63 byte layout so meld can't drift from
        // scry's decoder: magic, version, the two premise bytes.
        let bytes = sample(true, false).to_bytes();
        assert_eq!(&bytes[0..4], MAGIC, "magic 'SCPV'");
        assert_eq!(bytes[4], 3, "version byte = 3");
        assert_eq!(bytes[5], 1, "bounded_memory byte");
        assert_eq!(bytes[6], 0, "closed_world byte");
        // 32-byte sha then u32 LE count (2 entries).
        assert_eq!(&bytes[39..43], &2u32.to_le_bytes(), "entry count");
    }

    #[test]
    fn from_bytes_rejects_bad_magic_version_and_truncation() {
        assert!(ComponentProvenance::from_bytes(b"").is_err());
        assert!(
            ComponentProvenance::from_bytes(b"JSON{...}").is_err(),
            "bad magic"
        );
        let mut wrong_ver = sample(true, true).to_bytes();
        wrong_ver[4] = 2; // older/unknown version
        assert!(
            ComponentProvenance::from_bytes(&wrong_ver).is_err(),
            "version"
        );
        let full = sample(true, true).to_bytes();
        assert!(
            ComponentProvenance::from_bytes(&full[..full.len() - 3]).is_err(),
            "truncated entry"
        );
    }

    #[test]
    fn closed_world_host_namespace_classification() {
        // Host namespaces don't break closed_world; an unrecognised
        // (e.g. component-instance) namespace does, conservatively.
        let host = wat::parse_str(
            r#"(module (import "wasi_snapshot_preview1" "fd_write"
                (func (param i32 i32 i32 i32) (result i32))))"#,
        )
        .unwrap();
        assert!(fused_is_closed_world(&host), "wasi import is host → closed");
        let no_imports = wat::parse_str(r#"(module (func nop))"#).unwrap();
        assert!(
            fused_is_closed_world(&no_imports),
            "no imports → trivially closed"
        );
        let cross = wat::parse_str(r#"(module (import "auth-component" "login" (func)))"#).unwrap();
        assert!(
            !fused_is_closed_world(&cross),
            "non-host import → not closed"
        );
    }

    #[test]
    fn from_bytes_huge_count_does_not_overallocate() {
        // Mythos finding (#314): a crafted SCPV v3 section with
        // count = u32::MAX must NOT pre-allocate ~190 GiB and abort the
        // process — `from_bytes` bounds with_capacity by the bytes
        // remaining, then errors cleanly on the truncated first entry.
        let mut buf = Vec::new();
        buf.extend_from_slice(MAGIC);
        buf.push(VERSION as u8);
        buf.push(0); // bounded_memory
        buf.push(0); // closed_world
        buf.extend_from_slice(&[0u8; 32]); // sha256
        buf.extend_from_slice(&u32::MAX.to_le_bytes()); // count = 4.3e9
        // No entry bytes follow.
        let r = ComponentProvenance::from_bytes(&buf);
        assert!(
            r.is_err(),
            "huge count with no entry bytes must Err (truncation), not OOM"
        );
    }

    #[test]
    fn sha256_hex_is_lowercase_64_chars() {
        let h = sha256_hex(b"hello world");
        assert_eq!(h.len(), 64);
        assert!(
            h.chars()
                .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
        );
        // Pin the canonical value for "hello world" so the hash impl
        // can't silently swap algorithms.
        assert_eq!(
            h,
            "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"
        );
    }

    #[test]
    fn code_section_ranges_are_ordered_nonoverlapping_one_per_function() {
        // Two functions of clearly different body sizes so the spans
        // are distinguishable. wat → wasm gives a real code section.
        let wasm = wat::parse_str(
            r#"(module
                (func (result i32) i32.const 1)
                (func (param i32 i32) (result i32)
                    local.get 0 local.get 1 i32.add))"#,
        )
        .expect("wat parse");

        let ranges = code_section_function_ranges(&wasm);
        assert_eq!(ranges.len(), 2, "expected one range per defined function");

        // Each span is non-empty and ordered, and consecutive spans
        // do not overlap (code-section bodies are laid out in order).
        assert!(ranges[0].start < ranges[0].end);
        assert!(ranges[1].start < ranges[1].end);
        assert!(
            ranges[0].end <= ranges[1].start,
            "function bodies must not overlap: {ranges:?}"
        );
        // The first body does NOT begin at rebased offset 0: the base
        // is `CodeSectionStart.range.start`, which points at the
        // section's count LEB. The first body content (locals + code,
        // per wasmparser's `FunctionBody::range()`) therefore starts a
        // few bytes in — past the count LEB and the body's own size
        // prefix. Assert it's small but non-zero rather than pinning
        // the exact constant (the precise base is cross-checked in
        // `code_section_ranges_rebased_to_content_start`).
        assert!(
            ranges[0].start > 0 && ranges[0].start < 16,
            "first body should start just past the count + size prefix; got {}",
            ranges[0].start
        );
    }

    #[test]
    fn code_section_ranges_empty_when_no_code_section() {
        // A module with only a type section (no functions) yields no
        // ranges — the `None` path for Entry::code_range.
        let wasm = wat::parse_str(r#"(module (type (func)))"#).expect("wat parse");
        let ranges = code_section_function_ranges(&wasm);
        assert!(
            ranges.is_empty(),
            "no code section ⇒ no ranges; got {ranges:?}"
        );
    }

    #[test]
    fn code_section_ranges_rebased_to_content_start() {
        // Cross-check the rebasing: independently re-parse the module,
        // capture the code-section content start and each body's
        // absolute range, and confirm code_section_function_ranges
        // reports exactly (absolute - content_start).
        let wasm = wat::parse_str(r#"(module (func nop) (func (result i32) i32.const 7))"#)
            .expect("wat parse");

        let mut content_start = None;
        let mut expected = Vec::new();
        for payload in wasmparser::Parser::new(0).parse_all(&wasm) {
            match payload.expect("parse") {
                wasmparser::Payload::CodeSectionStart { range, .. } => {
                    content_start = Some(range.start);
                }
                wasmparser::Payload::CodeSectionEntry(body) => {
                    let base = content_start.expect("code section started");
                    let r = body.range();
                    expected.push(CodeRange {
                        start: (r.start - base) as u32,
                        end: (r.end - base) as u32,
                    });
                }
                _ => {}
            }
        }

        assert_eq!(code_section_function_ranges(&wasm), expected);
    }
}
