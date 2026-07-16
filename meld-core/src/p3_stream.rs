//! Cross-component `stream<T>` pairing detection — ADR-3, issue #141.
//!
//! When meld fuses two components that share a `stream<T>` end-to-end
//! (one holds the writable end, the other the readable end), both sides
//! today still lower their stream operations to host imports under
//! `pulseengine:async` (ADR-1). Every chunk crosses the host boundary
//! twice even though both ends now live in the merged module.
//!
//! This module is the **detection foundation** for the in-module stream
//! adapter (ADR-3, Path N). It builds a [`StreamPairGraph`]: the
//! merge-time inventory of which fused components form producer →
//! consumer stream pairings. The adapter *emitter* — the ring-buffer
//! (same-memory) and copy-chain (cross-memory) wasm codegen — is a
//! runtime-verified follow-up that consumes this graph; it is not in
//! this module.
//!
//! `stream<T>` data flow is inherently runtime — `stream.new` mints the
//! handle pair at runtime. What is *static* is the pairing: the
//! resolver knows component A's `stream<T>`-bearing export resolved to
//! component B's import. The detection here keys off that static fact
//! plus each component's canonical stream operations.
//!
//! ## Precision boundary
//!
//! A [`StreamPair`] is a **candidate** pairing, not a proof that two
//! endpoints carry the same runtime handle (unknowable at build time).
//! It is recorded only when two fusion-connected components have
//! complementary roles — one writes, one reads — on a stream of the
//! **same element type**. Pairing only on matching element type is the
//! line between an honest candidate and a hallucinated one: a
//! `stream<u8>` and a `stream<s32>` between the same two components are
//! two different streams. See ADR-3.

use crate::parser::{
    CanonicalEntry, ComponentFuncDef, ComponentTypeKind, ComponentValType, ParsedComponent,
    PrimitiveValType,
};
use std::collections::HashMap;
use wasmparser::ComponentExternalKind;

/// Depth bound for [`canonical_structural_key`] recursion.
///
/// Component-local type references (`Type(N)`) can in principle form
/// cycles or pathologically deep nests in adversarial input. The
/// structural canonicaliser returns `None` (→ non-pairable, host-routed)
/// once this bound is exceeded, so a cyclic or unbounded type can never
/// drive the canonicaliser into non-termination. 64 levels is far past
/// any genuine aggregate nesting a real component declares.
const CANON_MAX_DEPTH: usize = 64;

/// The element type carried by a `stream<T>`, parsed from the
/// component-type descriptor the parser records.
///
/// The parser stores stream types as
/// [`ComponentTypeKind::P3Async`] descriptor strings such as
/// `"stream<U8>"` or bare `"stream"`. Element types are compared by
/// descriptor string, never by component-local type index — index 5 in
/// component A and index 5 in component B are unrelated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StreamElement {
    /// `stream<T>` with a concrete element descriptor (the raw text
    /// between the angle brackets, e.g. `"U8"`).
    Typed(String),
    /// Bare `stream` with no element type.
    Untyped,
}

impl StreamElement {
    /// Parse from a [`ComponentTypeKind::P3Async`] descriptor.
    ///
    /// Returns `None` if the descriptor is not a stream (e.g. a
    /// `future<...>` or `map<...>` descriptor). `strip_suffix` removes
    /// exactly one `>`, so nested descriptors like `stream<list<U8>>`
    /// parse to the element `list<U8>`.
    pub fn from_descriptor(desc: &str) -> Option<Self> {
        let desc = desc.trim();
        if desc == "stream" {
            return Some(StreamElement::Untyped);
        }
        let inner = desc.strip_prefix("stream<")?.strip_suffix('>')?;
        Some(StreamElement::Typed(inner.trim().to_string()))
    }

    /// Whether this element type is safe to PAIR across components.
    ///
    /// A bare `Type(N)` descriptor is a component-LOCAL type index —
    /// component A's `Type(5)` and component B's `Type(5)` are unrelated —
    /// so it is not a valid cross-component key (LS-R-16). Primitive
    /// descriptors (scalar names such as `u8`) and the untyped stream are
    /// globally stable and pairable; a local-index descriptor is not
    /// (pairing on it risks an over-match that drives the bridge emitter to
    /// wire incompatible streams).
    ///
    /// As of #264, an aggregate element that DID resolve structurally is
    /// recorded as its structural key (e.g. `record{f0:u8,f1:list<s32>}`),
    /// which contains no `"Type("` and so is pairable — and pairs only with
    /// an identical key. An element that could NOT be canonicalised (a
    /// resource handle, a depth-bound or cycle hit, or an unresolvable
    /// index) keeps its raw `Type(N)` descriptor and stays host-routed.
    fn is_cross_component_pairable(&self) -> bool {
        match self {
            StreamElement::Untyped => true,
            StreamElement::Typed(s) => !s.contains("Type("),
        }
    }
}

/// A component's role on a particular stream element type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamRole {
    /// Declares [`CanonicalEntry::StreamWrite`] — writes the stream.
    Producer,
    /// Declares [`CanonicalEntry::StreamRead`] — reads the stream.
    Consumer,
}

/// Whether a fused pair's two endpoints share a linear memory.
///
/// Mirrors the synchronous-data multi-memory / shared-memory split.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamMemoryMode {
    /// `MemoryStrategy::SharedMemory` — ring-buffer adapter, zero-copy.
    SameMemory,
    /// `MemoryStrategy::MultiMemory` — `stream_read` → copy → `stream_write`.
    CrossMemory,
}

/// One endpoint of a detected cross-component stream pairing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StreamEndpoint {
    /// Index of the component into the fused `&[ParsedComponent]` slice.
    pub component: usize,
    /// Producer or consumer.
    pub role: StreamRole,
}

/// A detected cross-component stream pairing: one producer, one
/// consumer, fusion-connected, carrying the same element type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StreamPair {
    /// The writing endpoint.
    pub producer: StreamEndpoint,
    /// The reading endpoint.
    pub consumer: StreamEndpoint,
    /// Element type both endpoints carry (equal by construction — the
    /// builder only pairs matching element types).
    pub element: StreamElement,
    /// Whether the two endpoints share a memory.
    pub mode: StreamMemoryMode,
}

/// The merge-time inventory of cross-component stream pairings.
///
/// Attached to `DependencyGraph` next to the resource graph. The
/// adapter emitter (ADR-3 follow-up) and issue #142's static validation
/// both consume it.
#[derive(Debug, Clone, Default)]
pub struct StreamPairGraph {
    /// All detected candidate pairings.
    pub pairs: Vec<StreamPair>,
}

impl StreamPairGraph {
    /// `true` if no cross-component stream pairings were detected.
    pub fn is_empty(&self) -> bool {
        self.pairs.is_empty()
    }
}

/// Extract a component's `(element type, role)` pairs from its
/// canonical stream operations.
///
/// `CanonicalEntry::StreamWrite` ⇒ the component is a producer for that
/// stream's element type; `StreamRead` ⇒ a consumer. A component can be
/// both (a pipe). `StreamNew` / `StreamCancel*` / `StreamDrop*` carry no
/// producer/consumer signal and are ignored. Duplicates are collapsed.
pub fn component_stream_roles(comp: &ParsedComponent) -> Vec<(StreamElement, StreamRole)> {
    let mut out: Vec<(StreamElement, StreamRole)> = Vec::new();
    for entry in &comp.canonical_functions {
        let (ty, role) = match entry {
            CanonicalEntry::StreamWrite { ty, .. } => (*ty, StreamRole::Producer),
            CanonicalEntry::StreamRead { ty, .. } => (*ty, StreamRole::Consumer),
            _ => continue,
        };
        let Some(element) = stream_element_of_type(comp, ty) else {
            continue;
        };
        let key = (element, role);
        if !out.contains(&key) {
            out.push(key);
        }
    }
    out
}

/// Resolve a component-local type index to its stream element type, or
/// `None` if the index does not name a `stream<T>` type.
///
/// The element is canonicalised in the component's context (see
/// [`canonicalize_stream_element`]) so that an aggregate element recorded
/// as the component-LOCAL `Type(N)` descriptor becomes a cross-component
/// structural key, pairable iff structurally identical on the other side.
fn stream_element_of_type(comp: &ParsedComponent, ty: u32) -> Option<StreamElement> {
    match &comp.types.get(ty as usize)?.kind {
        ComponentTypeKind::P3Async(desc) => Some(canonicalize_stream_element(
            comp,
            StreamElement::from_descriptor(desc)?,
        )),
        _ => None,
    }
}

/// Canonicalise a parsed [`StreamElement`] in `comp`'s type context.
///
/// The parser records a non-primitive stream element as the Debug form of
/// a `wasmparser::ComponentValType`, which for an aggregate is the
/// component-LOCAL `Type(N)` index — e.g. `stream<record{..}>` parses to
/// `Typed("Type(3)")`. That local index is not a valid cross-component
/// key (LS-R-16): index 3 in component A and index 3 in component B are
/// unrelated.
///
/// This resolves `Type(N)` through `comp`'s type table to a
/// **cross-component-stable structural descriptor** via
/// [`canonical_structural_key`]. On success the element becomes
/// `Typed(structural_key)` — no longer containing `"Type("`, so it is
/// pairable, and pairs ONLY with an identical structural key. On failure
/// (resource handle at any depth, depth bound exceeded, or unresolvable
/// index) the original `Type(N)` descriptor is kept, which stays
/// non-pairable / host-routed — exactly the conservative LS-R-16
/// behaviour. Primitive and untyped elements pass through unchanged.
fn canonicalize_stream_element(comp: &ParsedComponent, element: StreamElement) -> StreamElement {
    let StreamElement::Typed(desc) = &element else {
        return element;
    };
    let Some(idx) = parse_type_index(desc) else {
        // Not a bare local-index descriptor (primitive scalar names, or
        // an already-structural nested form) — leave unchanged.
        return element;
    };
    match canonical_structural_key(comp, &ComponentValType::Type(idx), 0) {
        Some(key) => StreamElement::Typed(key),
        None => element,
    }
}

/// Render a component value type to a cross-component-stable structural
/// descriptor string, resolving component-local `Type(N)` references
/// through `comp`'s type table.
///
/// The key is **injective enough that structurally-different types
/// produce different strings**: field names AND order, element types,
/// arities, tuple/record/variant/flags membership, and discriminant case
/// names all contribute. This injectivity is the load-bearing safety
/// property — a key collision would re-introduce the exact over-match
/// LS-R-16 prevents, manufacturing a false pair that wires incompatible
/// streams.
///
/// Returns `None` (caller keeps the type non-pairable) when:
/// - the type contains a resource handle (`own<R>` / `borrow<R>`) at any
///   nesting depth. Cross-component resource identity overlaps the
///   unresolved #256 definer-attribution problem, so resource-element
///   streams stay host-routed (conservative, per the issue);
/// - `depth` exceeds [`CANON_MAX_DEPTH`] (cycle / unbounded-nest guard);
/// - a `Type(N)` reference does not resolve to a defined type.
///
/// Example: a `record { count: u8, data: list<s32> }` element renders to
/// `record{count:u8,data:list<s32>}`. A `tuple<u8, u8>` renders to
/// `tuple<u8,u8>`; an `option<u32>` to `option<u32>`.
fn canonical_structural_key(
    comp: &ParsedComponent,
    ty: &ComponentValType,
    depth: usize,
) -> Option<String> {
    if depth > CANON_MAX_DEPTH {
        return None;
    }
    let child = depth + 1;
    match ty {
        ComponentValType::Primitive(p) => Some(primitive_name(*p).to_string()),
        ComponentValType::String => Some("string".to_string()),
        ComponentValType::List(inner) => Some(format!(
            "list<{}>",
            canonical_structural_key(comp, inner, child)?
        )),
        ComponentValType::FixedSizeList(inner, len) => Some(format!(
            "fixed-list<{},{len}>",
            canonical_structural_key(comp, inner, child)?
        )),
        ComponentValType::Record(fields) => {
            let mut parts = Vec::with_capacity(fields.len());
            for (name, vt) in fields {
                parts.push(format!(
                    "{name}:{}",
                    canonical_structural_key(comp, vt, child)?
                ));
            }
            Some(format!("record{{{}}}", parts.join(",")))
        }
        ComponentValType::Tuple(items) => {
            let mut parts = Vec::with_capacity(items.len());
            for vt in items {
                parts.push(canonical_structural_key(comp, vt, child)?);
            }
            Some(format!("tuple<{}>", parts.join(",")))
        }
        ComponentValType::Option(inner) => Some(format!(
            "option<{}>",
            canonical_structural_key(comp, inner, child)?
        )),
        ComponentValType::Result { ok, err } => {
            let ok_s = match ok {
                Some(vt) => canonical_structural_key(comp, vt, child)?,
                None => "_".to_string(),
            };
            let err_s = match err {
                Some(vt) => canonical_structural_key(comp, vt, child)?,
                None => "_".to_string(),
            };
            Some(format!("result<{ok_s},{err_s}>"))
        }
        ComponentValType::Variant(cases) => {
            let mut parts = Vec::with_capacity(cases.len());
            for (name, opt) in cases {
                match opt {
                    Some(vt) => parts.push(format!(
                        "{name}({})",
                        canonical_structural_key(comp, vt, child)?
                    )),
                    None => parts.push(name.clone()),
                }
            }
            Some(format!("variant{{{}}}", parts.join(",")))
        }
        ComponentValType::Flags(names) => Some(format!("flags{{{}}}", names.join(","))),
        // Conservative on resources (#256): a handle element has no sound
        // cross-component identity yet → None keeps it host-routed.
        ComponentValType::Own(_) | ComponentValType::Borrow(_) => None,
        ComponentValType::Type(idx) => {
            let ct = comp.get_type_definition(*idx)?;
            match &ct.kind {
                ComponentTypeKind::Defined(inner) => canonical_structural_key(comp, inner, child),
                // A `Type(N)` that resolves to anything other than a
                // defined value type (resource declaration, function,
                // instance, nested async) has no structural value key —
                // stay conservative.
                _ => None,
            }
        }
    }
}

/// Stable scalar name for a primitive value type — the canonical-ABI
/// spelling, independent of any component-local representation.
fn primitive_name(p: PrimitiveValType) -> &'static str {
    match p {
        PrimitiveValType::Bool => "bool",
        PrimitiveValType::S8 => "s8",
        PrimitiveValType::U8 => "u8",
        PrimitiveValType::S16 => "s16",
        PrimitiveValType::U16 => "u16",
        PrimitiveValType::S32 => "s32",
        PrimitiveValType::U32 => "u32",
        PrimitiveValType::S64 => "s64",
        PrimitiveValType::U64 => "u64",
        PrimitiveValType::F32 => "f32",
        PrimitiveValType::F64 => "f64",
        PrimitiveValType::Char => "char",
    }
}

/// Derive the unordered set of fusion-connected component pairs from the
/// resolver's `resolved_imports` map.
///
/// Two components are fusion-connected if any resolved import links
/// them. Self-links (`importer == exporter`) are dropped; each unordered
/// pair appears once.
pub fn fusion_connections(
    resolved_imports: &HashMap<(usize, String), (usize, String)>,
) -> Vec<(usize, usize)> {
    let mut connected: Vec<(usize, usize)> = Vec::new();
    for ((importer, _), (exporter, _)) in resolved_imports {
        if importer == exporter {
            continue;
        }
        let pair = if importer < exporter {
            (*importer, *exporter)
        } else {
            (*exporter, *importer)
        };
        if !connected.contains(&pair) {
            connected.push(pair);
        }
    }
    connected.sort_unstable();
    connected
}

/// Pure pairing logic — the unit the ADR-3 gating fixtures pin.
///
/// `roles[c]` is component `c`'s `(element, role)` list (from
/// [`component_stream_roles`]). `connections` is the unordered
/// fusion-connected pairs (from [`fusion_connections`]). A
/// [`StreamPair`] is emitted for every connected `(producer, consumer)`
/// component pair that shares a stream element type — in both
/// directions, since either component of a connected pair may be the
/// producer.
pub fn pair_streams(
    roles: &[Vec<(StreamElement, StreamRole)>],
    connections: &[(usize, usize)],
    mode: StreamMemoryMode,
) -> Vec<StreamPair> {
    let mut pairs: Vec<StreamPair> = Vec::new();
    for &(a, b) in connections {
        // Either endpoint of the connected pair may hold the writable
        // end, so try both directions.
        for &(producer_c, consumer_c) in &[(a, b), (b, a)] {
            let (Some(producer_roles), Some(consumer_roles)) =
                (roles.get(producer_c), roles.get(consumer_c))
            else {
                continue;
            };
            for (p_elem, p_role) in producer_roles {
                if *p_role != StreamRole::Producer {
                    continue;
                }
                for (c_elem, c_role) in consumer_roles {
                    if *c_role != StreamRole::Consumer {
                        continue;
                    }
                    // Honest candidate only when element types match —
                    // see the ADR-3 precision boundary.
                    if p_elem != c_elem {
                        continue;
                    }
                    // LS-R-16 / #264: a non-primitive stream element type
                    // is recorded as `Type(N)` where N is a COMPONENT-LOCAL
                    // type index, so matching the raw index across
                    // components is unsound — two DIFFERENT element types
                    // that collide on the same local index N would
                    // string-match and manufacture a false pair that drives
                    // the bridge emitter to wire incompatible streams
                    // (H-3.1 type confusion), and the same real type at
                    // different indices would be missed. The element types
                    // here have already been run through
                    // `canonicalize_stream_element`: a resolvable aggregate
                    // now carries its structural key (pairable, pairs only
                    // with an identical structure), while a resource handle
                    // or an unresolvable / too-deep type keeps its raw
                    // `Type(N)` and is declined here — host-routed, which is
                    // safe. Primitives carry a stable scalar name.
                    if !p_elem.is_cross_component_pairable() {
                        continue;
                    }
                    let candidate = StreamPair {
                        producer: StreamEndpoint {
                            component: producer_c,
                            role: StreamRole::Producer,
                        },
                        consumer: StreamEndpoint {
                            component: consumer_c,
                            role: StreamRole::Consumer,
                        },
                        element: p_elem.clone(),
                        mode,
                    };
                    if !pairs.contains(&candidate) {
                        pairs.push(candidate);
                    }
                }
            }
        }
    }
    pairs
}

/// Build the [`StreamPairGraph`] for a set of fused components.
///
/// Pure function over the parsed components, the resolver's
/// `resolved_imports` map, and the chosen memory mode. Does not mutate
/// anything.
pub fn build_stream_pair_graph(
    components: &[ParsedComponent],
    resolved_imports: &HashMap<(usize, String), (usize, String)>,
    mode: StreamMemoryMode,
) -> StreamPairGraph {
    let roles: Vec<Vec<(StreamElement, StreamRole)>> =
        components.iter().map(component_stream_roles).collect();
    let connections = fusion_connections(resolved_imports);
    StreamPairGraph {
        pairs: pair_streams(&roles, &connections, mode),
    }
}

// ─── #142: static stream validation at build time ─────────────────────
//
// Of the four checks in #142's scope table, this module ships:
//
//   (i)   Stream type-mismatch on stream-carrying import edges.
//         For each fusion connection (a, b), if at least one resolved
//         import between them carries a `stream<T>` reference in its
//         type signature, apply the role-list pair check. Components
//         that share only sync calls (no stream-typed imports) are
//         skipped — that's the false-positive case LS-R-11's first
//         draft tripped over, which the Mythos delta-pass auto-scan
//         caught.
//
//         The check is filtered, not fully type-precise: we know that
//         (a, b) carry streams, but not which import binds to which
//         stream-handle pair. So the type-mismatch decision still
//         falls back to "do any of A's producer element types pair
//         with any of B's consumer element types?", same as the
//         original role-list test. Filtering eliminates the false
//         positive without requiring full export-side type-graph
//         walks (those need traversal of `component_func_defs` and
//         the component's func index space). Documented in LS-R-11
//         as the layer-1 fix; a fully precise per-edge check stays
//         on the LS-R-11 backlog for a future PR.
//
//   (iii) Circular stream dependencies — SCC of size ≥ 3 in the
//         directed `producer → consumer` graph built from detected
//         [`StreamPair`]s. Size-2 SCCs are excluded — that's the
//         legal bidirectional-pipe pattern (two independent streams
//         in opposite directions, each individually acyclic).
//
//   (iv) Resource lifetime across async boundaries — a resource
//        handle (`own<R>` / `borrow<R>`) carried as a `stream<T>` /
//        `future<T>` element type. A `borrow<R>` is only valid within
//        its lending call, but a stream/future is read *after* that
//        call returns across the async boundary → use-after-scope; an
//        `own<R>` transferred into a stream and then dropped by the
//        producer while the consumer still holds it is the
//        drop-while-referenced hazard #142 names. See
//        [`resource_lifetime_issues`].
//
// Check **(ii) bounded-channel capacity** is **not applicable**: the
// Component-Model canonical ABI has no bounded-channel / capacity
// concept — `stream.new` (`CanonicalEntry::StreamNew { ty }`) takes no
// capacity, and streams are unbounded by construction. There is nothing
// in the component binary to validate; "declare a capacity" presupposes
// an annotation mechanism the ABI does not provide (#142).

/// A validation issue raised by [`validate_stream_pair_graph`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StreamValidationIssue {
    /// Two fusion-connected components have at least one resolved
    /// import edge carrying a `stream<T>` reference, but their
    /// producer/consumer role lists share no element type — so the
    /// optimized in-module adapter cannot be emitted and the
    /// host-routed path will mis-type the wire bytes at runtime.
    /// The element-type Vecs preserve the local lists so the error
    /// message names what the user wired up.
    TypeMismatch {
        producer_component: usize,
        consumer_component: usize,
        producer_types: Vec<StreamElement>,
        consumer_types: Vec<StreamElement>,
    },
    /// The directed `producer → consumer` graph of detected
    /// [`StreamPair`]s contains a strongly-connected component of size
    /// ≥ 3. Could deadlock at runtime if every component is waiting on
    /// inbound stream data before producing outbound data.
    Cycle { component_cycle: Vec<usize> },
    /// Check (iv): a `stream<T>` / `future<T>` carries a resource handle
    /// as its element type. `owned == false` is a `borrow<R>` —
    /// definitely invalid, the borrow cannot outlive its lending call
    /// across the async boundary. `owned == true` is an `own<R>` —
    /// permitted only if the producer never drops the handle while the
    /// consumer still references it (the drop-while-referenced hazard
    /// meld cannot rule out statically). `descriptor` is the offending
    /// `stream<…>` / `future<…>` type descriptor.
    ResourceLifetime {
        component: usize,
        descriptor: String,
        resource_type_id: u32,
        owned: bool,
    },
}

/// Return every `stream<T>` element type reachable from the given
/// component-level type reference.
///
/// Walks `ComponentTypeRef::Type(Eq idx)` directly resolving to a
/// stream type, `Func(idx)` recursing through every param/result,
/// and `Instance(idx)` recursing through every export. Returns an
/// empty Vec when no streams are present, which is the signal for
/// "this import edge carries no streams" used by check (i).
pub fn stream_elements_in_typeref(
    comp: &ParsedComponent,
    ty_ref: &wasmparser::ComponentTypeRef,
) -> Vec<StreamElement> {
    use wasmparser::ComponentTypeRef as Ref;
    use wasmparser::TypeBounds;
    let mut out = Vec::new();
    match ty_ref {
        Ref::Type(TypeBounds::Eq(idx)) => {
            if let Some(ty) = comp.types.get(*idx as usize) {
                match &ty.kind {
                    ComponentTypeKind::P3Async(desc) => {
                        if let Some(elem) = StreamElement::from_descriptor(desc) {
                            out.push(canonicalize_stream_element(comp, elem));
                        }
                    }
                    ComponentTypeKind::Function { params, results } => {
                        for (_, vt) in params {
                            out.extend(stream_elements_in_valtype(comp, vt));
                        }
                        for (_, vt) in results {
                            out.extend(stream_elements_in_valtype(comp, vt));
                        }
                    }
                    ComponentTypeKind::Instance { exports } => {
                        for (_, inner_ref) in exports {
                            out.extend(stream_elements_in_typeref(comp, inner_ref));
                        }
                    }
                    _ => {}
                }
            }
        }
        Ref::Func(idx) => {
            if let Some(ty) = comp.types.get(*idx as usize)
                && let ComponentTypeKind::Function { params, results } = &ty.kind
            {
                for (_, vt) in params {
                    out.extend(stream_elements_in_valtype(comp, vt));
                }
                for (_, vt) in results {
                    out.extend(stream_elements_in_valtype(comp, vt));
                }
            }
        }
        Ref::Instance(idx) => {
            if let Some(ty) = comp.types.get(*idx as usize)
                && let ComponentTypeKind::Instance { exports } = &ty.kind
            {
                for (_, inner_ref) in exports {
                    out.extend(stream_elements_in_typeref(comp, inner_ref));
                }
            }
        }
        _ => {}
    }
    out
}

/// Recurse through a `ComponentValType`, collecting every reachable
/// `stream<T>` element type. Handles composite types (list / option /
/// result / record / variant / tuple / fixed-size list) by
/// descending into their payload value types; halts at primitives,
/// strings, flags, and resource handles.
///
/// Streams appear in the AST only via `Type(idx)` references to a
/// `ComponentTypeKind::P3Async("stream<...>")` entry; the walker does
/// not chase further through `Type(idx)` referring to non-stream
/// composite types, so a `stream<T>` hidden inside an aliased record
/// won't surface here. That's an acknowledged limit, not a target.
pub fn stream_elements_in_valtype(
    comp: &ParsedComponent,
    val_ty: &ComponentValType,
) -> Vec<StreamElement> {
    let mut out = Vec::new();
    match val_ty {
        ComponentValType::Type(idx) => {
            if let Some(ty) = comp.types.get(*idx as usize)
                && let ComponentTypeKind::P3Async(desc) = &ty.kind
                && let Some(elem) = StreamElement::from_descriptor(desc)
            {
                out.push(canonicalize_stream_element(comp, elem));
            }
        }
        ComponentValType::List(inner)
        | ComponentValType::Option(inner)
        | ComponentValType::FixedSizeList(inner, _) => {
            out.extend(stream_elements_in_valtype(comp, inner));
        }
        ComponentValType::Record(fields) => {
            for (_, vt) in fields {
                out.extend(stream_elements_in_valtype(comp, vt));
            }
        }
        ComponentValType::Variant(arms) => {
            for (_, opt) in arms {
                if let Some(vt) = opt {
                    out.extend(stream_elements_in_valtype(comp, vt));
                }
            }
        }
        ComponentValType::Tuple(items) => {
            for vt in items {
                out.extend(stream_elements_in_valtype(comp, vt));
            }
        }
        ComponentValType::Result { ok, err } => {
            if let Some(vt) = ok {
                out.extend(stream_elements_in_valtype(comp, vt));
            }
            if let Some(vt) = err {
                out.extend(stream_elements_in_valtype(comp, vt));
            }
        }
        _ => {}
    }
    out
}

/// `true` if any resolved import edge between components `a` and `b`
/// (in either direction) carries a `stream<T>` reference somewhere in
/// its component-level import type signature.
///
/// Used by the type-mismatch validator (LS-R-11) to filter out pairs
/// that are merely sync-connected — those can have unrelated stream
/// roles on each side without that being a wiring bug. Returns
/// `false` if neither side imports any stream from the other.
pub fn pair_has_stream_typed_import(
    components: &[ParsedComponent],
    resolved_imports: &HashMap<(usize, String), (usize, String)>,
    a: usize,
    b: usize,
) -> bool {
    for ((importer, import_name), (exporter, _)) in resolved_imports {
        let on_pair = (*importer == a && *exporter == b) || (*importer == b && *exporter == a);
        if !on_pair {
            continue;
        }
        let Some(importer_comp) = components.get(*importer) else {
            continue;
        };
        let Some(import) = importer_comp
            .imports
            .iter()
            .find(|i| &i.name == import_name)
        else {
            continue;
        };
        if !stream_elements_in_typeref(importer_comp, &import.ty).is_empty() {
            return true;
        }
    }
    false
}

/// Resolve a component-level `Func` export by name to the stream
/// element types its signature carries.
///
/// Walks `comp.component_func_defs[export.index]` to find the source
/// of the exported function:
///
/// - [`ComponentFuncDef::Import`] → look up `comp.imports[idx].ty`
///   and reuse [`stream_elements_in_typeref`].
/// - [`ComponentFuncDef::Lift`] → look up the `CanonicalEntry::Lift`
///   entry, extract its `type_index`, and walk it as
///   `ComponentTypeRef::Func(type_index)`.
/// - [`ComponentFuncDef::InstanceExportAlias`] → returns empty for
///   now; alias chains require chasing through nested instance
///   types and are deferred. The common-case stream-bearing exports
///   are Lift entries (component-defined functions) or Import
///   re-exports (forwarding pattern), both covered above.
///
/// Returns an empty Vec for non-Func exports, unresolved indices,
/// or alias-export chains — same "this edge carries no streams"
/// signal as the importer-side walker.
pub fn export_stream_elements(comp: &ParsedComponent, export_name: &str) -> Vec<StreamElement> {
    let Some(export) = comp.exports.iter().find(|e| e.name == export_name) else {
        return Vec::new();
    };
    if !matches!(export.kind, ComponentExternalKind::Func) {
        return Vec::new();
    }
    let Some(def) = comp.component_func_defs.get(export.index as usize) else {
        return Vec::new();
    };
    match def {
        ComponentFuncDef::Import(import_idx) => comp
            .imports
            .get(*import_idx)
            .map(|imp| stream_elements_in_typeref(comp, &imp.ty))
            .unwrap_or_default(),
        ComponentFuncDef::Lift(canon_idx) => {
            let Some(entry) = comp.canonical_functions.get(*canon_idx) else {
                return Vec::new();
            };
            let CanonicalEntry::Lift { type_index, .. } = entry else {
                return Vec::new();
            };
            stream_elements_in_typeref(comp, &wasmparser::ComponentTypeRef::Func(*type_index))
        }
        ComponentFuncDef::InstanceExportAlias(_) => {
            // Deferred — would require following the alias chain
            // through `comp.component_aliases[idx]` and then
            // resolving the alias's target instance type. Tracked
            // in LS-R-11's "limits" block.
            Vec::new()
        }
        ComponentFuncDef::ExportAlias(target) => {
            // A func export-alias (#355) just re-binds another func index; the
            // aliased func carries the real signature. Follow it one hop (no
            // cycles: an export aliases an already-defined func).
            match comp.component_func_defs.get(*target as usize) {
                Some(ComponentFuncDef::Lift(canon_idx)) => {
                    match comp.canonical_functions.get(*canon_idx) {
                        Some(CanonicalEntry::Lift { type_index, .. }) => {
                            stream_elements_in_typeref(
                                comp,
                                &wasmparser::ComponentTypeRef::Func(*type_index),
                            )
                        }
                        _ => Vec::new(),
                    }
                }
                Some(ComponentFuncDef::Import(import_idx)) => comp
                    .imports
                    .get(*import_idx)
                    .map(|imp| stream_elements_in_typeref(comp, &imp.ty))
                    .unwrap_or_default(),
                _ => Vec::new(),
            }
        }
    }
}

/// Run #142's static validation passes over a built [`StreamPairGraph`].
///
/// Returns an empty vec when no issues were found. Caller decides
/// whether to surface as warnings or hard errors (the resolver hoists
/// each issue into [`crate::error::Error::StreamValidation`]).
///
/// **Check (i) precision**: per-edge type comparison. For each
/// resolved import where both sides carry stream<T> references,
/// the importer-side and exporter-side element types are compared
/// directly. Falls back to the role-list heuristic only when the
/// exporter side is unresolvable (alias-chain exports, which
/// haven't been threaded through `component_func_defs` walking
/// yet). The previous v0.13.0 release shipped only the heuristic;
/// v0.15.0 promotes most fusion connections to the precise check.
pub fn validate_stream_pair_graph(
    components: &[ParsedComponent],
    resolved_imports: &HashMap<(usize, String), (usize, String)>,
    graph: &StreamPairGraph,
) -> Vec<StreamValidationIssue> {
    let roles: Vec<Vec<(StreamElement, StreamRole)>> =
        components.iter().map(component_stream_roles).collect();

    let mut issues = Vec::new();
    let mut precise_pairs: std::collections::HashSet<(usize, usize)> =
        std::collections::HashSet::new();

    // Check (i), layer 2 (per-edge precise): walk every resolved
    // import. If the importer's import is stream-typed AND the
    // exporter's matching export is stream-typed AND the element-
    // type multisets differ, emit a TypeMismatch keyed to the
    // exact (importer, exporter) component pair. Once a pair has
    // been precisely checked (whether or not it raised), suppress
    // the layer-1 heuristic for that pair to avoid double-counting.
    for ((importer, import_name), (exporter, export_name)) in resolved_imports {
        if importer == exporter {
            continue;
        }
        let Some(importer_comp) = components.get(*importer) else {
            continue;
        };
        let Some(import) = importer_comp
            .imports
            .iter()
            .find(|i| &i.name == import_name)
        else {
            continue;
        };
        let imp_elems = stream_elements_in_typeref(importer_comp, &import.ty);
        if imp_elems.is_empty() {
            continue;
        }
        let Some(exporter_comp) = components.get(*exporter) else {
            continue;
        };
        let exp_elems = export_stream_elements(exporter_comp, export_name);
        if exp_elems.is_empty() {
            // Exporter side unresolved (alias chain, missing
            // export, etc.). Leave to the layer-1 heuristic.
            continue;
        }
        precise_pairs.insert((*importer, *exporter));

        // Compare as multisets. Sort + equality is fine for the
        // small list sizes typical of stream-bearing function
        // signatures (usually 1 stream per signature).
        let mut imp_sorted: Vec<_> = imp_elems.iter().collect();
        let mut exp_sorted: Vec<_> = exp_elems.iter().collect();
        imp_sorted.sort_by_key(|e| format!("{e:?}"));
        exp_sorted.sort_by_key(|e| format!("{e:?}"));
        if imp_sorted != exp_sorted {
            let issue = StreamValidationIssue::TypeMismatch {
                producer_component: *exporter,
                consumer_component: *importer,
                producer_types: exp_elems.clone(),
                consumer_types: imp_elems.clone(),
            };
            if !issues.contains(&issue) {
                issues.push(issue);
            }
        }
    }

    // Check (i), layer 1 (role-list heuristic, filtered): only fire
    // on fusion connections that DID NOT get a precise check above.
    // The filter still gates by stream-typed-import presence so
    // sync-only connections with unrelated streams stay silent.
    let connections = fusion_connections(resolved_imports);
    for &(a, b) in &connections {
        if precise_pairs.contains(&(a, b)) || precise_pairs.contains(&(b, a)) {
            continue;
        }
        if !pair_has_stream_typed_import(components, resolved_imports, a, b) {
            continue;
        }
        for &(producer_c, consumer_c) in &[(a, b), (b, a)] {
            let (Some(producer_roles), Some(consumer_roles)) =
                (roles.get(producer_c), roles.get(consumer_c))
            else {
                continue;
            };
            let producer_types: Vec<StreamElement> = producer_roles
                .iter()
                .filter(|(_, r)| *r == StreamRole::Producer)
                .map(|(e, _)| e.clone())
                .collect();
            let consumer_types: Vec<StreamElement> = consumer_roles
                .iter()
                .filter(|(_, r)| *r == StreamRole::Consumer)
                .map(|(e, _)| e.clone())
                .collect();
            if producer_types.is_empty() || consumer_types.is_empty() {
                continue;
            }
            let any_matched = producer_types
                .iter()
                .any(|p| consumer_types.iter().any(|c| p == c));
            if !any_matched {
                let issue = StreamValidationIssue::TypeMismatch {
                    producer_component: producer_c,
                    consumer_component: consumer_c,
                    producer_types: producer_types.clone(),
                    consumer_types: consumer_types.clone(),
                };
                if !issues.contains(&issue) {
                    issues.push(issue);
                }
            }
        }
    }

    // Check (iii): SCC ≥ 3 in the directed producer → consumer graph.
    issues.extend(cycle_issues_from_pairs(graph));

    issues
}

/// Check (iv): flag any `stream<T>` / `future<T>` whose element type is
/// a resource handle (`own<R>` / `borrow<R>`).
///
/// The P3Async descriptor records the element type as the Debug form of
/// the wasmparser `ComponentValType`, so a handle element appears as
/// `stream<Type(N)>` where component type index `N` resolves to a
/// `Defined(Own(R))` / `Defined(Borrow(R))`. We parse the `Type(N)`
/// index out and reuse [`ParsedComponent::resolve_to_resource`] — the
/// same `Type(idx)` → handle chase meld already applies to function
/// params — rather than trusting the Debug text for the handle kind.
///
/// Limitations (acknowledged, not targets): only a *direct* handle
/// element is detected. A handle nested inside a composite element
/// (`stream<list<own<R>>>` → `stream<List(..)>`) is not flagged, the
/// same boundary as [`stream_elements_in_valtype`].
pub fn resource_lifetime_issues(components: &[ParsedComponent]) -> Vec<StreamValidationIssue> {
    let mut issues = Vec::new();
    for (ci, comp) in components.iter().enumerate() {
        for ty in &comp.types {
            let ComponentTypeKind::P3Async(desc) = &ty.kind else {
                continue;
            };
            let Some(inner) = desc
                .strip_prefix("stream<")
                .or_else(|| desc.strip_prefix("future<"))
                .and_then(|s| s.strip_suffix('>'))
            else {
                continue;
            };
            let Some(idx) = parse_type_index(inner.trim()) else {
                continue;
            };
            if let Some((resource_type_id, owned)) =
                comp.resolve_to_resource(&ComponentValType::Type(idx))
            {
                issues.push(StreamValidationIssue::ResourceLifetime {
                    component: ci,
                    descriptor: desc.clone(),
                    resource_type_id,
                    owned,
                });
            }
        }
    }
    issues
}

/// Parse the wasmparser `ComponentValType::Type(N)` Debug form
/// (`"Type(N)"`) back to its index. Returns `None` for any other shape
/// (e.g. `"Primitive(U8)"`, `"List(..)"`).
fn parse_type_index(s: &str) -> Option<u32> {
    s.strip_prefix("Type(")?
        .strip_suffix(')')?
        .trim()
        .parse()
        .ok()
}

/// Cycle-only sub-pass — exposed so tests that only care about (iii)
/// don't have to construct `ParsedComponent` fixtures.
pub fn cycle_issues_from_pairs(graph: &StreamPairGraph) -> Vec<StreamValidationIssue> {
    let mut issues = Vec::new();
    for scc in strongly_connected_components(&graph.pairs) {
        if scc.len() >= 3 {
            issues.push(StreamValidationIssue::Cycle {
                component_cycle: scc,
            });
        }
    }
    issues
}

/// Strongly-connected-components on the directed graph induced by
/// `pair.producer.component → pair.consumer.component`. Returns each
/// multi-node SCC as a sorted `Vec<component_index>`. Singleton SCCs
/// (a component with no stream-pair self-loop, or one whose edges all
/// leave the SCC) are excluded.
///
/// Iterative Tarjan — uses an explicit work stack rather than direct
/// recursion. A recursive implementation overflows the default Rust
/// thread stack at roughly 40 000 nodes (Mythos delta-pass identified
/// this on the first draft of this code, and `petgraph 0.8`'s own
/// `tarjan_scc` is also recursive). Meld's practical fusion input is
/// bounded by component count, but moving the recursion off the call
/// stack lets the same routine survive pathological or
/// attacker-controlled input shapes too.
fn strongly_connected_components(pairs: &[StreamPair]) -> Vec<Vec<usize>> {
    let mut adj: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut nodes: Vec<usize> = Vec::new();
    for p in pairs {
        let (from, to) = (p.producer.component, p.consumer.component);
        adj.entry(from).or_default().push(to);
        for &n in &[from, to] {
            if !nodes.contains(&n) {
                nodes.push(n);
            }
        }
    }

    let mut index_counter: i64 = 0;
    let mut tarjan_stack: Vec<usize> = Vec::new();
    let mut on_stack: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut index: HashMap<usize, i64> = HashMap::new();
    let mut lowlink: HashMap<usize, i64> = HashMap::new();
    let mut out: Vec<Vec<usize>> = Vec::new();

    // Each work-stack entry holds (current node, next successor index
    // to inspect). On first entry the index is 0; after returning from
    // a child the index points one past the child we just finished, so
    // `succs[index - 1]` identifies which child's lowlink to fold in.
    let mut work: Vec<(usize, usize)> = Vec::new();
    let empty: Vec<usize> = Vec::new();

    for &v in &nodes {
        if index.contains_key(&v) {
            continue;
        }
        work.push((v, 0));

        while let Some(&(u, ci)) = work.last() {
            if ci == 0 {
                index.insert(u, index_counter);
                lowlink.insert(u, index_counter);
                index_counter += 1;
                tarjan_stack.push(u);
                on_stack.insert(u);
            } else {
                // Just returned from succs[ci - 1] — fold its lowlink
                // back into our own. Only safe to read after the
                // child has finished, which is exactly this branch.
                let succs = adj.get(&u).unwrap_or(&empty);
                let prev_w = succs[ci - 1];
                let w_low = lowlink[&prev_w];
                let u_low = lowlink[&u];
                lowlink.insert(u, u_low.min(w_low));
            }

            // Scan for the next successor we still need to descend
            // into. Already-visited successors that are on the
            // tarjan_stack contribute to our lowlink directly; nodes
            // with no remaining unvisited successors fall through to
            // the SCC-root check below.
            let succs = adj.get(&u).unwrap_or(&empty);
            let mut next_ci = ci;
            let mut descended = false;
            while next_ci < succs.len() {
                let w = succs[next_ci];
                if !index.contains_key(&w) {
                    work.last_mut().expect("work non-empty").1 = next_ci + 1;
                    work.push((w, 0));
                    descended = true;
                    break;
                } else {
                    if on_stack.contains(&w) {
                        let wi = index[&w];
                        let u_low = lowlink[&u];
                        lowlink.insert(u, u_low.min(wi));
                    }
                    next_ci += 1;
                }
            }

            if !descended {
                // All children of u are settled. Pop the SCC if u is
                // a root, then return to the parent (or end the
                // outer scan).
                if lowlink[&u] == index[&u] {
                    let mut scc = Vec::new();
                    loop {
                        let w = tarjan_stack.pop().expect("stack non-empty inside SCC root");
                        on_stack.remove(&w);
                        scc.push(w);
                        if w == u {
                            break;
                        }
                    }
                    scc.sort_unstable();
                    out.push(scc);
                }
                work.pop();
            }
        }
    }

    out.into_iter().filter(|scc| scc.len() > 1).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn typed(s: &str) -> StreamElement {
        StreamElement::Typed(s.to_string())
    }

    #[test]
    fn from_descriptor_parses_typed_untyped_and_rejects_non_stream() {
        assert_eq!(
            StreamElement::from_descriptor("stream<U8>"),
            Some(typed("U8"))
        );
        assert_eq!(
            StreamElement::from_descriptor("stream"),
            Some(StreamElement::Untyped)
        );
        // Nested element type — strip_suffix removes exactly one '>'.
        assert_eq!(
            StreamElement::from_descriptor("stream<list<U8>>"),
            Some(typed("list<U8>"))
        );
        // Not a stream.
        assert_eq!(StreamElement::from_descriptor("future<U8>"), None);
        assert_eq!(StreamElement::from_descriptor("map<U8, U8>"), None);
    }

    #[test]
    fn fusion_connections_dedups_and_drops_self_links() {
        let mut resolved: HashMap<(usize, String), (usize, String)> = HashMap::new();
        // 0 imports from 1 (two different functions — one connection).
        resolved.insert((0, "f".into()), (1, "f".into()));
        resolved.insert((0, "g".into()), (1, "g".into()));
        // 2 imports from 0.
        resolved.insert((2, "h".into()), (0, "h".into()));
        // Self-link — must be dropped.
        resolved.insert((3, "k".into()), (3, "k".into()));

        let conns = fusion_connections(&resolved);
        assert_eq!(conns, vec![(0, 1), (0, 2)]);
    }

    /// ADR-3 gating fixture: a producer component and a consumer
    /// component linked by a resolved import yield exactly one
    /// `StreamPair` with the correct roles and shared element type.
    #[test]
    fn stream_pair_detected_for_connected_producer_consumer() {
        // Component 0 produces stream<U8>; component 1 consumes it.
        let roles = vec![
            vec![(typed("U8"), StreamRole::Producer)],
            vec![(typed("U8"), StreamRole::Consumer)],
        ];
        let pairs = pair_streams(&roles, &[(0, 1)], StreamMemoryMode::CrossMemory);
        assert_eq!(pairs.len(), 1, "exactly one pair expected; got {pairs:?}");
        let p = &pairs[0];
        assert_eq!(p.producer.component, 0);
        assert_eq!(p.producer.role, StreamRole::Producer);
        assert_eq!(p.consumer.component, 1);
        assert_eq!(p.consumer.role, StreamRole::Consumer);
        assert_eq!(p.element, typed("U8"));
        assert_eq!(p.mode, StreamMemoryMode::CrossMemory);
    }

    /// LS-R-16 gate (over-match prevention): a raw, un-canonicalised
    /// component-LOCAL `Type(N)` descriptor must NEVER pair.
    ///
    /// After #264 the pairing layer keys on STRUCTURAL descriptors, but a
    /// raw `Type(N)` is exactly what `canonicalize_stream_element` returns
    /// when it declines to resolve a type — a resource handle, a
    /// depth-bound / cycle hit, or an unresolvable index. So `Type(N)` is
    /// the canonical "conservative fallback" element, and this test pins
    /// the invariant that such a fallback element is non-pairable: two
    /// DIFFERENT real types that both happened to fall back at the same
    /// local index `Type(0)` would string-match and manufacture a false
    /// pair that drives the bridge emitter to wire incompatible streams.
    /// `pair_streams` must decline it; the streams stay host-routed.
    ///
    /// The positive direction (a genuine aggregate that DOES canonicalise,
    /// at different local indices, pairing exactly once) and the structural
    /// over-match guard (two different aggregates at the SAME local index,
    /// no pair) are pinned separately by the `#264` tests below, which
    /// exercise the canonicaliser end-to-end through `component_stream_roles`.
    #[test]
    fn ls_r_16_local_index_element_descriptors_do_not_pair() {
        // Producer's element is its local Type(0); consumer's element is a
        // DIFFERENT type that happens to also sit at its local Type(0).
        // (Stand-in for any element the canonicaliser declined to resolve.)
        let roles = vec![
            vec![(typed("Type(0)"), StreamRole::Producer)],
            vec![(typed("Type(0)"), StreamRole::Consumer)],
        ];
        let pairs = pair_streams(&roles, &[(0, 1)], StreamMemoryMode::CrossMemory);
        assert!(
            pairs.is_empty(),
            "local-index `Type(N)` descriptors are not a valid cross-component \
             key and must not be paired (over-match would wire incompatible \
             streams); got {pairs:?}"
        );
        // Sanity: stable scalar descriptors on the same shape DO still pair.
        let prim_roles = vec![
            vec![(typed("u8"), StreamRole::Producer)],
            vec![(typed("u8"), StreamRole::Consumer)],
        ];
        assert_eq!(
            pair_streams(&prim_roles, &[(0, 1)], StreamMemoryMode::CrossMemory).len(),
            1,
            "primitive stream element types remain pairable"
        );
    }

    /// ADR-3 gating fixture: a producer and a consumer of the same
    /// stream element type that are NOT linked by a resolved import
    /// yield no pair.
    #[test]
    fn no_pair_when_components_not_fusion_connected() {
        let roles = vec![
            vec![(typed("U8"), StreamRole::Producer)],
            vec![(typed("U8"), StreamRole::Consumer)],
        ];
        // No connections at all.
        let pairs = pair_streams(&roles, &[], StreamMemoryMode::CrossMemory);
        assert!(pairs.is_empty(), "unconnected components must not pair");
    }

    /// ADR-3 gating fixture: two connected components that both only
    /// produce (or both only consume) a stream yield no pair.
    #[test]
    fn no_pair_without_producer_consumer_complementarity() {
        // Both components are producers — no consumer end.
        let both_produce = vec![
            vec![(typed("U8"), StreamRole::Producer)],
            vec![(typed("U8"), StreamRole::Producer)],
        ];
        assert!(
            pair_streams(&both_produce, &[(0, 1)], StreamMemoryMode::CrossMemory).is_empty(),
            "two producers must not pair"
        );

        // Both components are consumers.
        let both_consume = vec![
            vec![(typed("U8"), StreamRole::Consumer)],
            vec![(typed("U8"), StreamRole::Consumer)],
        ];
        assert!(
            pair_streams(&both_consume, &[(0, 1)], StreamMemoryMode::CrossMemory).is_empty(),
            "two consumers must not pair"
        );
    }

    /// ADR-3 gating fixture: the recorded memory mode follows the
    /// caller-supplied strategy.
    #[test]
    fn memory_mode_follows_strategy() {
        let roles = vec![
            vec![(typed("U8"), StreamRole::Producer)],
            vec![(typed("U8"), StreamRole::Consumer)],
        ];
        let same = pair_streams(&roles, &[(0, 1)], StreamMemoryMode::SameMemory);
        assert_eq!(same[0].mode, StreamMemoryMode::SameMemory);
        let cross = pair_streams(&roles, &[(0, 1)], StreamMemoryMode::CrossMemory);
        assert_eq!(cross[0].mode, StreamMemoryMode::CrossMemory);
    }

    #[test]
    fn mismatched_element_types_do_not_pair() {
        // Connected producer of stream<u8> + consumer of stream<s32>:
        // two different streams, not a pair. The honest-candidate rule.
        let roles = vec![
            vec![(typed("U8"), StreamRole::Producer)],
            vec![(typed("S32"), StreamRole::Consumer)],
        ];
        assert!(
            pair_streams(&roles, &[(0, 1)], StreamMemoryMode::CrossMemory).is_empty(),
            "stream<u8> and stream<s32> are different streams — no pair"
        );
    }

    #[test]
    fn bidirectional_pipe_pairs_in_both_directions() {
        // Component 0 produces AND consumes; component 1 produces AND
        // consumes; connected. Two distinct pairings: 0→1 and 1→0.
        let roles = vec![
            vec![
                (typed("U8"), StreamRole::Producer),
                (typed("U8"), StreamRole::Consumer),
            ],
            vec![
                (typed("U8"), StreamRole::Producer),
                (typed("U8"), StreamRole::Consumer),
            ],
        ];
        let pairs = pair_streams(&roles, &[(0, 1)], StreamMemoryMode::SameMemory);
        assert_eq!(pairs.len(), 2, "pipe pairs both directions; got {pairs:?}");
        assert!(
            pairs
                .iter()
                .any(|p| p.producer.component == 0 && p.consumer.component == 1)
        );
        assert!(
            pairs
                .iter()
                .any(|p| p.producer.component == 1 && p.consumer.component == 0)
        );
    }

    // ─── #142 validation tests ────────────────────────────────────────

    fn pair(producer: usize, consumer: usize, elem: &str) -> StreamPair {
        StreamPair {
            producer: StreamEndpoint {
                component: producer,
                role: StreamRole::Producer,
            },
            consumer: StreamEndpoint {
                component: consumer,
                role: StreamRole::Consumer,
            },
            element: typed(elem),
            mode: StreamMemoryMode::CrossMemory,
        }
    }

    /// Bidirectional pipe (2-cycle) is the canonical legal pattern: two
    /// independent streams in opposite directions. The cycle detector
    /// must NOT flag this.
    #[test]
    fn bidirectional_pipe_is_not_flagged_as_cycle() {
        let roles = vec![
            vec![
                (typed("U8"), StreamRole::Producer),
                (typed("U8"), StreamRole::Consumer),
            ],
            vec![
                (typed("U8"), StreamRole::Producer),
                (typed("U8"), StreamRole::Consumer),
            ],
        ];
        let graph = StreamPairGraph {
            pairs: pair_streams(&roles, &[(0, 1)], StreamMemoryMode::CrossMemory),
        };
        assert_eq!(graph.pairs.len(), 2, "precondition: pipe pairs both ways");

        let issues = cycle_issues_from_pairs(&graph);
        let cycles = issues
            .iter()
            .filter(|i| matches!(i, StreamValidationIssue::Cycle { .. }))
            .count();
        assert_eq!(cycles, 0, "2-cycle is the legal pipe — must not flag");
    }

    /// LS-R-12 regression: a 3-component stream loop (A→B, B→C,
    /// C→A) is the smallest non-trivial cycle. Must be flagged.
    #[test]
    fn ls_r_12_stream_three_component_cycle_flagged() {
        let graph = StreamPairGraph {
            pairs: vec![pair(0, 1, "U8"), pair(1, 2, "U8"), pair(2, 0, "U8")],
        };

        let issues = cycle_issues_from_pairs(&graph);
        let cycle_components: Vec<Vec<usize>> = issues
            .iter()
            .filter_map(|i| match i {
                StreamValidationIssue::Cycle { component_cycle } => Some(component_cycle.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(
            cycle_components,
            vec![vec![0, 1, 2]],
            "expected one SCC {{0,1,2}}, got {cycle_components:?}"
        );
    }

    /// A 4-component cycle (A→B, B→C, C→D, D→A) must also fire — the
    /// SCC detector is size-agnostic above the size-2 threshold.
    #[test]
    fn four_component_cycle_flagged() {
        let graph = StreamPairGraph {
            pairs: vec![
                pair(0, 1, "U8"),
                pair(1, 2, "U8"),
                pair(2, 3, "U8"),
                pair(3, 0, "U8"),
            ],
        };
        let issues = cycle_issues_from_pairs(&graph);
        let cycles: Vec<_> = issues
            .iter()
            .filter_map(|i| match i {
                StreamValidationIssue::Cycle { component_cycle } => Some(component_cycle.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(cycles, vec![vec![0, 1, 2, 3]]);
    }

    /// Regression: the SCC implementation must tolerate deep linear
    /// chains without exhausting the call stack. A recursive Tarjan
    /// would overflow the default 8 MB Rust thread stack at roughly
    /// 40 000 nodes (Mythos delta-pass identified this on the first
    /// draft of this code; the fix swapped to petgraph's iterative
    /// implementation). 50 000 nodes is comfortably past that limit
    /// and well into "would have crashed" territory for the recursive
    /// version, so a clean run here pins the iterative backend in
    /// place.
    #[test]
    fn deep_linear_chain_does_not_overflow_stack() {
        let n = 50_000usize;
        let mut pairs = Vec::with_capacity(n - 1);
        for i in 0..(n - 1) {
            pairs.push(pair(i, i + 1, "U8"));
        }
        let graph = StreamPairGraph { pairs };
        let issues = cycle_issues_from_pairs(&graph);
        assert!(
            issues.is_empty(),
            "linear chain of {n} components must not flag a cycle; got {issues:?}"
        );
    }

    /// Acyclic pipeline (A→B→C, no edge back to A) must NOT flag a
    /// cycle. This is the common dataflow shape.
    #[test]
    fn linear_pipeline_is_not_flagged() {
        let graph = StreamPairGraph {
            pairs: vec![pair(0, 1, "U8"), pair(1, 2, "U8")],
        };
        let issues = cycle_issues_from_pairs(&graph);
        assert!(
            issues.is_empty(),
            "linear pipeline must not flag; got {issues:?}"
        );
    }

    // ─── LS-R-11 (precise stream type-mismatch) tests ─────────────────

    use crate::parser::{
        CanonicalOptions, ComponentExport, ComponentImport, ComponentType, ComponentTypeKind,
        ComponentValType, PrimitiveValType,
    };
    use wasmparser::ComponentExternalKind;

    /// Build a minimal `ParsedComponent` with the given imports, types,
    /// and stream-role-bearing canonical functions. Most fields are
    /// left empty — the validator only reads `imports`, `types`, and
    /// `canonical_functions` for these checks.
    fn make_component(
        imports: Vec<ComponentImport>,
        exports: Vec<ComponentExport>,
        types: Vec<ComponentType>,
        canonical_functions: Vec<CanonicalEntry>,
    ) -> ParsedComponent {
        make_component_with_func_defs(imports, exports, types, canonical_functions, vec![])
    }

    fn make_component_with_func_defs(
        imports: Vec<ComponentImport>,
        exports: Vec<ComponentExport>,
        types: Vec<ComponentType>,
        canonical_functions: Vec<CanonicalEntry>,
        component_func_defs: Vec<ComponentFuncDef>,
    ) -> ParsedComponent {
        ParsedComponent {
            name: None,
            core_modules: vec![],
            imports,
            exports,
            types,
            instances: vec![],
            canonical_functions,
            sub_components: vec![],
            component_aliases: vec![],
            component_instances: vec![],
            core_entity_order: vec![],
            component_func_defs,
            component_instance_defs: vec![],
            component_type_defs: vec![],
            original_size: 0,
            original_hash: String::new(),
            depth_0_sections: vec![],
            p3_async_features: vec![],
        }
    }

    fn stream_type(elem: &str) -> ComponentType {
        ComponentType {
            kind: ComponentTypeKind::P3Async(format!("stream<{elem}>")),
        }
    }

    fn func_type_taking_stream(stream_ty_idx: u32) -> ComponentType {
        ComponentType {
            kind: ComponentTypeKind::Function {
                params: vec![("s".to_string(), ComponentValType::Type(stream_ty_idx))],
                results: vec![],
            },
        }
    }

    fn options() -> CanonicalOptions {
        CanonicalOptions::default()
    }

    /// LS-R-11 layer-1 regression: when component A imports a function
    /// whose signature takes `stream<u8>` and that import resolves to
    /// component B's export, but A and B's role lists declare
    /// incompatible element types (u8 vs s32), the validator MUST
    /// raise a TypeMismatch. This is the case that motivated #142 (i).
    #[test]
    fn ls_r_11_stream_typed_import_with_mismatched_roles_raises() {
        // Component 0: imports a function taking stream<U8>; has a
        // producer role on stream<U8>.
        let comp_a = make_component(
            vec![ComponentImport {
                name: "consume".into(),
                ty: wasmparser::ComponentTypeRef::Func(1),
            }],
            vec![],
            vec![
                stream_type("U8"),          // types[0]
                func_type_taking_stream(0), // types[1]
            ],
            vec![CanonicalEntry::StreamWrite {
                ty: 0,
                options: options(),
            }],
        );
        // Component 1: exports the matching function name; declares
        // a consumer role on stream<S32> (the mismatch).
        let comp_b = make_component(
            vec![],
            vec![ComponentExport {
                name: "consume".into(),
                kind: ComponentExternalKind::Func,
                index: 0,
            }],
            vec![stream_type("S32")], // types[0]
            vec![CanonicalEntry::StreamRead {
                ty: 0,
                options: options(),
            }],
        );
        let components = vec![comp_a, comp_b];
        let mut resolved: HashMap<(usize, String), (usize, String)> = HashMap::new();
        resolved.insert((0, "consume".into()), (1, "consume".into()));

        // pair_streams drops the mismatch silently, so the pair graph
        // is empty — but the validator still picks up the issue via
        // the resolved-import walk.
        let graph = StreamPairGraph::default();

        let issues = validate_stream_pair_graph(&components, &resolved, &graph);
        let mismatches: Vec<_> = issues
            .iter()
            .filter(|i| matches!(i, StreamValidationIssue::TypeMismatch { .. }))
            .collect();
        assert_eq!(
            mismatches.len(),
            1,
            "expected exactly one TypeMismatch, got issues {issues:?}"
        );
    }

    /// LS-R-11 Mythos-finding regression: components A and B are
    /// sync-connected via a non-stream function, and each independently
    /// has unrelated stream operations on incompatible element types.
    /// The validator MUST NOT raise a TypeMismatch — the streams belong
    /// to other connections, not A↔B. This is the false positive the
    /// Mythos delta-pass auto-scan caught in PR #188.
    #[test]
    fn ls_r_11_sync_only_connection_with_unrelated_streams_does_not_raise() {
        // types[0] = u32 primitive (used as the sync import's param);
        // ComponentTypeRef::Type referring to it does NOT carry a stream.
        let u32_func_type = ComponentType {
            kind: ComponentTypeKind::Function {
                params: vec![(
                    "x".into(),
                    ComponentValType::Primitive(PrimitiveValType::U32),
                )],
                results: vec![],
            },
        };

        // Component 0: imports a sync function (no stream); has a
        // stream<U8> producer for an unrelated wiring.
        let comp_a = make_component(
            vec![ComponentImport {
                name: "sync_call".into(),
                ty: wasmparser::ComponentTypeRef::Func(1),
            }],
            vec![],
            vec![
                stream_type("U8"), // types[0]: unrelated stream
                u32_func_type,     // types[1]: the sync import's type
            ],
            vec![CanonicalEntry::StreamWrite {
                ty: 0,
                options: options(),
            }],
        );
        // Component 1: exports the matching sync function; has a
        // stream<S32> consumer for an unrelated wiring.
        let comp_b = make_component(
            vec![],
            vec![ComponentExport {
                name: "sync_call".into(),
                kind: ComponentExternalKind::Func,
                index: 0,
            }],
            vec![stream_type("S32")],
            vec![CanonicalEntry::StreamRead {
                ty: 0,
                options: options(),
            }],
        );
        let components = vec![comp_a, comp_b];
        let mut resolved: HashMap<(usize, String), (usize, String)> = HashMap::new();
        resolved.insert((0, "sync_call".into()), (1, "sync_call".into()));
        let graph = StreamPairGraph::default();

        let issues = validate_stream_pair_graph(&components, &resolved, &graph);
        let mismatches: Vec<_> = issues
            .iter()
            .filter(|i| matches!(i, StreamValidationIssue::TypeMismatch { .. }))
            .collect();
        assert!(
            mismatches.is_empty(),
            "Mythos finding regression: sync-only connection with unrelated streams must not raise; got {issues:?}"
        );
    }

    /// Negative: when the stream types DO match across the
    /// stream-typed import edge, no mismatch is raised.
    #[test]
    fn stream_typed_import_with_matching_types_does_not_raise() {
        let comp_a = make_component(
            vec![ComponentImport {
                name: "consume".into(),
                ty: wasmparser::ComponentTypeRef::Func(1),
            }],
            vec![],
            vec![stream_type("U8"), func_type_taking_stream(0)],
            vec![CanonicalEntry::StreamWrite {
                ty: 0,
                options: options(),
            }],
        );
        let comp_b = make_component(
            vec![],
            vec![ComponentExport {
                name: "consume".into(),
                kind: ComponentExternalKind::Func,
                index: 0,
            }],
            vec![stream_type("U8")],
            vec![CanonicalEntry::StreamRead {
                ty: 0,
                options: options(),
            }],
        );
        let components = vec![comp_a, comp_b];
        let mut resolved: HashMap<(usize, String), (usize, String)> = HashMap::new();
        resolved.insert((0, "consume".into()), (1, "consume".into()));
        let graph = StreamPairGraph::default();

        let issues = validate_stream_pair_graph(&components, &resolved, &graph);
        assert!(
            issues.is_empty(),
            "matching stream types must not raise; got {issues:?}"
        );
    }

    /// Direct unit test of the type walker: a `Func` typeref whose
    /// param is a `Type(idx)` resolving to a `P3Async("stream<U8>")`
    /// must surface as a single `Typed("U8")` element.
    #[test]
    fn stream_elements_in_typeref_walks_func_param() {
        let comp = make_component(
            vec![],
            vec![],
            vec![stream_type("U8"), func_type_taking_stream(0)],
            vec![],
        );
        let elems = stream_elements_in_typeref(&comp, &wasmparser::ComponentTypeRef::Func(1));
        assert_eq!(elems, vec![typed("U8")]);
    }

    /// Direct unit test: a `Func` typeref with no streams returns an
    /// empty Vec — that's the "this edge carries no streams" signal
    /// the filter relies on.
    #[test]
    fn stream_elements_in_typeref_returns_empty_for_sync_func() {
        let sync_func = ComponentType {
            kind: ComponentTypeKind::Function {
                params: vec![(
                    "x".into(),
                    ComponentValType::Primitive(PrimitiveValType::U32),
                )],
                results: vec![],
            },
        };
        let comp = make_component(vec![], vec![], vec![sync_func], vec![]);
        let elems = stream_elements_in_typeref(&comp, &wasmparser::ComponentTypeRef::Func(0));
        assert!(
            elems.is_empty(),
            "sync function must not surface stream elements; got {elems:?}"
        );
    }

    // ─── LS-R-11 layer-2 (precise per-edge) tests ─────────────────────

    /// Direct unit test of [`export_stream_elements`] for the
    /// `ComponentFuncDef::Lift` resolution path. A component that
    /// exports a `canon lift` of a function taking `stream<U8>` must
    /// surface that stream element type via the export-side walker —
    /// this is the path the layer-2 precise check relies on.
    #[test]
    fn export_stream_elements_walks_lift_function_signature() {
        let comp = make_component_with_func_defs(
            vec![],
            vec![ComponentExport {
                name: "produce".into(),
                kind: ComponentExternalKind::Func,
                index: 0,
            }],
            vec![
                stream_type("U8"),          // types[0]: stream<U8>
                func_type_taking_stream(0), // types[1]: fn(stream<U8>)
            ],
            vec![CanonicalEntry::Lift {
                core_func_index: 0,
                type_index: 1,
                options: options(),
            }],
            // component_func_defs[0] = Lift(0) — the exported function
            // came from canonical_functions[0].
            vec![ComponentFuncDef::Lift(0)],
        );
        let elems = export_stream_elements(&comp, "produce");
        assert_eq!(elems, vec![typed("U8")]);
    }

    /// `export_stream_elements` must return empty for an export
    /// resolved through an alias chain (`InstanceExportAlias`) —
    /// that path is deferred per the LS-R-11 limits documentation,
    /// and the precise check falls back to the layer-1 heuristic
    /// for those edges.
    #[test]
    fn export_stream_elements_returns_empty_for_alias_export() {
        let comp = make_component_with_func_defs(
            vec![],
            vec![ComponentExport {
                name: "aliased".into(),
                kind: ComponentExternalKind::Func,
                index: 0,
            }],
            vec![],
            vec![],
            // component_func_defs[0] = InstanceExportAlias(0). The
            // alias index doesn't matter for this test — the walker
            // returns empty without inspecting it.
            vec![ComponentFuncDef::InstanceExportAlias(0)],
        );
        let elems = export_stream_elements(&comp, "aliased");
        assert!(
            elems.is_empty(),
            "alias-export path should return empty until alias chains are walked; got {elems:?}"
        );
    }

    /// LS-R-11 layer-2 regression: when the importer's
    /// `stream<u8>` import is resolved to an exporter's Lift-defined
    /// `stream<s32>` export, the per-edge precise check MUST raise
    /// a TypeMismatch with the actual element types — not just
    /// "no element type pairs".
    #[test]
    fn ls_r_11_per_edge_lift_export_mismatch_raises() {
        let comp_a = make_component_with_func_defs(
            vec![ComponentImport {
                name: "data".into(),
                ty: wasmparser::ComponentTypeRef::Func(1),
            }],
            vec![],
            vec![stream_type("U8"), func_type_taking_stream(0)],
            vec![],
            vec![ComponentFuncDef::Import(0)],
        );
        let comp_b = make_component_with_func_defs(
            vec![],
            vec![ComponentExport {
                name: "data".into(),
                kind: ComponentExternalKind::Func,
                index: 0,
            }],
            vec![
                stream_type("S32"),         // types[0]: stream<S32> ≠ A's stream<U8>
                func_type_taking_stream(0), // types[1]: fn(stream<S32>)
            ],
            vec![CanonicalEntry::Lift {
                core_func_index: 0,
                type_index: 1,
                options: options(),
            }],
            vec![ComponentFuncDef::Lift(0)],
        );
        let components = vec![comp_a, comp_b];
        let mut resolved: HashMap<(usize, String), (usize, String)> = HashMap::new();
        resolved.insert((0, "data".into()), (1, "data".into()));
        let graph = StreamPairGraph::default();

        let issues = validate_stream_pair_graph(&components, &resolved, &graph);
        let mismatch = issues.iter().find_map(|i| match i {
            StreamValidationIssue::TypeMismatch {
                producer_component,
                consumer_component,
                producer_types,
                consumer_types,
            } => Some((
                *producer_component,
                *consumer_component,
                producer_types.clone(),
                consumer_types.clone(),
            )),
            _ => None,
        });
        let mismatch = mismatch.expect("expected exactly one TypeMismatch");
        // Per-edge: producer is the exporter (comp 1), consumer is
        // the importer (comp 0). Types are the precise element types
        // from each side's signature, not role-list multisets.
        assert_eq!(mismatch.0, 1, "producer_component should be the exporter");
        assert_eq!(mismatch.1, 0, "consumer_component should be the importer");
        assert_eq!(mismatch.2, vec![typed("S32")]);
        assert_eq!(mismatch.3, vec![typed("U8")]);
    }

    /// LS-R-11 layer-2: matching stream types on a resolved edge
    /// must NOT raise (precise check path, not the heuristic). Pins
    /// the no-false-positive property of the precise check.
    #[test]
    fn per_edge_matching_lift_export_does_not_raise() {
        let comp_a = make_component_with_func_defs(
            vec![ComponentImport {
                name: "data".into(),
                ty: wasmparser::ComponentTypeRef::Func(1),
            }],
            vec![],
            vec![stream_type("U8"), func_type_taking_stream(0)],
            vec![],
            vec![ComponentFuncDef::Import(0)],
        );
        let comp_b = make_component_with_func_defs(
            vec![],
            vec![ComponentExport {
                name: "data".into(),
                kind: ComponentExternalKind::Func,
                index: 0,
            }],
            vec![stream_type("U8"), func_type_taking_stream(0)],
            vec![CanonicalEntry::Lift {
                core_func_index: 0,
                type_index: 1,
                options: options(),
            }],
            vec![ComponentFuncDef::Lift(0)],
        );
        let components = vec![comp_a, comp_b];
        let mut resolved: HashMap<(usize, String), (usize, String)> = HashMap::new();
        resolved.insert((0, "data".into()), (1, "data".into()));
        let graph = StreamPairGraph::default();

        let issues = validate_stream_pair_graph(&components, &resolved, &graph);
        assert!(
            issues.is_empty(),
            "matching stream types on resolved edge must not raise; got {issues:?}"
        );
    }

    // ─── (iv) resource lifetime across async boundaries ──────────────

    /// Pin the wasmparser `ComponentValType::Type(N)` Debug form that
    /// `parse_type_index` depends on. If a wasmparser upgrade changes
    /// this, the resource-lifetime check would silently stop detecting
    /// handle elements — this test fails first.
    #[test]
    fn wasmparser_type_debug_form_is_stable() {
        assert_eq!(
            format!("{:?}", wasmparser::ComponentValType::Type(7)),
            "Type(7)"
        );
        assert_eq!(parse_type_index("Type(7)"), Some(7));
        assert_eq!(parse_type_index("Primitive(U8)"), None);
        assert_eq!(parse_type_index("List(..)"), None);
    }

    /// Build a component whose type table is all defined types, with a
    /// matching all-`Defined` `component_type_defs` so
    /// `get_type_definition(idx)` (and thus `resolve_to_resource`)
    /// resolves `Type(idx)` to `types[idx]`.
    fn comp_with_defined_types(types: Vec<ComponentType>) -> ParsedComponent {
        let defs = vec![crate::parser::ComponentTypeDef::Defined; types.len()];
        let mut c = make_component(vec![], vec![], types, vec![]);
        c.component_type_defs = defs;
        c
    }

    fn defined(vt: ComponentValType) -> ComponentType {
        ComponentType {
            kind: ComponentTypeKind::Defined(vt),
        }
    }

    #[test]
    fn ls_r_14_borrow_handle_in_stream_flagged() {
        // types[0] = stream<Type(1)>; types[1] = borrow<resource 42>.
        let comp = comp_with_defined_types(vec![
            stream_type("Type(1)"),
            defined(ComponentValType::Borrow(42)),
        ]);
        let issues = resource_lifetime_issues(&[comp]);
        assert_eq!(issues.len(), 1, "borrow-in-stream must flag: {issues:?}");
        match &issues[0] {
            StreamValidationIssue::ResourceLifetime {
                component,
                resource_type_id,
                owned,
                ..
            } => {
                assert_eq!(*component, 0);
                assert_eq!(*resource_type_id, 42);
                assert!(!owned, "borrow ⇒ owned = false");
            }
            other => panic!("expected ResourceLifetime, got {other:?}"),
        }
    }

    #[test]
    fn ls_r_14_own_handle_in_future_flagged_as_owned() {
        // types[0] = future<Type(1)>; types[1] = own<resource 5>.
        let future_ty = ComponentType {
            kind: ComponentTypeKind::P3Async("future<Type(1)>".to_string()),
        };
        let comp = comp_with_defined_types(vec![future_ty, defined(ComponentValType::Own(5))]);
        let issues = resource_lifetime_issues(&[comp]);
        assert_eq!(issues.len(), 1, "own-in-future must flag: {issues:?}");
        assert!(
            matches!(
                &issues[0],
                StreamValidationIssue::ResourceLifetime {
                    owned: true,
                    resource_type_id: 5,
                    ..
                }
            ),
            "own ⇒ owned = true; got {:?}",
            issues[0]
        );
    }

    #[test]
    fn ls_r_14_primitive_element_stream_not_flagged() {
        // A plain data stream carries no handle — must not flag.
        let comp = comp_with_defined_types(vec![
            stream_type("Primitive(U8)"),
            defined(ComponentValType::Primitive(PrimitiveValType::U8)),
        ]);
        assert!(
            resource_lifetime_issues(&[comp]).is_empty(),
            "primitive-element stream must not flag (iv)"
        );
    }

    // ─── #264: structural canonicalisation of aggregate stream elements ──

    fn prim(p: PrimitiveValType) -> ComponentValType {
        ComponentValType::Primitive(p)
    }

    /// Direct unit tests of the structural canonicaliser. Pins the key
    /// format and — crucially — its injectivity: structurally different
    /// types must produce different keys (the LS-R-16 safety property).
    #[test]
    fn canonical_key_format_and_injectivity() {
        // record { count: u8, data: list<s32> } at types[0].
        let rec = comp_with_defined_types(vec![defined(ComponentValType::Record(vec![
            ("count".into(), prim(PrimitiveValType::U8)),
            (
                "data".into(),
                ComponentValType::List(Box::new(prim(PrimitiveValType::S32))),
            ),
        ]))]);
        assert_eq!(
            canonical_structural_key(&rec, &ComponentValType::Type(0), 0).as_deref(),
            Some("record{count:u8,data:list<s32>}")
        );

        // tuple<u8, u8> vs record{f0:u8,f1:u8} — different structures, keys differ.
        let tup = comp_with_defined_types(vec![defined(ComponentValType::Tuple(vec![
            prim(PrimitiveValType::U8),
            prim(PrimitiveValType::U8),
        ]))]);
        assert_eq!(
            canonical_structural_key(&tup, &ComponentValType::Type(0), 0).as_deref(),
            Some("tuple<u8,u8>")
        );

        // Field-name sensitivity: record{a:u8} ≠ record{b:u8}.
        let rec_a = comp_with_defined_types(vec![defined(ComponentValType::Record(vec![(
            "a".into(),
            prim(PrimitiveValType::U8),
        )]))]);
        let rec_b = comp_with_defined_types(vec![defined(ComponentValType::Record(vec![(
            "b".into(),
            prim(PrimitiveValType::U8),
        )]))]);
        assert_ne!(
            canonical_structural_key(&rec_a, &ComponentValType::Type(0), 0),
            canonical_structural_key(&rec_b, &ComponentValType::Type(0), 0),
            "field-name difference must yield different structural keys"
        );

        // option / result / variant / flags / fixed-list spellings.
        let opt = comp_with_defined_types(vec![defined(ComponentValType::Option(Box::new(prim(
            PrimitiveValType::U32,
        ))))]);
        assert_eq!(
            canonical_structural_key(&opt, &ComponentValType::Type(0), 0).as_deref(),
            Some("option<u32>")
        );
        let res = comp_with_defined_types(vec![defined(ComponentValType::Result {
            ok: Some(Box::new(prim(PrimitiveValType::U8))),
            err: None,
        })]);
        assert_eq!(
            canonical_structural_key(&res, &ComponentValType::Type(0), 0).as_deref(),
            Some("result<u8,_>")
        );
        let var = comp_with_defined_types(vec![defined(ComponentValType::Variant(vec![
            ("none".into(), None),
            ("some".into(), Some(prim(PrimitiveValType::U8))),
        ]))]);
        assert_eq!(
            canonical_structural_key(&var, &ComponentValType::Type(0), 0).as_deref(),
            Some("variant{none,some(u8)}")
        );
        let fl = comp_with_defined_types(vec![defined(ComponentValType::Flags(vec![
            "a".into(),
            "b".into(),
        ]))]);
        assert_eq!(
            canonical_structural_key(&fl, &ComponentValType::Type(0), 0).as_deref(),
            Some("flags{a,b}")
        );
        let fll = comp_with_defined_types(vec![defined(ComponentValType::FixedSizeList(
            Box::new(prim(PrimitiveValType::U8)),
            4,
        ))]);
        assert_eq!(
            canonical_structural_key(&fll, &ComponentValType::Type(0), 0).as_deref(),
            Some("fixed-list<u8,4>")
        );
    }

    /// Conservative: a resource handle anywhere in the element type → None,
    /// so the stream stays non-pairable / host-routed (#256 deferred).
    #[test]
    fn canonical_key_resource_returns_none() {
        let own = comp_with_defined_types(vec![defined(ComponentValType::Own(7))]);
        assert_eq!(
            canonical_structural_key(&own, &ComponentValType::Type(0), 0),
            None,
            "own<R> element must not canonicalise"
        );
        // Nested handle: record { h: own<R> } — still None.
        let nested = comp_with_defined_types(vec![defined(ComponentValType::Record(vec![(
            "h".into(),
            ComponentValType::Own(7),
        )]))]);
        assert_eq!(
            canonical_structural_key(&nested, &ComponentValType::Type(0), 0),
            None,
            "a handle nested inside a record must still force None"
        );
    }

    /// Cycle / unbounded-nest guard: a `Type(N)` that refers to itself
    /// must terminate and return None rather than recurse forever.
    #[test]
    fn canonical_key_self_cycle_returns_none() {
        // types[0] = list<Type(0)> — a self-referential alias cycle.
        let cyclic = comp_with_defined_types(vec![defined(ComponentValType::List(Box::new(
            ComponentValType::Type(0),
        )))]);
        assert_eq!(
            canonical_structural_key(&cyclic, &ComponentValType::Type(0), 0),
            None,
            "a self-referential type must hit the depth bound and return None"
        );
    }

    /// Helper: a component whose types are `[stream<Type(1)>, defined(elem)]`
    /// with a `StreamWrite`/`StreamRead` role on the stream type at index 0.
    /// The stream's element sits at LOCAL index 1.
    fn stream_role_component(elem: ComponentValType, role: CanonicalEntry) -> ParsedComponent {
        let mut c = comp_with_defined_types(vec![stream_type("Type(1)"), defined(elem)]);
        c.canonical_functions = vec![role];
        c
    }

    /// Same, but the element type is placed at a DIFFERENT local index so
    /// the two components cannot share a raw `Type(N)` string — only a
    /// structural key can match them. types = [pad, stream<Type(2)>, elem];
    /// stream type is at index 1.
    fn stream_role_component_shifted(
        elem: ComponentValType,
        role: CanonicalEntry,
    ) -> ParsedComponent {
        let mut c = comp_with_defined_types(vec![
            defined(prim(PrimitiveValType::Bool)), // padding at index 0
            stream_type("Type(2)"),
            defined(elem),
        ]);
        // The role references the stream type, which is now at index 1.
        let role = match role {
            CanonicalEntry::StreamWrite { options, .. } => {
                CanonicalEntry::StreamWrite { ty: 1, options }
            }
            CanonicalEntry::StreamRead { options, .. } => {
                CanonicalEntry::StreamRead { ty: 1, options }
            }
            other => other,
        };
        c.canonical_functions = vec![role];
        c
    }

    fn record_count_data() -> ComponentValType {
        ComponentValType::Record(vec![
            ("count".into(), prim(PrimitiveValType::U8)),
            (
                "data".into(),
                ComponentValType::List(Box::new(prim(PrimitiveValType::S32))),
            ),
        ])
    }

    /// POSITIVE (#264 / LS-R-16 Finding-A, now enabled): a producer and a
    /// consumer share a genuine aggregate element type T, but at DIFFERENT
    /// local type indices. Structural canonicalisation makes their keys
    /// equal, so exactly ONE pair is detected. Non-vacuity: the producer's
    /// element lives at local index 1 and the consumer's at index 2, so a
    /// raw-`Type(N)`-string comparison (the pre-#264 behaviour) would NOT
    /// have matched them — only structural equality does.
    #[test]
    fn structural_aggregate_pairs_across_different_local_indices() {
        let producer = stream_role_component(
            record_count_data(),
            CanonicalEntry::StreamWrite {
                ty: 0,
                options: options(),
            },
        );
        let consumer = stream_role_component_shifted(
            record_count_data(),
            CanonicalEntry::StreamRead {
                ty: 0,
                options: options(),
            },
        );

        // Precondition: the two endpoints' raw local indices differ
        // (producer at Type(1), consumer at Type(2)) — proves the match is
        // structural, not a coincidental shared index.
        let p_roles = component_stream_roles(&producer);
        let c_roles = component_stream_roles(&consumer);
        assert_eq!(
            p_roles,
            vec![(
                typed("record{count:u8,data:list<s32>}"),
                StreamRole::Producer
            )],
            "producer element should canonicalise to the structural key"
        );
        assert_eq!(
            c_roles,
            vec![(
                typed("record{count:u8,data:list<s32>}"),
                StreamRole::Consumer
            )],
            "consumer element should canonicalise to the same structural key"
        );

        let roles = vec![p_roles, c_roles];
        let pairs = pair_streams(&roles, &[(0, 1)], StreamMemoryMode::CrossMemory);
        assert_eq!(
            pairs.len(),
            1,
            "structurally identical aggregate elements must pair exactly once; got {pairs:?}"
        );
        assert_eq!(pairs[0].element, typed("record{count:u8,data:list<s32>}"));
    }

    /// NEGATIVE / over-match still prevented (the critical regression
    /// guard): two DIFFERENT aggregate types that sit at the SAME local
    /// index in their respective components must NOT pair. A key collision
    /// here would re-introduce the exact LS-R-16 over-match. Producer's
    /// element is `record{count:u8,data:list<s32>}`, consumer's is
    /// `tuple<u8,u8>` — both at local index 1.
    #[test]
    fn structurally_different_aggregates_at_same_index_do_not_pair() {
        let producer = stream_role_component(
            record_count_data(),
            CanonicalEntry::StreamWrite {
                ty: 0,
                options: options(),
            },
        );
        let consumer = stream_role_component(
            ComponentValType::Tuple(vec![prim(PrimitiveValType::U8), prim(PrimitiveValType::U8)]),
            CanonicalEntry::StreamRead {
                ty: 0,
                options: options(),
            },
        );

        let p_roles = component_stream_roles(&producer);
        let c_roles = component_stream_roles(&consumer);
        // Both came from local Type(1) but their structural keys differ.
        assert_eq!(
            p_roles,
            vec![(
                typed("record{count:u8,data:list<s32>}"),
                StreamRole::Producer
            )]
        );
        assert_eq!(c_roles, vec![(typed("tuple<u8,u8>"), StreamRole::Consumer)]);

        let roles = vec![p_roles, c_roles];
        let pairs = pair_streams(&roles, &[(0, 1)], StreamMemoryMode::CrossMemory);
        assert!(
            pairs.is_empty(),
            "different aggregate types at the same local index must NOT pair \
             (over-match prevention); got {pairs:?}"
        );
    }

    /// RESOURCE conservative: a `stream<own<R>>` element keeps its raw
    /// `Type(N)` descriptor (canonicalisation declines resources) and so
    /// stays non-pairable / host-routed — exactly today's behaviour, the
    /// #256 boundary.
    #[test]
    fn resource_element_stream_stays_host_routed() {
        let producer = stream_role_component(
            ComponentValType::Own(42),
            CanonicalEntry::StreamWrite {
                ty: 0,
                options: options(),
            },
        );
        let consumer = stream_role_component(
            ComponentValType::Own(42),
            CanonicalEntry::StreamRead {
                ty: 0,
                options: options(),
            },
        );
        let p_roles = component_stream_roles(&producer);
        let c_roles = component_stream_roles(&consumer);
        // Element kept its raw local-index descriptor (not canonicalised).
        assert_eq!(p_roles, vec![(typed("Type(1)"), StreamRole::Producer)]);
        assert_eq!(c_roles, vec![(typed("Type(1)"), StreamRole::Consumer)]);

        let roles = vec![p_roles, c_roles];
        let pairs = pair_streams(&roles, &[(0, 1)], StreamMemoryMode::CrossMemory);
        assert!(
            pairs.is_empty(),
            "resource-handle stream elements must stay host-routed (#256); got {pairs:?}"
        );
    }
}
