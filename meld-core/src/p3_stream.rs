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

use crate::parser::{CanonicalEntry, ComponentTypeKind, ParsedComponent};
use std::collections::HashMap;

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
fn stream_element_of_type(comp: &ParsedComponent, ty: u32) -> Option<StreamElement> {
    match &comp.types.get(ty as usize)?.kind {
        ComponentTypeKind::P3Async(desc) => StreamElement::from_descriptor(desc),
        _ => None,
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
}
