//! # P3 async lowering — host-intrinsic ABI
//!
//! This module defines the **build-time ABI** that meld lowers P3 async
//! constructs (`stream<T>`, `future<T>`, async lift/lower) **to**, and
//! provides detection helpers used by the parser and fuser.
//!
//! ## Why a host-intrinsic ABI?
//!
//! Per RFC #46 (toolchain architecture), meld is a *static fusion* tool:
//! everything that can be resolved at build time is resolved at build time,
//! and everything else is lowered to a documented import surface that the
//! runtime (kiln, wasmtime, …) implements.
//!
//! Async constructs (`stream<T>`, `future<T>`) cannot be resolved statically
//! because they represent temporal data flow. They CAN, however, be lowered
//! to import calls against a fixed ABI. Meld emits these imports; consumers
//! provide the implementation.
//!
//! ## ABI surface (`pulseengine:async`)
//!
//! All host intrinsics live in the import module **`pulseengine:async`**.
//! The intrinsic surface is intentionally minimal — it is the
//! lowest-common-denominator over what P3 async constructs need at the core
//! WebAssembly level, after canonical lift/lower has been applied.
//!
//! Stream operations (handle is the canonical ABI stream handle, `i32`):
//!
//! | Function                    | Signature                              | Semantics |
//! |-----------------------------|----------------------------------------|-----------|
//! | `stream_new`                | `() -> i64`                            | Allocate a new stream handle pair. Low 32 bits = readable end, high 32 bits = writable end. |
//! | `stream_read`               | `(handle: i32, buf_ptr: i32, buf_len: i32, mem_idx: i32) -> i32` | Read up to `buf_len` bytes into `buf_ptr` of memory `mem_idx`. Returns bytes read (0 = EOF, negative = error code). |
//! | `stream_write`              | `(handle: i32, data_ptr: i32, data_len: i32, mem_idx: i32) -> i32` | Write `data_len` bytes from `data_ptr`. Returns bytes accepted (may be < `data_len` for backpressure). |
//! | `stream_cancel_read`        | `(handle: i32) -> i32`                 | Cancel a pending read. Returns 1 if cancelled, 0 if no read was pending. |
//! | `stream_cancel_write`       | `(handle: i32) -> i32`                 | Cancel a pending write. |
//! | `stream_drop_readable`      | `(handle: i32)`                        | Drop the readable end. Closing both ends destroys the stream. |
//! | `stream_drop_writable`      | `(handle: i32)`                        | Drop the writable end. |
//!
//! Future operations (handle is `i32`):
//!
//! | Function                    | Signature                              | Semantics |
//! |-----------------------------|----------------------------------------|-----------|
//! | `future_new`                | `() -> i64`                            | Allocate a new future handle pair. Low 32 = read end, high 32 = write end. |
//! | `future_read`               | `(handle: i32, buf_ptr: i32, mem_idx: i32) -> i32` | Read the resolved value into `buf_ptr` (size = canonical layout of `T`). Returns 1 if resolved, 0 if not yet, negative = error. |
//! | `future_write`              | `(handle: i32, data_ptr: i32, mem_idx: i32) -> i32` | Resolve the future. |
//! | `future_cancel_read`        | `(handle: i32) -> i32`                 | Cancel a pending read. |
//! | `future_cancel_write`       | `(handle: i32) -> i32`                 | Cancel a pending write. |
//! | `future_drop_readable`      | `(handle: i32)`                        | Drop the readable end. |
//! | `future_drop_writable`      | `(handle: i32)`                        | Drop the writable end. |
//!
//! ### Design notes
//!
//! * **Element width is hidden in the handle.** A `stream<u8>` and a
//!   `stream<record { x: u32, y: u32 }>` use the *same* `stream_read` /
//!   `stream_write` primitives. The byte-level canonical-ABI lowering of
//!   `T` happens in adapter glue meld emits *around* the call. This keeps
//!   the host intrinsic count constant.
//! * **`mem_idx` parameter** is required because meld supports
//!   multi-memory components (each fused component keeps its own memory).
//!   The runtime needs to know which memory to read/write.
//! * **Backpressure** is exposed via the bytes-written return: a write that
//!   accepts fewer bytes than requested means the consumer is slow and the
//!   producer should retry. There is no separate "wait" primitive — that
//!   composes with the existing `[waitable-set-wait]` builtin already
//!   handled by `component_wrap.rs`.
//! * **No async-export callback intrinsics here.** Async exports are
//!   already handled by meld's existing P3 callback-driving adapter
//!   (`component_wrap.rs::generate_callback_driving_adapter`). This module
//!   only provides the *data-plane* (stream/future) intrinsics.
//!
//! ## Detection
//!
//! [`P3AsyncFeatures`] summarises what P3 async constructs a parsed component
//! contains. [`detect_features`] inspects a [`crate::parser::ParsedComponent`]
//! and returns the summary. This is a **pure inspection** — it never
//! mutates the component.
//!
//! ## Scope of the foundation PR (#94 partial)
//!
//! This module ships the **detection + ABI documentation** layer. The
//! actual lowering pass (rewriting `(canon stream.new)` etc. to import
//! calls in the fused output) is split out per the ADR; tracker issues
//! list the deferred work.

use crate::parser::{CanonicalEntry, ComponentTypeKind, ParsedComponent};

/// Import module name used for all P3 async host intrinsics emitted by
/// meld. The runtime (kiln, wasmtime, …) is expected to satisfy these
/// imports.
pub const HOST_INTRINSIC_MODULE: &str = "pulseengine:async";

/// Names of all stream-related host intrinsic imports.
pub mod stream {
    /// `() -> i64` — allocate a new stream. Returns packed (write << 32 | read).
    pub const NEW: &str = "stream_new";
    /// `(i32, i32, i32, i32) -> i32` — `(handle, buf_ptr, buf_len, mem_idx)`.
    pub const READ: &str = "stream_read";
    /// `(i32, i32, i32, i32) -> i32` — `(handle, data_ptr, data_len, mem_idx)`.
    pub const WRITE: &str = "stream_write";
    /// `(i32) -> i32` — cancel a pending read on the given handle.
    pub const CANCEL_READ: &str = "stream_cancel_read";
    /// `(i32) -> i32` — cancel a pending write on the given handle.
    pub const CANCEL_WRITE: &str = "stream_cancel_write";
    /// `(i32) -> ()` — drop the readable end of the stream.
    pub const DROP_READABLE: &str = "stream_drop_readable";
    /// `(i32) -> ()` — drop the writable end of the stream.
    pub const DROP_WRITABLE: &str = "stream_drop_writable";
}

/// Names of all future-related host intrinsic imports.
pub mod future {
    /// `() -> i64` — allocate a new future. Returns packed (write << 32 | read).
    pub const NEW: &str = "future_new";
    /// `(i32, i32, i32) -> i32` — `(handle, buf_ptr, mem_idx)`.
    pub const READ: &str = "future_read";
    /// `(i32, i32, i32) -> i32` — `(handle, data_ptr, mem_idx)`.
    pub const WRITE: &str = "future_write";
    /// `(i32) -> i32` — cancel a pending read on the given future.
    pub const CANCEL_READ: &str = "future_cancel_read";
    /// `(i32) -> i32` — cancel a pending write on the given future.
    pub const CANCEL_WRITE: &str = "future_cancel_write";
    /// `(i32) -> ()` — drop the readable end of the future.
    pub const DROP_READABLE: &str = "future_drop_readable";
    /// `(i32) -> ()` — drop the writable end of the future.
    pub const DROP_WRITABLE: &str = "future_drop_writable";
}

/// A specific P3 async canonical built-in, mapped to the host intrinsic
/// it lowers to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HostIntrinsic {
    StreamNew,
    StreamRead,
    StreamWrite,
    StreamCancelRead,
    StreamCancelWrite,
    StreamDropReadable,
    StreamDropWritable,
    FutureNew,
    FutureRead,
    FutureWrite,
    FutureCancelRead,
    FutureCancelWrite,
    FutureDropReadable,
    FutureDropWritable,
}

impl HostIntrinsic {
    /// The unqualified intrinsic name (the `name` half of the import).
    pub const fn name(self) -> &'static str {
        match self {
            Self::StreamNew => stream::NEW,
            Self::StreamRead => stream::READ,
            Self::StreamWrite => stream::WRITE,
            Self::StreamCancelRead => stream::CANCEL_READ,
            Self::StreamCancelWrite => stream::CANCEL_WRITE,
            Self::StreamDropReadable => stream::DROP_READABLE,
            Self::StreamDropWritable => stream::DROP_WRITABLE,
            Self::FutureNew => future::NEW,
            Self::FutureRead => future::READ,
            Self::FutureWrite => future::WRITE,
            Self::FutureCancelRead => future::CANCEL_READ,
            Self::FutureCancelWrite => future::CANCEL_WRITE,
            Self::FutureDropReadable => future::DROP_READABLE,
            Self::FutureDropWritable => future::DROP_WRITABLE,
        }
    }

    /// Fully qualified import: `(HOST_INTRINSIC_MODULE, name())`.
    pub const fn import(self) -> (&'static str, &'static str) {
        (HOST_INTRINSIC_MODULE, self.name())
    }

    /// Map a parsed `CanonicalEntry` to its host intrinsic, if any.
    /// Returns `None` for non-async canonicals (lift/lower/resource ops).
    pub fn from_canonical_entry(entry: &CanonicalEntry) -> Option<Self> {
        match entry {
            CanonicalEntry::StreamNew { .. } => Some(Self::StreamNew),
            CanonicalEntry::StreamRead { .. } => Some(Self::StreamRead),
            CanonicalEntry::StreamWrite { .. } => Some(Self::StreamWrite),
            CanonicalEntry::StreamCancelRead { .. } => Some(Self::StreamCancelRead),
            CanonicalEntry::StreamCancelWrite { .. } => Some(Self::StreamCancelWrite),
            CanonicalEntry::StreamDropReadable { .. } => Some(Self::StreamDropReadable),
            CanonicalEntry::StreamDropWritable { .. } => Some(Self::StreamDropWritable),
            CanonicalEntry::FutureNew { .. } => Some(Self::FutureNew),
            CanonicalEntry::FutureRead { .. } => Some(Self::FutureRead),
            CanonicalEntry::FutureWrite { .. } => Some(Self::FutureWrite),
            CanonicalEntry::FutureCancelRead { .. } => Some(Self::FutureCancelRead),
            CanonicalEntry::FutureCancelWrite { .. } => Some(Self::FutureCancelWrite),
            CanonicalEntry::FutureDropReadable { .. } => Some(Self::FutureDropReadable),
            CanonicalEntry::FutureDropWritable { .. } => Some(Self::FutureDropWritable),
            _ => None,
        }
    }
}

/// Summary of P3 async features used by a parsed component.
///
/// Built by [`detect_features`]. Use [`is_empty`](Self::is_empty) to check
/// whether a component is "P3-async-clean" (no async features).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct P3AsyncFeatures {
    /// Component-level types that are `stream<T>`. Stored as type-index → human-readable description.
    pub stream_types: Vec<(u32, String)>,
    /// Component-level types that are `future<T>`.
    pub future_types: Vec<(u32, String)>,
    /// Distinct host intrinsics that meld would emit imports for, given
    /// the canonical built-ins this component already declares.
    pub required_intrinsics: Vec<HostIntrinsic>,
    /// Whether any canonical lift uses `(canon lift ... async ...)`.
    pub uses_async_lift: bool,
    /// Whether any canonical lift carries a `(callback ...)` option (P3
    /// callback mode for async exports).
    pub uses_callback_lift: bool,
    /// Whether any canonical lower uses `(canon lower ... async ...)`.
    pub uses_async_lower: bool,
}

impl P3AsyncFeatures {
    /// `true` if the component uses no P3 async constructs at all.
    pub fn is_empty(&self) -> bool {
        self.stream_types.is_empty()
            && self.future_types.is_empty()
            && self.required_intrinsics.is_empty()
            && !self.uses_async_lift
            && !self.uses_callback_lift
            && !self.uses_async_lower
    }

    /// `true` if the component uses any *data-plane* (stream/future) construct.
    pub fn uses_data_plane(&self) -> bool {
        !self.stream_types.is_empty()
            || !self.future_types.is_empty()
            || !self.required_intrinsics.is_empty()
    }

    /// `true` if the component uses any *control-plane* (async lift/lower /
    /// callback) construct.
    pub fn uses_control_plane(&self) -> bool {
        self.uses_async_lift || self.uses_callback_lift || self.uses_async_lower
    }
}

/// Inspect a parsed component and summarise its P3 async usage.
///
/// Pure inspection — does not mutate `comp`.
pub fn detect_features(comp: &ParsedComponent) -> P3AsyncFeatures {
    let mut feats = P3AsyncFeatures::default();
    let mut required: std::collections::BTreeSet<HostIntrinsic> = std::collections::BTreeSet::new();

    // Walk component-level types looking for stream/future declarations.
    for (idx, ty) in comp.types.iter().enumerate() {
        if let ComponentTypeKind::P3Async(desc) = &ty.kind {
            if desc.contains("stream") {
                feats.stream_types.push((idx as u32, desc.clone()));
            } else if desc.contains("future") {
                feats.future_types.push((idx as u32, desc.clone()));
            }
            // `map<K,V>` is also P3Async but not handled by this ABI;
            // it's tracked in `comp.p3_async_features` for the warning path.
        }
    }

    // Walk canonicals to find any data-plane intrinsic the component
    // already declares, and detect async lift/lower options.
    for entry in &comp.canonical_functions {
        if let Some(intr) = HostIntrinsic::from_canonical_entry(entry) {
            required.insert(intr);
        }
        match entry {
            CanonicalEntry::Lift { options, .. } => {
                if options.async_ {
                    feats.uses_async_lift = true;
                }
                if options.callback.is_some() {
                    feats.uses_callback_lift = true;
                }
            }
            CanonicalEntry::Lower { options, .. } if options.async_ => {
                feats.uses_async_lower = true;
            }
            _ => {}
        }
    }

    feats.required_intrinsics = required.into_iter().collect();
    feats
}

// `BTreeSet<HostIntrinsic>` requires `Ord`. Provide a deterministic ordering.
impl PartialOrd for HostIntrinsic {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for HostIntrinsic {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (*self as u8).cmp(&(*other as u8))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{
        CanonStringEncoding, CanonicalEntry, CanonicalOptions, ComponentType, ComponentTypeKind,
    };

    fn empty_component() -> ParsedComponent {
        // Use the same test helper pattern parser.rs uses.
        ParsedComponent {
            name: None,
            core_modules: vec![],
            imports: vec![],
            exports: vec![],
            types: vec![],
            instances: vec![],
            canonical_functions: vec![],
            sub_components: vec![],
            component_aliases: vec![],
            component_instances: vec![],
            core_entity_order: vec![],
            component_func_defs: vec![],
            component_instance_defs: vec![],
            component_type_defs: vec![],
            original_size: 0,
            original_hash: String::new(),
            depth_0_sections: vec![],
            p3_async_features: vec![],
        }
    }

    #[test]
    fn empty_component_has_no_p3_features() {
        let comp = empty_component();
        let feats = detect_features(&comp);
        assert!(feats.is_empty());
        assert!(!feats.uses_data_plane());
        assert!(!feats.uses_control_plane());
    }

    #[test]
    fn stream_type_is_detected() {
        let mut comp = empty_component();
        comp.types.push(ComponentType {
            kind: ComponentTypeKind::P3Async("stream<u8>".to_string()),
        });
        let feats = detect_features(&comp);
        assert!(!feats.is_empty());
        assert_eq!(feats.stream_types.len(), 1);
        assert!(feats.stream_types[0].1.contains("stream"));
        assert!(feats.uses_data_plane());
    }

    #[test]
    fn future_type_is_detected() {
        let mut comp = empty_component();
        comp.types.push(ComponentType {
            kind: ComponentTypeKind::P3Async("future<string>".to_string()),
        });
        let feats = detect_features(&comp);
        assert_eq!(feats.future_types.len(), 1);
        assert!(feats.uses_data_plane());
    }

    #[test]
    fn stream_canonical_maps_to_intrinsic() {
        let mut comp = empty_component();
        comp.canonical_functions
            .push(CanonicalEntry::StreamNew { ty: 0 });
        comp.canonical_functions.push(CanonicalEntry::StreamRead {
            ty: 0,
            options: CanonicalOptions::default(),
        });
        comp.canonical_functions
            .push(CanonicalEntry::StreamDropReadable { ty: 0 });

        let feats = detect_features(&comp);
        assert!(
            feats
                .required_intrinsics
                .contains(&HostIntrinsic::StreamNew)
        );
        assert!(
            feats
                .required_intrinsics
                .contains(&HostIntrinsic::StreamRead)
        );
        assert!(
            feats
                .required_intrinsics
                .contains(&HostIntrinsic::StreamDropReadable)
        );
        // De-duplicated even if declared twice
        comp.canonical_functions.push(CanonicalEntry::StreamRead {
            ty: 0,
            options: CanonicalOptions::default(),
        });
        let feats2 = detect_features(&comp);
        assert_eq!(
            feats2
                .required_intrinsics
                .iter()
                .filter(|i| **i == HostIntrinsic::StreamRead)
                .count(),
            1
        );
    }

    #[test]
    fn async_lift_detected() {
        let mut comp = empty_component();
        let opts = CanonicalOptions {
            string_encoding: CanonStringEncoding::Utf8,
            memory: Some(0),
            realloc: None,
            post_return: None,
            async_: true,
            callback: Some(7),
        };
        comp.canonical_functions.push(CanonicalEntry::Lift {
            core_func_index: 0,
            type_index: 0,
            options: opts,
        });
        let feats = detect_features(&comp);
        assert!(feats.uses_async_lift);
        assert!(feats.uses_callback_lift);
        assert!(feats.uses_control_plane());
    }

    #[test]
    fn intrinsic_imports_have_pulseengine_module() {
        for intr in [
            HostIntrinsic::StreamNew,
            HostIntrinsic::StreamRead,
            HostIntrinsic::StreamWrite,
            HostIntrinsic::FutureNew,
            HostIntrinsic::FutureRead,
        ] {
            let (module, name) = intr.import();
            assert_eq!(module, "pulseengine:async");
            assert!(!name.is_empty());
            assert!(!name.contains(' '));
        }
    }

    #[test]
    fn intrinsic_names_are_distinct() {
        let all = [
            HostIntrinsic::StreamNew,
            HostIntrinsic::StreamRead,
            HostIntrinsic::StreamWrite,
            HostIntrinsic::StreamCancelRead,
            HostIntrinsic::StreamCancelWrite,
            HostIntrinsic::StreamDropReadable,
            HostIntrinsic::StreamDropWritable,
            HostIntrinsic::FutureNew,
            HostIntrinsic::FutureRead,
            HostIntrinsic::FutureWrite,
            HostIntrinsic::FutureCancelRead,
            HostIntrinsic::FutureCancelWrite,
            HostIntrinsic::FutureDropReadable,
            HostIntrinsic::FutureDropWritable,
        ];
        let names: std::collections::HashSet<&'static str> = all.iter().map(|i| i.name()).collect();
        assert_eq!(names.len(), all.len(), "intrinsic names must be unique");
    }
}
