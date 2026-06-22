//! Adapter generation for cross-component calls
//!
//! This module provides the abstraction layer for generating adapter functions
//! (trampolines) that handle the Canonical ABI lifting/lowering between components.
//!
//! ## Architecture
//!
//! The adapter system is designed with an abstraction layer to allow different
//! implementations:
//!
//! - `FactStyleGenerator`: FACT-style adapter generation (like wasmtime's FACT)
//! - `NativeGenerator`: Future standalone implementation
//!
//! ## What Adapters Do
//!
//! When component A calls a function in component B, the adapter:
//! 1. Reads arguments from A's linear memory (lowering)
//! 2. Converts/copies data as needed (e.g., string transcoding)
//! 3. Calls the target function in B
//! 4. Writes results back to A's memory (lifting)

pub(crate) mod fact;

pub use fact::FactStyleGenerator;

/// Test-support: build the #272 inc-1 UTF-8 → UTF-16 transcode oracle module.
/// `#[doc(hidden)]` — not a supported API; see the function's own docs.
#[doc(hidden)]
pub use fact::build_utf8_to_utf16_transcode_test_module;

/// Test-support: build the #272 inc-2 UTF-16 → UTF-8 transcode oracle module.
/// `#[doc(hidden)]` — not a supported API; see the function's own docs.
#[doc(hidden)]
pub use fact::build_utf16_to_utf8_transcode_test_module;

/// Test-support: build the #272 inc-4a latin1+utf16 → UTF-16 transcode oracle
/// module. `#[doc(hidden)]` — not a supported API; see the function's own docs.
#[doc(hidden)]
pub use fact::build_latin1_to_utf16_transcode_test_module;

/// Test-support: build the #272 inc-4a latin1+utf16 → UTF-8 transcode oracle
/// module. `#[doc(hidden)]` — not a supported API; see the function's own docs.
#[doc(hidden)]
pub use fact::build_latin1_to_utf8_transcode_test_module;

/// Test-support: build the #272 inc-4b UTF-8 → latin1+utf16 (DEST-latin1,
/// tag-PRODUCING) transcode oracle module. `#[doc(hidden)]` — not a supported
/// API; see the function's own docs.
#[doc(hidden)]
pub use fact::build_utf8_to_latin1_transcode_test_module;

/// Test-support: build the #272 inc-4b UTF-16 → latin1+utf16 (DEST-latin1,
/// tag-PRODUCING) transcode oracle module. `#[doc(hidden)]` — not a supported
/// API; see the function's own docs.
#[doc(hidden)]
pub use fact::build_utf16_to_latin1_transcode_test_module;

/// Test-support: build the #272 inc-5a NESTED `list<string>` RESULT transcode
/// (UTF-8 → UTF-16) oracle module. `#[doc(hidden)]` — not a supported API; see
/// the function's own docs.
#[doc(hidden)]
pub use fact::build_nested_list_string_utf8_to_utf16_result_test_module;

/// Test-support: build the #272 inc-5a NESTED `list<u8>` RESULT NOT-transcoded
/// (raw-copied) oracle module. `#[doc(hidden)]` — not a supported API; see the
/// function's own docs.
#[doc(hidden)]
pub use fact::build_nested_list_u8_result_not_transcoded_test_module;

/// Test-support: build the #272 inc-5b NESTED `list<string>` RESULT transcode
/// oracle module for an ARBITRARY result direction (`callee_enc → caller_enc`).
/// `#[doc(hidden)]` — not a supported API; see the function's own docs.
#[doc(hidden)]
pub use fact::build_nested_list_string_result_test_module;

/// Test-support: build the #286 5d DEPTH-2 NESTED `list<list<string>>` RESULT
/// transcode oracle module (exercises the codegen-time recursion).
/// `#[doc(hidden)]` — not a supported API; see the function's own docs.
#[doc(hidden)]
pub use fact::build_nested_list_list_string_result_test_module;

/// Test-support: build the #272 inc-5c-a NESTED `list<string>` PARAM transcode
/// (UTF-8 → UTF-16) oracle module. `#[doc(hidden)]` — not a supported API; see
/// the function's own docs.
#[doc(hidden)]
pub use fact::build_nested_list_string_utf8_to_utf16_param_test_module;

/// Test-support: build the #272 inc-5c-a NESTED `list<u8>` PARAM deep-copied
/// (NOT transcoded — closes #281) oracle module. `#[doc(hidden)]` — not a
/// supported API; see the function's own docs.
#[doc(hidden)]
pub use fact::build_nested_list_u8_param_deep_copied_test_module;

/// Test-support: build the #272 inc-5c-b NESTED `list<string>` PARAM transcode
/// oracle module for an ARBITRARY param direction (`caller_enc → callee_enc`).
/// `#[doc(hidden)]` — not a supported API; see the function's own docs.
#[doc(hidden)]
pub use fact::build_nested_list_string_param_test_module;

/// Test-support: build the #286 5d DEPTH-2 NESTED `list<list<string>>` PARAM
/// transcode oracle module (exercises the codegen-time param recursion).
/// `#[doc(hidden)]` — not a supported API; see the function's own docs.
#[doc(hidden)]
pub use fact::build_nested_list_list_string_param_test_module;

use crate::Result;
use crate::merger::MergedModule;
use crate::resolver::DependencyGraph;
use wasm_encoder::Function;

/// Configuration for adapter generation
#[derive(Debug, Clone)]
pub struct AdapterConfig {
    /// Whether to inline adapter code instead of generating separate functions
    pub inline_adapters: bool,

    /// Whether to optimize string copies (reuse buffers when possible)
    pub optimize_string_copies: bool,
}

impl Default for AdapterConfig {
    fn default() -> Self {
        Self {
            inline_adapters: true,
            optimize_string_copies: true,
        }
    }
}

/// Class of a generated adapter, at the granularity meld actually emits
/// (#144 inc 4 / #130 §Phase 3).
///
/// #130 sketched per-class attribution as "transcode / cabi_realloc /
/// lift / lower", assuming wasmtime-FACT-style separate functions. meld
/// emits ONE fused trampoline per call site, with lowering, allocation
/// (a call to the callee's own `cabi_realloc`, not a meld-emitted one),
/// copying, and lifting inline in that body — so the honest class
/// granularity is per-trampoline-kind, matching the generator's actual
/// dispatch. Consumed by `dwarf::adapter_spans` to assign per-class
/// `<meld-adapter>` line numbers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdapterClass {
    /// Thin call shim — same memory, no transcoding (direct adapter).
    Direct,
    /// Cross-memory `(ptr, len)` copy chain: lower → `cabi_realloc`
    /// call → `memory.copy` → lift, fused in one body.
    MemoryCopy,
    /// Cross-memory + string-encoding conversion (UTF-8/UTF-16/Latin-1
    /// transcode loop) fused in one body.
    Transcode,
    /// P3 async adapter (callback-driving or stackful trampoline).
    Async,
}

/// A generated adapter function
#[derive(Debug, Clone)]
pub struct AdapterFunction {
    /// Name for debugging/tracing
    pub name: String,

    /// Type index in merged type section
    pub type_idx: u32,

    /// Function body
    pub body: Function,

    /// Source call site this adapts
    pub source_component: usize,
    pub source_module: usize,

    /// Target call site
    pub target_component: usize,
    pub target_module: usize,
    pub target_function: u32,

    /// Emitter class, for synthetic DWARF attribution (#144 inc 4).
    pub class: AdapterClass,

    /// #304: when this adapter is a *pure identity trampoline* (a `Direct`
    /// adapter whose body only re-pushes params and `call`s the target — no
    /// transcoding, no resource conversion, no post-return), and adapter
    /// inlining is enabled, this holds the target function's merged index.
    /// `wire_adapter_indices` then wires the caller's import **directly** to the
    /// target instead of to this thunk, so no forwarding indirection is
    /// interposed at runtime; the now-unreferenced adapter is left for loom to
    /// DCE. `None` means "keep the thunk" (the conservative default — set only
    /// when the no-op forwarding is provable). See `inline_adapters`.
    pub inline_target: Option<u32>,
}

/// Trait for adapter generators
///
/// This abstraction allows different implementations of adapter generation.
/// The FACT-style generator is the default, but alternative implementations
/// could be added for specific use cases.
pub trait AdapterGenerator {
    /// Generate adapters for all cross-component calls
    fn generate(
        &self,
        merged: &MergedModule,
        graph: &DependencyGraph,
    ) -> Result<Vec<AdapterFunction>>;
}

/// String encoding used by a component
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum StringEncoding {
    /// UTF-8 encoding
    #[default]
    Utf8,
    /// UTF-16 encoding (little-endian)
    Utf16,
    /// Latin-1 encoding (single byte per character)
    Latin1,
}

/// Options for a single adapter
#[derive(Debug, Clone)]
pub struct AdapterOptions {
    /// String encoding on the caller side
    pub caller_string_encoding: StringEncoding,

    /// String encoding on the callee side
    pub callee_string_encoding: StringEncoding,

    /// Memory index for caller
    pub caller_memory: u32,

    /// Memory index for callee
    pub callee_memory: u32,

    /// Realloc function for caller (if any)
    pub caller_realloc: Option<u32>,

    /// Realloc function for callee (if any)
    pub callee_realloc: Option<u32>,

    /// Whether the target function returns a `(ptr: i32, len: i32)` pair
    /// that must be copied back from callee memory to caller memory
    pub returns_pointer_pair: bool,

    /// Post-return function index in merged module (if any).
    /// Called after results have been copied back, to allow callee cleanup.
    pub callee_post_return: Option<u32>,

    /// Resource borrow params needing handle conversion.
    ///
    /// Per the canonical ABI, `borrow<T>` params need different handling
    /// depending on who defines the resource:
    ///
    /// - **Callee defines T**: adapter calls `[resource-rep](handle) → rep`
    ///   and passes rep to callee (which expects raw pointer via identity lift).
    ///
    /// - **Neither defines T** (3-component chain): adapter calls caller's
    ///   `[resource-rep](handle) → rep`, then callee's `[resource-new](rep) → new_handle`,
    ///   and passes new_handle to callee (which expects a handle in its own table).
    ///
    /// `own<T>` params are never converted (callee calls from_handle internally).
    pub resource_rep_calls: Vec<ResourceBorrowTransfer>,
    /// Resource own<T> results needing rep→handle conversion (3-component chains).
    pub resource_new_calls: Vec<ResourceOwnResultTransfer>,
    /// Resolved inner resource handles for list elements.
    /// Used after bulk list copy to convert `borrow<T>` handles in callee
    /// memory. See [`InnerResourceFixup`] — each carries a per-element
    /// discriminant-guard chain (UCA-A-16) so handles inside
    /// option/result/variant payloads are translated only when their case is
    /// live. An empty chain = unconditional (Record/Tuple/FixedSizeList).
    pub inner_resource_fixups: Vec<InnerResourceFixup>,
    /// Resource borrow handles inside the params-ptr buffer that need
    /// handle→rep conversion. Each entry contains the byte offset within the
    /// buffer and the merged function index of `[resource-rep]`.
    pub params_area_borrow_fixups: Vec<ParamsAreaResourceFixup>,
}

/// A per-element `borrow<T>` → rep conversion for a list element, applied
/// after the bulk copy. `byte_offset` is relative to each element's base and
/// `rep_func` is the merged function index of the matching `[resource-rep]`
/// import. `guards` is a chain of [`crate::resolver::DiscriminantGuard`]s the
/// adapter AND-evaluates per element before firing the conversion — non-empty
/// when the handle lives inside an option/result/variant payload (UCA-A-16 /
/// H-11.5). Empty = unconditional. Mirrors [`crate::resolver::InnerPointer`]'s
/// guard handling.
#[derive(Debug, Clone)]
pub struct InnerResourceFixup {
    pub byte_offset: u32,
    pub rep_func: u32,
    pub guards: Vec<crate::resolver::DiscriminantGuard>,
}

/// Describes a resource handle inside the params-ptr buffer that needs conversion.
#[derive(Debug, Clone)]
pub struct ParamsAreaResourceFixup {
    /// Byte offset within the params buffer
    pub byte_offset: u32,
    /// Merged function index of `[resource-rep]` to convert handle → rep
    pub rep_func: u32,
    /// Whether this is an own<T> (true) or borrow<T> (false)
    pub is_owned: bool,
}

/// Describes how to transfer a `borrow<T>` handle across an adapter boundary.
#[derive(Debug, Clone)]
pub struct ResourceBorrowTransfer {
    /// The flat parameter index holding the handle
    pub param_idx: u32,
    /// Merged function index of `[resource-rep]` to convert handle → rep
    pub rep_func: u32,
    /// If the callee doesn't define the resource, the merged function index
    /// of `[resource-new]` to convert rep → new handle in callee's table.
    /// None when the callee defines the resource (rep is passed directly).
    pub new_func: Option<u32>,
}

/// Describes how to convert an `own<T>` result via `[resource-rep]` then `[resource-new]`.
///
/// The callee returns a handle. To transfer to the caller's table:
///   1. `resource.rep(handle)` on callee's type extracts the representation
///   2. `resource.new(rep)` on caller's type mints a fresh handle
#[derive(Debug, Clone)]
pub struct ResourceOwnResultTransfer {
    /// Flat result index (non-retptr path)
    pub position: u32,
    /// Byte offset in return area (retptr path)
    pub byte_offset: u32,
    /// Merged function index of callee's `[resource-rep]` (handle → rep)
    pub rep_func: u32,
    /// Merged function index of caller's `[resource-new]` (rep → handle)
    pub new_func: u32,
}

impl Default for AdapterOptions {
    fn default() -> Self {
        Self {
            caller_string_encoding: StringEncoding::Utf8,
            callee_string_encoding: StringEncoding::Utf8,
            caller_memory: 0,
            callee_memory: 0,
            caller_realloc: None,
            callee_realloc: None,
            returns_pointer_pair: false,
            callee_post_return: None,
            resource_rep_calls: Vec::new(),
            resource_new_calls: Vec::new(),
            inner_resource_fixups: Vec::new(),
            params_area_borrow_fixups: Vec::new(),
        }
    }
}
