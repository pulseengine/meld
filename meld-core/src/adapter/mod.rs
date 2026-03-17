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

mod fact;

pub use fact::FactStyleGenerator;

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
    /// Each entry: (byte_offset_in_element, merged_func_idx of [resource-rep]).
    /// Used after bulk list copy to convert handles in callee memory.
    pub inner_resource_fixups: Vec<(u32, u32)>,
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

/// Describes how to convert an `own<T>` result via `[resource-new]`.
#[derive(Debug, Clone)]
pub struct ResourceOwnResultTransfer {
    /// Flat result index (non-retptr path)
    pub position: u32,
    /// Byte offset in return area (retptr path)
    pub byte_offset: u32,
    /// Merged function index of `[resource-new]`
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
        }
    }
}
