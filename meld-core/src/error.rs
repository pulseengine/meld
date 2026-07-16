//! Error types for meld-core

use thiserror::Error;

/// Result type alias using meld Error
pub type Result<T> = std::result::Result<T, Error>;

/// Errors that can occur during component fusion
#[derive(Debug, Error)]
pub enum Error {
    /// No components provided for fusion
    #[error("no components provided for fusion")]
    NoComponents,

    /// Invalid WebAssembly binary
    #[error("invalid WebAssembly binary: {0}")]
    InvalidWasm(String),

    /// Input is not a WebAssembly component
    #[error("input is not a WebAssembly component (expected component, got core module)")]
    NotAComponent,

    /// Component parsing error
    #[error("failed to parse component: {0}")]
    ParseError(String),

    /// No core modules found in component
    #[error("no core modules found in component")]
    NoCoreModules,

    /// Component has unsupported feature
    #[error("unsupported component feature: {0}")]
    UnsupportedFeature(String),

    /// Import resolution error
    #[error("unresolved import: {module}::{name}")]
    UnresolvedImport { module: String, name: String },

    /// Export conflict during merge
    #[error("conflicting exports: {name} defined in multiple components")]
    ConflictingExports { name: String },

    /// Circular dependency detected
    #[error("circular dependency detected between components")]
    CircularDependency,

    /// Circular dependency detected between modules within a component
    #[error("circular module dependency in component {component_idx}: {cycle}")]
    ModuleDependencyCycle { component_idx: usize, cycle: String },

    /// Type mismatch during resolution
    #[error("type mismatch: import expects {expected}, but export provides {actual}")]
    TypeMismatch { expected: String, actual: String },

    /// Memory strategy not supported
    #[error("memory strategy not supported: {0}")]
    MemoryStrategyUnsupported(String),

    /// A core module must be placed at a non-zero shared-memory base but
    /// carries no relocation metadata, so meld cannot rebase its absolute
    /// addresses into the shared window (issue #326, ADR-6 path-F). Emitting
    /// it unchanged would collide it with a prior module's addresses and
    /// silently corrupt memory, so fusion hard-fails instead.
    #[error(
        "component '{component}' module {module} is placed at a non-zero shared-memory base but \
         carries no relocation metadata (linking/reloc.*); its absolute addresses cannot be \
         rebased safely. Rebuild it with relocations retained on the FINAL link \
         (`-C link-arg=--emit-relocs`) — an unresolved relocatable object \
         (`wasm-ld -r`) is NOT sufficient, its stored values are addends, not final \
         addresses — or fuse without shared memory"
    )]
    MissingRelocMetadata {
        /// Display name of the component that owns the offending module.
        component: String,
        /// The offending module's index within its component.
        module: String,
    },

    /// A `reloc.CODE` memory-address relocation site does not land on a
    /// rebasable immediate in the emitted code (issue #351). This is the
    /// signature of stale relocation offsets — e.g. a producer that relaxed
    /// address immediates from 5-byte-padded to minimal LEB128 without
    /// rewriting `reloc.*` offsets in lockstep (pulseengine/wasm-tools#3),
    /// leaving each site drifted by the accumulated width reduction. meld
    /// cannot safely rebase from misaligned relocs: applying them at the wrong
    /// site (or silently skipping a drifted one) corrupts the shared address
    /// space. Hard-fail rather than emit a plausible-but-wrong module.
    #[error(
        "component '{component}' module {module}: relocation site at code offset {offset} \
         (reloc.CODE) does not land on a rebasable address immediate — the relocation \
         metadata is stale relative to the emitted code (a producer relaxed LEB immediates \
         without updating reloc offsets; see pulseengine/wasm-tools#3 and meld#351). \
         Cannot rebase safely under `--memory shared --address-rebase`"
    )]
    MisalignedReloc {
        /// Display name of the component that owns the offending module.
        component: String,
        /// The offending module's index within its component.
        module: String,
        /// The stale reloc.CODE code-content offset that failed to align.
        offset: u32,
    },

    /// Adapter generation error
    #[error("adapter generation failed: {0}")]
    AdapterGeneration(String),

    /// Encoding error
    #[error("failed to encode output module: {0}")]
    EncodingError(String),

    /// Index out of bounds
    #[error("index out of bounds: {kind} index {index} (max {max})")]
    IndexOutOfBounds {
        kind: &'static str,
        index: u32,
        max: u32,
    },

    /// Canonical ABI error
    #[error("canonical ABI error: {0}")]
    CanonicalAbi(String),

    /// Same core module instantiated more than once in a component
    #[error(
        "component {component_idx} instantiates core module {module_idx} more than once (multiply-instantiated modules are not yet supported)"
    )]
    DuplicateModuleInstantiation {
        component_idx: usize,
        module_idx: u32,
    },

    /// Two core modules within one component export the same flat name.
    /// In the flat-name resolution path the previous code silently
    /// overwrote the first module's entry with the second (last-writer
    /// wins), routing any import of that name to the wrong module and
    /// violating the semantic-preservation invariant. The instance-graph
    /// path is not vulnerable, so this error is only reachable for
    /// components without an `InstanceSection`; rejecting the collision
    /// makes the violation loud instead of silent (LS-P-11).
    #[error(
        "component {component_idx}: core modules {first_module_idx} and {second_module_idx} both export `{export_name}` in the flat-name resolver path; ambiguous, and the previous behavior silently picked the latter"
    )]
    DuplicateModuleExport {
        component_idx: usize,
        export_name: String,
        first_module_idx: usize,
        second_module_idx: usize,
    },

    /// P3 async component model features are not yet supported
    #[error("P3 async component features not supported: {0}")]
    P3AsyncNotSupported(String),

    /// Static stream validation (issue #142) found at least one wiring
    /// problem in the fused component graph. The message lists each
    /// detected issue (type-mismatch near-misses, multi-component
    /// cycles) so the user can act on all of them at once instead of
    /// having to re-run after each fix.
    #[error("stream validation failed:\n{0}")]
    StreamValidation(String),

    /// I/O error
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}

impl From<wasmparser::BinaryReaderError> for Error {
    fn from(err: wasmparser::BinaryReaderError) -> Self {
        Error::ParseError(err.to_string())
    }
}
