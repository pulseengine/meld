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
    UnresolvedImport {
        module: String,
        name: String,
    },

    /// Export conflict during merge
    #[error("conflicting exports: {name} defined in multiple components")]
    ConflictingExports {
        name: String,
    },

    /// Circular dependency detected
    #[error("circular dependency detected between components")]
    CircularDependency,

    /// Type mismatch during resolution
    #[error("type mismatch: import expects {expected}, but export provides {actual}")]
    TypeMismatch {
        expected: String,
        actual: String,
    },

    /// Memory strategy not supported
    #[error("memory strategy not supported: {0}")]
    MemoryStrategyUnsupported(String),

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

    /// I/O error
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}

impl From<wasmparser::BinaryReaderError> for Error {
    fn from(err: wasmparser::BinaryReaderError) -> Self {
        Error::ParseError(err.to_string())
    }
}
