/// Simple index offset mapping model for meld.
///
/// This mirrors the idea of re-indexing during fusion (e.g., segment or
/// function index offsets) and is intentionally minimal to keep translation
/// stable for rocq-of-rust.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IndexMap {
    pub base: u32,
}

impl IndexMap {
    pub fn new(base: u32) -> Self {
        IndexMap { base }
    }

    pub fn map(&self, idx: u32) -> u32 {
        self.base + idx
    }
}
