//! # Meld Core
//!
//! Core library for static WebAssembly component fusion.
//!
//! This library provides the core functionality for fusing multiple P2/P3
//! WebAssembly components into a single core module, eliminating the need
//! for runtime linking.
//!
//! ## Pipeline
//!
//! ```text
//! P2/P3 Components → Parser → Resolver → Merger → Adapter Gen → Single Module
//! ```
//!
//! 1. **Parser**: Extracts core modules and type information from components
//! 2. **Resolver**: Builds import/export graph, performs topological sort
//! 3. **Merger**: Combines function/memory/table/global index spaces
//! 4. **Adapter Generator**: Creates Canonical ABI trampolines
//!
//! ## Example
//!
//! ```ignore
//! use meld_core::{Fuser, FuserConfig};
//!
//! let config = FuserConfig::default();
//! let mut fuser = Fuser::new(config);
//!
//! // Add components to fuse
//! fuser.add_component(&component_a_bytes)?;
//! fuser.add_component(&component_b_bytes)?;
//!
//! // Perform fusion
//! let fused_module = fuser.fuse()?;
//! ```
//!
//! ## Memory Strategy
//!
//! - **Auto** (default): Resolves to shared memory + address rebasing when
//!   no input module contains `memory.grow` and the inputs carry two or
//!   more memories; multi-memory otherwise. See [`MemoryStrategy::Auto`]
//!   and issue #172.
//! - **Multi-memory**: Each component keeps its own linear memory.
//!   Cross-component pointer-passing calls use adapters with `cabi_realloc`
//!   and `memory.copy`. Downstream tools need multi-memory support
//!   (`wasm-opt --enable-multimemory`); no single-address-space lowering.
//! - **Shared memory**: All components share one memory. Broken when
//!   any component uses `memory.grow`.

pub mod abi_proofs;
pub mod adapter;
pub mod attestation;
pub mod component_wrap;
pub mod custom_merge;
pub mod dwarf;
mod error;
pub mod mcu_dissolve;
pub mod memory_probe;
pub mod merger;
pub mod p3_async;
pub mod p3_bridge;
pub mod p3_stream;
pub mod parser;
pub mod provenance;
pub mod reloc;
pub mod resolver;
pub mod resource_graph;
pub mod rewriter;
pub mod segments;

pub use adapter::{AdapterConfig, AdapterGenerator};
pub use error::{Error, Result};
pub use merger::{MergedModule, Merger};
pub use parser::{ComponentParser, ParsedComponent};
pub use resolver::{DependencyGraph, Resolver};

#[cfg(not(feature = "attestation"))]
use crate::attestation::{FUSION_ATTESTATION_SECTION, FusionAttestationBuilder};
use wasm_encoder::Module as EncodedModule;

/// Configuration for the fusion process
#[derive(Debug, Clone)]
pub struct FuserConfig {
    /// Memory strategy for fused output
    pub memory_strategy: MemoryStrategy,

    /// Whether to generate attestation data
    pub attestation: bool,

    /// Whether to emit a byte-reproducible attestation (#325): derive the
    /// attestation id from the output content and source the timestamp from
    /// `SOURCE_DATE_EPOCH` (default epoch 0) instead of a random UUID + the
    /// wall clock, so identical input yields an identical fused artifact.
    pub reproducible: bool,

    /// Whether to emit the `component-provenance` custom section
    /// (issue #192). When enabled (the default), every defined
    /// function in the fused module gets a back-pointer entry
    /// `{ component_id, originating_func_idx }` in a JSON payload
    /// under the section name `component-provenance`. Consumers
    /// (notably `pulseengine/scry`'s sound abstract interpreter)
    /// use this to project Component-Model invariants onto fused-
    /// module locations. Section overhead is ~120 bytes per fused
    /// function; opting out via `--no-component-provenance` is
    /// supported for size-sensitive builds.
    pub component_provenance: bool,

    /// Whether to rebase per-module memory addresses into a shared memory
    pub address_rebasing: bool,

    /// Whether to preserve debug names
    pub preserve_names: bool,

    /// Custom section handling
    pub custom_sections: CustomSectionHandling,

    /// DWARF (`.debug_*`) section handling.
    ///
    /// Default `Remap` since v0.25.0 (#143/#144 complete): single-source
    /// input DWARF is address-remapped against the fused code section
    /// (correct-or-tombstone per address, LS-D-1), meld-generated code
    /// gets the synthetic `<meld-adapter>` per-class unit (LS-D-2), and
    /// the multi-source case drops source DWARF rather than emit wrong
    /// addresses (#208 lifts that). Witness-measured on hello_rust:
    /// 75.9% of fused branch offsets resolve to source (83.0% unfused;
    /// the unfused 17% is debug-info-less libc, the fusion delta is
    /// tombstoned/dropped ranges — tracked under #208). `Strip` remains
    /// available; `PassThrough` is opt-in and lossy (its addresses are
    /// wrong against the fused code section).
    pub dwarf_handling: DwarfHandling,

    /// Output format: core module (default) or P2 component
    pub output_format: OutputFormat,

    /// Resources whose representation is opaque to wit-bindgen-rust user code
    /// (constructed by `pulseengine/wit-bindgen feat/opaque-rep-attribute` with
    /// `--opaque-export-resources`). Each entry is `(interface, resource_name)`.
    ///
    /// Opaque-rep resources are routed differently than standard Box-pattern
    /// resources:
    /// 1. `merger.rs::allocate_handle_tables` skips them — their reps are
    ///    already valid integer handles, no parallel handle table needed.
    /// 2. `component_wrap.rs::local_resource_types` keys them by
    ///    `(component_idx, resource_name)` rather than `resource_name` alone,
    ///    giving each component its own wasmtime resource type. This matches
    ///    the un-fused composition's semantics where each component owns
    ///    its own resource table.
    pub opaque_resources: Vec<(String, String)>,
}

impl Default for FuserConfig {
    fn default() -> Self {
        Self {
            memory_strategy: MemoryStrategy::Auto,
            attestation: true,
            reproducible: false,
            component_provenance: true,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: CustomSectionHandling::Merge,
            dwarf_handling: DwarfHandling::Remap,
            output_format: OutputFormat::CoreModule,
            opaque_resources: Vec::new(),
        }
    }
}

/// Memory strategy for the fused output
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryStrategy {
    /// All components share a single memory.
    /// Broken when any component uses `memory.grow` — one component's
    /// growth corrupts every other component's address space.
    SharedMemory,

    /// Each component keeps its own memory.
    /// Cross-component pointer-passing calls use adapters with
    /// `cabi_realloc` and `memory.copy`. Requires WebAssembly
    /// multi-memory (Core Spec 3.0) — downstream tools such as
    /// `wasm-opt` need `--enable-multimemory`, and single-address-
    /// space (MCU) targets have no lowering for it (issue #172).
    MultiMemory,

    /// Resolve to `SharedMemory` + address rebasing when that is
    /// provably sound, `MultiMemory` otherwise (default; issue #172).
    ///
    /// Resolution happens once, at the start of fusion, from two
    /// static facts about the inputs:
    /// 1. No input module contains a `memory.grow` instruction
    ///    (`memory_probe`) — growth is what breaks shared memory.
    /// 2. The inputs carry two or more linear memories — with at most
    ///    one, multi-memory output is already single-memory, so the
    ///    rebasing path adds risk without benefit.
    ///
    /// Both hold → `SharedMemory` with address rebasing. Otherwise →
    /// `MultiMemory`. If the shared-memory plan itself refuses the
    /// input (`Error::MemoryStrategyUnsupported`), fusion retries as
    /// `MultiMemory`, so `Auto` never fails on input that the
    /// multi-memory strategy accepts.
    Auto,
}

/// Output format for the fused binary
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OutputFormat {
    /// Output as a core wasm module (default, current behavior)
    #[default]
    CoreModule,
    /// Wrap the fused core module as a P2 component with the original WIT interface
    Component,
}

/// How to handle custom sections during fusion
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CustomSectionHandling {
    /// Merge custom sections with same name
    Merge,
    /// Prefix section names with component identifier
    Prefix,
    /// Drop all custom sections
    Drop,
}

/// How to handle DWARF (`.debug_*`) custom sections during fusion.
///
/// Distinct from [`CustomSectionHandling`] because DWARF sections carry
/// code-section byte offsets that meld does NOT yet remap (issue #130
/// Phase 2). Passing them through unchanged is strictly worse than
/// dropping them — downstream consumers like `pulseengine/witness`
/// would silently produce wrong source-line attribution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DwarfHandling {
    /// Drop all `.debug_*` sections (default).
    ///
    /// The fused module carries no DWARF; downstream MC/DC tooling
    /// degrades to its no-DWARF fallback. Correct, lossy.
    Strip,

    /// Pass DWARF sections through verbatim from each input core
    /// module.
    ///
    /// Addresses inside the sections refer to per-input code-section
    /// offsets and will be wrong against the merged code section.
    /// Use only if the consumer can tolerate or detect that.
    PassThrough,

    /// Remap DWARF code addresses to the fused code section (#143).
    ///
    /// Reads the input `.debug_*` sections, translates every code
    /// address through an [`crate::dwarf::AddressRemap`] built from the
    /// actual input→output instruction layout, and emits a single
    /// rewritten DWARF set. Currently supports the case where exactly
    /// one input core module carries DWARF; with zero or more than one
    /// DWARF source — or if any address fails to map — it falls back to
    /// [`DwarfHandling::Strip`] (never emitting a wrong address).
    Remap,
}

/// Statistics about the fusion process
#[derive(Debug, Clone, Default)]
pub struct FusionStats {
    /// Number of components fused
    pub components_fused: usize,

    /// Number of core modules merged
    pub modules_merged: usize,

    /// Number of functions in output
    pub total_functions: usize,

    /// Number of adapter functions generated
    pub adapter_functions: usize,

    /// Number of identity-trampoline adapters inlined away (#304): the caller's
    /// import was wired directly to the target instead of through the thunk, so
    /// no forwarding indirection survives. The thunk itself is left unreferenced
    /// for loom to DCE. Subset of `adapter_functions`.
    pub adapters_inlined: usize,

    /// Number of imports resolved internally
    pub imports_resolved: usize,

    /// Number of exports in output
    pub total_exports: usize,

    /// Size of input components (bytes)
    pub input_size: usize,

    /// Size of fused output (bytes)
    pub output_size: usize,

    /// The memory strategy the output was actually built with ("shared" or
    /// "multi"). With `MemoryStrategy::Auto` this reports the resolution
    /// outcome (#172), so callers can tell the user what was selected.
    pub memory_strategy: String,
}

/// Main fuser interface for static component fusion
pub struct Fuser {
    config: FuserConfig,
    components: Vec<ParsedComponent>,
    /// Original (un-flattened) parsed components, used by component_wrap
    /// to access depth_0_sections and component_instance_defs.
    original_components: Vec<ParsedComponent>,
    /// Directed wiring hints from composition graph.
    wiring_hints: WiringHints,
    /// The memory strategy/rebasing pair as originally requested, captured
    /// before `MemoryStrategy::Auto` resolution mutates `config`. Restored
    /// at the start of every fuse so resolution is re-derived from the
    /// CURRENT component set — without this, a fuse → `add_component` →
    /// fuse sequence would reuse a stale resolution (Mythos finding A,
    /// PR #220 / UCA-M-11).
    requested_memory: Option<(MemoryStrategy, bool)>,
}

impl Fuser {
    /// Create a new fuser with the given configuration
    pub fn new(config: FuserConfig) -> Self {
        Self {
            config,
            components: Vec::new(),
            original_components: Vec::new(),
            wiring_hints: std::collections::HashMap::new(),
            requested_memory: None,
        }
    }

    /// Create a fuser with default configuration
    pub fn with_defaults() -> Self {
        Self::new(FuserConfig::default())
    }

    /// Add a component to be fused
    ///
    /// Components are parsed immediately and validated.
    pub fn add_component(&mut self, bytes: &[u8]) -> Result<()> {
        self.add_component_named(bytes, None)
    }

    /// Add a component with a name for better error messages
    pub fn add_component_named(&mut self, bytes: &[u8], name: Option<&str>) -> Result<()> {
        let parser = ComponentParser::new();
        let mut parsed = parser.parse(bytes)?;

        if let Some(n) = name {
            parsed.name = Some(n.to_string());
        }

        self.original_components.push(parsed.clone());
        let (flattened, hints) = flatten_nested_components(parsed)?;
        // Adjust wiring hint indices by current component count
        let offset = self.components.len();
        for ((importer, name), exporter) in hints {
            self.wiring_hints
                .insert((importer + offset, name), exporter + offset);
        }
        self.components.extend(flattened);
        Ok(())
    }

    /// Get the number of components added
    pub fn component_count(&self) -> usize {
        self.components.len()
    }

    /// Inspect P3 async usage across all added components.
    ///
    /// Returns a per-component summary of stream/future types and async
    /// canonical built-ins. Pure inspection — does not consume the fuser.
    /// See [`crate::p3_async`] for the host-intrinsic ABI meld lowers
    /// these constructs to.
    pub fn p3_async_summary(&self) -> Vec<(Option<String>, p3_async::P3AsyncFeatures)> {
        self.components
            .iter()
            .map(|c| (c.name.clone(), p3_async::detect_features(c)))
            .collect()
    }

    /// Borrow the flattened parsed components.
    ///
    /// Useful for benchmarks and tools that want to drive `Resolver` /
    /// `Merger` directly with the same flattened slice the fusion pipeline
    /// uses internally, without having to re-implement
    /// `flatten_nested_components`.
    pub fn components(&self) -> &[ParsedComponent] {
        &self.components
    }

    /// Borrow the wiring hints derived from composition graphs (component
    /// instance / alias wiring). Pair with `components()` when calling
    /// `Resolver::resolve_with_hints` for parity with the in-pipeline call.
    pub fn wiring_hints(&self) -> &WiringHints {
        &self.wiring_hints
    }

    /// Perform the fusion and return the fused module bytes
    pub fn fuse(&mut self) -> Result<Vec<u8>> {
        let (bytes, _stats) = self.fuse_with_stats()?;
        Ok(bytes)
    }

    /// Perform fusion and return both the bytes and statistics
    ///
    /// Takes `&mut self` because `MemoryStrategy::Auto` is resolved here,
    /// in place, to a concrete strategy before the pipeline runs (#172) —
    /// every later read of `self.config` then sees the resolved values.
    pub fn fuse_with_stats(&mut self) -> Result<(Vec<u8>, FusionStats)> {
        if self.components.is_empty() {
            return Err(Error::NoComponents);
        }
        // Restore the originally-requested strategy before resolving, so a
        // repeated fuse (e.g. after another `add_component`) re-derives the
        // resolution from the CURRENT component set instead of reusing a
        // stale one (Mythos finding A, PR #220).
        let (requested_strategy, requested_rebasing) = *self
            .requested_memory
            .get_or_insert((self.config.memory_strategy, self.config.address_rebasing));
        self.config.memory_strategy = requested_strategy;
        self.config.address_rebasing = requested_rebasing;
        if self.config.memory_strategy == MemoryStrategy::Auto {
            self.resolve_auto_memory_strategy();
            let result = if self.config.memory_strategy == MemoryStrategy::SharedMemory {
                match self.fuse_with_stats_resolved() {
                    Err(Error::MemoryStrategyUnsupported(msg)) => {
                        // Auto must never fail on input multi-memory accepts:
                        // a shared-plan refusal downgrades to multi-memory
                        // instead of surfacing as an error.
                        log::warn!(
                            "memory strategy auto: shared-memory fusion refused \
                             ({msg}); retrying with multi-memory"
                        );
                        self.config.memory_strategy = MemoryStrategy::MultiMemory;
                        self.config.address_rebasing = false;
                        self.fuse_with_stats_resolved()
                    }
                    other => other,
                }
            } else {
                self.fuse_with_stats_resolved()
            };
            // #300 / ADR-4: `Auto` resolved a safety-relevant property (which
            // inter-component isolation model protects components) automatically.
            // Functional-safety builds must choose the strategy EXPLICITLY — so
            // on an attested build (the release/safety build) surface the
            // automatic choice loudly rather than letting it pass silently.
            // `memory_strategy_label()` here is the FINAL strategy, after any
            // shared->multi downgrade above.
            if self.config.attestation {
                log::warn!(
                    "memory strategy: `Auto` resolved to '{}' for an attested build; \
                     functional-safety builds should select `--memory` explicitly \
                     (ADR-4: explicit, not auto)",
                    self.memory_strategy_label()
                );
            }
            return result;
        }
        // #326: explicit `--memory shared --address-rebase` is an opt-in to an
        // unsound transform — address rebasing does not rebase computed memory
        // addresses, so it silently corrupts real components. `auto` no longer
        // selects this path; when a caller requests it explicitly, warn loudly
        // rather than corrupt silently (LS-D-1). The build still proceeds.
        if self.config.memory_strategy == MemoryStrategy::SharedMemory
            && self.config.address_rebasing
        {
            log::warn!(
                "memory strategy: explicit shared-memory + address rebasing is UNSOUND \
                 for components that access memory via computed pointers (#326) — the \
                 dynamic address operand of ordinary loads/stores is not rebased, so \
                 per-component memory can silently collide. Prefer `--memory multi` \
                 unless every input addresses memory only via static offsets."
            );
        }
        self.fuse_with_stats_resolved()
    }

    /// Resolve `MemoryStrategy::Auto` against the added components.
    ///
    /// Auto always selects **multi-memory** — it is the sound strategy. Shared
    /// memory + address rebasing was previously auto-selected for grow-free,
    /// multi-memory inputs, but that path is **unsound** (#326): rebasing does
    /// not relocate the dynamic address operand of ordinary loads/stores, so
    /// components addressing memory via computed pointers silently collide.
    /// Until correct dynamic rebasing lands, Auto never picks shared+rebase;
    /// it remains reachable only via explicit `--memory shared --address-rebase`
    /// (which warns loudly). Any user-supplied `address_rebasing` value is
    /// overridden — Auto owns both knobs.
    fn resolve_auto_memory_strategy(&mut self) {
        let mut memory_count = 0usize;
        let mut grows = false;
        for component in &self.components {
            for module in &component.core_modules {
                memory_count += module.memories.len();
                memory_count += module
                    .imports
                    .iter()
                    .filter(|imp| matches!(imp.kind, parser::ImportKind::Memory(_)))
                    .count();
                if !grows && memory_probe::module_uses_memory_grow(&module.bytes) {
                    grows = true;
                }
            }
        }

        if grows {
            log::info!(
                "memory strategy auto: input uses memory.grow; selecting multi-memory \
                 (shared memory is unsound under growth)"
            );
            self.config.memory_strategy = MemoryStrategy::MultiMemory;
            self.config.address_rebasing = false;
        } else if memory_count < 2 {
            log::info!(
                "memory strategy auto: {memory_count} input memory(ies); selecting \
                 multi-memory (output is already single-memory)"
            );
            self.config.memory_strategy = MemoryStrategy::MultiMemory;
            self.config.address_rebasing = false;
        } else {
            // #326: address rebasing does NOT rebase the dynamic address
            // operand of ordinary loads/stores (only the static memarg offset
            // and bulk-memory ops) — so shared-memory fusion silently corrupts
            // any component that addresses memory via a computed pointer (heap,
            // shadow stack — i.e. all real components). Until correct dynamic
            // rebasing lands, `auto` must NOT silently pick shared+rebase.
            // Fall back to multi-memory, which is sound (LS-D-1: emit correct
            // output, never a plausible-but-wrong one). Explicit
            // `--memory shared --address-rebase` remains available as an
            // opt-in, and warns loudly (see `warn_if_unsound_rebasing`).
            log::warn!(
                "memory strategy auto: {memory_count} memories, no memory.grow — \
                 shared-memory fusion would apply here, but address rebasing is \
                 unsound for computed memory addresses (#326); selecting \
                 multi-memory instead. Use `--memory shared --address-rebase` to \
                 override explicitly (unsound; corrupts computed-pointer access)."
            );
            self.config.memory_strategy = MemoryStrategy::MultiMemory;
            self.config.address_rebasing = false;
        }
    }

    /// #298 — whether the fused core's `cabi_realloc` is provably vestigial and
    /// therefore safe to drop (so loom can DCE the allocator + `memory.grow`,
    /// unblocking the single-address-space `--memory shared` MCU path).
    ///
    /// **Fail-safe and currently INERT.** This computes the verdict only; it is
    /// not yet wired to change merge/encode behavior — that's the
    /// corruption-critical step gated *behind* this verdict (the tolerant
    /// rewriter + dead-function stubbing, see #298 / #299). The default on any
    /// uncertainty is `false` (keep `cabi_realloc`): under-drop is a missed
    /// optimization, over-drop is silent marshalling corruption.
    ///
    /// `cabi_realloc` is the component's *own* allocator, used by `canon lift`
    /// when the host calls in with pointer-carrying args/results. So the
    /// relevant surface is each component's **lifts** (exports): if every lift
    /// is scalar (no string/list params or results) nothing needs the
    /// allocator. (`canon lower`/imports use the *callee's* realloc, not this
    /// one.) Two sound conservatisms: it also counts lifts that fusion will
    /// internalize (over-keep), and it bails to `false` on any unresolvable
    /// type, non-core output, or adapter presence.
    fn cabi_realloc_drop_provably_safe(&self, graph: &resolver::DependencyGraph) -> bool {
        // (1) Core-module output only: a P2 wrap aliases cabi_realloc for
        //     `canon lower`, so dropping it there corrupts marshalling.
        if self.config.output_format != OutputFormat::CoreModule {
            return false;
        }
        // (2) No cross-component adapters: an adapter may marshal pointers and
        //     consume the allocator. Over-keep; refine to per-site later.
        if !graph.adapter_sites.is_empty() {
            return false;
        }
        // (3) Every lift's component-level type must be provably scalar.
        for comp in &self.components {
            for entry in &comp.canonical_functions {
                let parser::CanonicalEntry::Lift { type_index, .. } = entry else {
                    continue;
                };
                let Some(td) = comp.get_type_definition(*type_index) else {
                    return false; // unresolvable type => fail-safe keep
                };
                let parser::ComponentTypeKind::Function { params, results } = &td.kind else {
                    return false; // non-function lift type => keep
                };
                if params.iter().any(|(_, t)| comp.type_contains_pointers(t))
                    || results.iter().any(|(_, t)| comp.type_contains_pointers(t))
                {
                    return false;
                }
            }
        }
        true
    }

    /// #298 (FINDING 1) — is every input's allocator genuinely dead once the
    /// vestigial `cabi_realloc*` exports are dropped?
    ///
    /// [`Self::cabi_realloc_drop_provably_safe`] proves the *interface boundary*
    /// needs no realloc; it does NOT prove the allocator unreachable. A
    /// scalar-interface component may still allocate internally (`Vec`/`String`/
    /// `Box` → `dlmalloc`/`sbrk` → `memory.grow`) from a live export, and the
    /// grow-defer is module-wide — so without this gate a live grow would be
    /// rewritten to `unreachable` and trap at runtime instead of hard-failing
    /// at fuse time. This ANDs an extra, strictly-stricter condition into the
    /// drop/defer wiring: it returns `true` only when NO `memory.grow` is
    /// reachable from any live root (all exports except the dropped
    /// `cabi_realloc*`, plus `start` and every indirectly-referenced function)
    /// in ANY core module of ANY input. Fail-safe: an unparseable module counts
    /// as having a live grow (via [`memory_probe::module_has_reachable_memory_grow`]).
    fn allocator_grow_is_dead(&self) -> bool {
        self.components.iter().all(|comp| {
            comp.core_modules
                .iter()
                .all(|module| !memory_probe::module_has_reachable_memory_grow(&module.bytes))
        })
    }

    /// The fusion pipeline proper. `self.config.memory_strategy` is a
    /// concrete strategy here — `Auto` has been resolved by the caller.
    fn fuse_with_stats_resolved(&self) -> Result<(Vec<u8>, FusionStats)> {
        if self.config.address_rebasing
            && self.config.memory_strategy != MemoryStrategy::SharedMemory
        {
            return Err(Error::MemoryStrategyUnsupported(
                "address rebasing requires shared memory strategy".to_string(),
            ));
        }

        // Log P3 async feature usage (informational, no longer a rejection).
        for (idx, comp) in self.components.iter().enumerate() {
            if !comp.p3_async_features.is_empty() {
                let default_name = format!("component {idx}");
                let comp_name = comp.name.as_deref().unwrap_or(&default_name);
                log::info!(
                    "P3 async types in '{comp_name}': {}",
                    comp.p3_async_features.join(", ")
                );
            }
        }

        let mut stats = FusionStats {
            components_fused: self.components.len(),
            memory_strategy: self.memory_strategy_label().to_string(),
            ..Default::default()
        };

        // Calculate input size
        for comp in &self.components {
            stats.input_size += comp.original_size;
            stats.modules_merged += comp.core_modules.len();
        }

        // Step 1: Resolve dependencies
        log::info!(
            "Resolving dependencies for {} components",
            self.components.len()
        );
        let resolver = Resolver::with_strategy(self.config.memory_strategy);
        let graph = resolver.resolve_with_hints(&self.components, &self.wiring_hints)?;
        stats.imports_resolved = graph.resolved_imports.len();

        // #298: compute the vestigial-`cabi_realloc` verdict. When it holds
        // AND we are on the address-rebasing (single-address-space MCU) path —
        // the only path a surviving allocator `memory.grow` hard-blocks — the
        // allocator is provably dead: drop its exports (below, so loom can DCE
        // it) and defer its now-unreachable `memory.grow` to `unreachable`
        // (via the merger flag) instead of hard-failing. On a false verdict, or
        // any non-rebasing fuse, behavior is byte-identical to before.
        // #298 FINDING 1: the interface-boundary verdict proves only that the
        // boundary needs no realloc — NOT that the allocator is dead. A
        // scalar-interface component can still allocate internally (`Vec` →
        // `dlmalloc` → `memory.grow`) reachable from a live export. Deferring
        // every `memory.grow` there would fuse-`Ok` then trap at runtime.
        // `allocator_grow_is_dead` closes the gap: it fires the drop/defer only
        // when NO `memory.grow` is reachable from any live root once the
        // `cabi_realloc*` exports are dropped. `&&` short-circuits, so this
        // call-graph scan runs only on the boundary-clean rebasing path.
        let drop_vestigial_realloc = self.cabi_realloc_drop_provably_safe(&graph)
            && self.config.address_rebasing
            && self.allocator_grow_is_dead();
        if drop_vestigial_realloc {
            log::debug!(
                "#298: cabi_realloc is provably vestigial for this rebasing fuse \
                 (scalar lift surface, core output, no adapters) — dropping its \
                 exports and deferring the dead allocator's memory.grow"
            );
        }

        // Step 2: Merge modules
        log::info!("Merging {} core modules", stats.modules_merged);
        let merger = Merger::new(self.config.memory_strategy, self.config.address_rebasing)
            .with_opaque_resources(self.config.opaque_resources.clone())
            .with_defer_grow_under_rebase(drop_vestigial_realloc);
        let mut merged = merger.merge(&self.components, &graph)?;

        // #298: drop the now-vestigial `cabi_realloc*` exports. Removing the
        // export (not the function body — out of scope per #298) makes the
        // allocator + its `dlmalloc`/`sbrk`/`memory.grow` DCE-eligible for
        // loom downstream. The merger emits these under exactly two names:
        // the bare `cabi_realloc`, and the suffixed `cabi_realloc$<N>` forms
        // (per-memory-index in multi-memory mode); match both. Gated on the
        // verdict AND the rebasing path, so every other fuse is unchanged.
        if drop_vestigial_realloc {
            merged
                .exports
                .retain(|e| !memory_probe::is_vestigial_realloc_export_name(&e.name));
        }
        stats.total_functions = merged.functions.len();
        stats.total_exports = merged.exports.len();

        // Step 2.4: Lower P3 async canonical built-ins to `pulseengine:async`
        // core-module imports. This adds one import per distinct intrinsic
        // (stream.new, stream.read, …, future.drop-writable) and shifts
        // every reference to defined functions up to make room. No-op when
        // the components contain no P3 async data-plane constructs (the
        // 73-test wit_bindgen_runtime suite). See `p3_async::lower_p3_async_intrinsics`
        // and ADR-1 for the full design.
        let _p3_lowering_plan = p3_async::lower_p3_async_intrinsics(&mut merged, &self.components)?;

        // Step 2.5: Generate task.return shims for internal fused async calls.
        //
        // For each [task-return]N import used by an internal async callee,
        // generate a shim that stores result values to globals. The
        // callback-driving adapter (generated next) reads these globals
        // after EXIT. Must run BEFORE adapter generation so shim info
        // is available to the async adapter.
        self.generate_task_return_shims(&mut merged, &graph)?;

        // Step 2.6: Cross-component stream-bridge emitter (#141, SR-33).
        //
        // When the resolver detected cross-component stream pairs
        // (graph.stream_pair_graph, ADR-3 detection foundation), emit the
        // bridge memory + per-component dispatch shims and rewire every
        // stream-intrinsic call site to its component's shim. This MUST
        // run before adapter generation/wiring: adapters are encoded
        // after merged.functions, so wire_adapter_indices bakes adapter
        // indices derived from functions.len() into call sites —
        // appending shim functions any later would shift those indices
        // off-target. Running here, the shims are plain merged functions
        // that every later index computation already accounts for.
        if let Some(stream_pairs) = graph.stream_pair_graph.as_ref()
            && !stream_pairs.is_empty()
        {
            p3_bridge::emit_stream_bridge(
                &mut merged,
                &self.components,
                stream_pairs,
                self.config.memory_strategy,
                self.config.address_rebasing,
            )?;
        }

        // Step 3: Generate adapters
        log::info!("Generating adapters");
        let adapter_config = AdapterConfig {
            inline_adapters: true,
            optimize_string_copies: true,
        };
        let generator = adapter::FactStyleGenerator::new(adapter_config);
        let adapters = generator.generate(&merged, &graph)?;
        stats.adapter_functions = adapters.len();

        // Step 3.5: Wire adapter function indices into the call graph
        //
        // The merger (step 2) maps cross-component imports directly to the
        // export target's merged index, bypassing adapters.  Now that adapters
        // have been generated we know their merged indices — they are appended
        // after all core functions — so we can patch function_index_map and
        // re-rewrite the affected function bodies so that call sites go through
        // the adapter trampolines instead of calling the target directly.
        if !adapters.is_empty() {
            stats.adapters_inlined = self.wire_adapter_indices(&mut merged, &adapters, &graph)?;
        }

        // Step 3.6: #334 MCU-dissolve fixups (SR-49, `--memory shared` only).
        //
        // Coalesce the N per-provider `__stack_pointer` globals into one
        // shared shadow stack, and drop the vestigial lowered-import shim's
        // keep-alive export so the downstream
        // `synth --native-pointer-abi --shadow-stack-size` dissolve proceeds
        // without gale's hand WAT surgery. Runs AFTER adapter wiring (so
        // direct-call flattening is already reflected in the bodies) and
        // BEFORE encoding (so all three encode passes, DWARF remap, and the
        // attestation/provenance hashes see the coalesced module). The
        // non-shared paths never reach here, keeping their output unchanged.
        if self.config.memory_strategy == MemoryStrategy::SharedMemory {
            mcu_dissolve::dissolve_fixups(&mut merged, &self.components)?;
        }

        // Step 4: Encode output module.
        //
        // Two-pass dance: first encode without any self-referential
        // custom sections, then build attestation (#wsc) and
        // provenance (#192) over THAT byte sequence and re-encode
        // with both as extras. Both sections' SHA-256 hashes refer
        // to the bytes-without-extras, so consumers strip both
        // sections before verifying.
        log::info!("Encoding fused module");
        // Pass A: encode without DWARF and without meld-extras. Its
        // code-section offsets are what the DWARF remap targets (trailing
        // custom sections do not shift code offsets, so the same offsets
        // hold in passes B and C).
        let bytes_for_remap = self.encode_output(&merged, &adapters, &[], &[])?;

        // Build the remapped `.debug_*` sections (only under Remap; a
        // miss or unsupported shape returns no sections → DWARF stripped).
        let dwarf_sections: Vec<(String, Vec<u8>)> =
            if self.config.dwarf_handling == DwarfHandling::Remap {
                {
                    let adapter_classes: Vec<adapter::AdapterClass> =
                        adapters.iter().map(|a| a.class).collect();
                    dwarf::remap_for_output(
                        &self.components,
                        &merged,
                        &adapter_classes,
                        &bytes_for_remap,
                    )
                    .unwrap_or_default()
                }
            } else {
                Vec::new()
            };

        // Pass B: re-encode with the remapped DWARF embedded. These are
        // the bytes the attestation/provenance hashes cover.
        let output_without_extras = if dwarf_sections.is_empty() {
            bytes_for_remap
        } else {
            log::info!(
                "Embedding {} remapped DWARF section(s)",
                dwarf_sections.len()
            );
            self.encode_output(&merged, &adapters, &[], &dwarf_sections)?
        };

        let mut extra_sections: Vec<(&str, Vec<u8>)> = Vec::new();

        if self.config.attestation {
            let mut attestation_stats = stats.clone();
            attestation_stats.output_size = output_without_extras.len();
            let (section_name, payload) =
                self.build_attestation_payload(&output_without_extras, &attestation_stats)?;
            extra_sections.push((section_name, payload));
        }

        if self.config.component_provenance {
            let provenance = provenance::build(
                &merged,
                &self.components,
                &output_without_extras,
                self.config.reproducible,
            );
            // SCPV v3 binary payload (#313 / scry#63) — infallible encode.
            extra_sections.push((provenance::SECTION_NAME, provenance.to_bytes()));
        }

        let output = if extra_sections.is_empty() {
            output_without_extras
        } else {
            self.encode_output(&merged, &adapters, &extra_sections, &dwarf_sections)?
        };

        // Optionally wrap the fused core module as a P2 component
        let output = if self.config.output_format == OutputFormat::Component {
            log::info!("Wrapping fused module as P2 component");
            component_wrap::wrap_as_component(
                &output,
                &self.components,
                &self.original_components,
                &graph,
                &merged,
                self.config.memory_strategy,
                &self.config.opaque_resources,
            )?
        } else {
            output
        };

        stats.output_size = output.len();

        log::info!(
            "Fusion complete: {} components → {} bytes ({}% of input)",
            stats.components_fused,
            stats.output_size,
            (stats.output_size * 100)
                .checked_div(stats.input_size)
                .unwrap_or(100)
        );

        Ok((output, stats))
    }

    /// Wire adapter function indices into the merged module's call graph.
    ///
    /// The merger maps cross-component imports directly to the export target's
    /// merged index.  This method corrects those mappings so that call sites
    /// go through the generated adapter trampolines instead.  For each adapter
    /// we:
    ///   1. Compute its merged function index (core functions + adapter offset).
    ///   2. Find the import function index in the source module that this
    ///      adapter replaces.
    ///   3. Update `function_index_map` so that import resolves to the adapter.
    ///   4. Re-rewrite the function bodies of the source module so that the
    ///      already-encoded `call` instructions reference the adapter.
    fn wire_adapter_indices(
        &self,
        merged: &mut merger::MergedModule,
        adapters: &[adapter::AdapterFunction],
        graph: &resolver::DependencyGraph,
    ) -> Result<usize> {
        // #304: count of identity trampolines inlined away (caller wired
        // straight to the target instead of through the thunk).
        let mut inlined_count = 0usize;
        use std::collections::{HashMap, HashSet};
        use wasm_encoder::{Function, Instruction, ValType};

        let original_func_count = merged.functions.len() as u32;
        let func_base = merged.import_counts.func;

        // Pre-scan: identify adapters needing P3 async widening wrappers.
        // A wrapper is needed when the caller's import type has wider result
        // types than the adapter's (e.g., caller expects i64, adapter returns
        // i32 task handle). Wrappers are placed in merged.functions BEFORE the
        // adapters, so we must pre-count them to compute correct adapter indices.
        struct WrapperInfo {
            adapter_offset: usize,
            comp_idx: usize,
            mod_idx: usize,
            caller_type_idx: u32,
        }
        let mut wrapper_infos: Vec<WrapperInfo> = Vec::new();

        for (adapter_offset, (adapter, site)) in
            adapters.iter().zip(graph.adapter_sites.iter()).enumerate()
        {
            if let Some(local_ti) = site.import_func_type_idx
                && let Some(&caller_ti) =
                    merged
                        .type_index_map
                        .get(&(site.from_component, site.from_module, local_ti))
                && caller_ti != adapter.type_idx
            {
                let caller_type = &merged.types[caller_ti as usize];
                let adapter_type = &merged.types[adapter.type_idx as usize];
                // Only wrap when there is actual result widening (i32→i64)
                let has_widening = caller_type.params.len() == adapter_type.params.len()
                    && caller_type.results.len() == adapter_type.results.len()
                    && caller_type
                        .results
                        .iter()
                        .zip(adapter_type.results.iter())
                        .any(|(c, a)| *a == ValType::I32 && *c == ValType::I64);
                if has_widening {
                    wrapper_infos.push(WrapperInfo {
                        adapter_offset,
                        comp_idx: site.from_component,
                        mod_idx: site.from_module,
                        caller_type_idx: caller_ti,
                    });
                }
            }
        }

        let num_wrappers = wrapper_infos.len() as u32;

        // Adapter base accounts for wrappers prepended into merged.functions.
        // Layout: [imports] [original funcs] [wrappers] [adapters]
        let adapter_base = func_base + original_func_count + num_wrappers;

        // Map adapter_offset → wrapper merged index for adapters that have wrappers.
        let mut adapter_to_wrapper: HashMap<usize, u32> = HashMap::new();
        for (wi, info) in wrapper_infos.iter().enumerate() {
            adapter_to_wrapper.insert(
                info.adapter_offset,
                func_base + original_func_count + wi as u32,
            );
        }

        // For each adapter, update function_index_map to point the source
        // import to the wrapper (if one exists) or the adapter's merged index.
        let mut affected_modules: HashSet<(usize, usize)> = HashSet::new();

        for (adapter_offset, (adapter, site)) in
            adapters.iter().zip(graph.adapter_sites.iter()).enumerate()
        {
            // #304: a pure identity trampoline is bypassed — wire the caller's
            // import straight to the target. (A widening wrapper, if any, takes
            // precedence; the two are mutually exclusive since an identity
            // forward has no result widening, but order defensively.) The
            // bypassed thunk is left unreferenced for loom to DCE.
            let target_idx = if let Some(&wrapper_idx) = adapter_to_wrapper.get(&adapter_offset) {
                wrapper_idx
            } else if let Some(inline_target) = adapter.inline_target {
                inlined_count += 1;
                inline_target
            } else {
                adapter_base + adapter_offset as u32
            };
            let comp_idx = adapter.source_component;
            let mod_idx = adapter.source_module;
            let module = &self.components[comp_idx].core_modules[mod_idx];

            // Find the import function index that this adapter replaces by
            // scanning the source module's imports for the matching name.
            let mut import_func_idx = 0u32;
            let mut found = false;
            for imp in &module.imports {
                if !matches!(imp.kind, parser::ImportKind::Function(_)) {
                    continue;
                }
                if (imp.name == site.import_name || imp.module == site.import_name)
                    && (imp.module == site.import_module || imp.name == site.import_module)
                {
                    merged
                        .function_index_map
                        .insert((comp_idx, mod_idx, import_func_idx), target_idx);
                    affected_modules.insert((comp_idx, mod_idx));
                    found = true;
                    break;
                }
                import_func_idx += 1;
            }
            if !found {
                log::warn!(
                    "adapter {} could not find matching import '{}' in component {} module {}",
                    adapter.name,
                    site.import_name,
                    comp_idx,
                    mod_idx
                );
            }
        }

        // Create wrapper functions for P3 async type widening.
        for info in &wrapper_infos {
            let adapter_merged_idx = adapter_base + info.adapter_offset as u32;
            let caller_type = &merged.types[info.caller_type_idx as usize];
            let adapter_type = &merged.types[adapters[info.adapter_offset].type_idx as usize];

            let mut body = Function::new([]);
            for i in 0..caller_type.params.len() {
                body.instruction(&Instruction::LocalGet(i as u32));
            }
            body.instruction(&Instruction::Call(adapter_merged_idx));
            for (caller_r, adapter_r) in caller_type.results.iter().zip(adapter_type.results.iter())
            {
                if *adapter_r == ValType::I32 && *caller_r == ValType::I64 {
                    body.instruction(&Instruction::I64ExtendI32U);
                }
            }
            body.instruction(&Instruction::End);

            merged.functions.push(merger::MergedFunction {
                type_idx: info.caller_type_idx,
                body,
                origin: (info.comp_idx, info.mod_idx, u32::MAX),
                synthetic_kind: Some(merger::SyntheticKind::AdapterShim),
            });
            affected_modules.insert((info.comp_idx, info.mod_idx));
        }

        // Re-rewrite function bodies for every module that had an import
        // redirected to an adapter, so the already-encoded `call` instructions
        // pick up the corrected indices.
        for &(comp_idx, mod_idx) in &affected_modules {
            let module = &self.components[comp_idx].core_modules[mod_idx];

            let memory_base_offset = 0u64; // only nonzero for shared-memory rebasing
            let module_memory = if self.config.address_rebasing {
                merger::module_memory_type(module)?
            } else {
                None
            };
            let memory64 = module_memory
                .as_ref()
                .map(|mem| mem.memory64)
                .unwrap_or(false);
            let memory_initial_pages = module_memory.as_ref().map(|mem| mem.initial);

            // Post-merge re-rewrite: recover this module's segment bases from
            // the merge-time record (`merged.*.len()` is now the total, not
            // the base).
            let (data_segment_base, elem_segment_base) = merged
                .segment_bases
                .get(&(comp_idx, mod_idx))
                .copied()
                .unwrap_or((0, 0));

            let index_maps = merger::build_index_maps_for_module(
                comp_idx,
                mod_idx,
                module,
                merged,
                self.config.memory_strategy,
                self.config.address_rebasing,
                memory_base_offset,
                memory64,
                memory_initial_pages,
                data_segment_base,
                elem_segment_base,
                // #326: this adapter-redirect re-rewrite runs with
                // `memory_base_offset == 0` (no rebasing), so no reloc
                // consumption is needed here.
                None,
            );

            let import_func_count = module
                .imports
                .iter()
                .filter(|i| matches!(i.kind, parser::ImportKind::Function(_)))
                .count() as u32;

            // Walk through defined functions of this module and re-rewrite
            // their bodies using the corrected index maps.
            for (old_idx, &type_idx) in module.functions.iter().enumerate() {
                let old_func_idx = import_func_count + old_idx as u32;
                let param_count = module
                    .types
                    .get(type_idx as usize)
                    .map(|ty| ty.params.len() as u32)
                    .unwrap_or(0);

                let body =
                    merger::extract_function_body(module, old_idx, param_count, &index_maps)?;

                // Find and replace the corresponding MergedFunction entry.
                if let Some(mf) = merged
                    .functions
                    .iter_mut()
                    .find(|f| f.origin == (comp_idx, mod_idx, old_func_idx))
                {
                    mf.body = body;
                }
            }
        }

        log::info!(
            "Wired {} adapter(s) into {} source module(s); {} identity trampoline(s) inlined",
            adapters.len(),
            affected_modules.len(),
            inlined_count
        );

        Ok(inlined_count)
    }

    /// Generate task.return shim functions for internal fused async calls.
    ///
    /// For each [task-return]N import used by an internal async callee,
    /// generates a shim function that stores result params to globals.
    /// The callback-driving adapter reads these globals after EXIT.
    fn generate_task_return_shims(
        &self,
        merged: &mut merger::MergedModule,
        graph: &resolver::DependencyGraph,
    ) -> Result<()> {
        use std::collections::{HashMap, HashSet};

        // Collect component indices that have internal async adapter sites
        let async_callee_components: HashSet<usize> = graph
            .adapter_sites
            .iter()
            .filter(|site| site.is_async_lift)
            .map(|site| site.to_component)
            .collect();

        if async_callee_components.is_empty() {
            return Ok(());
        }

        // For each async callee component, build:
        //   - name_to_result: function name → result type (via Lifts)
        //   - taskreturn_types: ordered list of resolved TaskReturn result
        //     types (used for greedy ordered claiming when name matching
        //     fails for shims whose original_func_name couldn't be recovered)
        let mut comp_func_result_types: HashMap<usize, HashMap<String, parser::ComponentValType>> =
            HashMap::new();
        let mut comp_taskreturn_types: HashMap<usize, Vec<parser::ComponentValType>> =
            HashMap::new();
        for &comp_idx in &async_callee_components {
            let comp = &self.components[comp_idx];
            let mut name_to_result: HashMap<String, parser::ComponentValType> = HashMap::new();

            // Build core_func_index → result type from canonical Lift entries.
            let mut core_func_to_result: HashMap<u32, parser::ComponentValType> = HashMap::new();
            for entry in &comp.canonical_functions {
                if let parser::CanonicalEntry::Lift {
                    core_func_index,
                    type_index,
                    ..
                } = entry
                    && let Some(td) = comp.get_type_definition(*type_index)
                    && let parser::ComponentTypeKind::Function { results, .. } = &td.kind
                    && let Some((_, ty)) = results.first()
                {
                    core_func_to_result.insert(
                        *core_func_index,
                        component_wrap::resolve_component_val_type(ty, comp),
                    );
                }
            }

            // Build component-level core func index → core export name.
            // Walk core_entity_order: each CoreAlias of a Function export
            // bumps the component core func counter and records the name.
            // CanonicalFunction entries also bump the counter (with no name).
            let mut comp_corefn_to_name: HashMap<u32, String> = HashMap::new();
            let mut corefn_idx = 0u32;
            for def in &comp.core_entity_order {
                match def {
                    parser::CoreEntityDef::CoreAlias(alias_idx) => {
                        if let Some(parser::ComponentAliasEntry::CoreInstanceExport {
                            kind: wasmparser::ExternalKind::Func,
                            name,
                            ..
                        }) = comp.component_aliases.get(*alias_idx)
                        {
                            comp_corefn_to_name.insert(corefn_idx, name.clone());
                            corefn_idx += 1;
                        }
                    }
                    parser::CoreEntityDef::CanonicalFunction(canon_idx) => {
                        if let Some(entry) = comp.canonical_functions.get(*canon_idx)
                            && !matches!(entry, parser::CanonicalEntry::Lift { .. })
                        {
                            corefn_idx += 1;
                        }
                    }
                }
            }

            // For each Lift, look up the alias name and extract the function
            // name from `[async-lift]<iface>#<func>` (or just `[async-lift]<func>`).
            for entry in &comp.canonical_functions {
                if let parser::CanonicalEntry::Lift {
                    core_func_index, ..
                } = entry
                    && let Some(name) = comp_corefn_to_name.get(core_func_index)
                    && let Some(rest) = name.strip_prefix("[async-lift]")
                    && let Some(rt) = core_func_to_result.get(core_func_index)
                {
                    let func_name = rest.rsplit_once('#').map(|(_, n)| n).unwrap_or(rest);
                    name_to_result.insert(func_name.to_string(), rt.clone());
                }
            }
            // Collect ordered TaskReturn types for greedy claiming fallback.
            let tr_types: Vec<parser::ComponentValType> = comp
                .canonical_functions
                .iter()
                .filter_map(|entry| match entry {
                    parser::CanonicalEntry::TaskReturn {
                        result: Some(t), ..
                    } => Some(component_wrap::resolve_component_val_type(t, comp)),
                    _ => None,
                })
                .collect();
            comp_taskreturn_types.insert(comp_idx, tr_types);

            log::debug!(
                "comp {} async-result name→type entries: {}",
                comp_idx,
                name_to_result.len()
            );
            comp_func_result_types.insert(comp_idx, name_to_result);
        }

        // Build mapping: (component_idx, func_name) → element segment position.
        // The main module (mod 0) has task-return imports in a specific order.
        // The forwarding module mirrors this order. The element segment at
        // position N has the merged import for the Nth task-return function.
        // We track positions (among task-return imports only) so we can later
        // match shim globals to adapter functions.
        // Build mapping: (comp_idx, func_name) → element segment position.
        // Only count task-return imports that are resolved INTRA-COMPONENT
        // (forwarding). Directly-resolved imports don't go through element
        // segments and are handled by the name-based fallback.
        let mut func_name_to_elem_position: HashMap<(usize, String), usize> = HashMap::new();
        for &comp_idx in &async_callee_components {
            let component = &self.components[comp_idx];
            if let Some(module) = component.core_modules.first() {
                let mut elem_position = 0usize;
                let mut func_idx = 0u32;
                for module_imp in &module.imports {
                    if !matches!(module_imp.kind, parser::ImportKind::Function(_)) {
                        continue;
                    }
                    if module_imp.name.starts_with("[task-return]") {
                        // Check if this import is resolved intra-component
                        // (goes to a forwarding function, not a merged import)
                        let is_forwarding = merged
                            .function_index_map
                            .get(&(comp_idx, 0, func_idx))
                            .map(|&idx| idx >= merged.import_counts.func)
                            .unwrap_or(false);

                        if is_forwarding {
                            let func_name = module_imp
                                .name
                                .strip_prefix("[task-return]")
                                .unwrap_or(&module_imp.name)
                                .to_string();
                            func_name_to_elem_position.insert((comp_idx, func_name), elem_position);
                            elem_position += 1;
                        }
                    }
                    func_idx += 1;
                }
            }
        }

        // Find task.return imports belonging to async callee components
        // and generate shims for them.
        let mut affected_modules: HashSet<(usize, usize)> = HashSet::new();
        // Per-component cursor into comp_taskreturn_types — advances each
        // time we need to claim a TaskReturn entry by ordered position.
        let mut comp_tr_cursor: HashMap<usize, usize> = HashMap::new();

        for (import_idx, imp) in merged.imports.iter().enumerate() {
            if !imp.name.starts_with("[task-return]") {
                continue;
            }
            // Check if this import belongs to an internal async callee
            let comp_idx = match imp.component_idx {
                Some(idx) if async_callee_components.contains(&idx) => idx,
                _ => continue,
            };

            // Extract original function name from the source core module's
            // `[task-return]<name>` import, used for the adapter's name-based
            // shim matching and for result-type resolution below.
            //
            // The merged FUNCTION index for this import is its position
            // among function imports in `merged.imports`, NOT its position
            // in the imports vector overall. Compute it by counting only
            // function imports up to import_idx.
            let merged_func_idx = merged.imports[..import_idx]
                .iter()
                .filter(|i| matches!(i.entity_type, wasm_encoder::EntityType::Function(_)))
                .count() as u32;
            let mut original_func_name = imp.name.clone();
            let component = &self.components[comp_idx];
            if let Some(module) = component.core_modules.first() {
                let mut fidx = 0u32;
                for mimp in &module.imports {
                    if !matches!(mimp.kind, parser::ImportKind::Function(_)) {
                        continue;
                    }
                    if mimp.name.starts_with("[task-return]")
                        && merged.function_index_map.get(&(comp_idx, 0, fidx)).copied()
                            == Some(merged_func_idx)
                    {
                        original_func_name = mimp
                            .name
                            .strip_prefix("[task-return]")
                            .unwrap_or(&mimp.name)
                            .to_string();
                    }
                    fidx += 1;
                }
            }

            // Get the import's function type to know the param signature.
            let import_type = match &imp.entity_type {
                wasm_encoder::EntityType::Function(type_idx) => {
                    merged.types.get(*type_idx as usize).cloned()
                }
                _ => continue,
            };
            let import_type = match import_type {
                Some(t) => t,
                None => continue,
            };

            // Generate globals for each param (the result values)
            let mut result_globals = Vec::new();
            for param_ty in &import_type.params {
                let global_idx = merged.import_counts.global + merged.globals.len() as u32;
                merged.globals.push(merger::MergedGlobal {
                    ty: wasm_encoder::GlobalType {
                        val_type: *param_ty,
                        mutable: true,
                        shared: false,
                    },
                    init_expr: match param_ty {
                        wasm_encoder::ValType::I32 => wasm_encoder::ConstExpr::i32_const(0),
                        wasm_encoder::ValType::I64 => wasm_encoder::ConstExpr::i64_const(0),
                        wasm_encoder::ValType::F32 => {
                            wasm_encoder::ConstExpr::f32_const(0.0_f32.into())
                        }
                        wasm_encoder::ValType::F64 => {
                            wasm_encoder::ConstExpr::f64_const(0.0_f64.into())
                        }
                        _ => wasm_encoder::ConstExpr::i32_const(0),
                    },
                });
                result_globals.push((global_idx, *param_ty));
            }

            // Resolve result type early — needed both for shim body (when
            // we add callee-side stabilization for nested indirections) and
            // for the TaskReturnShimInfo stored later.
            let mut early_result_type = comp_func_result_types
                .get(&comp_idx)
                .and_then(|m| m.get(&original_func_name))
                .cloned();
            if early_result_type.is_none()
                && let Some(tr_list) = comp_taskreturn_types.get(&comp_idx)
            {
                let comp = &self.components[comp_idx];
                let cursor_peek = comp_tr_cursor.entry(comp_idx).or_insert(0);
                // Peek without advancing — we'll re-resolve later with the
                // same cursor state for the canonical TaskReturnShimInfo.
                let mut peek_cursor = *cursor_peek;
                while peek_cursor < tr_list.len() {
                    let candidate = &tr_list[peek_cursor];
                    peek_cursor += 1;
                    let flat =
                        component_wrap::flat_task_return_params_resolved(Some(candidate), comp);
                    if flat == import_type.params {
                        early_result_type = Some(candidate.clone());
                        break;
                    }
                }
            }

            // For lists with indirections (e.g., list<record<string,_>>),
            // the wit-bindgen Cleanup guard for the records buffer drops
            // when the async block ends — between EXIT and our adapter
            // reading globals. To survive that race, the shim deep-copies
            // both the records buffer and each indirect string into a
            // stable callee-side allocation, then stores stable pointers
            // to globals. The adapter's existing cross-mem copy then
            // operates on stable data.
            let stabilization = early_result_type.as_ref().and_then(|ty| match ty {
                parser::ComponentValType::List(elem)
                | parser::ComponentValType::FixedSizeList(elem, _) => {
                    let indirections = crate::adapter::fact::collect_indirections(elem, 0);
                    if indirections.is_empty() {
                        None
                    } else {
                        let (elem_size, elem_align) = crate::adapter::fact::cabi_size_align(elem);
                        Some((elem_size, elem_align, indirections))
                    }
                }
                _ => None,
            });

            let (callee_realloc_for_shim, callee_memory_for_shim) = if stabilization.is_some() {
                (
                    merger::component_realloc_index(merged, comp_idx),
                    merger::component_memory_index(merged, comp_idx),
                )
            } else {
                (None, 0)
            };

            // Generate shim function. Default body: store args to globals.
            // With stabilization: copy records + strings to stable callee
            // buffers first, then store stable pointers.
            let shim_func_idx = merged.import_counts.func + merged.functions.len() as u32;
            let shim_type = merger::Merger::find_or_add_type(
                &mut merged.types,
                &import_type.params,
                &[], // void return
            );

            let body = if let (Some((elem_size, elem_align, indirections)), Some(realloc_fn)) =
                (stabilization.as_ref(), callee_realloc_for_shim)
            {
                generate_stabilizing_shim(
                    &result_globals,
                    *elem_size,
                    *elem_align,
                    indirections,
                    realloc_fn,
                    callee_memory_for_shim,
                )
            } else {
                let mut b = wasm_encoder::Function::new([]);
                for (i, (global_idx, _)) in result_globals.iter().enumerate() {
                    b.instruction(&wasm_encoder::Instruction::LocalGet(i as u32));
                    b.instruction(&wasm_encoder::Instruction::GlobalSet(*global_idx));
                }
                b.instruction(&wasm_encoder::Instruction::End);
                b
            };

            merged.functions.push(merger::MergedFunction {
                type_idx: shim_type,
                body,
                origin: (comp_idx, 0, u32::MAX),
                synthetic_kind: Some(merger::SyntheticKind::TaskReturnShim),
            });

            // Export the shim so the component wrapper can alias it
            // instead of using canonical task.return.
            merged.exports.push(merger::MergedExport {
                name: format!("$task_return_shim_{}", import_idx),
                kind: wasm_encoder::ExportKind::Func,
                index: shim_func_idx,
            });

            // Remap the task.return import to the shim in function_index_map.
            // Only match direct imports with the fused name.
            let component = &self.components[comp_idx];
            for (mod_idx, module) in component.core_modules.iter().enumerate() {
                let mut func_idx = 0u32;
                for module_imp in &module.imports {
                    if !matches!(module_imp.kind, parser::ImportKind::Function(_)) {
                        continue;
                    }
                    if module_imp.name == imp.name
                        || (module_imp.name.starts_with("[task-return]")
                            && merged
                                .imports
                                .get(
                                    *merged
                                        .function_index_map
                                        .get(&(comp_idx, mod_idx, func_idx))
                                        .unwrap_or(&u32::MAX)
                                        as usize,
                                )
                                .is_some_and(|m| m.name == imp.name))
                    {
                        merged
                            .function_index_map
                            .insert((comp_idx, mod_idx, func_idx), shim_func_idx);
                        affected_modules.insert((comp_idx, mod_idx));
                    }
                    func_idx += 1;
                }
            }

            // Note: intra-component forwarding functions (call_indirect table[N])
            // for this task.return are handled by the component wrapper, which
            // provides the shim export ($task_return_shim_N) as the table entry.

            // Find the WIT result type by matching CanonicalEntry::TaskReturn
            // entries from the source component against the import's flat
            // core params. Without this, the adapter treats the result as
            // opaque bytes and can't compute correct sizes for typed lists.
            // Resolve result type. First try by name lookup (works for
            // shims whose source core import was directly mapped to a
            // merged import). Fall back to ordered claim from the source
            // component's TaskReturn entries — pick the next entry whose
            // flat shape matches the import. Greedy ordering gives a
            // stable per-component pairing for the typical case where
            // the merger generates shims in source canonical order.
            let mut result_type = comp_func_result_types
                .get(&comp_idx)
                .and_then(|m| m.get(&original_func_name))
                .cloned();
            if result_type.is_none()
                && let Some(tr_list) = comp_taskreturn_types.get(&comp_idx)
            {
                let comp = &self.components[comp_idx];
                let cursor = comp_tr_cursor.entry(comp_idx).or_insert(0);
                while *cursor < tr_list.len() {
                    let candidate = &tr_list[*cursor];
                    *cursor += 1;
                    let flat =
                        component_wrap::flat_task_return_params_resolved(Some(candidate), comp);
                    if flat == import_type.params {
                        result_type = Some(candidate.clone());
                        break;
                    }
                }
            }
            log::debug!(
                "task.return shim {} '{}' orig='{}' typed={}",
                import_idx,
                imp.name,
                original_func_name,
                result_type.is_some()
            );

            // Store shim info for the adapter to use
            merged.task_return_shims.insert(
                import_idx as u32,
                merger::TaskReturnShimInfo {
                    shim_func: shim_func_idx,
                    result_globals,
                    component_idx: comp_idx,
                    import_name: imp.name.clone(),
                    original_func_name: original_func_name.clone(),
                    result_type,
                },
            );

            let shim = &merged.task_return_shims[&(import_idx as u32)];
            log::info!(
                "task.return shim: import {} '{}' orig='{}' → shim func {} globals {:?}",
                import_idx,
                imp.name,
                shim.original_func_name,
                shim.shim_func,
                shim.result_globals
                    .iter()
                    .map(|(g, _)| *g)
                    .collect::<Vec<_>>(),
            );
        }

        // Re-rewrite function bodies for affected modules
        for &(comp_idx, mod_idx) in &affected_modules {
            let module = &self.components[comp_idx].core_modules[mod_idx];
            let (data_segment_base, elem_segment_base) = merged
                .segment_bases
                .get(&(comp_idx, mod_idx))
                .copied()
                .unwrap_or((0, 0));
            let index_maps = merger::build_index_maps_for_module(
                comp_idx,
                mod_idx,
                module,
                merged,
                self.config.memory_strategy,
                self.config.address_rebasing,
                0u64,
                false,
                None,
                data_segment_base,
                elem_segment_base,
                None, // code_addr_relocs (#326): base 0, no rebasing on this pass
            );
            let import_func_count = module
                .imports
                .iter()
                .filter(|i| matches!(i.kind, parser::ImportKind::Function(_)))
                .count() as u32;

            for (old_idx, &type_idx) in module.functions.iter().enumerate() {
                let old_func_idx = import_func_count + old_idx as u32;
                let param_count = module
                    .types
                    .get(type_idx as usize)
                    .map(|ty| ty.params.len() as u32)
                    .unwrap_or(0);
                let body =
                    merger::extract_function_body(module, old_idx, param_count, &index_maps)?;
                if let Some(mf) = merged
                    .functions
                    .iter_mut()
                    .find(|f| f.origin == (comp_idx, mod_idx, old_func_idx))
                {
                    mf.body = body;
                }
            }
        }

        // Patch element segments: replace task.return import references
        // with shim function references. This ensures that indirect calls
        // through element-segment-initialized tables call the shim instead
        // of the (stub) import.
        if !merged.task_return_shims.is_empty() {
            // Build a map: import merged index → shim func index
            let mut import_to_shim: HashMap<u32, u32> = HashMap::new();
            for (import_idx, shim_info) in &merged.task_return_shims {
                import_to_shim.insert(*import_idx, shim_info.shim_func);
            }

            for elem in &mut merged.elements {
                if let crate::segments::ReindexedElementItems::Functions(ref mut indices) =
                    elem.items
                {
                    for idx in indices.iter_mut() {
                        if let Some(&shim_idx) = import_to_shim.get(idx) {
                            log::debug!(
                                "element segment: replaced import {} with shim {}",
                                idx,
                                shim_idx,
                            );
                            *idx = shim_idx;
                        }
                    }
                }
            }

            // Build async_result_globals: (comp_idx, func_name) → globals.
            // For each func_name, find its element segment position, look up
            // the shim function at that position, and get its globals.
            let shim_func_to_globals: HashMap<u32, Vec<(u32, wasm_encoder::ValType)>> = merged
                .task_return_shims
                .values()
                .map(|s| (s.shim_func, s.result_globals.clone()))
                .collect();

            for ((comp_idx, func_name), elem_pos) in &func_name_to_elem_position {
                // Find the component's $imports table index.
                // The forwarding module (typically mod 2) defines the table.
                // Look up via table_index_map.
                let comp_tables: HashSet<u32> = merged
                    .table_index_map
                    .iter()
                    .filter(|&(&(ci, _, _), _)| ci == *comp_idx)
                    .map(|(_, &idx)| idx)
                    .collect();

                // Find the element segment for this component's table
                for elem in &merged.elements {
                    let elem_table = match &elem.mode {
                        crate::segments::ElementSegmentMode::Active { table_index, .. } => {
                            *table_index
                        }
                        _ => continue,
                    };
                    if !comp_tables.contains(&elem_table) {
                        continue;
                    }
                    if let crate::segments::ReindexedElementItems::Functions(ref indices) =
                        elem.items
                        && let Some(func_idx) = indices.get(*elem_pos)
                        && let Some(globals) = shim_func_to_globals.get(func_idx)
                    {
                        merged
                            .async_result_globals
                            .insert((*comp_idx, func_name.clone()), globals.clone());
                        break;
                    }
                }
            }
            log::info!(
                "async_result_globals: {} entries: {:?}",
                merged.async_result_globals.len(),
                merged.async_result_globals.keys().collect::<Vec<_>>(),
            );
        }

        Ok(())
    }

    /// Encode the merged module to binary
    fn encode_output(
        &self,
        merged: &MergedModule,
        adapters: &[adapter::AdapterFunction],
        extra_custom_sections: &[(&str, Vec<u8>)],
        dwarf_sections: &[(String, Vec<u8>)],
    ) -> Result<Vec<u8>> {
        let mut module = EncodedModule::new();

        // Encode types
        if !merged.types.is_empty() {
            let mut types = wasm_encoder::TypeSection::new();
            for ty in &merged.types {
                types
                    .ty()
                    .function(ty.params.iter().copied(), ty.results.iter().copied());
            }
            module.section(&types);
        }

        // Encode imports (remaining unresolved imports)
        if !merged.imports.is_empty() {
            let mut imports = wasm_encoder::ImportSection::new();
            for imp in &merged.imports {
                imports.import(&imp.module, &imp.name, imp.entity_type);
            }
            module.section(&imports);
        }

        // Encode functions (type references)
        if !merged.functions.is_empty() || !adapters.is_empty() {
            let mut functions = wasm_encoder::FunctionSection::new();
            for func in &merged.functions {
                functions.function(func.type_idx);
            }
            // Add adapter function types
            for adapter in adapters {
                functions.function(adapter.type_idx);
            }
            module.section(&functions);
        }

        // Encode tables
        if !merged.tables.is_empty() {
            let mut tables = wasm_encoder::TableSection::new();
            for table in &merged.tables {
                tables.table(*table);
            }
            module.section(&tables);
        }

        // Encode memories
        if !merged.memories.is_empty() {
            let mut memories = wasm_encoder::MemorySection::new();
            for mem in &merged.memories {
                memories.memory(*mem);
            }
            module.section(&memories);
        }

        // Encode globals
        if !merged.globals.is_empty() {
            let mut globals = wasm_encoder::GlobalSection::new();
            for global in &merged.globals {
                globals.global(global.ty, &global.init_expr);
            }
            module.section(&globals);
        }

        // Encode exports
        if !merged.exports.is_empty() {
            let mut exports = wasm_encoder::ExportSection::new();
            for exp in &merged.exports {
                exports.export(&exp.name, exp.kind, exp.index);
            }
            module.section(&exports);
        }

        // Encode start function if present
        if let Some(start_idx) = merged.start_function {
            module.section(&wasm_encoder::StartSection {
                function_index: start_idx,
            });
        }

        // Encode element section (reindexed segments)
        if !merged.elements.is_empty() {
            let mut elements = wasm_encoder::ElementSection::new();
            for segment in &merged.elements {
                segments::encode_element_segment(&mut elements, segment);
            }
            module.section(&elements);
        }

        // Encode data count section before code (required by bulk memory)
        if !merged.data_segments.is_empty() {
            module.section(&wasm_encoder::DataCountSection {
                count: merged.data_segments.len() as u32,
            });
        }

        // Encode code section
        if !merged.functions.is_empty() || !adapters.is_empty() {
            let mut code = wasm_encoder::CodeSection::new();

            // Add merged function bodies
            for func in &merged.functions {
                code.function(&func.body);
            }

            // Add adapter function bodies
            for adapter in adapters {
                code.function(&adapter.body);
            }

            module.section(&code);
        }

        // Encode data section (reindexed segments)
        if !merged.data_segments.is_empty() {
            let mut data = wasm_encoder::DataSection::new();
            for segment in &merged.data_segments {
                data.segment(segments::encode_data_segment(segment));
            }
            module.section(&data);
        }

        // Handle custom sections based on config
        if self.config.custom_sections != CustomSectionHandling::Drop {
            let kept: Vec<(String, Vec<u8>)> = merged
                .custom_sections
                .iter()
                .filter(|(name, _)| {
                    if !self.config.preserve_names && name == "name" {
                        return false;
                    }
                    // #326: `linking` + `reloc.*` metadata describes each INPUT
                    // module's own section layout; after fusion the section
                    // indices/offsets they name are stale (and, where address
                    // rebasing consumed them, already applied). Never emit them
                    // on the fused module.
                    if name == "linking" || name.starts_with("reloc.") {
                        return false;
                    }
                    // Only PassThrough emits raw per-input `.debug_*`
                    // sections. Strip drops them; Remap drops them here and
                    // emits a single remapped set below.
                    if self.config.dwarf_handling != DwarfHandling::PassThrough
                        && name.starts_with(".debug_")
                    {
                        return false;
                    }
                    true
                })
                .cloned()
                .collect();
            // Under Merge, coalesce same-name tool-metadata sections
            // (`producers`, `target_features`) into one section each, in
            // the canonical order LLVM's wasm reader enforces (#222) —
            // duplicate `producers` sections make llvm-dwarfdump reject
            // the whole module.
            let kept = if self.config.custom_sections == CustomSectionHandling::Merge {
                custom_merge::coalesce(&kept)
            } else {
                kept
            };
            for (name, contents) in &kept {
                module.section(&wasm_encoder::CustomSection {
                    name: std::borrow::Cow::Borrowed(name),
                    data: std::borrow::Cow::Borrowed(contents),
                });
            }

            // #328: emit ONE coalesced `name` section (function names) whose
            // indices are already remapped into the fused space. This
            // replaces the old verbatim per-module `name` copies (duplicate
            // sections → llvm-dwarfdump rejects; stale indices → wrong
            // labels). The merger no longer routes `name` into
            // `custom_sections`, so this is the sole emitter under
            // `preserve_names`.
            if self.config.preserve_names && !merged.fused_function_names.is_empty() {
                let mut fnames = wasm_encoder::NameMap::new();
                for (idx, fname) in &merged.fused_function_names {
                    fnames.append(*idx, fname);
                }
                let mut names = wasm_encoder::NameSection::new();
                names.functions(&fnames);
                module.section(&names);
            }
        }

        // Remapped DWARF (DwarfHandling::Remap): a single `.debug_*` set
        // whose code addresses target the fused code section, replacing
        // the per-input sections skipped above. Emitted before the
        // meld-metadata extras so they sit at a stable byte offset
        // across the encode passes (the attestation/provenance hash
        // covers these bytes; the extras are stripped before verifying).
        for (name, contents) in dwarf_sections {
            module.section(&wasm_encoder::CustomSection {
                name: std::borrow::Cow::Borrowed(name),
                data: std::borrow::Cow::Borrowed(contents),
            });
        }

        for (name, contents) in extra_custom_sections {
            module.section(&wasm_encoder::CustomSection {
                name: std::borrow::Cow::Borrowed(*name),
                data: std::borrow::Cow::Borrowed(contents),
            });
        }

        Ok(module.finish())
    }

    fn build_attestation_payload(
        &self,
        output_bytes: &[u8],
        stats: &FusionStats,
    ) -> Result<(&'static str, Vec<u8>)> {
        #[cfg(feature = "attestation")]
        {
            let attestation = self.build_wsc_attestation(output_bytes, stats);
            let payload = attestation
                .to_json_compact()
                .map_err(|e| {
                    Error::EncodingError(format!("attestation serialization failed: {e}"))
                })?
                .into_bytes();
            Ok((wsc_attestation::TRANSFORMATION_ATTESTATION_SECTION, payload))
        }

        #[cfg(not(feature = "attestation"))]
        {
            let attestation = self.build_attestation(output_bytes, stats);
            let bytes = attestation.to_bytes().map_err(|e| {
                Error::EncodingError(format!("attestation serialization failed: {e}"))
            })?;
            Ok((FUSION_ATTESTATION_SECTION, bytes))
        }
    }

    #[cfg(not(feature = "attestation"))]
    fn build_attestation(
        &self,
        output_bytes: &[u8],
        stats: &FusionStats,
    ) -> attestation::FusionAttestation {
        let mut builder = FusionAttestationBuilder::new("meld", env!("CARGO_PKG_VERSION"))
            .memory_strategy(self.memory_strategy_label())
            .reproducible(self.config.reproducible);

        for (index, component) in self.components.iter().enumerate() {
            // #341: under `--reproducible` the input name must not carry the
            // caller-supplied path — otherwise byte-identical inputs at
            // different paths (e.g. two CI checkouts / temp dirs) fuse to
            // different sha256s. Use the positional identifier; the input's
            // content stays pinned by `original_hash` below.
            let name = if self.config.reproducible {
                format!("component-{}", index)
            } else {
                component
                    .name
                    .clone()
                    .unwrap_or_else(|| format!("component-{}", index))
            };
            builder = builder.add_input_descriptor(
                name,
                component.core_modules.len(),
                component.original_hash.clone(),
                component.original_size as u64,
            );
        }

        builder.build(output_bytes, stats)
    }

    #[cfg(feature = "attestation")]
    fn build_wsc_attestation(
        &self,
        output_bytes: &[u8],
        stats: &FusionStats,
    ) -> wsc_attestation::TransformationAttestation {
        use std::collections::HashMap;
        use wsc_attestation::{
            ArtifactDescriptor, AttestationSignature, InputArtifact, SignatureStatus, ToolInfo,
            TransformationAttestation, TransformationType,
        };

        let output_hash = attestation::compute_sha256(output_bytes);
        // #325: in reproducible mode, derive the id from the output content and
        // the timestamp from SOURCE_DATE_EPOCH so the fused artifact is
        // byte-stable across runs; otherwise keep the wall-clock/random id.
        let (timestamp, attestation_id) = if self.config.reproducible {
            (
                attestation::chrono_timestamp_from(attestation::source_date_epoch()),
                attestation::generate_uuid_from(attestation::entropy_from_hex(&output_hash)),
            )
        } else {
            (
                attestation::chrono_timestamp(),
                attestation::generate_uuid(),
            )
        };

        let mut inputs = Vec::new();
        for (index, component) in self.components.iter().enumerate() {
            // #341: see build_attestation — under `--reproducible` the input
            // name must not carry the caller-supplied path.
            let name = if self.config.reproducible {
                format!("component-{}", index)
            } else {
                component
                    .name
                    .clone()
                    .unwrap_or_else(|| format!("component-{}", index))
            };
            inputs.push(InputArtifact {
                artifact: ArtifactDescriptor {
                    name,
                    hash: component.original_hash.clone(),
                    size: component.original_size as u64,
                },
                signature_status: SignatureStatus::Unsigned,
                signature_info: None,
                provenance: None,
                transformation_chain: None,
            });
        }

        let mut tool_parameters = HashMap::new();
        tool_parameters.insert(
            "memory_strategy".to_string(),
            serde_json::json!(self.memory_strategy_label()),
        );
        tool_parameters.insert(
            "address_rebasing".to_string(),
            serde_json::json!(self.config.address_rebasing),
        );
        tool_parameters.insert(
            "preserve_names".to_string(),
            serde_json::json!(self.config.preserve_names),
        );
        tool_parameters.insert(
            "custom_sections".to_string(),
            serde_json::json!(self.custom_sections_label()),
        );
        tool_parameters.insert(
            "dwarf_handling".to_string(),
            serde_json::json!(self.dwarf_handling_label()),
        );
        tool_parameters.insert(
            "output_format".to_string(),
            serde_json::json!(self.output_format_label()),
        );

        let mut metadata = HashMap::new();
        metadata.insert(
            "memory_strategy".to_string(),
            serde_json::json!(self.memory_strategy_label()),
        );
        metadata.insert(
            "components_fused".to_string(),
            serde_json::json!(stats.components_fused),
        );
        metadata.insert(
            "modules_merged".to_string(),
            serde_json::json!(stats.modules_merged),
        );
        metadata.insert(
            "adapters_generated".to_string(),
            serde_json::json!(stats.adapter_functions),
        );
        metadata.insert(
            "imports_resolved".to_string(),
            serde_json::json!(stats.imports_resolved),
        );
        let size_reduction = if stats.input_size > 0 {
            ((stats.input_size as f64 - stats.output_size as f64) / stats.input_size as f64) * 100.0
        } else {
            0.0
        };
        metadata.insert(
            "size_reduction_percent".to_string(),
            serde_json::json!(size_reduction),
        );

        TransformationAttestation {
            version: "1.0".to_string(),
            transformation_type: TransformationType::Composition,
            attestation_id,
            timestamp: timestamp.clone(),
            output: ArtifactDescriptor {
                name: "fused.wasm".to_string(),
                hash: output_hash,
                size: output_bytes.len() as u64,
            },
            inputs,
            tool: ToolInfo {
                name: "meld".to_string(),
                version: env!("CARGO_PKG_VERSION").to_string(),
                tool_hash: None,
                parameters: tool_parameters,
            },
            attestation_signature: AttestationSignature {
                algorithm: "unsigned".to_string(),
                signature: String::new(),
                key_id: None,
                public_key: None,
                signer_identity: None,
                certificate_chain: None,
                rekor_uuid: None,
                signed_at: timestamp,
            },
            metadata,
        }
    }

    fn memory_strategy_label(&self) -> &'static str {
        match self.config.memory_strategy {
            MemoryStrategy::SharedMemory => "shared",
            MemoryStrategy::MultiMemory => "multi",
            // Unreachable after `resolve_auto_memory_strategy`; kept as an
            // honest label in case attestation is ever built pre-resolution.
            MemoryStrategy::Auto => "auto",
        }
    }

    #[cfg(feature = "attestation")]
    fn custom_sections_label(&self) -> &'static str {
        match self.config.custom_sections {
            CustomSectionHandling::Merge => "merge",
            CustomSectionHandling::Prefix => "prefix",
            CustomSectionHandling::Drop => "drop",
        }
    }

    #[cfg(feature = "attestation")]
    fn dwarf_handling_label(&self) -> &'static str {
        match self.config.dwarf_handling {
            DwarfHandling::Strip => "strip",
            DwarfHandling::PassThrough => "passthrough",
            DwarfHandling::Remap => "remap",
        }
    }

    #[cfg(feature = "attestation")]
    fn output_format_label(&self) -> &'static str {
        match self.config.output_format {
            OutputFormat::CoreModule => "core-module",
            OutputFormat::Component => "component",
        }
    }
}

/// Recursively flatten nested sub-components into a flat `Vec<ParsedComponent>`.
///
/// When a composed component contains `ComponentSection` payloads, the parser
/// collects them as `sub_components`. This function:
///
/// 1. Recursively flattens each sub-component (handling arbitrary nesting).
/// 2. Translates the outer component's `component_instances` and
///    `component_aliases` wiring into `imports`/`exports` on the
///    sub-components so the existing cross-component resolver can
///    handle inter-sub-component connections.
///
/// When no sub-components exist, returns the input component as-is
/// (backward compatible).
fn flatten_nested_components(
    mut outer: ParsedComponent,
) -> Result<(Vec<ParsedComponent>, WiringHints)> {
    if outer.sub_components.is_empty() {
        return Ok((vec![outer], std::collections::HashMap::new()));
    }

    // Take sub_components out of outer so we can move them and still borrow outer later.
    let sub_components = std::mem::take(&mut outer.sub_components);

    // Recursively flatten each sub-component
    let mut flattened_subs: Vec<Vec<ParsedComponent>> = Vec::new();
    let mut child_hints: WiringHints = std::collections::HashMap::new();
    for sub in sub_components {
        let (flat, hints) = flatten_nested_components(sub)?;
        // Child hints are relative to their own flat list; we'll adjust later
        child_hints.extend(hints);
        flattened_subs.push(flat);
    }

    // The outer component itself may contain core modules, instances,
    // canonical functions, etc. If it does, it becomes the first entry
    // in the flat list (index 0). Sub-component ranges are offset accordingly.
    let outer_has_content = !outer.core_modules.is_empty();
    let base_offset = if outer_has_content { 1usize } else { 0usize };

    // Build a mapping from original sub-component index to the range
    // of indices in the final flat list.
    let mut sub_index_ranges: Vec<std::ops::Range<usize>> = Vec::new();
    let mut offset = base_offset;
    for subs in &flattened_subs {
        let len = subs.len();
        sub_index_ranges.push(offset..offset + len);
        offset += len;
    }

    // Collect all components into one vec
    let mut result: Vec<ParsedComponent> = Vec::new();

    // Include the outer component itself if it has core modules
    if outer_has_content {
        result.push(outer.clone());
    }

    for subs in flattened_subs {
        result.extend(subs);
    }

    // Propagate the outer component's wiring into the flat sub-components
    let wiring_hints = propagate_outer_wiring(&outer, &sub_index_ranges, &mut result)?;

    Ok((result, wiring_hints))
}

/// Translate the outer component's `component_instances` and `component_aliases`
/// into `imports` and `exports` on the flattened sub-components.
///
/// The outer component's `ComponentInstanceSection` describes how sub-components
/// are wired together (which sub-component's exports satisfy which other
/// sub-component's imports). We parse this wiring and add matching
/// `ComponentImport`/`ComponentExport` entries so the existing cross-component
/// resolver can handle the connections.
///
/// The outer component's top-level `imports` (e.g., WASI interfaces) are
/// propagated to whichever sub-component consumes them.
/// Directed resolution hints from the composition graph.
/// Maps (importer_flat_idx, interface_name) → exporter_flat_idx.
pub type WiringHints = std::collections::HashMap<(usize, String), usize>;

#[allow(clippy::collapsible_if)]
fn propagate_outer_wiring(
    outer: &ParsedComponent,
    sub_index_ranges: &[std::ops::Range<usize>],
    result: &mut [ParsedComponent],
) -> Result<WiringHints> {
    use parser::ComponentLevelInstance;
    use wasmparser::ComponentExternalKind;
    let mut wiring_hints: WiringHints = std::collections::HashMap::new();

    // Build a map: component-level instance index → info about that instance.
    // Component instances created by ComponentInstanceSection are numbered
    // sequentially. Each maps to either an instantiation of a sub-component
    // or a bag of exports.
    #[derive(Clone)]
    struct InstanceInfo {
        /// If this instance was created by instantiating a sub-component,
        /// this is the sub-component index in the original (pre-flattened)
        /// sub_components list.
        sub_component_idx: Option<u32>,
    }

    // Build instance info map indexed by ABSOLUTE instance index (not just
    // ComponentInstanceSection position). This handles imports, instantiations,
    // and alias-created instances.
    let mut instance_infos: std::collections::HashMap<u32, InstanceInfo> =
        std::collections::HashMap::new();
    for (abs_idx, def) in outer.component_instance_defs.iter().enumerate() {
        match def {
            parser::ComponentInstanceDef::Instance(ci_idx) => {
                if let Some(ci) = outer.component_instances.get(*ci_idx) {
                    match ci {
                        ComponentLevelInstance::Instantiate {
                            component_index, ..
                        } => {
                            instance_infos.insert(
                                abs_idx as u32,
                                InstanceInfo {
                                    sub_component_idx: Some(*component_index),
                                },
                            );
                        }
                        ComponentLevelInstance::FromExports(_) => {
                            instance_infos.insert(
                                abs_idx as u32,
                                InstanceInfo {
                                    sub_component_idx: None,
                                },
                            );
                        }
                    }
                }
            }
            parser::ComponentInstanceDef::InstanceExportAlias(alias_idx) => {
                // Chase alias: inherit the source instance's sub_component_idx
                // so instantiation args referencing this alias are correctly wired.
                if let Some(parser::ComponentAliasEntry::InstanceExport {
                    instance_index, ..
                }) = outer.component_aliases.get(*alias_idx)
                {
                    if let Some(info) = instance_infos.get(instance_index).cloned() {
                        instance_infos.insert(abs_idx as u32, info);
                    }
                }
            }
            parser::ComponentInstanceDef::Import(_) => {}
        }
    }

    // Build alias resolution: some component_aliases reference instance exports.
    // Track: alias index → (instance_index, export_name, kind)
    // This helps resolve when an instantiation arg references an aliased item.
    struct AliasResolution {
        instance_index: u32,
        kind: ComponentExternalKind,
        export_name: String,
    }
    let mut alias_resolutions: Vec<Option<AliasResolution>> = Vec::new();
    for alias in &outer.component_aliases {
        match alias {
            parser::ComponentAliasEntry::InstanceExport {
                kind,
                instance_index,
                name,
            } => {
                alias_resolutions.push(Some(AliasResolution {
                    instance_index: *instance_index,
                    kind: *kind,
                    export_name: name.clone(),
                }));
            }
            _ => {
                alias_resolutions.push(None);
            }
        }
    }

    // Now process ComponentInstanceSection entries to wire sub-components together.
    // When sub-component A is instantiated with an arg that comes from
    // sub-component B's export, we add a matching import to A and export to B
    // so the cross-component resolver will wire them.
    for ci in &outer.component_instances {
        if let ComponentLevelInstance::Instantiate {
            component_index,
            args,
        } = ci
        {
            let target_sub_idx = *component_index as usize;
            if target_sub_idx >= sub_index_ranges.len() {
                continue;
            }

            // The "first" flattened component for this sub-component is the
            // natural target for adding imports.
            let target_flat_idx = sub_index_ranges[target_sub_idx].start;

            for (arg_name, arg_kind, arg_index) in args {
                // The arg references something in the outer component's index
                // space. For ComponentExternalKind::Instance, arg_index is a
                // component instance index. Check if it maps to another
                // sub-component.
                if *arg_kind == ComponentExternalKind::Instance {
                    if let Some(info) = instance_infos.get(arg_index)
                        && let Some(source_sub_idx) = info.sub_component_idx
                    {
                        let source_sub = source_sub_idx as usize;
                        if source_sub < sub_index_ranges.len() {
                            let source_flat_idx = sub_index_ranges[source_sub].start;

                            // Add a component-level import to the target so the
                            // resolver sees it needs something named arg_name.
                            // Add a matching export to the source.
                            let import_name = arg_name.clone();
                            if !result[target_flat_idx]
                                .imports
                                .iter()
                                .any(|i| i.name == import_name)
                            {
                                result[target_flat_idx]
                                    .imports
                                    .push(parser::ComponentImport {
                                        name: import_name.clone(),
                                        ty: wasmparser::ComponentTypeRef::Instance(0),
                                    });
                            }
                            if !result[source_flat_idx]
                                .exports
                                .iter()
                                .any(|e| e.name == import_name)
                            {
                                result[source_flat_idx]
                                    .exports
                                    .push(parser::ComponentExport {
                                        name: import_name.clone(),
                                        kind: ComponentExternalKind::Instance,
                                        index: 0,
                                    });
                            }
                            // Record directed wiring hint
                            wiring_hints.insert((target_flat_idx, import_name), source_flat_idx);
                        }
                    }
                }

                // For other kinds, the arg references an alias. For Func/Type,
                // arg_index is a per-kind index into component_func_defs/component_type_defs
                // which may contain an InstanceExportAlias pointing to the actual alias.
                if *arg_kind == ComponentExternalKind::Component
                    || *arg_kind == ComponentExternalKind::Func
                    || *arg_kind == ComponentExternalKind::Type
                    || *arg_kind == ComponentExternalKind::Value
                {
                    // Resolve per-kind index to alias index
                    let alias_idx = match arg_kind {
                        ComponentExternalKind::Func => {
                            // Component func defs track how each func was created
                            outer
                                .component_func_defs
                                .get(*arg_index as usize)
                                .and_then(|def| {
                                    if let parser::ComponentFuncDef::InstanceExportAlias(ai) = def {
                                        Some(*ai)
                                    } else {
                                        None
                                    }
                                })
                        }
                        ComponentExternalKind::Type => outer
                            .component_type_defs
                            .get(*arg_index as usize)
                            .and_then(|def| {
                                if let parser::ComponentTypeDef::InstanceExportAlias(ai) = def {
                                    Some(*ai)
                                } else {
                                    None
                                }
                            }),
                        _ => {
                            // For Component/Value, arg_index might be direct alias
                            if (*arg_index as usize) < alias_resolutions.len() {
                                Some(*arg_index as usize)
                            } else {
                                None
                            }
                        }
                    };
                    let alias_idx = match alias_idx {
                        Some(idx) => idx,
                        None => continue,
                    };
                    if alias_idx < alias_resolutions.len()
                        && let Some(alias_res) = &alias_resolutions[alias_idx]
                    {
                        if let Some(info) = instance_infos.get(&alias_res.instance_index)
                            && let Some(source_sub_idx) = info.sub_component_idx
                        {
                            let source_sub = source_sub_idx as usize;
                            if source_sub < sub_index_ranges.len() {
                                let source_flat_idx = sub_index_ranges[source_sub].start;
                                let import_name = arg_name.clone();
                                if !result[target_flat_idx]
                                    .imports
                                    .iter()
                                    .any(|i| i.name == import_name)
                                {
                                    result[target_flat_idx]
                                        .imports
                                        .push(parser::ComponentImport {
                                            name: import_name.clone(),
                                            ty: wasmparser::ComponentTypeRef::Instance(0),
                                        });
                                }
                                if !result[source_flat_idx]
                                    .exports
                                    .iter()
                                    .any(|e| e.name == import_name)
                                {
                                    result[source_flat_idx]
                                        .exports
                                        .push(parser::ComponentExport {
                                            name: import_name.clone(),
                                            kind: alias_res.kind,
                                            index: 0,
                                        });
                                }
                                // Record directed wiring hint
                                wiring_hints.insert(
                                    (target_flat_idx, import_name.clone()),
                                    source_flat_idx,
                                );
                                // When the wiring renames an export (arg_name differs
                                // from alias export_name), add a synthetic core module
                                // export so the adapter site finder can locate the
                                // function by import_name.
                                if import_name != alias_res.export_name {
                                    for m in &mut result[source_flat_idx].core_modules {
                                        if let Some(original) = m
                                            .exports
                                            .iter()
                                            .find(|e| {
                                                e.name == alias_res.export_name
                                                    && e.kind == parser::ExportKind::Function
                                            })
                                            .cloned()
                                        {
                                            if !m.exports.iter().any(|e| e.name == import_name) {
                                                m.exports.push(parser::ModuleExport {
                                                    name: import_name,
                                                    kind: original.kind,
                                                    index: original.index,
                                                });
                                            }
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Propagate outer-level imports (e.g. WASI) to sub-components that need them.
    // Sub-components that already have matching imports keep them; we also
    // propagate to sub-components that have core modules importing names that
    // look like WASI interfaces but lack a component-level import for them.
    for outer_import in &outer.imports {
        for comp in result.iter_mut() {
            // Check if any core module in this sub-component imports something
            // that matches this outer import name (common for WASI interfaces).
            let needs_import = comp.core_modules.iter().any(|m| {
                m.imports
                    .iter()
                    .any(|i| i.module == outer_import.name || i.module.contains(&outer_import.name))
            });
            if needs_import && !comp.imports.iter().any(|i| i.name == outer_import.name) {
                comp.imports.push(outer_import.clone());
            }
        }
    }

    Ok(wiring_hints)
}

/// Generate a task.return shim body that deep-copies the records buffer
/// (and each indirect string) into a stable callee-side allocation before
/// storing the stabilized pointer to globals.
///
/// Why: wit-bindgen's lowering for `list<record-with-string>` allocates
/// the records buffer via `Cleanup::new`, whose drop guard runs at the
/// end of the async block — between EXIT and our adapter reading the
/// globals. The original records buffer is freed and overwritten with
/// allocator free-list patterns by the time the adapter sees it. This
/// shim makes a parallel copy that the callee allocator owns, free of
/// the Cleanup guard.
///
/// Shim signature: `(ptr: i32, len: i32) -> ()`.
/// Body shape (for `list<record { string, ... }>` with one indirection
/// at offset 0, sub-element size 1):
/// ```text
///   byte_count = len * elem_size
///   stable_records = realloc(0, 0, elem_align, byte_count)
///   memory.copy stable_records <- ptr, byte_count   ; intra-callee
///   for i in 0..len:
///     rec = stable_records + i*elem_size
///     for each indirection (offset, sub_elem_size) in indirections:
///       old_str = mem.load(rec + offset)
///       str_len = mem.load(rec + offset + 4) * sub_size
///       stable_str = realloc(0, 0, 1, str_len)
///       memory.copy stable_str <- old_str, str_len   ; intra-callee
///       mem.store(rec + offset, stable_str)
///   global[ptr_global] = stable_records
///   global[len_global] = len
/// ```
fn generate_stabilizing_shim(
    result_globals: &[(u32, wasm_encoder::ValType)],
    elem_size: u32,
    elem_align: u32,
    indirections: &[crate::adapter::fact::Indirection],
    realloc_func: u32,
    callee_memory: u32,
) -> wasm_encoder::Function {
    use wasm_encoder::{BlockType, Function, Instruction};

    // Locals layout (after the 2 i32 params: ptr=0, len=1):
    //   2 = stable_records
    //   3 = byte_count
    //   4 = i
    //   5 = rec
    //   6 = old_str
    //   7 = str_len
    //   8 = stable_str
    let l_stable = 2u32;
    let l_byte_count = 3u32;
    let l_i = 4u32;
    let l_rec = 5u32;
    let l_old_str = 6u32;
    let l_str_len = 7u32;
    let l_stable_str = 8u32;

    let mut body = Function::new([(7, wasm_encoder::ValType::I32)]);

    // byte_count = len * elem_size
    crate::adapter::fact::emit_overflow_guard(&mut body, 1, elem_size);
    body.instruction(&Instruction::LocalGet(1));
    body.instruction(&Instruction::I32Const(elem_size as i32));
    body.instruction(&Instruction::I32Mul);
    body.instruction(&Instruction::LocalSet(l_byte_count));

    // stable_records = realloc(0, 0, elem_align, byte_count)
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::I32Const(elem_align as i32));
    body.instruction(&Instruction::LocalGet(l_byte_count));
    crate::adapter::fact::emit_checked_realloc(&mut body, realloc_func, l_stable);

    // memory.copy stable_records <- ptr, byte_count (intra-callee, mem 0)
    body.instruction(&Instruction::LocalGet(l_stable));
    body.instruction(&Instruction::LocalGet(0));
    body.instruction(&Instruction::LocalGet(l_byte_count));
    body.instruction(&Instruction::MemoryCopy {
        dst_mem: callee_memory,
        src_mem: callee_memory,
    });

    // for i in 0..len: stabilize indirections in record i
    body.instruction(&Instruction::I32Const(0));
    body.instruction(&Instruction::LocalSet(l_i));
    body.instruction(&Instruction::Block(BlockType::Empty));
    body.instruction(&Instruction::Loop(BlockType::Empty));

    body.instruction(&Instruction::LocalGet(l_i));
    body.instruction(&Instruction::LocalGet(1));
    body.instruction(&Instruction::I32GeU);
    body.instruction(&Instruction::BrIf(1));

    // rec = stable_records + i * elem_size
    body.instruction(&Instruction::LocalGet(l_stable));
    body.instruction(&Instruction::LocalGet(l_i));
    body.instruction(&Instruction::I32Const(elem_size as i32));
    body.instruction(&Instruction::I32Mul);
    body.instruction(&Instruction::I32Add);
    body.instruction(&Instruction::LocalSet(l_rec));

    // The string-ness `kind` is unused here: callee-side stabilization is a
    // verbatim intra-memory deep-copy that PRESERVES bytes for both nested
    // strings and nested `list<u8>` — no transcoding happens at stabilization
    // time, so the string-ness signal does not change this raw copy. #286
    // 5d-pre: field-access over the type-carrying descriptor; `offset`/`sub_size`
    // stay references so the `*offset`/`*sub_size` body reads are unchanged.
    for ind in indirections {
        let offset = &ind.offset;
        let sub_size = &ind.sub_elem_size;
        let mem_arg_ptr = wasm_encoder::MemArg {
            offset: *offset as u64,
            align: 2,
            memory_index: callee_memory,
        };
        let mem_arg_len = wasm_encoder::MemArg {
            offset: (*offset + 4) as u64,
            align: 2,
            memory_index: callee_memory,
        };

        // old_str = mem.load(rec + offset)
        body.instruction(&Instruction::LocalGet(l_rec));
        body.instruction(&Instruction::I32Load(mem_arg_ptr));
        body.instruction(&Instruction::LocalSet(l_old_str));

        // str_len = mem.load(rec + offset + 4) * sub_size
        // Stash raw (pre-multiply) len in l_str_len for the overflow guard,
        // then multiply to produce the byte count.
        body.instruction(&Instruction::LocalGet(l_rec));
        body.instruction(&Instruction::I32Load(mem_arg_len));
        body.instruction(&Instruction::LocalSet(l_str_len));
        crate::adapter::fact::emit_overflow_guard(&mut body, l_str_len, *sub_size);
        body.instruction(&Instruction::LocalGet(l_str_len));
        if *sub_size != 1 {
            body.instruction(&Instruction::I32Const(*sub_size as i32));
            body.instruction(&Instruction::I32Mul);
        }
        body.instruction(&Instruction::LocalSet(l_str_len));

        // stable_str = realloc(0, 0, 1, str_len)
        body.instruction(&Instruction::I32Const(0));
        body.instruction(&Instruction::I32Const(0));
        body.instruction(&Instruction::I32Const(1));
        body.instruction(&Instruction::LocalGet(l_str_len));
        crate::adapter::fact::emit_checked_realloc(&mut body, realloc_func, l_stable_str);

        // memory.copy stable_str <- old_str, str_len (intra-callee)
        body.instruction(&Instruction::LocalGet(l_stable_str));
        body.instruction(&Instruction::LocalGet(l_old_str));
        body.instruction(&Instruction::LocalGet(l_str_len));
        body.instruction(&Instruction::MemoryCopy {
            dst_mem: callee_memory,
            src_mem: callee_memory,
        });

        // mem.store(rec + offset, stable_str)
        body.instruction(&Instruction::LocalGet(l_rec));
        body.instruction(&Instruction::LocalGet(l_stable_str));
        body.instruction(&Instruction::I32Store(mem_arg_ptr));
    }

    // i++; continue
    body.instruction(&Instruction::LocalGet(l_i));
    body.instruction(&Instruction::I32Const(1));
    body.instruction(&Instruction::I32Add);
    body.instruction(&Instruction::LocalSet(l_i));
    body.instruction(&Instruction::Br(0));

    body.instruction(&Instruction::End); // end loop
    body.instruction(&Instruction::End); // end block

    // Store stable_records to ptr_global, len to len_global.
    if let [(ptr_global, _), (len_global, _)] = result_globals {
        body.instruction(&Instruction::LocalGet(l_stable));
        body.instruction(&Instruction::GlobalSet(*ptr_global));
        body.instruction(&Instruction::LocalGet(1));
        body.instruction(&Instruction::GlobalSet(*len_global));
    }

    body.instruction(&Instruction::End);
    body
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- #298 inert vestigial-cabi_realloc verdict oracles ----------------
    //
    // These pin `cabi_realloc_drop_provably_safe` (the fail-safe verdict the
    // future drop is gated behind). The verdict is INERT today — it only
    // decides keep-vs-drop; nothing acts on it yet. Each oracle exercises one
    // gate so the corruption-critical default (keep) cannot silently regress.

    fn empty_graph_298() -> crate::resolver::DependencyGraph {
        crate::resolver::DependencyGraph {
            instantiation_order: Vec::new(),
            resolved_imports: std::collections::HashMap::new(),
            adapter_sites: Vec::new(),
            module_resolutions: Vec::new(),
            resource_graph: None,
            stream_pair_graph: None,
            reexporter_components: Vec::new(),
            reexporter_resources: Vec::new(),
            unresolved_imports: Vec::new(),
        }
    }

    /// A component exporting exactly one lifted function with the given params
    /// (no results). Empty params ⟹ scalar surface; a `String` param ⟹ pointer.
    fn component_with_one_lift_298(
        params: Vec<(String, crate::parser::ComponentValType)>,
    ) -> crate::parser::ParsedComponent {
        crate::parser::ParsedComponent {
            name: None,
            core_modules: Vec::new(),
            imports: Vec::new(),
            exports: Vec::new(),
            types: vec![crate::parser::ComponentType {
                kind: crate::parser::ComponentTypeKind::Function {
                    params,
                    results: Vec::new(),
                },
            }],
            instances: Vec::new(),
            canonical_functions: vec![crate::parser::CanonicalEntry::Lift {
                core_func_index: 0,
                type_index: 0,
                options: crate::parser::CanonicalOptions::default(),
            }],
            sub_components: Vec::new(),
            component_aliases: Vec::new(),
            component_instances: Vec::new(),
            core_entity_order: Vec::new(),
            component_func_defs: Vec::new(),
            component_instance_defs: Vec::new(),
            component_type_defs: vec![crate::parser::ComponentTypeDef::Defined],
            original_size: 0,
            original_hash: String::new(),
            depth_0_sections: Vec::new(),
            p3_async_features: Vec::new(),
        }
    }

    fn fuser_with_components_298(
        components: Vec<crate::parser::ParsedComponent>,
        output_format: OutputFormat,
    ) -> Fuser {
        let mut fuser = Fuser::new(FuserConfig {
            output_format,
            ..Default::default()
        });
        fuser.components = components;
        fuser
    }

    /// Scalar lift surface + core output + no adapters ⟹ droppable (true).
    #[test]
    fn test_298_verdict_scalar_lift_surface_is_droppable() {
        let fuser = fuser_with_components_298(
            vec![component_with_one_lift_298(Vec::new())],
            OutputFormat::CoreModule,
        );
        assert!(fuser.cabi_realloc_drop_provably_safe(&empty_graph_298()));
    }

    /// A pointer-carrying (string) lift param ⟹ cabi_realloc needed ⟹ keep.
    #[test]
    fn test_298_verdict_pointer_lift_surface_keeps_realloc() {
        let fuser = fuser_with_components_298(
            vec![component_with_one_lift_298(vec![(
                "s".to_string(),
                crate::parser::ComponentValType::String,
            )])],
            OutputFormat::CoreModule,
        );
        assert!(!fuser.cabi_realloc_drop_provably_safe(&empty_graph_298()));
    }

    /// Even a scalar surface must keep realloc when the output is a P2 wrap:
    /// the wrap aliases cabi_realloc for `canon lower` (over-drop = corruption).
    #[test]
    fn test_298_verdict_component_output_keeps_realloc() {
        let fuser = fuser_with_components_298(
            vec![component_with_one_lift_298(Vec::new())],
            OutputFormat::Component,
        );
        assert!(!fuser.cabi_realloc_drop_provably_safe(&empty_graph_298()));
    }

    /// Any cross-component adapter site ⟹ keep (an adapter may marshal pointers
    /// and consume the allocator).
    #[test]
    fn test_298_verdict_adapter_sites_keep_realloc() {
        let fuser = fuser_with_components_298(
            vec![component_with_one_lift_298(Vec::new())],
            OutputFormat::CoreModule,
        );
        let mut graph = empty_graph_298();
        graph.adapter_sites.push(crate::resolver::AdapterSite {
            from_component: 0,
            from_module: 0,
            import_name: "f".to_string(),
            import_module: "m".to_string(),
            import_func_type_idx: None,
            to_component: 0,
            to_module: 0,
            export_name: "f".to_string(),
            export_func_idx: 0,
            crosses_memory: false,
            is_async_lift: false,
            requirements: crate::resolver::AdapterRequirements::default(),
        });
        assert!(!fuser.cabi_realloc_drop_provably_safe(&graph));
    }

    /// #172: the library default is `Auto` — shared+rebase when provably
    /// safe, multi-memory otherwise. Pin it so a change is deliberate.
    #[test]
    fn test_fuser_config_default() {
        let config = FuserConfig::default();
        assert_eq!(config.memory_strategy, MemoryStrategy::Auto);
        assert!(config.attestation);
        assert!(!config.address_rebasing);
        assert!(!config.preserve_names);
    }

    #[test]
    fn test_fuser_empty_components_error() {
        let mut fuser = Fuser::with_defaults();
        let result = fuser.fuse();
        assert!(matches!(result, Err(Error::NoComponents)));
    }

    /// SR-19: Deterministic output — same input must always produce identical bytes.
    ///
    /// This catches non-determinism from HashMap iteration order (LS-CP-2) or any
    /// other source of randomness in the fusion pipeline. We run the full pipeline
    /// multiple times with identical input and assert byte-for-byte equality.
    #[test]
    fn test_deterministic_output() {
        use wasm_encoder::{
            CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection,
            Instruction, MemorySection, MemoryType, Module as EncoderModule, ModuleSection,
            TypeSection,
        };

        /// Build a minimal valid WebAssembly component containing one core module
        /// with a function, a memory, and exports for both.
        fn build_minimal_component() -> Vec<u8> {
            let mut types = TypeSection::new();
            types.ty().function([], [wasm_encoder::ValType::I32]);

            let mut functions = FunctionSection::new();
            functions.function(0);

            let mut memory = MemorySection::new();
            memory.memory(MemoryType {
                minimum: 1,
                maximum: None,
                memory64: false,
                shared: false,
                page_size_log2: None,
            });

            let mut exports = ExportSection::new();
            exports.export("run", ExportKind::Func, 0);
            exports.export("memory", ExportKind::Memory, 0);

            let mut code = CodeSection::new();
            let mut func = Function::new([]);
            func.instruction(&Instruction::I32Const(42));
            func.instruction(&Instruction::End);
            code.function(&func);

            let mut module = EncoderModule::new();
            module
                .section(&types)
                .section(&functions)
                .section(&memory)
                .section(&exports)
                .section(&code);

            let mut component = Component::new();
            component.section(&ModuleSection(&module));
            component.finish()
        }

        let component_bytes = build_minimal_component();

        // Disable attestation: it embeds timestamps and UUIDs which are
        // intentionally non-deterministic and would mask the HashMap-order
        // non-determinism we are trying to detect.
        let config = FuserConfig {
            attestation: false,
            ..FuserConfig::default()
        };

        // Fuse once to get the reference output.
        let mut reference_fuser = Fuser::new(config.clone());
        reference_fuser
            .add_component(&component_bytes)
            .expect("failed to add component to reference fuser");
        let reference_output = reference_fuser.fuse().expect("reference fuse failed");

        // Repeat with fresh Fuser instances. HashMap seeds are randomised per
        // process but also per HashMap instance, so creating new Fusers (and
        // therefore new internal HashMaps) on each iteration maximises the
        // chance of catching iteration-order divergence.
        for iteration in 0..5 {
            let mut fuser = Fuser::new(config.clone());
            fuser
                .add_component(&component_bytes)
                .expect("failed to add component");
            let output = fuser.fuse().expect("fuse failed");

            assert_eq!(
                reference_output, output,
                "Fusion output diverged on iteration {} — non-determinism detected (SR-19 / LS-CP-2)",
                iteration
            );
        }
    }

    /// #325: with `reproducible: true`, the fused artifact is byte-identical
    /// across runs — the attestation id is derived from the output content and
    /// the timestamp from `SOURCE_DATE_EPOCH` (default epoch 0), so the
    /// random-UUID + wall-clock non-determinism is removed. The control
    /// (reproducible off) must differ, proving the flag is what fixes it.
    ///
    /// Scoped to the default build (the shipped configuration). Under the
    /// optional `attestation` (wsc) feature the emitted section additionally
    /// carries `tool_parameters` / `metadata` as `wsc_attestation` `HashMap`
    /// fields, whose serialization order meld cannot control from this side —
    /// full byte-reproducibility on that path needs an upstream fix (sorted /
    /// BTreeMap serialization). The default `FusionAttestationBuilder` path has
    /// no such maps and is fully reproducible.
    #[cfg(not(feature = "attestation"))]
    #[test]
    fn test_reproducible_attestation_is_byte_stable() {
        use wasm_encoder::{
            CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection,
            Instruction, MemorySection, MemoryType, Module as EncoderModule, ModuleSection,
            TypeSection, ValType,
        };
        fn build_minimal_component() -> Vec<u8> {
            let mut types = TypeSection::new();
            types.ty().function([], [ValType::I32]);
            let mut functions = FunctionSection::new();
            functions.function(0);
            let mut memory = MemorySection::new();
            memory.memory(MemoryType {
                minimum: 1,
                maximum: None,
                memory64: false,
                shared: false,
                page_size_log2: None,
            });
            let mut exports = ExportSection::new();
            exports.export("run", ExportKind::Func, 0);
            exports.export("memory", ExportKind::Memory, 0);
            let mut code = CodeSection::new();
            let mut func = Function::new([]);
            func.instruction(&Instruction::I32Const(42));
            func.instruction(&Instruction::End);
            code.function(&func);
            let mut module = EncoderModule::new();
            module
                .section(&types)
                .section(&functions)
                .section(&memory)
                .section(&exports)
                .section(&code);
            let mut component = Component::new();
            component.section(&ModuleSection(&module));
            component.finish()
        }
        let component_bytes = build_minimal_component();

        let fuse_once = |reproducible: bool| -> Vec<u8> {
            let config = FuserConfig {
                attestation: true,
                reproducible,
                ..FuserConfig::default()
            };
            let mut fuser = Fuser::new(config);
            fuser
                .add_component(&component_bytes)
                .expect("add_component failed");
            fuser.fuse().expect("fuse failed")
        };

        // Reproducible: identical bytes across independent runs.
        let a = fuse_once(true);
        let b = fuse_once(true);
        assert_eq!(
            a, b,
            "#325: reproducible fusion must be byte-identical across runs"
        );

        // Control: without reproducible, the attestation's random UUID makes
        // the output differ — otherwise the flag would be a no-op.
        let c = fuse_once(false);
        let d = fuse_once(false);
        assert_ne!(
            c, d,
            "#325: non-reproducible fusion is expected to differ (random attestation id); \
             if this ever holds, the reproducible flag is testing nothing"
        );

        // #341: byte-identical input under DIFFERENT names/paths must fuse to
        // the SAME output when reproducible (the input's path leaked into the
        // attestation + provenance component_id). Two CI checkouts / temp dirs
        // fusing the same component must agree.
        let fuse_named = |name: &str, reproducible: bool| -> Vec<u8> {
            let config = FuserConfig {
                attestation: true,
                reproducible,
                ..FuserConfig::default()
            };
            let mut fuser = Fuser::new(config);
            fuser
                .add_component_named(&component_bytes, Some(name))
                .expect("add_component_named failed");
            fuser.fuse().expect("fuse failed")
        };
        let pa = fuse_named("/tmp/pa/falcon.wasm", true);
        let pb = fuse_named("/tmp/pb/falcon.wasm", true);
        assert_eq!(
            pa, pb,
            "#341: reproducible fusion must not depend on the input file path/name"
        );
        // Control: without reproducible the human-friendly name IS retained, so
        // different names produce different attestation bytes (name is not
        // silently dropped off the reproducible path).
        let qa = fuse_named("/tmp/pa/falcon.wasm", false);
        let qb = fuse_named("/tmp/pb/falcon.wasm", false);
        assert_ne!(
            qa, qb,
            "#341 control: non-reproducible fusion retains the caller-supplied name"
        );
    }

    /// SR-20 / SC-8: Fail-fast when a core module (not a component) is passed
    /// to `add_component()`.
    ///
    /// The parser must reject core modules immediately with `Error::NotAComponent`
    /// rather than silently misinterpreting the binary.
    #[test]
    fn test_fuser_rejects_core_module_input() {
        let core_module_bytes = wasm_encoder::Module::new().finish();

        let mut fuser = Fuser::with_defaults();
        let result = fuser.add_component(&core_module_bytes);

        assert!(
            matches!(result, Err(Error::NotAComponent)),
            "expected Error::NotAComponent for a core module, got: {:?}",
            result
        );
    }

    /// SR-20 / SC-9: Fail-fast when address rebasing is requested with
    /// multi-memory strategy.
    ///
    /// Address rebasing only makes sense with shared memory. The fuser must
    /// reject the incompatible configuration immediately via
    /// `Error::MemoryStrategyUnsupported`.
    #[test]
    fn test_fuser_address_rebasing_requires_shared_memory() {
        use wasm_encoder::{
            CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection,
            Instruction, MemorySection, MemoryType, Module as EncoderModule, ModuleSection,
            TypeSection,
        };

        // Build a minimal component so we get past the NoComponents check.
        let mut types = TypeSection::new();
        types.ty().function([], [wasm_encoder::ValType::I32]);

        let mut functions = FunctionSection::new();
        functions.function(0);

        let mut memory = MemorySection::new();
        memory.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        let mut exports = ExportSection::new();
        exports.export("run", ExportKind::Func, 0);
        exports.export("memory", ExportKind::Memory, 0);

        let mut code = CodeSection::new();
        let mut func = Function::new([]);
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::End);
        code.function(&func);

        let mut module = EncoderModule::new();
        module
            .section(&types)
            .section(&functions)
            .section(&memory)
            .section(&exports)
            .section(&code);

        let mut component = Component::new();
        component.section(&ModuleSection(&module));
        let component_bytes = component.finish();

        let config = FuserConfig {
            memory_strategy: MemoryStrategy::MultiMemory,
            address_rebasing: true,
            attestation: false,
            ..FuserConfig::default()
        };

        let mut fuser = Fuser::new(config);
        fuser
            .add_component(&component_bytes)
            .expect("add_component should succeed for a valid component");

        let result = fuser.fuse();
        assert!(
            matches!(result, Err(Error::MemoryStrategyUnsupported(_))),
            "expected Error::MemoryStrategyUnsupported when address_rebasing=true with MultiMemory, got: {:?}",
            result
        );
    }

    /// SR-20 / SC-8: Fail-fast on garbage input bytes.
    ///
    /// Completely invalid bytes must be rejected immediately rather than
    /// causing panics or undefined behavior deeper in the pipeline.
    #[test]
    fn test_fuser_rejects_invalid_wasm() {
        let garbage = b"not wasm";

        let mut fuser = Fuser::with_defaults();
        let result = fuser.add_component(garbage);

        assert!(
            result.is_err(),
            "expected an error for garbage input, got Ok(())"
        );

        // The parser should detect the bad magic number and return InvalidWasm.
        assert!(
            matches!(result, Err(Error::InvalidWasm(_))),
            "expected Error::InvalidWasm for garbage bytes, got: {:?}",
            result
        );
    }

    /// LS-R-13: the stream-cycle detector must not exhaust the call
    /// stack on a deep linear chain. Re-pins, at lib scope where the LS
    /// verification gate discovers it, what
    /// `p3_stream::tests::deep_linear_chain_does_not_overflow_stack`
    /// pins module-internally: a 50 000-component producer→consumer
    /// chain (deep enough to overflow the default 8 MB thread stack
    /// under a recursive Tarjan, which both the first draft and
    /// petgraph 0.8's tarjan_scc were) is validated without a stack
    /// overflow and without flagging a spurious cycle. Built entirely
    /// through the public `p3_stream` API.
    #[test]
    fn ls_r_13_deep_linear_chain_does_not_overflow_stack() {
        use crate::p3_stream::{
            StreamElement, StreamEndpoint, StreamMemoryMode, StreamPair, StreamPairGraph,
            StreamRole, cycle_issues_from_pairs,
        };

        let n = 50_000usize;
        let mut pairs = Vec::with_capacity(n - 1);
        for i in 0..(n - 1) {
            pairs.push(StreamPair {
                producer: StreamEndpoint {
                    component: i,
                    role: StreamRole::Producer,
                },
                consumer: StreamEndpoint {
                    component: i + 1,
                    role: StreamRole::Consumer,
                },
                element: StreamElement::Typed("U8".to_string()),
                mode: StreamMemoryMode::CrossMemory,
            });
        }
        let graph = StreamPairGraph { pairs };
        let issues = cycle_issues_from_pairs(&graph);
        assert!(
            issues.is_empty(),
            "linear chain of {n} components must not flag a cycle; got {issues:?}"
        );
    }

    /// LS-M-6: the `component-provenance` custom section must be
    /// present in fused output under the default config (provenance and
    /// attestation both enabled). The full round-trip/attribution
    /// oracle lives in tests/component_provenance.rs (an integration
    /// test, invisible to the LS verification gate's lib scan); this
    /// lib-scope test pins the minimal contract: fuse two trivial
    /// components and assert exactly one section named
    /// `provenance::SECTION_NAME` exists with a non-empty payload.
    #[test]
    fn ls_m_6_provenance_section_present_in_fused_output() {
        use wasm_encoder::{
            CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection,
            Instruction, MemorySection, MemoryType, Module as EncoderModule, ModuleSection,
            TypeSection,
        };

        /// Minimal valid component: one core module with one function
        /// returning a constant, one exported memory.
        fn build_trivial_component(func_export: &str, value: i32) -> Vec<u8> {
            let mut types = TypeSection::new();
            types.ty().function([], [wasm_encoder::ValType::I32]);

            let mut functions = FunctionSection::new();
            functions.function(0);

            let mut memory = MemorySection::new();
            memory.memory(MemoryType {
                minimum: 1,
                maximum: None,
                memory64: false,
                shared: false,
                page_size_log2: None,
            });

            let mut exports = ExportSection::new();
            exports.export(func_export, ExportKind::Func, 0);
            exports.export("memory", ExportKind::Memory, 0);

            let mut code = CodeSection::new();
            let mut func = Function::new([]);
            func.instruction(&Instruction::I32Const(value));
            func.instruction(&Instruction::End);
            code.function(&func);

            let mut module = EncoderModule::new();
            module
                .section(&types)
                .section(&functions)
                .section(&memory)
                .section(&exports)
                .section(&code);

            let mut component = Component::new();
            component.section(&ModuleSection(&module));
            component.finish()
        }

        // Default config: component_provenance = true, attestation = true.
        let config = FuserConfig::default();
        assert!(config.component_provenance && config.attestation);

        let mut fuser = Fuser::new(config);
        fuser
            .add_component_named(&build_trivial_component("run-a", 1), Some("comp-a"))
            .expect("add component a");
        fuser
            .add_component_named(&build_trivial_component("run-b", 2), Some("comp-b"))
            .expect("add component b");
        let output = fuser.fuse().expect("fuse");

        let mut provenance_payloads: Vec<&[u8]> = Vec::new();
        for payload in wasmparser::Parser::new(0).parse_all(&output) {
            if let wasmparser::Payload::CustomSection(reader) =
                payload.expect("fused output must parse")
                && reader.name() == provenance::SECTION_NAME
            {
                provenance_payloads.push(reader.data());
            }
        }
        assert_eq!(
            provenance_payloads.len(),
            1,
            "fused output must carry exactly one `{}` custom section (LS-M-6)",
            provenance::SECTION_NAME
        );
        assert!(
            !provenance_payloads[0].is_empty(),
            "`{}` section payload must not be empty",
            provenance::SECTION_NAME
        );
    }
}
