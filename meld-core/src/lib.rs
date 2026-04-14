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
//! let fuser = Fuser::new(config);
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
//! - **Multi-memory** (default): Each component keeps its own linear memory.
//!   Cross-component pointer-passing calls use adapters with `cabi_realloc`
//!   and `memory.copy`.
//! - **Shared memory** (legacy): All components share one memory. Broken when
//!   any component uses `memory.grow`.

pub mod adapter;
pub mod attestation;
pub mod component_wrap;
mod error;
pub mod merger;
pub mod parser;
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

    /// Whether to rebase per-module memory addresses into a shared memory
    pub address_rebasing: bool,

    /// Whether to preserve debug names
    pub preserve_names: bool,

    /// Custom section handling
    pub custom_sections: CustomSectionHandling,

    /// Output format: core module (default) or P2 component
    pub output_format: OutputFormat,
}

impl Default for FuserConfig {
    fn default() -> Self {
        Self {
            memory_strategy: MemoryStrategy::MultiMemory,
            attestation: true,
            address_rebasing: false,
            preserve_names: false,
            custom_sections: CustomSectionHandling::Merge,
            output_format: OutputFormat::CoreModule,
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

    /// Each component keeps its own memory (default).
    /// Cross-component pointer-passing calls use adapters with
    /// `cabi_realloc` and `memory.copy`. Requires WebAssembly
    /// multi-memory (Core Spec 3.0).
    MultiMemory,
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

    /// Number of imports resolved internally
    pub imports_resolved: usize,

    /// Number of exports in output
    pub total_exports: usize,

    /// Size of input components (bytes)
    pub input_size: usize,

    /// Size of fused output (bytes)
    pub output_size: usize,
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
}

impl Fuser {
    /// Create a new fuser with the given configuration
    pub fn new(config: FuserConfig) -> Self {
        Self {
            config,
            components: Vec::new(),
            original_components: Vec::new(),
            wiring_hints: std::collections::HashMap::new(),
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

    /// Perform the fusion and return the fused module bytes
    pub fn fuse(&self) -> Result<Vec<u8>> {
        let (bytes, _stats) = self.fuse_with_stats()?;
        Ok(bytes)
    }

    /// Perform fusion and return both the bytes and statistics
    pub fn fuse_with_stats(&self) -> Result<(Vec<u8>, FusionStats)> {
        if self.components.is_empty() {
            return Err(Error::NoComponents);
        }
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

        // Step 2: Merge modules
        log::info!("Merging {} core modules", stats.modules_merged);
        let merger = Merger::new(self.config.memory_strategy, self.config.address_rebasing);
        let mut merged = merger.merge(&self.components, &graph)?;
        stats.total_functions = merged.functions.len();
        stats.total_exports = merged.exports.len();

        // Step 2.5: Generate task.return shims for internal fused async calls.
        //
        // For each [task-return]N import used by an internal async callee,
        // generate a shim that stores result values to globals. The
        // callback-driving adapter (generated next) reads these globals
        // after EXIT. Must run BEFORE adapter generation so shim info
        // is available to the async adapter.
        self.generate_task_return_shims(&mut merged, &graph)?;

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
            self.wire_adapter_indices(&mut merged, &adapters, &graph)?;
        }

        // Step 4: Encode output module
        log::info!("Encoding fused module");
        let output_without_attestation = self.encode_output(&merged, &adapters, &[])?;
        let output = if self.config.attestation {
            // Build attestation from the output without the attestation section to avoid
            // self-referential hashing.
            let mut attestation_stats = stats.clone();
            attestation_stats.output_size = output_without_attestation.len();
            let (section_name, payload) =
                self.build_attestation_payload(&output_without_attestation, &attestation_stats)?;
            let extra_sections = vec![(section_name, payload)];
            self.encode_output(&merged, &adapters, &extra_sections)?
        } else {
            output_without_attestation
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
    ) -> Result<()> {
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
            let target_idx = if let Some(&wrapper_idx) = adapter_to_wrapper.get(&adapter_offset) {
                wrapper_idx
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
            "Wired {} adapter(s) into {} source module(s)",
            adapters.len(),
            affected_modules.len()
        );

        Ok(())
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

        // Build mapping: fused import name → original function name.
        // The original component's core module has imports like "[task-return]fibonacci".
        // After fusion, these become "[task-return]2" (renumbered by core_func_idx).
        // We need the original name to match with async adapter site export names.
        //
        // Strategy: for each async callee component, collect the task-return
        // import names from the ORIGINAL core module (which have function names).
        // Order matters — the Nth task-return import becomes [task-return]N in
        // the fused module (via build_canon_import_names).
        let mut task_return_original_names: HashMap<(usize, usize), String> = HashMap::new();
        for &comp_idx in &async_callee_components {
            let component = &self.components[comp_idx];
            let mut tr_idx = 0usize;
            for module in &component.core_modules {
                for module_imp in &module.imports {
                    if matches!(module_imp.kind, parser::ImportKind::Function(_))
                        && module_imp.name.starts_with("[task-return]")
                    {
                        let func_name = module_imp
                            .name
                            .strip_prefix("[task-return]")
                            .unwrap_or(&module_imp.name)
                            .to_string();
                        task_return_original_names.insert((comp_idx, tr_idx), func_name);
                        tr_idx += 1;
                    }
                }
            }
        }

        // Find task.return imports belonging to async callee components
        // and generate shims for them.
        let mut affected_modules: HashSet<(usize, usize)> = HashSet::new();
        let mut tr_counter_per_comp: HashMap<usize, usize> = HashMap::new();

        for (import_idx, imp) in merged.imports.iter().enumerate() {
            if !imp.name.starts_with("[task-return]") {
                continue;
            }
            // Check if this import belongs to an internal async callee
            let comp_idx = match imp.component_idx {
                Some(idx) if async_callee_components.contains(&idx) => idx,
                _ => continue,
            };

            // Track the task-return index per component to recover the
            // original function name from the mapping built above.
            let tr_idx = tr_counter_per_comp.entry(comp_idx).or_insert(0);
            let original_func_name = task_return_original_names
                .get(&(comp_idx, *tr_idx))
                .cloned()
                .unwrap_or_default();
            *tr_counter_per_comp.get_mut(&comp_idx).unwrap() += 1;

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

            // Generate shim function: stores each param to its global
            let shim_func_idx = merged.import_counts.func + merged.functions.len() as u32;
            let _type_idx = import_type.params.len(); // find or create type
            let shim_type = merger::Merger::find_or_add_type(
                &mut merged.types,
                &import_type.params,
                &[], // void return
            );

            let mut body = wasm_encoder::Function::new([]);
            for (i, (global_idx, _)) in result_globals.iter().enumerate() {
                body.instruction(&wasm_encoder::Instruction::LocalGet(i as u32));
                body.instruction(&wasm_encoder::Instruction::GlobalSet(*global_idx));
            }
            body.instruction(&wasm_encoder::Instruction::End);

            merged.functions.push(merger::MergedFunction {
                type_idx: shim_type,
                body,
                origin: (comp_idx, 0, u32::MAX),
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

            // Store shim info for the adapter to use
            merged.task_return_shims.insert(
                import_idx as u32,
                merger::TaskReturnShimInfo {
                    shim_func: shim_func_idx,
                    result_globals,
                    component_idx: comp_idx,
                    import_name: imp.name.clone(),
                    original_func_name: original_func_name.clone(),
                },
            );

            log::info!(
                "task.return shim: import {} '{}' → shim func {} with {} globals",
                import_idx,
                imp.name,
                shim_func_idx,
                merged.task_return_shims[&(import_idx as u32)]
                    .result_globals
                    .len(),
            );
        }

        // Re-rewrite function bodies for affected modules
        for &(comp_idx, mod_idx) in &affected_modules {
            let module = &self.components[comp_idx].core_modules[mod_idx];
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

        Ok(())
    }

    /// Encode the merged module to binary
    fn encode_output(
        &self,
        merged: &MergedModule,
        adapters: &[adapter::AdapterFunction],
        extra_custom_sections: &[(&str, Vec<u8>)],
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
                elements.segment(segments::encode_element_segment(segment));
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
            for (name, contents) in &merged.custom_sections {
                if !self.config.preserve_names && name == "name" {
                    continue;
                }
                module.section(&wasm_encoder::CustomSection {
                    name: std::borrow::Cow::Borrowed(name),
                    data: std::borrow::Cow::Borrowed(contents),
                });
            }
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
            .memory_strategy(self.memory_strategy_label());

        for (index, component) in self.components.iter().enumerate() {
            let name = component
                .name
                .clone()
                .unwrap_or_else(|| format!("component-{}", index));
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
        let timestamp = attestation::chrono_timestamp();
        let attestation_id = attestation::generate_uuid();

        let mut inputs = Vec::new();
        for (index, component) in self.components.iter().enumerate() {
            let name = component
                .name
                .clone()
                .unwrap_or_else(|| format!("component-{}", index));
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
type WiringHints = std::collections::HashMap<(usize, String), usize>;

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fuser_config_default() {
        let config = FuserConfig::default();
        assert_eq!(config.memory_strategy, MemoryStrategy::MultiMemory);
        assert!(config.attestation);
        assert!(!config.address_rebasing);
        assert!(!config.preserve_names);
    }

    #[test]
    fn test_fuser_empty_components_error() {
        let fuser = Fuser::with_defaults();
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
}
