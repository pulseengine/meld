//! Meld CLI - Static WebAssembly Component Fusion
//!
//! This CLI tool fuses multiple WebAssembly components into a single
//! core module, eliminating the need for runtime linking.
//!
//! ## Usage
//!
//! ```bash
//! # Fuse two components
//! meld fuse component_a.wasm component_b.wasm -o fused.wasm
//!
//! # Fuse with statistics
//! meld fuse --stats component_a.wasm component_b.wasm -o fused.wasm
//!
//! # Show version
//! meld version
//! ```

use anyhow::{Context, Result, anyhow};
use clap::{Parser, Subcommand};
use meld_core::{
    DwarfHandling, Fuser, FuserConfig, FusionStats, MemoryStrategy, OutputFormat, Profile,
};
use std::fs;
use std::path::Path;
use std::time::Instant;

mod docs;

#[derive(Parser)]
#[command(name = "meld")]
#[command(author = "PulseEngine")]
#[command(version = env!("CARGO_PKG_VERSION"))]
#[command(about = "Static WebAssembly component fusion", long_about = None)]
#[command(propagate_version = true)]
struct Cli {
    /// Enable verbose logging
    #[arg(short, long, global = true)]
    verbose: bool,

    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Fuse multiple WebAssembly components into a single module
    Fuse {
        /// Input component files (.wasm)
        #[arg(required = true)]
        inputs: Vec<String>,

        /// Output file path
        #[arg(short, long, default_value = "fused.wasm")]
        output: String,

        /// Memory strategy. "auto" (default) always selects multi-memory, the
        /// strategy that is sound for every input; it never selects shared
        /// memory or address rebasing on its own (#326, #409). "multi" keeps one
        /// linear memory per input component; the fused module then
        /// needs `wasm-opt --enable-multimemory` and has no single-
        /// address-space (MCU) lowering. "shared" forces one merged
        /// memory; pair it with --address-rebase. Unsound if any input
        /// grows memory. See issue #172.
        #[arg(long, default_value = "auto")]
        memory: String,

        /// Build profile: 'ecosystem' (default) or 'safety'. Under 'safety'
        /// every safety-relevant property must be stated explicitly — inferring
        /// one is a hard error rather than a warning (ADR-7's sealed-safety
        /// profile; ADR-4 "explicit, not auto"). Today that means `--memory`
        /// must be given: 'auto' is refused. A build that passes under 'safety'
        /// produces byte-identical output to the same explicit invocation under
        /// 'ecosystem' — the profile only decides what may be inferred.
        #[arg(long, default_value = "ecosystem")]
        profile: String,

        /// Rebase memory addresses for shared memory (experimental).
        /// Only valid with --memory shared. Not accepted with "auto", which
        /// always selects multi-memory and never rebases.
        #[arg(long)]
        address_rebase: bool,

        /// Compact used-extent rebasing for single-address-space (MCU)
        /// targets. Places each component at its actual used data extent
        /// (16-byte aligned) instead of its declared page count, and sizes
        /// the merged memory to the packed total — so three thin drivers fit
        /// in a few KiB instead of one 64 KiB page each. Implies
        /// --address-rebase and requires --memory shared. OPT-IN and sound
        /// ONLY when a component references no address above its last data
        /// segment (no separately-addressed .bss, no heap, no computed
        /// pointers); such components must use --address-rebase instead.
        #[arg(long)]
        pack_rebase: bool,

        /// Collapse the per-provider shadow stacks into ONE shared region.
        /// Builds on --pack-rebase (implies it): reserves a single shadow-stack
        /// region of max(sp) at base 0 and packs each provider's data right
        /// above it, coalescing every __stack_pointer onto one survivor —
        /// reclaiming the (N-1) duplicated stack reservations (the last MCU-fit
        /// gap after --pack-rebase). Requires every provider to carry a
        /// __stack_pointer AND __heap_base marker and be stack-first (all data
        /// above sp); fails loud otherwise. OPT-IN and sound ONLY when the
        /// providers are non-reentrant, single-threaded, mutually-non-calling,
        /// and one-live-at-a-time (a shared stack sized to the MAX, not the
        /// SUM, of their stack use).
        #[arg(long)]
        share_stack: bool,

        /// SR-86 / #427: group inputs into memory domains — fuse within a
        /// domain, keep the Canonical ABI between. Repeat once per domain:
        ///
        ///   --domain tenant=a.wasm,b.wasm --domain supervisor=c.wasm
        ///
        /// Every input must be named in exactly one domain; meld refuses a
        /// grouping that does not partition them rather than placing a
        /// component somewhere by default. Requires --memory shared (with
        /// --address-rebase), because under --memory multi every component
        /// already has its own memory and the grouping would do nothing.
        ///
        /// A grouping is a TRUST decision, not a layout hint: components in
        /// one domain share a linear memory and can therefore address each
        /// other's handle tables, so two mutually distrusting tenants must not
        /// share a domain. It is recorded in the attestation for that reason.
        #[arg(long = "domain", value_name = "NAME=INPUT[,INPUT...]")]
        domain: Vec<String>,

        /// Show fusion statistics
        #[arg(long)]
        stats: bool,

        /// Explain the per-boundary strategy: for every fused cross-component
        /// call, the call-lowering class chosen for it (direct / memory-copy /
        /// transcode / async-lift) and how it was wired (inlined-direct /
        /// widening-wrapper / thunk). The same records are embedded in the
        /// fusion attestation, so a shipped artifact can be audited after the
        /// fact (ADR-7: per-boundary strategy declared, attested, observable).
        #[arg(long)]
        explain: bool,

        /// Disable attestation in output
        #[arg(long)]
        no_attestation: bool,

        /// Emit a byte-reproducible artifact (#325): derive the attestation
        /// id from the output content and take the timestamp from
        /// `SOURCE_DATE_EPOCH` (default epoch 0) instead of a random UUID +
        /// wall clock, so identical input yields an identical sha256.
        ///
        /// Also replaces each attested input NAME with a positional identifier
        /// (`component-0`, `component-1`, ...), because a caller-supplied path
        /// differs between checkouts and would otherwise change the hash (#341).
        /// Input content stays pinned by its recorded sha256, but if your
        /// provenance story depends on the input names themselves, they are not
        /// preserved under this flag.
        #[arg(long)]
        reproducible: bool,

        /// Disable the `component-provenance` custom section (#192).
        /// The section maps each fused-module function index back to
        /// its originating component + function index; downstream
        /// consumers (pulseengine/scry) use it to project
        /// Component-Model invariants onto fused-module locations.
        /// Section overhead is ~120 bytes per fused function.
        #[arg(long)]
        no_component_provenance: bool,

        /// Emit the `meld.signature-manifest` section (#400): per export, the
        /// WIT signature, the core signature meld emitted, the flattened
        /// parameter count, and the memory / allocator / post-return a host
        /// must use to invoke it. Without it a host cannot tell an export
        /// taking a plain `u32` from one taking a pointer — both lower to
        /// `(i32) -> i32`, and the Canonical ABI passes garbage rather than
        /// erroring. Opt-in: the section adds bytes.
        #[arg(long)]
        emit_manifest: bool,

        /// DWARF debug-info handling: `remap` (default since v0.25.0 —
        /// translate code addresses to the fused code section; meld-
        /// generated code is attributed to per-class `<meld-adapter>`
        /// lines), `strip` (drop all `.debug_*`), or `passthrough`
        /// (copy verbatim; addresses are wrong against the fused code
        /// section). With multiple DWARF-bearing input modules, `remap`
        /// drops the source DWARF (never wrong addresses, #208) but
        /// still emits the synthetic adapter unit.
        #[arg(long, value_name = "MODE", default_value = "remap")]
        dwarf: String,

        /// Preserve debug names in output
        #[arg(long)]
        preserve_names: bool,

        /// Validate output with wasmparser. Implied on the single-address-space
        /// paths (`--memory shared`, and therefore `--address-rebase`,
        /// `--pack-rebase`, `--share-stack`); pass this to force it elsewhere.
        #[arg(long)]
        validate: bool,

        /// Skip the validation that `--memory shared` implies.
        ///
        /// Validation is on by default there because that is where meld does its
        /// most invasive rewriting — rebasing addresses and bridging calling
        /// conventions inside one address space — and a defect shows up as a
        /// module that no runtime accepts. #390 and #393 both shipped as invalid
        /// or wrong output at exit 0; the reporter noted they would have caught
        /// the first months earlier had this been the default. The cost is one
        /// wasmparser pass over an artifact just built.
        #[arg(long, conflicts_with = "validate")]
        no_validate: bool,

        /// Output as P2 component instead of core module
        #[arg(long)]
        component: bool,

        /// Write a JSON import map to the given path (for synth/kiln integration)
        #[arg(long, value_name = "PATH")]
        emit_import_map: Option<String>,

        /// Mark a resource as opaque-rep (for re-exporters whose representation
        /// is treated as a `u32` rather than a boxed pointer). Repeatable.
        ///
        /// Format: `<interface>.<resource>` (qualified). Example:
        /// `--opaque-rep test:resource-floats-opaque/chain.float`
        ///
        /// Opaque-rep resources skip meld's per-resource handle table layer
        /// and get their own wasmtime resource type per component (rather
        /// than the shared-by-name default). This matches the architecture
        /// of pulseengine/wit-bindgen `feat/opaque-rep-attribute`.
        #[arg(long, value_name = "IFACE.RESOURCE")]
        opaque_rep: Vec<String>,
    },

    /// Inspect a WebAssembly component
    Inspect {
        /// Input component file
        #[arg(required = true)]
        input: String,

        /// Show detailed type information
        #[arg(long)]
        types: bool,

        /// Show imports and exports
        #[arg(long)]
        interfaces: bool,
    },

    /// Show version information
    Version,

    /// Show embedded, queryable documentation (offline).
    ///
    /// `meld docs` lists topics; `meld docs <topic>` shows one;
    /// `meld docs --grep <q>` searches all topics; `--format json` emits the
    /// list (or a single topic, with its body) for machine queries.
    /// `meld docs check --coverage` reports subcommands without a topic
    /// (`--strict` exits non-zero — the CI gate).
    Docs {
        /// A topic slug to show, or `check` to run the coverage invariant.
        topic: Option<String>,

        /// List all topics (the default when no topic is given).
        #[arg(long)]
        list: bool,

        /// Search across all topic titles and bodies.
        #[arg(long, value_name = "QUERY")]
        grep: Option<String>,

        /// (check) Report subcommands lacking a documented topic.
        #[arg(long)]
        coverage: bool,

        /// (check --coverage) Exit non-zero if any subcommand is undocumented.
        #[arg(long)]
        strict: bool,

        /// Output format: `text` (default) or `json` for machine queries —
        /// applies to the topic list and to a single `meld docs <topic>`.
        #[arg(long, value_name = "FMT", default_value = "text")]
        format: String,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    // Initialize logging
    if cli.verbose {
        env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("debug")).init();
    } else {
        env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("warn")).init();
    }

    match cli.command {
        Some(Commands::Fuse {
            inputs,
            output,
            memory,
            address_rebase,
            stats,
            no_attestation,
            reproducible,
            no_component_provenance,
            emit_manifest,
            dwarf,
            preserve_names,
            validate,
            no_validate,
            component,
            emit_import_map,
            opaque_rep,
            pack_rebase,
            share_stack,
            profile,
            explain,
            domain,
        }) => {
            fuse_command(
                inputs,
                output,
                memory,
                profile,
                explain,
                domain,
                address_rebase,
                pack_rebase,
                share_stack,
                stats,
                no_attestation,
                reproducible,
                no_component_provenance,
                emit_manifest,
                dwarf,
                preserve_names,
                validate,
                no_validate,
                component,
                emit_import_map,
                opaque_rep,
            )?;
        }

        Some(Commands::Inspect {
            input,
            types,
            interfaces,
        }) => {
            inspect_command(input, types, interfaces)?;
        }

        Some(Commands::Version) => {
            println!("meld v{}", env!("CARGO_PKG_VERSION"));
            println!("Static WebAssembly Component Fusion");
            println!();
            println!("Part of the pulseengine toolchain:");
            println!("  - loom: WebAssembly optimizer");
            println!("  - meld: Static component fuser");
            println!();
            println!("Project: https://github.com/pulseengine/meld");
            println!("License: Apache-2.0");
        }

        Some(Commands::Docs {
            topic,
            list,
            grep,
            coverage,
            strict,
            format,
        }) => {
            docs_command(
                topic.as_deref(),
                list,
                grep.as_deref(),
                coverage,
                strict,
                &format,
            )?;
        }

        None => {
            println!("meld - Static WebAssembly Component Fusion");
            println!();
            println!("Usage: meld <COMMAND>");
            println!();
            println!("Commands:");
            println!("  fuse      Fuse multiple components into a single module");
            println!("  inspect   Inspect a WebAssembly component");
            println!("  version   Show version information");
            println!("  docs      Show embedded, queryable documentation");
            println!("  help      Print this message or help for subcommands");
            println!();
            println!("For more information, run: meld help <command>");
        }
    }

    Ok(())
}

/// SR-86 / #427: turn `--domain NAME=a.wasm,b.wasm` specs into the index
/// groups the core API takes.
///
/// Resolves against the input list the user actually wrote, so the error can
/// name the file rather than an index. Refusing an unknown name matters more
/// than it looks: a typo would otherwise drop that input into no domain, and
/// "in no domain" is the one thing a privilege boundary must never be.
fn parse_domains(specs: &[String], inputs: &[String]) -> Result<Vec<Vec<usize>>> {
    let mut groups = Vec::with_capacity(specs.len());
    for spec in specs {
        let (name, members) = spec.split_once('=').ok_or_else(|| {
            anyhow::anyhow!(
                "--domain expects NAME=INPUT[,INPUT...], got {spec:?} (no '='). \
                 Example: --domain tenant=a.wasm,b.wasm"
            )
        })?;
        if name.trim().is_empty() {
            return Err(anyhow::anyhow!("--domain {spec:?} has an empty name"));
        }
        let mut group = Vec::new();
        for member in members.split(',').map(str::trim).filter(|m| !m.is_empty()) {
            let idx = inputs.iter().position(|i| i == member).ok_or_else(|| {
                anyhow::anyhow!(
                    "--domain {name}={member:?} names an input that was not given. \
                     Inputs are: {}",
                    inputs.join(", ")
                )
            })?;
            group.push(idx);
        }
        if group.is_empty() {
            return Err(anyhow::anyhow!(
                "--domain {name} lists no inputs — an empty domain states nothing"
            ));
        }
        groups.push(group);
    }
    Ok(groups)
}

/// Fuse command implementation
#[allow(clippy::too_many_arguments)]
fn fuse_command(
    inputs: Vec<String>,
    output: String,
    memory: String,
    profile: String,
    explain: bool,
    domain: Vec<String>,
    address_rebase: bool,
    pack_rebase: bool,
    share_stack: bool,
    show_stats: bool,
    no_attestation: bool,
    reproducible: bool,
    no_component_provenance: bool,
    emit_manifest: bool,
    dwarf: String,
    preserve_names: bool,
    validate: bool,
    no_validate: bool,
    component: bool,
    emit_import_map: Option<String>,
    opaque_rep: Vec<String>,
) -> Result<()> {
    println!(
        "Meld v{} - Static Component Fusion",
        env!("CARGO_PKG_VERSION")
    );

    // Parse build profile (ADR-7: ecosystem vs sealed-safety).
    let profile = match profile.as_str() {
        "ecosystem" => Profile::Ecosystem,
        "safety" => {
            println!(
                "Safety profile: every safety-relevant property must be stated \
                 explicitly (ADR-4: explicit, not auto)"
            );
            Profile::Safety
        }
        other => {
            return Err(anyhow!(
                "Invalid --profile: {}. Use 'ecosystem' or 'safety'",
                other
            ));
        }
    };

    // Parse memory strategy
    let memory_strategy = match memory.as_str() {
        "auto" => {
            // #172 / #409: resolved during fusion, and always to multi-memory.
            // Auto never selects shared memory or address rebasing (#326).
            if address_rebase {
                return Err(anyhow!(
                    "--address-rebase requires --memory shared; \
                     'auto' always selects multi-memory and never rebases"
                ));
            }
            MemoryStrategy::Auto
        }
        "multi" => {
            // #172: multi-memory output needs --enable-multimemory in
            // wasm-opt and has no MCU (single-address-space) lowering.
            // Warn so a user who picked it deliberately still knows what
            // the next tool in the chain will require.
            eprintln!(
                "warning: --memory multi produces a multi-memory module \
                 when inputs carry more than one memory. wasm-opt needs \
                 --enable-multimemory to consume it, and it has no \
                 single-address-space (MCU) lowering. The default, \
                 `--memory auto`, resolves to multi-memory too; a \
                 single-address-space build needs `--memory shared` with \
                 `--address-rebase` or `--pack-rebase`, chosen explicitly."
            );
            MemoryStrategy::MultiMemory
        }
        "shared" => {
            println!("Using shared memory");
            MemoryStrategy::SharedMemory
        }
        _ => {
            return Err(anyhow!(
                "Invalid memory strategy: {}. Use 'auto', 'multi', or 'shared'",
                memory
            ));
        }
    };

    // --share-stack builds on --pack-rebase (SR-66): it needs the packed
    // byte-granular stride to reclaim the freed stack reservations.
    let pack_rebase = pack_rebase || share_stack;
    // --pack-rebase is a compact variant of --address-rebase; it requires the
    // same single shared memory and implies address rebasing (SR-57).
    if pack_rebase && memory_strategy != MemoryStrategy::SharedMemory {
        return Err(anyhow!(
            "--pack-rebase requires --memory shared (it is a compact, \
             used-extent variant of --address-rebase); 'auto'/'multi' \
             do not support it"
        ));
    }
    let address_rebase = address_rebase || pack_rebase;

    if share_stack {
        println!(
            "Shared shadow stack (--share-stack): one stack region for all \
             providers — sound ONLY when they are non-reentrant, \
             single-threaded, mutually-non-calling, and one-live-at-a-time"
        );
    }
    if pack_rebase {
        println!(
            "Compact used-extent rebasing (--pack-rebase): sound only for \
             components that address nothing above their last data segment"
        );
    } else if address_rebase {
        println!("Address rebasing is experimental and may have limitations");
    }

    // Configure fuser
    let output_format = if component {
        OutputFormat::Component
    } else {
        OutputFormat::CoreModule
    };
    // Parse --opaque-rep <iface>.<resource> values into (iface, resource)
    // tuples. Split on the LAST '.' so qualified interface names like
    // `test:resource-floats-opaque/chain` (which contain no '.') are kept
    // intact and only the trailing resource name is split off.
    let opaque_resources: Vec<(String, String)> = opaque_rep
        .iter()
        .map(|s| match s.rsplit_once('.') {
            Some((iface, rn)) => Ok((iface.to_string(), rn.to_string())),
            None => Err(anyhow!(
                "--opaque-rep value '{}' must be 'iface.resource' (e.g. 'test:foo/bar.baz')",
                s
            )),
        })
        .collect::<Result<_>>()?;
    if !opaque_resources.is_empty() {
        println!("Opaque-rep resources:");
        for (iface, rn) in &opaque_resources {
            println!("  {}.{}", iface, rn);
        }
    }

    let dwarf_handling = match dwarf.as_str() {
        "strip" => DwarfHandling::Strip,
        "passthrough" => DwarfHandling::PassThrough,
        "remap" => DwarfHandling::Remap,
        other => {
            return Err(anyhow!(
                "Invalid --dwarf mode: {}. Use 'strip', 'passthrough', or 'remap'",
                other
            ));
        }
    };

    // SR-86: resolve the grouping against the inputs before building the
    // config, so a typo in a trust boundary fails before any work is done.
    let domains = parse_domains(&domain, &inputs)?;

    let config = FuserConfig {
        profile,
        memory_strategy,
        attestation: !no_attestation,
        reproducible,
        component_provenance: !no_component_provenance,
        signature_manifest: emit_manifest,
        address_rebasing: address_rebase,
        pack_rebase,
        share_stack,
        preserve_names,
        output_format,
        opaque_resources,
        dwarf_handling,
        domains,
        ..Default::default()
    };

    let mut fuser = Fuser::new(config);

    println!();
    println!("Inputs:");

    let start = Instant::now();
    let mut total_input_size = 0usize;

    // Load and add components
    for input_path in &inputs {
        let path = Path::new(input_path);
        if !path.exists() {
            return Err(anyhow!("Input file not found: {}", input_path));
        }

        let bytes = fs::read(path).with_context(|| format!("Failed to read {}", input_path))?;

        let size = bytes.len();
        total_input_size += size;

        println!("  {} ({} bytes)", input_path, size);

        fuser
            .add_component_named(&bytes, Some(input_path))
            .with_context(|| format!("Failed to parse {}", input_path))?;
    }

    println!();
    println!("Fusing {} components...", fuser.input_count());

    // Perform fusion
    let (fused_bytes, stats) = fuser.fuse_with_stats().context("Fusion failed")?;

    if memory_strategy == MemoryStrategy::Auto {
        // #409 kept a dead `"shared"` arm here for a future ADR-7 path. It
        // described auto producing a single-memory output, which auto has not
        // done since #326, and the source-string guard flags it — correctly: a
        // false sentence about current behaviour does not earn its keep by
        // being unreachable. Naming whatever auto resolved to is what such a
        // path would need anyway.
        let resolved = stats.memory_strategy.as_str();
        println!("Memory strategy: {resolved} (auto)");
        if resolved == "multi" {
            eprintln!(
                "note: multi-memory output needs `wasm-opt \
                 --enable-multimemory` and has no single-address-\
                 space (MCU) lowering. See issue #172."
            );
        }
    }

    let elapsed = start.elapsed();

    // Validate the output.
    //
    // On by default for the single-address-space paths, because that is where
    // meld rewrites most invasively — rebasing absolute addresses and bridging
    // calling conventions within one memory — and where a defect surfaces as a
    // module no runtime will accept. #390 emitted invalid wasm at exit 0 and
    // #393 emitted a module that validated and returned the wrong number; both
    // reached a consumer. The cost of catching the first class is one
    // wasmparser pass over an artifact already in memory.
    //
    // `--validate` forces it on any path; `--no-validate` opts out.
    let implied = validation_is_implied(&memory_strategy, no_validate);
    if validate || implied {
        println!();
        if implied && !validate {
            println!("Validating output (implied by --memory shared; --no-validate to skip)...");
        } else {
            println!("Validating output...");
        }
        // Before the write: a module that fails here must not become a file
        // somebody can pick up.
        validate_wasm(&fused_bytes)?;
        println!("  Validation passed");
    }

    // Write output
    fs::write(&output, &fused_bytes).with_context(|| format!("Failed to write {}", output))?;

    // Emit import map if requested
    if let Some(ref map_path) = emit_import_map {
        write_import_map(&fused_bytes, map_path)
            .with_context(|| format!("Failed to write import map to {}", map_path))?;
        println!();
        println!("Import map: {}", map_path);
    }

    println!();
    println!("Output: {} ({} bytes)", output, fused_bytes.len());

    // Show statistics
    if explain {
        print_boundaries(&stats);
    }

    if show_stats {
        print_stats(&stats, total_input_size, elapsed);
    } else {
        let (label, value) = size_change(total_input_size, fused_bytes.len());
        println!("  {label}: {value}");
        println!("  Time: {:?}", elapsed);
    }

    println!();
    println!("Fusion complete!");

    Ok(())
}

/// Print detailed statistics
/// ADR-7 `--explain`: report the strategy chosen for every fused
/// cross-component call boundary. The same records are embedded in the fusion
/// attestation, so this is the live view of an artifact-auditable fact.
fn print_boundaries(stats: &FusionStats) {
    println!();
    println!("Boundary strategies");
    println!("{}", "=".repeat(50));

    if stats.boundaries.is_empty() {
        println!();
        println!("  (no fused cross-component calls — nothing to report)");
        return;
    }

    println!();
    for b in &stats.boundaries {
        let memory = if b.crosses_memory {
            "cross-memory"
        } else {
            "same-memory"
        };
        println!(
            "  c{}m{} -> c{}m{}  {}::{}",
            b.from_component, b.from_module, b.to_component, b.to_module, b.interface, b.function
        );
        println!(
            "      lowering: {:<12} wiring: {:<16} {}",
            b.lowering, b.wiring, memory
        );
    }

    // A short tally so the shape is visible without reading every line.
    let mut direct = 0usize;
    let mut copy = 0usize;
    let mut transcode = 0usize;
    let mut asynch = 0usize;
    let mut inlined = 0usize;
    for b in &stats.boundaries {
        match b.lowering.as_str() {
            "direct" => direct += 1,
            "memory-copy" => copy += 1,
            "transcode" => transcode += 1,
            _ => asynch += 1,
        }
        if b.wiring == "inlined-direct" {
            inlined += 1;
        }
    }
    println!();
    println!(
        "  {} boundaries: {} direct, {} memory-copy, {} transcode, {} async-lift          ({} wired with nothing interposed)",
        stats.boundaries.len(),
        direct,
        copy,
        transcode,
        asynch,
        inlined
    );

    print_placements(stats);
}

/// SR-70: the memory-axis half of `--explain` — where each module landed in the
/// fused address space and by which rule.
fn print_placements(stats: &FusionStats) {
    if stats.placements.is_empty() {
        // Not an omission: under `--memory multi` each module keeps its own
        // memory, so there is no placement decision to report.
        return;
    }
    println!();
    println!("Memory placement");
    println!("{}", "=".repeat(50));
    println!();
    let mut total = 0u64;
    for p in &stats.placements {
        println!(
            "  c{}m{}  base {:>10}  reserved {:>10} B  ({})",
            p.component, p.module, p.base, p.reserved, p.strategy
        );
        total += p.reserved;
    }
    println!();
    println!(
        "  {} modules placed, {} B reserved in total",
        stats.placements.len(),
        total
    );
}

/// The size-change label and value both summaries print, from the one shared
/// computation, so `--stats` and the default summary cannot disagree (#414).
fn size_change(input_bytes: usize, output_bytes: usize) -> (&'static str, String) {
    match meld_core::size_reduction_percent(input_bytes, output_bytes) {
        Some(p) if p >= 0.0 => ("Size reduction", format!("{p:.1}%")),
        Some(p) => ("Size increase", format!("{:.1}%", -p)),
        None => ("Size change", "unknown (input size is 0)".to_string()),
    }
}

fn print_stats(stats: &FusionStats, total_input_size: usize, elapsed: std::time::Duration) {
    println!();
    println!("Fusion Statistics");
    println!("{}", "=".repeat(50));

    println!();
    println!("Components:");
    println!("  Components fused:    {}", stats.components_fused);
    println!("  Core modules merged: {}", stats.modules_merged);

    println!();
    println!("Functions:");
    println!("  Total functions:     {}", stats.total_functions);
    println!("  Adapter functions:   {}", stats.adapter_functions);

    println!();
    println!("Resolution:");
    println!("  Imports resolved:    {}", stats.imports_resolved);
    println!("  Total exports:       {}", stats.total_exports);

    println!();
    println!("Size:");
    println!("  Input size:          {} bytes", total_input_size);
    println!("  Output size:         {} bytes", stats.output_size);

    let (label, value) = size_change(total_input_size, stats.output_size);
    println!("  {:<21}{value}", format!("{label}:"));

    println!();
    println!("Performance:");
    println!("  Fusion time:         {:?}", elapsed);
    let throughput = if elapsed.as_secs_f64() > 0.0 {
        (total_input_size as f64 / elapsed.as_secs_f64()) / (1024.0 * 1024.0)
    } else {
        0.0
    };
    println!("  Throughput:          {:.2} MB/s", throughput);

    println!("{}", "=".repeat(50));
}

/// Inspect command implementation
fn inspect_command(input: String, show_types: bool, show_interfaces: bool) -> Result<()> {
    let path = Path::new(&input);
    if !path.exists() {
        return Err(anyhow!("Input file not found: {}", input));
    }

    let bytes = fs::read(path).with_context(|| format!("Failed to read {}", input))?;

    println!("Inspecting: {}", input);
    println!("  Size: {} bytes", bytes.len());

    // Check if it's a component
    if bytes.len() < 8 {
        return Err(anyhow!("File too small to be a valid WASM file"));
    }

    if &bytes[0..4] != b"\0asm" {
        return Err(anyhow!("Invalid WASM magic number"));
    }

    let version = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
    let is_component = version == 0x0001_000d;

    if is_component {
        println!("  Format: WebAssembly Component (P2)");
    } else if version == 1 {
        println!("  Format: Core WebAssembly Module");
        println!();
        println!("Note: This is a core module, not a component.");
        println!("Use `wasm-tools component new` to convert it to a component.");
        return Ok(());
    } else {
        println!("  Format: Unknown (version {})", version);
        return Ok(());
    }

    // Parse the component
    let parser = meld_core::ComponentParser::new();
    let component = parser.parse(&bytes).context("Failed to parse component")?;

    println!("  Core modules: {}", component.core_modules.len());
    println!("  Imports: {}", component.imports.len());
    println!("  Exports: {}", component.exports.len());

    if show_types || show_interfaces {
        println!();
    }

    if show_interfaces {
        if !component.imports.is_empty() {
            println!("Imports:");
            for import in &component.imports {
                println!("  - {}", import.name);
            }
            println!();
        }

        if !component.exports.is_empty() {
            println!("Exports:");
            for export in &component.exports {
                println!("  - {} ({:?})", export.name, export.kind);
            }
        }
    }

    if show_types {
        println!();
        for (idx, module) in component.core_modules.iter().enumerate() {
            println!("Core Module {}:", idx);
            println!("  Types: {}", module.types.len());
            println!("  Functions: {}", module.functions.len());
            println!("  Imports: {}", module.imports.len());
            println!("  Exports: {}", module.exports.len());
            println!("  Memories: {}", module.memories.len());
            println!("  Tables: {}", module.tables.len());
            println!("  Globals: {}", module.globals.len());
        }
    }

    Ok(())
}

/// `meld docs` — embedded, queryable documentation (SR-64), modelled on
/// `rivet docs`. Lists/show/grep topics, `--format json` for machine queries,
/// and `check --coverage` (`--strict` gate) for the coverage invariant.
fn docs_command(
    topic: Option<&str>,
    list: bool,
    grep: Option<&str>,
    coverage: bool,
    strict: bool,
    format: &str,
) -> Result<()> {
    use clap::CommandFactory;

    let json = match format {
        "text" => false,
        "json" => true,
        other => {
            return Err(anyhow!(
                "unknown --format '{other}' (expected `text` or `json`)"
            ));
        }
    };

    // `meld docs check --coverage` (or `--coverage`) — the mechanical invariant.
    if coverage || topic == Some("check") {
        let cmd = Cli::command();
        let total = cmd.get_subcommands().count();
        let gaps = docs::coverage_gaps(&cmd);
        if gaps.is_empty() {
            println!("docs coverage: OK — all {total} subcommands have a topic");
            return Ok(());
        }
        eprintln!("docs coverage: {} subcommand(s) undocumented:", gaps.len());
        for g in &gaps {
            eprintln!("  {g}");
        }
        if strict {
            return Err(anyhow!(
                "undocumented subcommands (SR-64): {}",
                gaps.join(", ")
            ));
        }
        return Ok(());
    }

    if let Some(q) = grep {
        let hits = docs::grep(q);
        if hits.is_empty() {
            println!("no topic matches '{q}'");
        }
        for (slug, line) in hits {
            println!("{slug}: {line}");
        }
        return Ok(());
    }

    if list || topic.is_none() {
        if json {
            println!("{}", docs::render_json(None));
        } else {
            print!("{}", docs::render_list());
        }
        return Ok(());
    }

    let slug = topic.unwrap();
    match docs::find(slug) {
        Some(_) if json => println!("{}", docs::render_json(Some(slug))),
        Some(t) => println!("{}", t.body.trim_end()),
        None => {
            eprintln!("no topic '{slug}'.\n");
            print!("{}", docs::render_list());
            return Err(anyhow!("unknown topic: {slug}"));
        }
    }
    Ok(())
}

/// Write a JSON import map listing all function imports in the fused module.
///
/// The output is consumed by downstream tools (synth/kiln) to wire up host
/// imports when instantiating the fused core module.
fn write_import_map(wasm_bytes: &[u8], path: &str) -> Result<()> {
    use wasmparser::{Parser, Payload};

    let mut imports = Vec::new();
    let mut func_index: u32 = 0;

    let parser = Parser::new(0);
    for payload in parser.parse_all(wasm_bytes) {
        let payload = payload.context("Parse error while reading imports")?;
        if let Payload::ImportSection(reader) = payload {
            for import in reader.into_imports() {
                let import = import.context("Failed to read import entry")?;
                if matches!(
                    import.ty,
                    wasmparser::TypeRef::Func(_) | wasmparser::TypeRef::FuncExact(_)
                ) {
                    imports.push(serde_json::json!({
                        "index": func_index,
                        "module": import.module,
                        "name": import.name,
                        "kind": classify_import(import.module, import.name),
                    }));
                    func_index += 1;
                }
            }
        }
    }

    let map = serde_json::json!({ "imports": imports });
    let json = serde_json::to_string_pretty(&map).context("Failed to serialize import map")?;
    fs::write(path, json).with_context(|| format!("Failed to write {}", path))?;

    Ok(())
}

/// Classify a fused module import by its module/name pattern.
fn classify_import(module: &str, name: &str) -> &'static str {
    // Resource operations (can appear under any module)
    if name.starts_with("[resource-drop]")
        || name.starts_with("[resource-new]")
        || name.starts_with("[resource-rep]")
    {
        return "resource";
    }
    // P3 async builtins from $root or [export]$root
    if (module == "$root" || module == "[export]$root")
        && (name.starts_with("[task-return]")
            || name.starts_with("[context-")
            || name.starts_with("[waitable-")
            || name.starts_with("[task-cancel]")
            || name.starts_with("[backpressure-")
            || name.starts_with("[subtask-"))
    {
        return "p3-builtin";
    }
    // WASI imports
    if module.starts_with("wasi:") {
        return "wasi";
    }
    "function"
}

/// Validate WASM bytes (supports both core modules and components)
fn validate_wasm(bytes: &[u8]) -> Result<()> {
    use wasmparser::Validator;

    let features = wasmparser::WasmFeatures::default()
        | wasmparser::WasmFeatures::COMPONENT_MODEL
        | wasmparser::WasmFeatures::MULTI_MEMORY
        | wasmparser::WasmFeatures::CM_ASYNC
        | wasmparser::WasmFeatures::CM_FIXED_LENGTH_LISTS;

    let mut validator = Validator::new_with_features(features);
    validator.validate_all(bytes).context("Validation failed")?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cli_parses() {
        // Test that CLI struct can be parsed
        let cli = Cli::try_parse_from(["meld", "version"]);
        assert!(cli.is_ok());
    }

    #[test]
    fn test_cli_fuse_args() {
        let cli = Cli::try_parse_from([
            "meld", "fuse", "a.wasm", "b.wasm", "-o", "out.wasm", "--stats",
        ]);
        assert!(cli.is_ok());
    }

    #[test]
    fn test_cli_verbose() {
        let cli = Cli::parse_from(["meld", "-v", "version"]);
        assert!(cli.verbose);
    }

    #[test]
    fn test_cli_emit_import_map_arg() {
        let cli = Cli::try_parse_from([
            "meld",
            "fuse",
            "a.wasm",
            "-o",
            "out.wasm",
            "--emit-import-map",
            "/tmp/imports.json",
        ]);
        assert!(cli.is_ok());
        if let Some(Commands::Fuse {
            emit_import_map, ..
        }) = cli.unwrap().command
        {
            assert_eq!(emit_import_map, Some("/tmp/imports.json".to_string()));
        } else {
            panic!("Expected Fuse command");
        }
    }

    #[test]
    fn test_cli_memory_default_is_auto() {
        // #172: the `--memory` default is `auto`, which always resolves to
        // multi-memory (#326, #409). Pin it so a future
        // change to the default is a deliberate edit to this test
        // (flipping it is a high-blast-radius decision — see #172).
        let cli = Cli::try_parse_from(["meld", "fuse", "a.wasm", "-o", "out.wasm"])
            .expect("fuse args parse");
        match cli.command {
            Some(Commands::Fuse { memory, .. }) => assert_eq!(memory, "auto"),
            _ => panic!("Expected Fuse command"),
        }
    }

    #[test]
    fn test_cli_memory_shared_parses() {
        let cli = Cli::try_parse_from([
            "meld", "fuse", "a.wasm", "-o", "out.wasm", "--memory", "shared",
        ])
        .expect("fuse args parse");
        match cli.command {
            Some(Commands::Fuse { memory, .. }) => assert_eq!(memory, "shared"),
            _ => panic!("Expected Fuse command"),
        }
    }

    #[test]
    fn test_cli_memory_multi_parses() {
        let cli = Cli::try_parse_from([
            "meld", "fuse", "a.wasm", "-o", "out.wasm", "--memory", "multi",
        ])
        .expect("fuse args parse");
        match cli.command {
            Some(Commands::Fuse { memory, .. }) => assert_eq!(memory, "multi"),
            _ => panic!("Expected Fuse command"),
        }
    }

    #[test]
    fn test_write_import_map() {
        // Build a minimal core module with two function imports
        use wasm_encoder::{ImportSection, Module, TypeSection, ValType};

        let mut module = Module::new();

        let mut types = TypeSection::new();
        types.ty().function(vec![ValType::I32], vec![]);
        types.ty().function(vec![], vec![ValType::I32]);
        module.section(&types);

        let mut imports = ImportSection::new();
        imports.import(
            "wasi:cli/exit@0.2.6",
            "exit",
            wasm_encoder::EntityType::Function(0),
        );
        imports.import(
            "wasi:io/streams@0.2.6",
            "[method]output-stream.write",
            wasm_encoder::EntityType::Function(1),
        );
        module.section(&imports);

        let wasm_bytes = module.finish();

        let dir = std::env::temp_dir().join("meld_test_import_map");
        let _ = std::fs::create_dir_all(&dir);
        let map_path = dir.join("test_imports.json");

        write_import_map(&wasm_bytes, map_path.to_str().unwrap()).unwrap();

        let contents = std::fs::read_to_string(&map_path).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&contents).unwrap();

        let arr = parsed["imports"].as_array().unwrap();
        assert_eq!(arr.len(), 2);

        assert_eq!(arr[0]["index"], 0);
        assert_eq!(arr[0]["module"], "wasi:cli/exit@0.2.6");
        assert_eq!(arr[0]["name"], "exit");

        assert_eq!(arr[1]["index"], 1);
        assert_eq!(arr[1]["module"], "wasi:io/streams@0.2.6");
        assert_eq!(arr[1]["name"], "[method]output-stream.write");

        let _ = std::fs::remove_dir_all(&dir);
    }
}

/// Does the memory strategy imply validating the output? (#390 / #391)
///
/// Pulled out as a total function over its two inputs so the decision can be
/// enumerated rather than reasoned about: three strategies x two opt-out states
/// is six cases, all covered below. meld#397 makes the case that meld's own
/// decision seams deserve this treatment; this is a small one, so it gets it.
fn validation_is_implied(strategy: &MemoryStrategy, no_validate: bool) -> bool {
    if no_validate {
        return false;
    }
    // Shared memory is where meld rebases absolute addresses and bridges
    // calling conventions inside one address space — the rewriting whose
    // failures (#390, #393) reached consumers as invalid or wrong output.
    // `--memory multi` leaves each module's memory alone, so its output is not
    // exposed to that class and validation stays opt-in there.
    matches!(strategy, MemoryStrategy::SharedMemory)
}

#[cfg(test)]
mod validate_default_tests {
    use super::*;

    /// Every combination, not a sample: the point of a total function is that
    /// its table can be written down.
    // rivet: verifies SR-73
    #[test]
    fn validation_implication_table() {
        use MemoryStrategy::*;
        for (strategy, no_validate, expected) in [
            (SharedMemory, false, true),
            (SharedMemory, true, false),
            (MultiMemory, false, false),
            (MultiMemory, true, false),
            (Auto, false, false),
            (Auto, true, false),
        ] {
            assert_eq!(
                validation_is_implied(&strategy, no_validate),
                expected,
                "strategy={strategy:?} no_validate={no_validate}"
            );
        }
    }

    /// The opt-out must win regardless of strategy — otherwise `--no-validate`
    /// silently does nothing on exactly the path where someone would reach for
    /// it.
    // rivet: verifies SR-73
    #[test]
    fn no_validate_always_wins() {
        for strategy in [
            MemoryStrategy::SharedMemory,
            MemoryStrategy::MultiMemory,
            MemoryStrategy::Auto,
        ] {
            assert!(!validation_is_implied(&strategy, true));
        }
    }
}

#[cfg(test)]
mod auto_memory_claim_tests {
    use super::*;
    use clap::CommandFactory;

    /// Does a sentence claim that `auto` itself selects shared memory? (#409)
    ///
    /// Returns the offending sentences. A sentence qualifies when it names `auto`,
    /// names `shared`, and uses a selection verb or states a condition ("when",
    /// "if") — unless it also carries a negation or a past-tense marker, so "auto
    /// never selects shared" and "until #326 it chose shared" are left alone.
    ///
    /// Deliberately a heuristic over sentences rather than a blocklist of the
    /// phrasings #409 removed: a blocklist would only catch those exact strings,
    /// and the defect it guards against was phrased six different ways across
    /// help text, three doc topics, and code comments.
    fn claims_auto_selects_shared(text: &str) -> Vec<String> {
        const SELECTS: &[&str] = &[
            "pick", "choos", "chose", "select", "resolv", "decide", "escalat", "prefer",
        ];
        // Negation is matched on WHOLE WORDS. A substring match let "not" fire
        // inside "cannot", so "resolve Auto to shared-memory fusion exactly when
        // growth cannot occur" read as negated and a shipped false claim passed.
        // "cannot" is deliberately not a negation here: in that sentence it
        // negates the growth, not the selection.
        const NEGATED_WORDS: &[&str] = &["never", "not", "until", "formerly", "superseded"];
        const NEGATED_PHRASES: &[&[&str]] = &[&["no", "longer"], &["used", "to"]];
        const CONDITIONAL_WORDS: &[&str] = &["when", "if", "unless", "otherwise"];
        // The OUTCOME auto is wrongly said to select, however it is spelled.
        // "shared" alone was too narrow: the `--memory multi` warning said auto
        // "picks a single-memory form when sound" and never used the word, so
        // the guard read past it for three releases (found while measuring for
        // #427).
        const SUBJECT: &[&str] = &["shared", "single-memory", "single memory", "one memory"];
        // A label can attribute an outcome to auto with no verb at all:
        // "Memory strategy: shared + address rebasing (auto: no memory.grow in
        // inputs)". Note `--memory <auto|multi|shared>` carries neither marker,
        // so enumerating the values stays unflagged.
        const ATTRIBUTION: &[&str] = &["(auto", "auto:"];
        text.split(['.', ';'])
            .map(|s| s.split_whitespace().collect::<Vec<_>>().join(" "))
            .filter(|s| {
                let l = s.to_lowercase();
                let words: Vec<&str> = l
                    .split(|c: char| !(c.is_alphanumeric() || c == '\'' || c == '’'))
                    .filter(|w| !w.is_empty())
                    .collect();
                // "default is Auto — shared+rebase when provably safe" states a
                // conditional selection with no selection verb at all.
                let conditional = words.iter().any(|w| CONDITIONAL_WORDS.contains(w));
                let negated = words
                    .iter()
                    .any(|w| NEGATED_WORDS.contains(w) || w.ends_with("n't") || w.ends_with("n’t"))
                    || NEGATED_PHRASES
                        .iter()
                        .any(|p| words.windows(p.len()).any(|win| win == *p));
                l.contains("auto")
                    && SUBJECT.iter().any(|w| l.contains(w))
                    && (SELECTS.iter().any(|v| l.contains(v))
                        || conditional
                        || ATTRIBUTION.iter().any(|a| l.contains(a)))
                    && !negated
            })
            .collect()
    }

    /// The checker must fire on every false phrasing #409 removed. These are
    /// the real sentences from the shipped text, verbatim — if the checker
    /// cannot see them, the scan below proves nothing.
    // rivet: verifies SR-76
    #[test]
    fn checker_fires_on_the_phrasings_that_shipped() {
        for false_claim in [
            r#""auto" (default) picks shared memory with address rebasing when no input module contains `memory.grow`"#,
            "`auto` (default) — meld picks the sound single-memory form when it can: shared memory with address rebasing",
            "`--memory auto` therefore only chooses shared + rebase when no input carries `memory.grow`",
            "Fuser::fuse_with_stats uses it to resolve MemoryStrategy::Auto to shared-memory fusion exactly when the probe proves growth cannot occur",
            "the library default is `Auto` — shared+rebase when provably safe, multi-memory otherwise",
            // Found on 2026-09-18 while measuring boundary strategies for #427:
            // the `--memory multi` warning, shipped v0.56.1..v0.58.0. It never
            // says "shared" — the claim is spelled "single-memory form", which
            // the checker read past until SUBJECT was widened.
            "`--memory auto` (the default) picks a single-memory form when sound",
            // The dead `"shared"` print arm #409 kept, removed in the same pass.
            "Memory strategy: shared + address rebasing (auto: no memory.grow in inputs) — single-memory output",
        ] {
            assert!(
                !claims_auto_selects_shared(false_claim).is_empty(),
                "#409: the checker must flag this shipped false claim: {false_claim}"
            );
        }
    }

    /// And must NOT fire on the true statements that replaced them — otherwise
    /// the scan below would be permanently red and get ignored, or deleted.
    /// Every sentence here names both `auto` and `shared` and uses a selection
    /// verb, so each one reaches the negation check instead of passing because
    /// a keyword is missing.
    // rivet: verifies SR-76
    #[test]
    fn checker_leaves_true_statements_alone() {
        for true_claim in [
            r#""auto" (default) always selects multi-memory, the strategy that is sound for every input, and never selects shared memory or address rebasing on its own"#,
            "`--memory auto` never chooses shared + rebase, which happens only when you select `--memory shared` explicitly",
            "Until #326, auto chose shared + rebase for inputs without a grow instruction",
            "The auto strategy does not select shared memory, whatever the probe reports",
            "Auto no longer picks shared memory for grow-free inputs",
            "Auto doesn't choose shared memory",
        ] {
            assert!(
                claims_auto_selects_shared(true_claim).is_empty(),
                "#409: the checker falsely flagged a true statement: {true_claim}"
            );
        }
    }

    /// Source text with `#[cfg(test)]` modules removed, so a scan of shipped
    /// strings does not trip over this module's own fixtures — the verbatim
    /// false sentences it must flag.
    ///
    /// Line-based on purpose: a brace counter is fooled by the `'{'` and `'}'`
    /// char literals in this very module, and silently under-strips. A
    /// top-level module closes with `}` in column 0, which no string literal
    /// does in rustfmt-formatted source.
    fn without_test_modules(src: &str) -> String {
        let mut out = Vec::new();
        let mut skipping = false;
        for line in src.lines() {
            if !skipping && line.trim_start().starts_with("#[cfg(test)]") {
                skipping = true;
                continue;
            }
            if skipping {
                if line == "}" {
                    skipping = false;
                }
                continue;
            }
            out.push(line);
        }
        out.join("\n")
    }

    /// The human-readable text of a source file: comment bodies and string
    /// literals, with the code between them dropped.
    ///
    /// Scanning raw source made the guard flag its own explanation, because a
    /// line like `if memory_strategy == MemoryStrategy::Auto {` supplies the
    /// word "auto" while the keyword `if` reads as the conditional in
    /// "shared … if …". The requirement is about text meld SHOWS a user, so
    /// the scan reads text.
    ///
    /// Character-level, not line-based, because the claim that prompted this
    /// is a multi-line string with `\` continuations: no single line of it
    /// holds a matched pair of quotes, and a line-based extractor dropped the
    /// whole thing — a control that passed for exactly that reason.
    fn prose_and_literals(src: &str) -> String {
        let mut out = String::new();
        let mut chars = src.chars().peekable();
        while let Some(c) = chars.next() {
            match c {
                '/' if chars.peek() == Some(&'/') => {
                    for c in chars.by_ref() {
                        if c == '\n' {
                            break;
                        }
                        out.push(c);
                    }
                    out.push('\n');
                }
                '"' => {
                    while let Some(c) = chars.next() {
                        match c {
                            '\\' => {
                                // Skip the escaped character; a line
                                // continuation contributes nothing but
                                // whitespace anyway.
                                chars.next();
                                out.push(' ');
                            }
                            '"' => break,
                            _ => out.push(c),
                        }
                    }
                    out.push('\n');
                }
                _ => {}
            }
        }
        out
    }

    /// The same claim, hiding in a runtime message. #409 corrected the help and
    /// the doc topics; the `--memory multi` warning went on telling users that
    /// `auto` "picks a single-memory form when sound" for three more releases,
    /// because the scan above reads rendered help and topic bodies, not message
    /// literals. Found while measuring boundary strategies for #427.
    // rivet: verifies SR-82
    #[test]
    fn no_shipped_source_string_claims_auto_selects_shared() {
        let mut offending = Vec::new();
        for (label, src) in [
            ("meld-cli/src/main.rs", include_str!("main.rs")),
            ("meld-cli/src/docs.rs", include_str!("docs.rs")),
        ] {
            let scanned = prose_and_literals(&without_test_modules(src));
            assert!(
                scanned.len() > 1000,
                "guard: {label} scan is empty after stripping test modules"
            );
            for s in claims_auto_selects_shared(&scanned) {
                offending.push(format!("{label}: {s}"));
            }
        }
        assert!(
            offending.is_empty(),
            "#409: shipped source text claims `auto` selects shared memory:\n{}",
            offending.join("\n")
        );
    }

    /// The recurrence guard. Every string meld ships about the memory strategy —
    /// the full `fuse --help` and every `meld docs` topic body — must not claim
    /// that `auto` selects shared memory. SR-64's documentation invariant checks
    /// only that topics exist and exceed 40 characters, so it passed while three
    /// topics and the help text described the unsound behaviour SR-37 removed.
    // rivet: verifies SR-76
    #[test]
    fn no_shipped_help_or_doc_topic_claims_auto_selects_shared() {
        let mut cmd = Cli::command();
        let fuse = cmd
            .find_subcommand_mut("fuse")
            .expect("fuse subcommand exists");
        let help = fuse.render_long_help().to_string();

        // Guard the guard: prove the scan is reading real text, so an empty or
        // wrong source cannot pass vacuously.
        assert!(
            help.contains("--memory") && help.to_lowercase().contains("auto"),
            "scan is not reading the real `fuse --help` text"
        );
        assert!(
            docs::TOPICS.len() > 5,
            "scan is not reading the embedded doc topics"
        );
        assert!(
            docs::find("memory-strategies").is_some(),
            "the memory-strategies topic must be among the scanned topics"
        );

        let mut offending = Vec::new();
        for s in claims_auto_selects_shared(&help) {
            offending.push(format!("fuse --help: {s}"));
        }
        for topic in docs::TOPICS {
            for s in claims_auto_selects_shared(topic.body) {
                offending.push(format!("meld docs {}: {s}", topic.slug));
            }
        }
        assert!(
            offending.is_empty(),
            "#409: shipped text claims `auto` selects shared memory, which SR-37 \
             forbids as unsound (auto always selects multi-memory):\n{}",
            offending.join("\n")
        );

        // And the positive statement must actually be there.
        assert!(
            help.contains("always selects multi-memory"),
            "`fuse --help` must state what auto selects"
        );
    }
}
