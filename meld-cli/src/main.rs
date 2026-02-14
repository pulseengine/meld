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
use meld_core::{Fuser, FuserConfig, FusionStats, MemoryStrategy};
use std::fs;
use std::path::Path;
use std::time::Instant;

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

        /// Memory strategy: "shared" (default) or "multi"
        #[arg(long, default_value = "shared")]
        memory: String,

        /// Rebase memory addresses for shared memory (experimental)
        #[arg(long)]
        address_rebase: bool,

        /// Show fusion statistics
        #[arg(long)]
        stats: bool,

        /// Disable attestation in output
        #[arg(long)]
        no_attestation: bool,

        /// Preserve debug names in output
        #[arg(long)]
        preserve_names: bool,

        /// Validate output with wasmparser
        #[arg(long)]
        validate: bool,
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
            preserve_names,
            validate,
        }) => {
            fuse_command(
                inputs,
                output,
                memory,
                address_rebase,
                stats,
                no_attestation,
                preserve_names,
                validate,
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

        None => {
            println!("meld - Static WebAssembly Component Fusion");
            println!();
            println!("Usage: meld <COMMAND>");
            println!();
            println!("Commands:");
            println!("  fuse      Fuse multiple components into a single module");
            println!("  inspect   Inspect a WebAssembly component");
            println!("  version   Show version information");
            println!("  help      Print this message or help for subcommands");
            println!();
            println!("For more information, run: meld help <command>");
        }
    }

    Ok(())
}

/// Fuse command implementation
#[allow(clippy::too_many_arguments)]
fn fuse_command(
    inputs: Vec<String>,
    output: String,
    memory: String,
    address_rebase: bool,
    show_stats: bool,
    no_attestation: bool,
    preserve_names: bool,
    validate: bool,
) -> Result<()> {
    println!(
        "Meld v{} - Static Component Fusion",
        env!("CARGO_PKG_VERSION")
    );

    // Parse memory strategy
    let memory_strategy = match memory.as_str() {
        "shared" => MemoryStrategy::SharedMemory,
        "multi" => {
            println!("Multi-memory support is experimental (Phase 2)");
            MemoryStrategy::MultiMemory
        }
        _ => {
            return Err(anyhow!(
                "Invalid memory strategy: {}. Use 'shared' or 'multi'",
                memory
            ));
        }
    };

    if address_rebase {
        println!("Address rebasing is experimental and may have limitations");
    }

    // Configure fuser
    let config = FuserConfig {
        memory_strategy,
        attestation: !no_attestation,
        address_rebasing: address_rebase,
        preserve_names,
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
    println!("Fusing {} components...", fuser.component_count());

    // Perform fusion
    let (fused_bytes, stats) = fuser.fuse_with_stats().context("Fusion failed")?;

    let elapsed = start.elapsed();

    // Validate if requested
    if validate {
        println!();
        println!("Validating output...");
        validate_wasm(&fused_bytes)?;
        println!("  Validation passed");
    }

    // Write output
    fs::write(&output, &fused_bytes).with_context(|| format!("Failed to write {}", output))?;

    println!();
    println!("Output: {} ({} bytes)", output, fused_bytes.len());

    // Show statistics
    if show_stats {
        print_stats(&stats, total_input_size, elapsed);
    } else {
        let reduction = if total_input_size > 0 {
            ((total_input_size - fused_bytes.len()) as f64 / total_input_size as f64) * 100.0
        } else {
            0.0
        };
        println!("  Size reduction: {:.1}%", reduction);
        println!("  Time: {:?}", elapsed);
    }

    println!();
    println!("Fusion complete!");

    Ok(())
}

/// Print detailed statistics
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

    let reduction = if total_input_size > 0 {
        ((total_input_size - stats.output_size) as f64 / total_input_size as f64) * 100.0
    } else {
        0.0
    };
    println!("  Reduction:           {:.1}%", reduction);

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

/// Validate WASM bytes
fn validate_wasm(bytes: &[u8]) -> Result<()> {
    use wasmparser::{Parser, Payload, Validator};

    let mut validator = Validator::new();
    let parser = Parser::new(0);

    for payload in parser.parse_all(bytes) {
        let payload = payload.context("Parse error during validation")?;

        // Validate each payload
        match &payload {
            Payload::Version {
                num,
                encoding,
                range,
            } => {
                validator
                    .version(*num, *encoding, range)
                    .context("Invalid version")?;
            }
            _ => {
                // Other payloads validated through the parser
            }
        }
    }

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
}
