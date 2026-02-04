"""Bazel rules for meld static component fusion.

This module provides the `meld_fuse` rule for statically fusing WebAssembly
components into a single core module.

## Example Usage

```starlark
load("@meld//rules:meld.bzl", "meld_fuse")

# Fuse multiple components
meld_fuse(
    name = "my_fused_module",
    components = [
        ":component_a",
        ":component_b",
    ],
)

# Fuse with options
meld_fuse(
    name = "my_fused_module_optimized",
    components = [
        ":component_a",
        ":component_b",
    ],
    memory_strategy = "shared",
    attestation = True,
    stats = True,
)
```

## Integration with rules_wasm_component

This rule integrates with rules_wasm_component for a seamless build experience:

```starlark
load("@rules_wasm_component//rust:defs.bzl", "rust_wasm_component")
load("@meld//rules:meld.bzl", "meld_fuse")

rust_wasm_component(
    name = "component_a",
    # ...
)

rust_wasm_component(
    name = "component_b",
    # ...
)

meld_fuse(
    name = "fused",
    components = [":component_a", ":component_b"],
)
```
"""

load(":providers.bzl", "ComponentInfo", "MeldFusedInfo")

def _get_component_files(ctx, components):
    """Extract .wasm files from component targets."""
    files = []
    for component in components:
        # Handle different provider types
        if ComponentInfo in component:
            files.append(component[ComponentInfo].component)
        elif DefaultInfo in component:
            # Look for .wasm files in the default outputs
            for f in component[DefaultInfo].files.to_list():
                if f.path.endswith(".wasm"):
                    files.append(f)
                    break
    return files

def _meld_fuse_impl(ctx):
    """Implementation of meld_fuse rule."""

    # Get the meld binary
    meld = ctx.executable._meld

    # Collect input component files
    component_files = _get_component_files(ctx, ctx.attr.components)

    if not component_files:
        fail("No .wasm component files found in components")

    # Determine output file name
    output_name = ctx.attr.out if ctx.attr.out else ctx.label.name + ".wasm"
    output = ctx.actions.declare_file(output_name)

    # Build command arguments
    args = ctx.actions.args()
    args.add("fuse")

    # Add input files
    for f in component_files:
        args.add(f.path)

    # Output file
    args.add("--output", output.path)

    # Memory strategy
    args.add("--memory", ctx.attr.memory_strategy)

    # Optional flags
    if ctx.attr.address_rebase:
        args.add("--address-rebase")

    if not ctx.attr.attestation:
        args.add("--no-attestation")

    if ctx.attr.preserve_names:
        args.add("--preserve-names")

    if ctx.attr.validate:
        args.add("--validate")

    # Declare additional outputs
    outputs = [output]

    attestation_file = None
    if ctx.attr.attestation:
        attestation_file = ctx.actions.declare_file(ctx.label.name + ".attestation.json")
        # Note: meld embeds attestation in custom section, but we could also output separately

    stats_file = None
    if ctx.attr.stats:
        stats_file = ctx.actions.declare_file(ctx.label.name + ".stats.json")
        args.add("--stats")

    # Run meld
    ctx.actions.run(
        outputs = outputs,
        inputs = component_files,
        executable = meld,
        arguments = [args],
        mnemonic = "MeldFuse",
        progress_message = "Fusing %d components into %s" % (len(component_files), output.short_path),
    )

    # Build providers
    return [
        DefaultInfo(
            files = depset(outputs),
            runfiles = ctx.runfiles(files = outputs),
        ),
        MeldFusedInfo(
            fused_wasm = output,
            attestation = attestation_file,
            stats = stats_file,
            source_components = depset(component_files),
            memory_strategy = ctx.attr.memory_strategy,
        ),
    ]

meld_fuse = rule(
    implementation = _meld_fuse_impl,
    doc = """Fuses multiple WebAssembly components into a single core module.

This rule takes P2/P3 WebAssembly components and statically links them,
eliminating the need for runtime component linking. The output is a single
core WebAssembly module that can be optimized with LOOM and run directly
in browsers or WASM runtimes.

## Attributes

| Name | Description |
|------|-------------|
| components | List of component targets to fuse |
| out | Output filename (default: {name}.wasm) |
| memory_strategy | "shared" (default) or "multi" |
| address_rebase | Rebase memory addresses for shared memory (experimental) |
| attestation | Include transformation attestation |
| preserve_names | Keep debug names in output |
| stats | Generate statistics file |
| validate | Validate output with wasmparser |
""",
    attrs = {
        "components": attr.label_list(
            doc = "WebAssembly component targets to fuse.",
            mandatory = True,
            allow_files = [".wasm"],
        ),
        "out": attr.string(
            doc = "Output filename. Defaults to {name}.wasm.",
        ),
        "memory_strategy": attr.string(
            doc = "Memory strategy: 'shared' (all components share memory) or 'multi' (each component has own memory).",
            default = "shared",
            values = ["shared", "multi"],
        ),
        "address_rebase": attr.bool(
            doc = "Rebase memory addresses for shared memory (experimental).",
            default = False,
        ),
        "attestation": attr.bool(
            doc = "Include transformation attestation in output custom section.",
            default = True,
        ),
        "preserve_names": attr.bool(
            doc = "Preserve debug names in the output module.",
            default = False,
        ),
        "stats": attr.bool(
            doc = "Generate a JSON file with fusion statistics.",
            default = False,
        ),
        "validate": attr.bool(
            doc = "Validate the output module with wasmparser.",
            default = False,
        ),
        "_meld": attr.label(
            doc = "The meld CLI tool.",
            default = Label("//meld-cli:meld"),
            executable = True,
            cfg = "exec",
        ),
    },
)

def _meld_toolchain_impl(ctx):
    """Implementation of meld_toolchain rule."""
    toolchain_info = platform_common.ToolchainInfo(
        meld = ctx.executable.meld,
        version = ctx.attr.version,
    )
    return [toolchain_info]

meld_toolchain = rule(
    implementation = _meld_toolchain_impl,
    doc = "Defines a meld toolchain.",
    attrs = {
        "meld": attr.label(
            doc = "The meld binary.",
            mandatory = True,
            executable = True,
            cfg = "exec",
        ),
        "version": attr.string(
            doc = "Version of the meld tool.",
            default = "0.1.0",
        ),
    },
)

def meld_register_toolchains():
    """Register meld toolchains.

    Call this in your MODULE.bazel or WORKSPACE to register the meld toolchain.
    """
    native.register_toolchains("@meld//:meld_toolchain")
