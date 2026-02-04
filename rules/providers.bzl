"""Providers for meld Bazel rules.

These providers carry information between rules in the meld toolchain.
"""

MeldFusedInfo = provider(
    doc = "Information about a fused WebAssembly module produced by meld.",
    fields = {
        "fused_wasm": "File: The fused core WebAssembly module.",
        "attestation": "File: Optional attestation JSON file.",
        "stats": "File: Optional fusion statistics JSON file.",
        "source_components": "depset[File]: The source component files that were fused.",
        "memory_strategy": "string: Memory strategy used ('shared' or 'multi').",
    },
)

MeldToolchainInfo = provider(
    doc = "Information about the meld toolchain.",
    fields = {
        "meld_binary": "File: The meld CLI binary.",
        "version": "string: Version of the meld tool.",
    },
)

ComponentInfo = provider(
    doc = "Information about a WebAssembly component.",
    fields = {
        "component": "File: The component .wasm file.",
        "wit": "File: Optional WIT interface file.",
        "name": "string: Component name.",
    },
)
