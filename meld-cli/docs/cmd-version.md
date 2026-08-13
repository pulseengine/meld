# meld version — show version and toolchain context

`meld version` prints the meld release version (the crate version compiled into
the binary) together with a short description of the tool and its place in the
pulseengine toolchain — alongside `loom` (the WebAssembly optimizer) and the
other pulseengine components — plus the project URL and licence (Apache-2.0).

It takes no arguments and makes no changes; it is the quick way to confirm
which build you are running. Note that `--version` (the clap flag, e.g.
`meld --version`) prints just the bare version string, whereas the `version`
subcommand prints the fuller toolchain banner.
