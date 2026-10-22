# @pulseengine/meld

Static WebAssembly component fusion: the `meld` command-line tool.

```bash
npx @pulseengine/meld --version
npm install -g @pulseengine/meld
```

This package is a tiny launcher. The signed release binary ships in one
per-platform package (`@pulseengine/meld-<platform>`) that npm selects through
`optionalDependencies` by `os` / `cpu` / `libc`. There is no install script and
nothing is downloaded at install time. The binaries are the ones listed in the
cosign-signed `SHA256SUMS.txt` of the matching GitHub release.

Supported: macOS and Linux (glibc and musl) on x64 and arm64.

Docs and source: https://github.com/pulseengine/meld
