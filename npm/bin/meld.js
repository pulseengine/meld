#!/usr/bin/env node
// Launcher for the meld binary shipped in a per-platform package (#442).
//
// No install scripts and no downloads: npm installs exactly one of the
// optionalDependencies that matches this machine's `os` / `cpu` / `libc`, and
// this file finds it and execs it.
"use strict";

const { spawnSync } = require("child_process");
const fs = require("fs");
const path = require("path");

const SCOPE = "@pulseengine";
const BASE = "meld";

function isMusl() {
  // glibcVersionRuntime is only present in the report on glibc systems.
  try {
    const report = process.report && process.report.getReport();
    const header = report && (typeof report === "string" ? JSON.parse(report) : report).header;
    return !(header && header.glibcVersionRuntime);
  } catch (_) {
    return false;
  }
}

function candidates() {
  const arch = { x64: "x64", arm64: "arm64" }[process.arch];
  if (!arch) return [];
  if (process.platform === "darwin") return [`darwin-${arch}`];
  if (process.platform === "linux") {
    // The musl build is fully static, so it is a valid fallback on glibc hosts.
    return isMusl() ? [`linux-${arch}-musl`] : [`linux-${arch}-gnu`, `linux-${arch}-musl`];
  }
  return [];
}

function findBinary() {
  const tried = [];
  for (const platform of candidates()) {
    const pkg = `${SCOPE}/${BASE}-${platform}`;
    tried.push(pkg);
    let dir;
    try {
      dir = path.dirname(require.resolve(`${pkg}/package.json`));
    } catch (_) {
      continue;
    }
    const bin = path.join(dir, "bin", BASE);
    if (fs.existsSync(bin)) return bin;
  }
  const where = `${process.platform}/${process.arch}`;
  console.error(
    tried.length
      ? `meld: no installed platform package for ${where} (looked for ${tried.join(", ")}).\n` +
          `Reinstall without --omit=optional / --no-optional.`
      : `meld: unsupported platform ${where}. Supported: macOS and Linux on x64 and arm64.`
  );
  process.exit(1);
}

const bin = findBinary();
try {
  fs.accessSync(bin, fs.constants.X_OK);
} catch (_) {
  try {
    fs.chmodSync(bin, 0o755); // some extractors drop the executable bit
  } catch (_) {
    /* fall through; spawn reports the real error */
  }
}

const result = spawnSync(bin, process.argv.slice(2), { stdio: "inherit" });
if (result.error) {
  console.error(`meld: failed to run ${bin}: ${result.error.message}`);
  process.exit(1);
}
if (result.signal) {
  process.kill(process.pid, result.signal);
} else {
  process.exit(result.status === null ? 1 : result.status);
}
