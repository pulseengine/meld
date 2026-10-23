#!/usr/bin/env python3
"""Stage (and optionally `npm pack`) the @pulseengine/meld npm packages (#442).

    python3 -I npm/build_npm.py --tag v0.65.0 --assets DIR --out DIR [--pack]

Reuses the verification path of python/build_wheels.py (loaded by file path:
`python3 -I` does not put script directories on sys.path): SHA256SUMS.txt
checks for every tarball (fail closed), ELF/Mach-O architecture cross-checks,
`meld --version` == tag where runnable, workspace version == tag in-repo.

Output, under --out:
    pkgs/<platform>/        per-platform package: package.json (os/cpu/libc),
                            bin/meld (0755, the verified release binary), LICENSE
    pkgs/root/              @pulseengine/meld: bin/meld.js launcher +
                            optionalDependencies pinned to the exact version
    tarballs/*.tgz          with --pack (npm pack --ignore-scripts)
    npm-sha256.txt          sha256 of each tarball, with --pack

No install scripts are emitted anywhere.
"""

import argparse
import importlib.util
import json
import pathlib
import shutil
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("build_wheels", HERE.parent / "python" / "build_wheels.py")
bw = importlib.util.module_from_spec(_spec)
sys.modules["build_wheels"] = bw  # dataclass-free, but keeps tracebacks readable
_spec.loader.exec_module(bw)


def platform_pkg_name(root, tcfg):
    return f"{root}-{tcfg['npm-platform']}"


def stage_platform(config, version, rec, out):
    root = config["dist"]["npm-name"]
    tcfg = rec["cfg"]
    name = platform_pkg_name(root, tcfg)
    d = out / "pkgs" / tcfg["npm-platform"]
    if d.exists():
        shutil.rmtree(d)
    (d / "bin").mkdir(parents=True)
    exe = d / "bin" / config["dist"]["binary"]
    exe.write_bytes(rec["binary"])
    exe.chmod(0o755)
    if "license" not in rec:
        raise bw.DistError(f"{rec['target']}: tarball has no LICENSE")
    (d / "LICENSE").write_bytes(rec["license"])

    pkg = {
        "name": name,
        "version": version,
        "description": f"meld {version} binary for {rec['target']} (installed via {root})",
        "license": config["project"]["license"],
        "os": [tcfg["npm-os"]],
        "cpu": [tcfg["npm-cpu"]],
    }
    if "npm-libc" in tcfg:
        pkg["libc"] = [tcfg["npm-libc"]]
    pkg.update(
        {
            "files": ["bin/", "LICENSE"],
            "repository": {
                "type": "git",
                "url": "git+https://github.com/pulseengine/meld.git",
                "directory": "npm",
            },
            "homepage": config["project"]["urls"]["Homepage"],
            "publishConfig": {"access": "public"},
        }
    )
    (d / "package.json").write_text(json.dumps(pkg, indent=2) + "\n")
    return name, d


def stage_root(config, version, recs, platform_names, out):
    root = config["dist"]["npm-name"]
    src = HERE
    d = out / "pkgs" / "root"
    if d.exists():
        shutil.rmtree(d)
    (d / "bin").mkdir(parents=True)
    shutil.copy2(src / "bin" / "meld.js", d / "bin" / "meld.js")
    (d / "bin" / "meld.js").chmod(0o755)
    shutil.copy2(src / "README.md", d / "README.md")
    (d / "LICENSE").write_bytes(recs[0]["license"])
    pkg = json.loads((src / "package.json").read_text())
    if pkg["name"] != root:
        raise bw.DistError(f"npm/package.json name {pkg['name']} != pyproject npm-name {root}")
    pkg["version"] = version
    pkg["optionalDependencies"] = {n: version for n in sorted(platform_names)}
    for forbidden in ("scripts", "dependencies"):
        if forbidden in pkg:
            raise bw.DistError(f"npm/package.json must not define {forbidden} (no install scripts, no runtime deps)")
    (d / "package.json").write_text(json.dumps(pkg, indent=2) + "\n")
    return root, d


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--tag", required=True)
    ap.add_argument("--assets", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--cargo-toml")
    ap.add_argument("--no-cargo-check", action="store_true")
    ap.add_argument("--pack", action="store_true", help="run `npm pack --ignore-scripts` on every staged package")
    args = ap.parse_args(argv)

    try:
        config = bw.load_config()
        version, recs = bw.load_verified_release(
            args.tag, args.assets, config, pathlib.Path(args.cargo_toml) if args.cargo_toml else None,
            no_cargo_check=args.no_cargo_check,
        )
        out = pathlib.Path(args.out).resolve()  # npm pack runs with cwd=<package>, so relative paths break
        staged = []
        for rec in recs:
            staged.append(stage_platform(config, version, rec, out))
        # platform packages first, root last: this is also the publish order
        staged.append(stage_root(config, version, recs, [n for n, _ in staged], out))
    except bw.DistError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    for name, d in staged:
        print(f"staged {name}@{version}  {d}")

    if args.pack:
        tdir = out / "tarballs"
        tdir.mkdir(parents=True, exist_ok=True)
        lines = []
        for name, d in staged:
            res = subprocess.run(
                ["npm", "pack", "--ignore-scripts", "--pack-destination", str(tdir), "--json"],
                cwd=d, capture_output=True, text=True,
            )
            if res.returncode != 0:
                print(f"error: npm pack failed for {name}: {res.stderr}", file=sys.stderr)
                return 1
            fname = json.loads(res.stdout)[0]["filename"].replace("/", "-").lstrip("@")
            path = tdir / fname
            if not path.is_file():
                print(f"error: expected tarball {path} missing after npm pack", file=sys.stderr)
                return 1
            lines.append(f"{bw.sha256_file(path)}  {path.name}")
            print(f"packed {path.name}")
        (out / "npm-sha256.txt").write_text("\n".join(sorted(lines, key=lambda s: s.split()[1])) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
