#!/usr/bin/env python3
"""Repack the signed meld release binaries into PyPI platform wheels (#442).

    python3 -I python/build_wheels.py --tag v0.65.0 --assets DIR --out DIR

stdlib only. The wheels are REPACKED from the release tarballs, never rebuilt:
the `meld` inside each wheel is byte-for-byte the one whose sha256 sits in the
cosign-signed SHA256SUMS.txt.

Trust chain (this script owns the second link; the workflow owns the first):

  1. workflow : `cosign verify-blob` of SHA256SUMS.txt against its bundle
  2. here     : every tarball's sha256 must equal its SHA256SUMS.txt line.
                Fail closed: a missing line, a missing file, an extra
                unparsable line, or a mismatch aborts before ANY output is
                written.

This module is also the shared verification path for `npm/build_npm.py`, which
loads it by file path (`python3 -I` does not put the script directory on
sys.path, so a plain `import build_wheels` would not work).

Wheel tags are DERIVED from the binary, not guessed:

  * gnu  -> `manylinux_2_<N>_<arch>`. N is the highest `GLIBC_2.N` version in
            the ELF's SHT_GNU_verneed section (the versioned symbols the binary
            imports; `objdump -T` shows the same data). The ELF machine type
            must agree with the target's arch, a PT_INTERP must be present, and
            libgcc_s `GCC_x.y` versions (Rust's unwinder; libgcc_s.so.1 is on the
            manylinux allowed-library list) are accepted up to 4.8.0; any other
            versioned dependency (GLIBCXX_/CXXABI_, newer GCC_) fails closed
            because the manylinux policy would then need a check this script
            does not do. DT_NEEDED sonames are NOT audited (no auditwheel).
  * musl -> `musllinux_1_2_<arch>`. The musl assets are static (#432): the ELF
            must have NO PT_INTERP and NO versioned imports, otherwise it is
            not the portable asset the tag claims and the build fails.
  * macOS-> `macosx_<M>_<m>_<arch>` from the Mach-O LC_BUILD_VERSION (platform
            macOS) or LC_VERSION_MIN_MACOSX `minos` field (what
            `otool -l | grep -A4 LC_BUILD_VERSION` prints). pip's tag matcher
            only generates `macosx_<major>_0` for macOS >= 11, so a
            fractional minos such as 13.3 is rounded UP to the next major
            (14.0): claiming 13.0 would admit a Mac the binary cannot run on.
            Below 11 (10.x) the minor is kept.

The tag's version must equal `meld --version` of the native binary (when this
host can run one) and the workspace version in Cargo.toml (when found).
"""

import argparse
import base64
import hashlib
import os
import pathlib
import platform
import re
import stat
import struct
import subprocess
import sys
import tarfile
import tempfile
try:
    import tomllib
except ModuleNotFoundError:  # Python < 3.11, e.g. macOS /usr/bin/python3 (3.9)
    try:
        import tomli as tomllib
    except ModuleNotFoundError:
        sys.exit("build_wheels.py: needs Python 3.11+ (tomllib) or the tomli package")
import zipfile

HERE = pathlib.Path(__file__).resolve().parent
CONFIG_PATH = HERE / "pyproject.toml"
REPO_ROOT = HERE.parent

TAG_RE = re.compile(r"^v(\d+)\.(\d+)\.(\d+)$")
# Fixed timestamp so rebuilding the same inputs yields identical wheels.
ZIP_DATE = (2020, 1, 1, 0, 0, 0)


class DistError(Exception):
    """A verification or build failure. Always fatal, always explained."""


# --------------------------------------------------------------------------
# Config (single source of truth: python/pyproject.toml)
# --------------------------------------------------------------------------


def load_config(path=CONFIG_PATH):
    with open(path, "rb") as f:
        data = tomllib.load(f)
    project = data["project"]
    dist = data["tool"]["meld-dist"]
    if not dist.get("targets"):
        raise DistError(f"{path}: no [tool.meld-dist.targets.*] tables")
    return {"project": project, "dist": dist, "targets": dist["targets"]}


# --------------------------------------------------------------------------
# Version handling
# --------------------------------------------------------------------------


def version_from_tag(tag):
    if not TAG_RE.match(tag):
        raise DistError(
            f"tag {tag!r} is not vX.Y.Z. Pre-release tags are refused: PEP 440 and "
            f"semver spell them differently and registry uploads cannot be redone."
        )
    return tag[1:]


def workspace_version(cargo_toml):
    with open(cargo_toml, "rb") as f:
        data = tomllib.load(f)
    try:
        return data["workspace"]["package"]["version"]
    except KeyError:
        raise DistError(f"{cargo_toml}: no [workspace.package].version")


def check_cargo_version(version, cargo_toml, required):
    """Assert tag == workspace version. `cargo_toml=None` auto-detects the
    in-repo file; a missing file is only an error when `required`."""
    if cargo_toml is None:
        cargo_toml = REPO_ROOT / "Cargo.toml"
        if not cargo_toml.is_file():
            if required:
                raise DistError("Cargo.toml requested but not found")
            return None
    got = workspace_version(cargo_toml)
    if got != version:
        raise DistError(
            f"tag version {version} != workspace version {got} in {cargo_toml}. "
            f"Check out the tag, or pass --cargo-toml for that tag's Cargo.toml."
        )
    return got


# --------------------------------------------------------------------------
# Checksums: SHA256SUMS.txt -> tarball verification (fail closed)
# --------------------------------------------------------------------------

SUMS_LINE = re.compile(r"^([0-9a-f]{64})\s+\*?(?:\./)?(\S.*)$")


def parse_sums(text):
    sums = {}
    for n, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        m = SUMS_LINE.match(line)
        if not m:
            raise DistError(f"SHA256SUMS.txt line {n} is not '<sha256>  <name>': {line!r}")
        name = m.group(2)
        if name in sums:
            raise DistError(f"SHA256SUMS.txt lists {name} twice")
        sums[name] = m.group(1)
    if not sums:
        raise DistError("SHA256SUMS.txt is empty")
    return sums


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def verify_tarball(assets, name, sums):
    if name not in sums:
        raise DistError(f"{name} has no line in SHA256SUMS.txt - refusing to use an unlisted asset")
    path = assets / name
    if not path.is_file():
        raise DistError(f"{name} is listed in SHA256SUMS.txt but absent from {assets}")
    got = sha256_file(path)
    if got != sums[name]:
        raise DistError(
            f"CHECKSUM MISMATCH for {name}\n  SHA256SUMS.txt: {sums[name]}\n"
            f"  actual file   : {got}\nRefusing to build from a tarball that does not "
            f"match the signed checksum list."
        )
    return got


# --------------------------------------------------------------------------
# Tarball extraction (only the three files we expect, regular files only)
# --------------------------------------------------------------------------


def read_release_files(tarball, tag, target, binary_name):
    top = f"meld-{tag}-{target}"
    wanted = {"binary": f"{top}/{binary_name}", "license": f"{top}/LICENSE", "readme": f"{top}/README.md"}
    out = {}
    with tarfile.open(tarball, "r:gz") as tf:
        members = {m.name.lstrip("./"): m for m in tf.getmembers()}
        for key, name in wanted.items():
            m = members.get(name)
            if m is None:
                if key == "binary":
                    raise DistError(f"{tarball.name}: no {name} member")
                continue
            if not m.isreg():
                raise DistError(f"{tarball.name}: {name} is not a regular file")
            out[key] = tf.extractfile(m).read()
    if not out["binary"]:
        raise DistError(f"{tarball.name}: {wanted['binary']} is empty")
    return out


# --------------------------------------------------------------------------
# Binary inspection -> platform tag
# --------------------------------------------------------------------------

ELF_MACHINE = {62: "x86_64", 183: "aarch64"}
SHT_GNU_VERNEED = 0x6FFFFFFE
PT_INTERP = 3
GCC_VERSION = re.compile(r"GCC_\d+(?:\.\d+)*")
GCC_MAX = (4, 8, 0)  # manylinux2014-era ceiling for libgcc_s symbol versions


def inspect_elf(data):
    """Return {arch, has_interp, glibc_floor (minor or None), other_versions}."""
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise DistError("not a little-endian ELF64 binary")
    (e_machine,) = struct.unpack_from("<H", data, 18)
    e_phoff, e_shoff = struct.unpack_from("<QQ", data, 32)
    e_phentsize, e_phnum, e_shentsize, e_shnum = struct.unpack_from("<HHHH", data, 54)
    arch = ELF_MACHINE.get(e_machine)
    if arch is None:
        raise DistError(f"unsupported ELF e_machine {e_machine}")

    has_interp = False
    for i in range(e_phnum):
        (p_type,) = struct.unpack_from("<I", data, e_phoff + i * e_phentsize)
        if p_type == PT_INTERP:
            has_interp = True

    if e_shoff == 0 or e_shnum == 0:
        raise DistError("ELF has no section headers; cannot read symbol versions (fail closed)")
    sections = []
    for i in range(e_shnum):
        sh = struct.unpack_from("<IIQQQQIIQQ", data, e_shoff + i * e_shentsize)
        # name, type, flags, addr, offset, size, link, info, addralign, entsize
        sections.append({"type": sh[1], "offset": sh[4], "size": sh[5], "link": sh[6]})

    versions = []
    for sec in sections:
        if sec["type"] != SHT_GNU_VERNEED:
            continue
        strtab = sections[sec["link"]]
        off = sec["offset"]
        while True:
            _vn_version, vn_cnt, _vn_file, vn_aux, vn_next = struct.unpack_from("<HHIII", data, off)
            aux = off + vn_aux
            for _ in range(vn_cnt):
                _hash, _flags, _other, vna_name, vna_next = struct.unpack_from("<IHHII", data, aux)
                start = strtab["offset"] + vna_name
                versions.append(data[start : data.index(b"\0", start)].decode("ascii"))
                aux += vna_next
            if vn_next == 0:
                break
            off += vn_next

    glibc = []
    other = []
    for v in versions:
        m = re.fullmatch(r"GLIBC_2\.(\d+)(?:\.\d+)?", v)
        if m:
            glibc.append(int(m.group(1)))
        elif v == "GLIBC_PRIVATE":
            continue
        elif GCC_VERSION.fullmatch(v) and tuple(int(x) for x in v[4:].split(".")) <= GCC_MAX:
            # libgcc_s.so.1 (Rust's unwinder) is on the manylinux allowed-library
            # list; its symbol versions are accepted up to the policy ceiling.
            continue
        else:
            other.append(v)
    return {
        "arch": arch,
        "has_interp": has_interp,
        "glibc_floor": max(glibc) if glibc else None,
        "other_versions": other,
    }


MACHO_MAGIC_64 = 0xFEEDFACF
MACHO_CPU = {0x01000007: "x86_64", 0x0100000C: "arm64"}
LC_VERSION_MIN_MACOSX = 0x24
LC_BUILD_VERSION = 0x32
PLATFORM_MACOS = 1


def inspect_macho(data):
    """Return {arch, minos: (major, minor)} from a thin 64-bit Mach-O."""
    (magic,) = struct.unpack_from("<I", data, 0)
    if magic != MACHO_MAGIC_64:
        raise DistError(f"not a thin little-endian 64-bit Mach-O (magic {magic:#x}); fat binaries are refused")
    cputype, _sub, _ftype, ncmds, _sizeofcmds, _flags, _res = struct.unpack_from("<iiIIIII", data, 4)
    arch = MACHO_CPU.get(cputype & 0xFFFFFFFF)
    if arch is None:
        raise DistError(f"unsupported Mach-O cputype {cputype:#x}")
    off = 32
    minos = None
    for _ in range(ncmds):
        cmd, cmdsize = struct.unpack_from("<II", data, off)
        if cmd == LC_BUILD_VERSION:
            platform_id, v, _sdk, _ntools = struct.unpack_from("<IIII", data, off + 8)
            if platform_id == PLATFORM_MACOS:
                minos = (v >> 16, (v >> 8) & 0xFF)
        elif cmd == LC_VERSION_MIN_MACOSX and minos is None:
            v, _sdk = struct.unpack_from("<II", data, off + 8)
            minos = (v >> 16, (v >> 8) & 0xFF)
        off += cmdsize
    if minos is None:
        raise DistError("Mach-O has neither LC_BUILD_VERSION (macOS) nor LC_VERSION_MIN_MACOSX")
    return {"arch": arch, "minos": minos}


def macos_tag(arch, minos):
    major, minor = minos
    if major >= 11:
        if minor:
            major += 1  # round UP; see module docstring
        minor = 0
    return f"macosx_{major}_{minor}_{arch}"


def derive_platform_tag(target, tcfg, binary):
    """Return (platform_tag, explanation) or raise DistError."""
    if tcfg["os"] == "macos":
        info = inspect_macho(binary)
        if info["arch"] != tcfg["wheel-arch"]:
            raise DistError(f"{target}: Mach-O arch {info['arch']} != configured {tcfg['wheel-arch']}")
        tag = macos_tag(info["arch"], info["minos"])
        return tag, f"Mach-O minos {info['minos'][0]}.{info['minos'][1]}"

    info = inspect_elf(binary)
    if info["arch"] != tcfg["wheel-arch"]:
        raise DistError(f"{target}: ELF machine {info['arch']} != configured {tcfg['wheel-arch']}")
    if info["other_versions"]:
        raise DistError(
            f"{target}: versioned dependencies beyond glibc {info['other_versions']}; the "
            f"manylinux/musllinux claim needs a check this script does not implement"
        )
    if tcfg["libc"] == "glibc":
        if not info["has_interp"]:
            raise DistError(f"{target}: configured glibc but the ELF has no PT_INTERP")
        if info["glibc_floor"] is None:
            raise DistError(f"{target}: no GLIBC_2.x versioned imports found; refusing to guess a floor")
        return (
            f"manylinux_2_{info['glibc_floor']}_{info['arch']}",
            f"max GLIBC_2.{info['glibc_floor']} in SHT_GNU_verneed",
        )
    if info["has_interp"] or info["glibc_floor"] is not None:
        raise DistError(f"{target}: configured musl but the ELF is dynamically linked / glibc-versioned (#432 regression)")
    return f"musllinux_1_2_{info['arch']}", "static ELF (no PT_INTERP, no versioned imports)"


# --------------------------------------------------------------------------
# Shared entry point: verify everything, return per-target material
# --------------------------------------------------------------------------


def host_can_run(tcfg):
    machine = platform.machine().lower()
    arch = {"arm64": "arm64", "aarch64": "aarch64", "x86_64": "x86_64", "amd64": "x86_64"}.get(machine)
    if tcfg["os"] == "macos":
        return platform.system() == "Darwin" and arch == tcfg["wheel-arch"]
    if platform.system() != "Linux" or arch != tcfg["wheel-arch"]:
        return False
    if tcfg["libc"] == "musl":
        return True  # static: runs on glibc and musl hosts alike
    return platform.libc_ver()[0] == "glibc"


def native_version_check(target, binary, version):
    with tempfile.TemporaryDirectory() as d:
        exe = pathlib.Path(d) / "meld"
        exe.write_bytes(binary)
        exe.chmod(0o755)
        proc = subprocess.run([str(exe), "--version"], capture_output=True, text=True, timeout=60)
    out = proc.stdout.strip()
    if proc.returncode != 0 or out != f"meld {version}":
        raise DistError(
            f"{target}: `meld --version` printed {out!r} (rc={proc.returncode}); expected "
            f"'meld {version}' for tag v{version}. stderr: {proc.stderr.strip()!r}"
        )
    return out


def load_verified_release(tag, assets, config, cargo_toml=None, cargo_required=False, no_cargo_check=False, log=print):
    """Verify checksums for EVERY target before returning anything."""
    version = version_from_tag(tag)
    assets = pathlib.Path(assets)
    sums_path = assets / "SHA256SUMS.txt"
    if not sums_path.is_file():
        raise DistError(f"{sums_path} not found")
    sums = parse_sums(sums_path.read_text())

    if not no_cargo_check:
        got = check_cargo_version(version, cargo_toml, cargo_required or cargo_toml is not None)
        log(f"workspace version: {got if got else 'Cargo.toml not found, check skipped'}")

    binary_name = config["dist"]["binary"]
    # Pass 1: checksums for all targets, before touching any content.
    names = {t: f"meld-{tag}-{t}.tar.gz" for t in config["targets"]}
    for t, name in names.items():
        digest = verify_tarball(assets, name, sums)
        log(f"sha256 ok  {name}  {digest}")

    # Pass 2: extract, inspect.
    results = []
    for t, tcfg in config["targets"].items():
        files = read_release_files(assets / names[t], tag, t, binary_name)
        plat_tag, why = derive_platform_tag(t, tcfg, files["binary"])
        ran = None
        if host_can_run(tcfg):
            ran = native_version_check(t, files["binary"], version)
            log(f"native run {t}: {ran}")
        results.append({"target": t, "cfg": tcfg, "platform_tag": plat_tag, "tag_reason": why, "native": ran, **files})
    return version, results


# --------------------------------------------------------------------------
# Wheel writer
# --------------------------------------------------------------------------


def _b64_sha(data):
    return base64.urlsafe_b64encode(hashlib.sha256(data).digest()).rstrip(b"=").decode()


def make_metadata(config, version, long_description):
    p = config["project"]
    lines = [
        "Metadata-Version: 2.4",
        f"Name: {p['name']}",
        f"Version: {version}",
        f"Summary: {p['description']}",
        f"Keywords: {','.join(p.get('keywords', []))}",
        f"Author: {p['authors'][0]['name']}",
        f"License-Expression: {p['license']}",
    ]
    lines += [f"License-File: {f}" for f in p["license-files"]]
    lines += [f"Classifier: {c}" for c in p.get("classifiers", [])]
    lines += [f"Project-URL: {k}, {v}" for k, v in p["urls"].items()]
    lines.append(f"Requires-Python: {p['requires-python']}")
    if long_description:
        lines.append("Description-Content-Type: text/markdown")
    return "\n".join(lines) + "\n\n" + (long_description or "")


def build_wheel(config, version, rec, out_dir):
    name = config["project"]["name"].replace("-", "_")
    dist_info = f"{name}-{version}.dist-info"
    data_dir = f"{name}-{version}.data"
    tag = f"py3-none-{rec['platform_tag']}"
    filename = f"{name}-{version}-{tag}.whl"

    wheel_meta = "\n".join(
        [
            "Wheel-Version: 1.0",
            "Generator: meld/python/build_wheels.py (repacked release binary)",
            "Root-Is-Purelib: false",
            f"Tag: {tag}",
            "",
        ]
    )
    binary_name = config["dist"]["binary"]
    files = [(f"{data_dir}/scripts/{binary_name}", rec["binary"], 0o755)]
    files.append((f"{dist_info}/METADATA", make_metadata(config, version, (rec.get("readme") or b"").decode()).encode(), 0o644))
    files.append((f"{dist_info}/WHEEL", wheel_meta.encode(), 0o644))
    if "license" not in rec:
        raise DistError(f"{rec['target']}: tarball has no LICENSE; the wheel declares License-File")
    files.append((f"{dist_info}/licenses/LICENSE", rec["license"], 0o644))

    record = [f"{n},sha256={_b64_sha(d)},{len(d)}" for n, d, _ in files]
    record.append(f"{dist_info}/RECORD,,")
    files.append((f"{dist_info}/RECORD", ("\n".join(record) + "\n").encode(), 0o644))

    out_dir.mkdir(parents=True, exist_ok=True)
    path = out_dir / filename
    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as z:
        for n, d, mode in files:
            zi = zipfile.ZipInfo(n, ZIP_DATE)
            zi.compress_type = zipfile.ZIP_DEFLATED
            zi.external_attr = (stat.S_IFREG | mode) << 16
            zi.create_system = 3
            z.writestr(zi, d)
    return path


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--tag", required=True, help="release tag, vX.Y.Z")
    ap.add_argument("--assets", required=True, help="dir with the downloaded release assets")
    ap.add_argument("--out", required=True, help="output dir for wheels + wheel-sha256.txt")
    ap.add_argument("--cargo-toml", help="Cargo.toml to compare against (default: the repo's, if present)")
    ap.add_argument("--no-cargo-check", action="store_true", help="skip the workspace-version check")
    args = ap.parse_args(argv)

    try:
        config = load_config()
        version, results = load_verified_release(
            args.tag, args.assets, config, pathlib.Path(args.cargo_toml) if args.cargo_toml else None,
            no_cargo_check=args.no_cargo_check,
        )
        out = pathlib.Path(args.out)
        built = [(build_wheel(config, version, r, out), r) for r in results]
    except DistError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    lines = []
    for path, rec in built:
        lines.append(f"{sha256_file(path)}  {path.name}")
        print(f"built {path.name}  [{rec['platform_tag']}: {rec['tag_reason']}]")
    (out / "wheel-sha256.txt").write_text("\n".join(sorted(lines, key=lambda s: s.split()[1])) + "\n")
    print(f"wrote {len(built)} wheels + wheel-sha256.txt to {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
