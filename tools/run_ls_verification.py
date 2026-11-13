#!/usr/bin/env python3
"""Verify every approved LS-N entry in `safety/stpa/loss-scenarios.yaml`
has a passing regression test.

Each approved loss scenario must have at least one `#[test] fn
ls_<letter>_<num>_*` in `meld-core` (e.g. `LS-A-11` → `ls_a_11_*`).
This script:

1. Reads the project's loss scenarios via `rivet list --format json`
   (rivet on PATH, or $RIVET) and keeps those with `status: approved`.
2. For each ID, derives the test-name prefix (`LS-A-11` → `ls_a_11_`)
   and runs `cargo test --lib --no-fail-fast <prefix>`.
3. Buckets the result as `passed` (≥1 test, all green), `failed` (any
   test failed), or `missing` (no test matched the prefix).
4. Writes a structured JSON summary alongside human-readable stdout.

Usage:
    tools/run_ls_verification.py [--results-json PATH]
                                  [--scenarios-yaml PATH]
                                  [--package NAME]

Defaults:
    --results-json    verification-results.json
    --scenarios-yaml  safety/stpa/loss-scenarios.yaml
    --package         meld-core

Checked statuses: approved, implemented, verified. A scenario promoted past
`approved` still claims a regression test, so promotion must not drop it
from the gate (#608).

Missing tests are blocking unless listed in the exact ledger
`safety/stpa/ls-missing-tests.txt` (one ID per line, `#` comments). A new
gap fails; a gap that closed while its line remains also fails, so the
ledger stays exact and a later regression is not pre-approved.

Exit code (#608: the gate fails closed):
    0  every checked LS-N has a passing test, or is a ledgered gap
    1  a test failed, a test is missing and not ledgered, the ledger is
       stale, cargo failed without a failing test (e.g. a compile error),
       or no scenario was checked at all
    2  usage / environment error (rivet unavailable, inputs not found)
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path

# #608: every status that claims a regression test exists.
CHECKED_STATUSES = ("approved", "implemented", "verified")

DEFAULT_LEDGER = Path("safety/stpa/ls-missing-tests.txt")


@dataclass
class Result:
    total: int = 0
    passed_count: int = 0
    failed_count: int = 0
    missing_count: int = 0
    passed: list[str] = field(default_factory=list)
    failed: list[str] = field(default_factory=list)
    missing: list[str] = field(default_factory=list)
    errored: list[str] = field(default_factory=list)
    unledgered_missing: list[str] = field(default_factory=list)
    stale_ledger: list[str] = field(default_factory=list)


def id_to_test_prefix(ls_id: str) -> str:
    """`LS-A-11` -> `ls_a_11_`. Tail underscore matches Cargo's prefix filter."""
    return ls_id.lower().replace("-", "_") + "_"


def load_approved_ids(yaml_path: Path) -> list[str]:
    """Approved loss-scenario IDs, read through `rivet list --format json`.

    meld#500 (org policy: read your own inputs through rivet). Needs `rivet`
    >= 0.40 on PATH, or set $RIVET. rivet loads the project's sources from the
    repo root (cwd); `yaml_path` is only the file the caller checked exists, it
    is no longer parsed here. Order is rivet's (sorted by id), not file order.
    """
    rivet = os.environ.get("RIVET", "rivet")
    try:
        proc = subprocess.run(
            [rivet, "list", "--type", "loss-scenario", "--format", "json"],
            capture_output=True, text=True, check=True,
        )
    except (OSError, subprocess.CalledProcessError) as e:
        detail = getattr(e, "stderr", "") or e
        print(f"`{rivet} list --format json` failed: {detail}", file=sys.stderr)
        sys.exit(2)
    return [a["id"] for a in json.loads(proc.stdout)["artifacts"]
            if a.get("type") == "loss-scenario" and a.get("status") in CHECKED_STATUSES]


_TEST_LINE = re.compile(r"^test result: (?P<verdict>ok|FAILED)\. "
                        r"(?P<passed>\d+) passed; (?P<failed>\d+) failed; "
                        r"(?P<ignored>\d+) ignored;")


def run_prefix(package: str, prefix: str) -> tuple[int, int, int, int]:
    """Return (matched, passed, failed, returncode) for `cargo test <prefix>`.

    `matched` = total selected tests (passed + failed + ignored). When
    cargo finds no matching tests, it reports `0 passed; 0 failed; 0
    ignored` and still exits 0; the caller treats matched=0 as missing.

    Drops the `--lib` filter so integration tests under
    `<package>/tests/` are also scanned. Several LS-N scenarios pin
    their regression coverage in integration tests (e.g. LS-CP-4 in
    `dwarf_strip.rs`); excluding them caused the gate to misreport
    those entries as missing.
    """
    cmd = [
        "cargo",
        "test",
        "-p",
        package,
        "--no-fail-fast",
        "--",
        "--test-threads=1",
        prefix,
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    passed = failed = ignored = 0
    # cargo emits one `test result:` line per target (lib + each
    # integration test binary), so we sum across all of them. A
    # prefix that matches in *any* target counts as "matched".
    for line in proc.stdout.splitlines():
        m = _TEST_LINE.match(line)
        if m:
            passed += int(m["passed"])
            failed += int(m["failed"])
            ignored += int(m["ignored"])
    return passed + failed + ignored, passed, failed, proc.returncode


def read_ledger(path: Path) -> set[str]:
    if not path.is_file():
        return set()
    return {
        line.split("#", 1)[0].strip()
        for line in path.read_text().splitlines()
        if line.split("#", 1)[0].strip()
    }


def judge(result: Result, ledger: set[str]) -> int:
    """The gate's verdict (#608). Pure, so the self-test can exercise it."""
    result.unledgered_missing = sorted(set(result.missing) - ledger)
    # An entry whose cargo run errored proved nothing either way; it is not
    # evidence that a ledgered gap closed.
    result.stale_ledger = sorted(ledger - set(result.missing) - set(result.errored))
    if result.total == 0:
        return 1
    if result.failed or result.errored or result.unledgered_missing or result.stale_ledger:
        return 1
    return 0


def self_test() -> None:
    def r(**kw):
        x = Result()
        for k, v in kw.items():
            setattr(x, k, v)
        x.total = x.total or len(x.passed) + len(x.failed) + len(x.missing) + len(x.errored)
        return x
    assert judge(r(passed=["LS-A-1"]), set()) == 0
    assert judge(Result(), set()) == 1, "zero scenarios checked must fail"
    assert judge(r(passed=["LS-A-1"], failed=["LS-A-2"]), set()) == 1
    assert judge(r(passed=["LS-A-1"], errored=["LS-A-2"]), set()) == 1, "cargo error must fail"
    assert judge(r(missing=["LS-A-2"], passed=["LS-A-1"]), set()) == 1, "new gap must fail"
    assert judge(r(missing=["LS-A-2"], passed=["LS-A-1"]), {"LS-A-2"}) == 0, "ledgered gap passes"
    assert judge(r(passed=["LS-A-1", "LS-A-2"]), {"LS-A-2"}) == 1, "stale ledger must fail"
    x = r(errored=["LS-A-2"], passed=["LS-A-1"])
    assert judge(x, {"LS-A-2"}) == 1 and x.stale_ledger == [], "an error is not a closed gap"
    print("run_ls_verification self-test: ok")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--results-json",
        default="verification-results.json",
        type=Path,
        help="path for the JSON summary (default: %(default)s)",
    )
    parser.add_argument(
        "--scenarios-yaml",
        default="safety/stpa/loss-scenarios.yaml",
        type=Path,
        help="path to loss-scenarios.yaml (default: %(default)s)",
    )
    parser.add_argument(
        "--missing-ledger",
        default=DEFAULT_LEDGER,
        type=Path,
        help="exact ledger of LS IDs known to lack a test (default: %(default)s)",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="check the gate's verdict logic and exit",
    )
    parser.add_argument(
        "--package",
        default="meld-core",
        help="cargo package to run tests against (default: %(default)s)",
    )
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0

    result = Result()

    print("== meld LS-N verification gate ==")
    print(f"scenarios: {args.scenarios_yaml}")
    print(f"package:   {args.package}")
    print()

    if not args.scenarios_yaml.is_file():
        print(f"{args.scenarios_yaml} not found", file=sys.stderr)
        return 2

    ids = load_approved_ids(args.scenarios_yaml)
    if not ids:
        # #608: an empty set means the gate checked nothing, not that all is well.
        print("::error::no loss scenarios with status in "
              f"{CHECKED_STATUSES} were found; the gate would be vacuous",
              file=sys.stderr)
        args.results_json.write_text(json.dumps(asdict(result), indent=2))
        return 1

    print(f"checked LS entries ({', '.join(CHECKED_STATUSES)}): {len(ids)}")
    print()
    result.total = len(ids)

    for ls_id in ids:
        prefix = id_to_test_prefix(ls_id)
        matched, passed, failed, rc = run_prefix(args.package, prefix)
        if rc != 0 and failed == 0:
            # #608: cargo failed without a failing test: a build error, a
            # crashed harness. Before, this read as "missing", i.e. a pass.
            print(f"[ERR ] {ls_id} (cargo exited {rc} with no failing test)")
            result.errored.append(ls_id)
        elif matched == 0:
            print(f"[MISS] {ls_id} (no `{prefix}*` test found)")
            result.missing.append(ls_id)
        elif failed > 0:
            print(f"[FAIL] {ls_id} ({passed} pass, {failed} fail)")
            result.failed.append(ls_id)
        else:
            print(f"[ OK ] {ls_id} ({passed} pass)")
            result.passed.append(ls_id)

    result.passed_count = len(result.passed)
    result.failed_count = len(result.failed)
    result.missing_count = len(result.missing)

    args.results_json.write_text(json.dumps(asdict(result), indent=2))

    print()
    print("== summary ==")
    print(f"passed:  {result.passed_count}")
    print(f"failed:  {result.failed_count}")
    print(f"missing: {result.missing_count}")
    if result.failed:
        print("failed IDs:")
        for fid in result.failed:
            print(f"  - {fid}")
    if result.missing:
        print("missing IDs:")
        for mid in result.missing:
            print(f"  - {mid}")

    ledger = read_ledger(args.missing_ledger)
    verdict = judge(result, ledger)
    args.results_json.write_text(json.dumps(asdict(result), indent=2))
    if result.errored:
        print(f"::error::cargo failed for {len(result.errored)} entries without a failing test")
    if result.unledgered_missing:
        print("::error::missing regression tests not in "
              f"{args.missing_ledger}: {', '.join(result.unledgered_missing)}")
    if result.stale_ledger:
        print(f"::error::{args.missing_ledger} lists entries that now have a test: "
              f"{', '.join(result.stale_ledger)}; delete those lines")
    return verdict


if __name__ == "__main__":
    sys.exit(main())
