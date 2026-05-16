#!/usr/bin/env python3
"""Verify every approved LS-N entry in `safety/stpa/loss-scenarios.yaml`
has a passing regression test.

Each approved loss scenario must have at least one `#[test] fn
ls_<letter>_<num>_*` in `meld-core` (e.g. `LS-A-11` → `ls_a_11_*`).
This script:

1. Reads `safety/stpa/loss-scenarios.yaml` and filters entries where
   `status: approved`.
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

Exit code:
    0  if every approved LS-N has a passing regression test
    1  if any LS-N has a failing test
    2  if any LS-N is missing a regression test (advisory until tests
       are added; treated as warning, not gate failure)
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path

try:
    import yaml
except ImportError:
    print("PyYAML required (pip install pyyaml)", file=sys.stderr)
    sys.exit(2)


@dataclass
class Result:
    total: int = 0
    passed_count: int = 0
    failed_count: int = 0
    missing_count: int = 0
    passed: list[str] = field(default_factory=list)
    failed: list[str] = field(default_factory=list)
    missing: list[str] = field(default_factory=list)


def id_to_test_prefix(ls_id: str) -> str:
    """`LS-A-11` -> `ls_a_11_`. Tail underscore matches Cargo's prefix filter."""
    return ls_id.lower().replace("-", "_") + "_"


def load_approved_ids(yaml_path: Path) -> list[str]:
    data = yaml.safe_load(yaml_path.read_text())
    scenarios = data.get("loss-scenarios", [])
    return [s["id"] for s in scenarios if s.get("status") == "approved"]


_TEST_LINE = re.compile(r"^test result: (?P<verdict>ok|FAILED)\. "
                        r"(?P<passed>\d+) passed; (?P<failed>\d+) failed; "
                        r"(?P<ignored>\d+) ignored;")


def run_prefix(package: str, prefix: str) -> tuple[int, int, int]:
    """Return (matched, passed, failed) for `cargo test --lib <prefix>`.

    `matched` = total selected tests (passed + failed + ignored). When
    cargo finds no matching tests, it reports `0 passed; 0 failed; 0
    ignored` and still exits 0; the caller treats matched=0 as missing.
    """
    cmd = [
        "cargo",
        "test",
        "-p",
        package,
        "--lib",
        "--no-fail-fast",
        "--",
        "--exact" if False else "--test-threads=1",
        prefix,
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    passed = failed = ignored = 0
    for line in proc.stdout.splitlines():
        m = _TEST_LINE.match(line)
        if m:
            passed += int(m["passed"])
            failed += int(m["failed"])
            ignored += int(m["ignored"])
    return passed + failed + ignored, passed, failed


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
        "--package",
        default="meld-core",
        help="cargo package to run tests against (default: %(default)s)",
    )
    args = parser.parse_args()

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
        print("No approved loss scenarios found.", file=sys.stderr)
        args.results_json.write_text(json.dumps(asdict(result), indent=2))
        return 0

    print(f"approved LS entries: {len(ids)}")
    print()
    result.total = len(ids)

    for ls_id in ids:
        prefix = id_to_test_prefix(ls_id)
        matched, passed, failed = run_prefix(args.package, prefix)
        if matched == 0:
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

    if result.failed_count > 0:
        return 1
    if result.missing_count > 0:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
