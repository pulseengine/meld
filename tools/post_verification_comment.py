#!/usr/bin/env python3
"""Post (or update) a sticky PR comment summarising LS-N verification results.

Reads the JSON written by `tools/run_ls_verification.py` and calls the
GitHub REST API directly to upsert a single marker-tagged comment on the
PR. Re-running on the same PR replaces the prior body rather than
appending another comment. Pure stdlib (urllib) — no `gh` CLI dependency.

Usage:
    tools/post_verification_comment.py <pr-number> [--results-json PATH] [--repo OWNER/NAME]

Required env:
    GH_TOKEN (or GITHUB_TOKEN) with `pull-requests: write`.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.error
import urllib.request
from pathlib import Path

MARKER = "<!-- meld-ls-verification-gate -->"
API = "https://api.github.com"


def github_request(
    method: str, path: str, token: str, body: dict | None = None
) -> tuple[int, bytes]:
    url = f"{API}{path}"
    data = json.dumps(body).encode("utf-8") if body is not None else None
    req = urllib.request.Request(
        url,
        data=data,
        method=method,
        headers={
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {token}",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "meld-ls-verification-gate",
            "Content-Type": "application/json" if data else "application/octet-stream",
        },
    )
    try:
        with urllib.request.urlopen(req) as resp:
            return resp.status, resp.read()
    except urllib.error.HTTPError as e:
        return e.code, e.read()


def render_body(results: dict) -> str:
    passed = results["passed_count"]
    failed = results["failed_count"]
    missing = results["missing_count"]
    total = results["total"]
    failed_ids = results["failed"]
    missing_ids = results["missing"]

    if failed == 0 and missing == 0:
        status = f"✅ **{passed}/{total}** approved LS entries verified"
    elif failed == 0:
        status = (
            f"⚠️ **{passed}/{total}** verified — **{missing}** missing regression tests"
        )
    else:
        status = (
            f"❌ **{passed}/{total}** verified — **{failed}** failed, "
            f"**{missing}** missing regression tests"
        )

    failed_section = (
        "\n".join(f"- `{i}`" for i in failed_ids) if failed_ids else "_(none)_"
    )
    missing_section = (
        "\n".join(f"- `{i}`" for i in missing_ids) if missing_ids else "_(none)_"
    )

    return f"""{MARKER}
## LS-N verification gate

{status}

| | count |
|---|---:|
| Passed (≥1 test, all green) | {passed} |
| Failed (≥1 test failure) | {failed} |
| Missing (no `ls_*_NN_*` test found) | {missing} |

<sub>Approved `loss-scenarios.yaml` entries are expected to have a
regression test named `ls_<letter>_<num>_*` (e.g. `LS-A-11` →
`ls_a_11_*`). The gate runs each prefix via `cargo test --lib
--no-fail-fast` and aggregates pass/fail/missing.</sub>

<details><summary>Failed LS entries</summary>

{failed_section}

</details>

<details><summary>Missing regression tests</summary>

{missing_section}

</details>

<sub>Updated automatically by `tools/post_verification_comment.py`.
Source of truth: `safety/stpa/loss-scenarios.yaml`.</sub>"""


def find_marker_comment(repo: str, pr: int, token: str) -> int | None:
    """Page through PR comments looking for the marker. Returns comment id or None."""
    page = 1
    while True:
        status, body = github_request(
            "GET",
            f"/repos/{repo}/issues/{pr}/comments?per_page=100&page={page}",
            token,
        )
        if status != 200:
            print(f"GET comments failed: {status} {body[:200]}", file=sys.stderr)
            return None
        comments = json.loads(body)
        if not comments:
            return None
        for c in comments:
            if MARKER in (c.get("body") or ""):
                return c["id"]
        if len(comments) < 100:
            return None
        page += 1


def upsert_comment(repo: str, pr: int, body: str, token: str) -> None:
    existing = find_marker_comment(repo, pr, token)
    if existing is not None:
        print(f"updating comment {existing}", file=sys.stderr)
        status, resp = github_request(
            "PATCH",
            f"/repos/{repo}/issues/comments/{existing}",
            token,
            {"body": body},
        )
    else:
        print("creating new comment", file=sys.stderr)
        status, resp = github_request(
            "POST",
            f"/repos/{repo}/issues/{pr}/comments",
            token,
            {"body": body},
        )
    if status not in (200, 201):
        print(f"comment upsert failed: {status} {resp[:300]}", file=sys.stderr)
        sys.exit(2)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pr", type=int, help="pull-request number")
    parser.add_argument(
        "--results-json",
        default="verification-results.json",
        type=Path,
        help="path to the JSON summary (default: %(default)s)",
    )
    parser.add_argument(
        "--repo",
        default=os.environ.get("GH_REPO", "pulseengine/meld"),
        help="OWNER/NAME (default: %(default)s)",
    )
    args = parser.parse_args()

    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if not token:
        print("GH_TOKEN or GITHUB_TOKEN required", file=sys.stderr)
        return 2

    if not args.results_json.is_file():
        print(f"no {args.results_json} found; nothing to post", file=sys.stderr)
        return 0

    results = json.loads(args.results_json.read_text())
    body = render_body(results)
    upsert_comment(args.repo, args.pr, body, token)
    return 0


if __name__ == "__main__":
    sys.exit(main())
