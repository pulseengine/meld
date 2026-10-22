#!/usr/bin/env python3
"""Exit 0 only if <name>==<version> is absent from the PyPI-style index (#442).

    python3 -I python/check_registry_absent.py --index testpypi|pypi --version X.Y.Z

Registry uploads are immutable, so the publish jobs refuse a version that is
already there (no `skip-existing`): a partially-uploaded set must be a loud
stop for a human, not something a re-run papers over. Anything other than a
clean 404 (including network errors) is also a failure - fail closed.
"""

import argparse
import json
import sys
import urllib.error
import urllib.request

HOSTS = {"testpypi": "https://test.pypi.org", "pypi": "https://pypi.org"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--index", required=True, choices=sorted(HOSTS))
    ap.add_argument("--version", required=True)
    ap.add_argument("--name", default="meld-cli")
    args = ap.parse_args()

    url = f"{HOSTS[args.index]}/pypi/{args.name}/{args.version}/json"
    try:
        with urllib.request.urlopen(url, timeout=30) as resp:
            json.load(resp)
    except urllib.error.HTTPError as e:
        if e.code == 404:
            print(f"{args.name}=={args.version} is not on {args.index}")
            return 0
        print(f"error: {url} -> HTTP {e.code}; refusing to guess", file=sys.stderr)
        return 1
    except Exception as e:  # noqa: BLE001 - fail closed on anything
        print(f"error: could not query {url}: {e}", file=sys.stderr)
        return 1

    print(
        f"error: {args.name}=={args.version} already exists on {args.index}; "
        f"uploads are immutable and --skip-existing is deliberately not used",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
