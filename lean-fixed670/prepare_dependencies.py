#!/usr/bin/env python3
"""Check or fetch the nine public Git checkouts at exact locked commits."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from urllib.parse import urlparse

from replay_contract import dependency_checkouts


def run(*args: str) -> None:
    subprocess.run(args, check=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--fetch", action="store_true",
                    help="clone only missing public dependencies; never alter an existing checkout")
    args = ap.parse_args()
    package = Path(__file__).resolve().parent
    lock = json.loads((package / "lake-manifest.json").read_text())
    packages_dir = package / ".lake" / "packages"
    if args.fetch:
        packages_dir.mkdir(parents=True, exist_ok=True)
        for row in lock["packages"]:
            url = row["url"]
            parsed = urlparse(url)
            if parsed.scheme != "https" or parsed.hostname != "github.com" or not (
                    parsed.path.startswith("/leanprover/") or
                    parsed.path.startswith("/leanprover-community/")):
                raise ValueError(f"not an expected public Lean dependency URL: {url}")
            final = packages_dir / row["name"]
            if final.exists():
                continue
            temporary = Path(tempfile.mkdtemp(prefix=f".{row['name']}-", dir=packages_dir))
            try:
                checkout = temporary / "checkout"
                run("git", "clone", "--filter=blob:none", "--no-checkout", url, str(checkout))
                run("git", "-C", str(checkout), "fetch", "--depth=1", "origin", row["rev"])
                run("git", "-C", str(checkout), "checkout", "--detach", row["rev"])
                os.replace(checkout, final)
            finally:
                shutil.rmtree(temporary)
    checked, cache = dependency_checkouts(package, lock)
    print(f"PASS: {len(checked)} public dependency HEADs equal the lock; "
          f"all tracked and nonignored files are clean; "
          f"{cache['upstream_compiled_oleans_before']} cached upstream .olean files observed")
    print("Compiled upstream cache provenance is not authenticated by this check.")


if __name__ == "__main__":
    main()
