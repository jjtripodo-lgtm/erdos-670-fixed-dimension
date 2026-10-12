#!/usr/bin/env python3
"""Read-only SHA-256 verification of this exact private candidate tree."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
MANIFEST = "CANDIDATE_SHA256.json"
GENERATED_DIRS = {".git", ".lake", "__pycache__", "build-a", "build-b", "render", "replay-output"}


def inventory() -> dict[str, dict[str, int | str]]:
    result: dict[str, dict[str, int | str]] = {}
    for directory, dirs, files in os.walk(ROOT):
        for dirname in dirs:
            child = Path(directory) / dirname
            if child.is_symlink() and dirname not in GENERATED_DIRS:
                raise ValueError(f"symlink in candidate tree: {child.relative_to(ROOT)}")
        dirs[:] = sorted(name for name in dirs if name not in GENERATED_DIRS)
        for filename in sorted(files):
            path = Path(directory) / filename
            if path.is_symlink():
                raise ValueError(f"symlink in candidate tree: {path.relative_to(ROOT)}")
            name = path.relative_to(ROOT).as_posix()
            if name == MANIFEST:
                continue
            data = path.read_bytes()
            result[name] = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
    return result


def main() -> int:
    manifest = json.loads((ROOT / MANIFEST).read_text(encoding="utf-8"))
    if manifest.get("schema_version") != 1:
        raise ValueError("unsupported candidate manifest schema")
    expected = manifest["files"]
    actual = inventory()
    missing = sorted(set(expected) - set(actual))
    extra = sorted(set(actual) - set(expected))
    mismatched = sorted(name for name in set(actual) & set(expected)
                        if actual[name] != expected[name])
    if missing or extra or mismatched:
        print(json.dumps({"missing": missing, "extra": extra,
                          "mismatched": mismatched}, indent=2), file=sys.stderr)
        return 1
    print(f"PASS: {len(actual)} exact candidate files match SHA-256 and byte counts")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
