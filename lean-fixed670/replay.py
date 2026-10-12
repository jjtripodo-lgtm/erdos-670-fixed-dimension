#!/usr/bin/env python3
"""Replay the exact 54-module closure from zero project .olean files."""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import time

from replay_contract import (command_plan, dependency_checkouts, expected_oleans,
                             load_manifest, source_identity)
from verify_sources import verify


def project_oleans(package: Path) -> list[str]:
    return sorted(p.relative_to(package).as_posix()
                  for p in (package / ".lake" / "build").rglob("*.olean"))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    package = Path(__file__).resolve().parent
    candidate = package.parent
    dest = args.output.resolve()
    if dest.exists():
        raise SystemExit(f"Output path already exists: {dest}")
    errors = verify(package)
    if errors:
        raise SystemExit("\n".join(errors))
    manifest = load_manifest(candidate)
    plan = command_plan(manifest)
    expected = expected_oleans(manifest)
    before = project_oleans(package)
    if before:
        raise SystemExit("Use a fresh checkout: local project .olean files already exist.")
    lock = json.loads((package / "lake-manifest.json").read_text())
    checkouts_before, cache_before = dependency_checkouts(package, lock)
    identity_before = source_identity(candidate)
    dest.mkdir(parents=True, exist_ok=False)
    receipt = {
        "schema_version": 2,
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "platform": platform.platform(),
        "scope": "fresh 54 project modules; upstream compiled imports may be reused",
        "module_count": len(expected),
        "clean_project_olean_count_before": 0,
        "source_commit": manifest["source_commit"],
        "source_identity_sha256": identity_before,
        "dependency_checkouts_before": checkouts_before,
        "dependency_cache_before": cache_before,
        "commands": [],
        "status": "RUNNING",
    }

    def save() -> None:
        (dest / "RECEIPT.json").write_text(json.dumps(receipt, indent=2) + "\n")

    def fail(message: str) -> None:
        receipt["status"] = "VALIDATION_FAILED"
        receipt["failure_reason"] = message
        save()
        raise SystemExit(message)

    save()
    env = dict(os.environ, LEAN_NUM_THREADS="2")
    for i, (label, command, log_name) in enumerate(plan):
        log = dest / log_name
        start = time.monotonic()
        with log.open("wb") as output:
            result = subprocess.run(command, cwd=package, stdout=output,
                                    stderr=subprocess.STDOUT, env=env)
        receipt["commands"].append({
            "label": label, "command": command, "exit_code": result.returncode,
            "seconds": round(time.monotonic() - start, 3),
            "log": log_name, "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
        })
        if result.returncode:
            receipt["status"] = "FAILED"
        save()
        print(f"{i + 1}/{len(plan)} {label}: exit {result.returncode}", flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)

    if [(r["label"], r["command"], r["log"]) for r in receipt["commands"]] != plan:
        fail("Executed command structure differs from exact plan")
    if any(r["exit_code"] != 0 for r in receipt["commands"]):
        fail("A replay command did not exit successfully")
    audit = (dest / plan[-1][2]).read_text()
    declarations = re.findall(r"^#print axioms\s+(\S+)",
                              (package / "AxiomAudit.lean").read_text(), re.M)
    printed = re.findall(r"^'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit, re.M)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if ("sorryAx" in audit or len(printed) != 6 or len(declarations) != 6 or
            [name for name, _ in printed] != declarations or
            any({x.strip() for x in row.split(",")} != allowed for _, row in printed)):
        fail("Unexpected axiom audit result")
    actual = project_oleans(package)
    receipt["produced_project_oleans"] = actual
    if actual != expected:
        fail("Produced project .olean paths differ from exact 54-module set")
    if verify(package):
        fail("Source, import graph, lock or frozen-file identity changed during replay")
    if source_identity(candidate) != identity_before:
        fail("Source or replay script hashes changed during replay")
    checkouts_after, cache_after = dependency_checkouts(package, lock)
    receipt["dependency_checkouts_after"] = checkouts_after
    receipt["dependency_cache_after"] = cache_after
    receipt["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    receipt["status"] = "PASS"
    save()


if __name__ == "__main__":
    main()
