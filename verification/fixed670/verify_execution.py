#!/usr/bin/env python3
"""Read-only validation of the revised exact replay receipt and logs."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean-fixed670"))
from replay_contract import command_plan, expected_oleans, load_manifest, source_identity  # noqa: E402
from verify_sources import verify as verify_sources  # noqa: E402


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def validate_checkouts(rows: list[dict], lock: dict, label: str) -> None:
    expected = lock["packages"]
    require(len(rows) == len(expected) == 9, f"{label}: dependency count")
    for row, pinned in zip(rows, expected):
        name = pinned["name"]
        require(row["name"] == name, f"{label}: dependency order/name: {name}")
        require(row["locked_rev"] == pinned["rev"] == row["checkout_head"],
                f"{label}: checkout HEAD differs from lock: {name}")
        require(row["git_status_porcelain"] == "", f"{label}: dirty checkout: {name}")
        require(row["path"] == f".lake/packages/{name}", f"{label}: checkout path: {name}")
        require(type(row["cached_olean_count_before"]) is int and
                row["cached_olean_count_before"] >= 0,
                f"{label}: invalid cached output count: {name}")


def validate_cache(cache: dict, rows: list[dict], label: str) -> None:
    require(type(cache["packages_root_is_symlink"]) is bool,
            f"{label}: packages root symlink marker")
    require(cache["upstream_compiled_oleans_before"] ==
            sum(row["cached_olean_count_before"] for row in rows),
            f"{label}: upstream cached output count")
    require(cache["cache_provenance_authenticated"] is False,
            f"{label}: unsupported compiled-cache authentication claim")


def check_receipt(root: Path = ROOT, receipt: dict | None = None) -> None:
    evidence = root / "verification/fixed670"
    package = root / "lean-fixed670"
    manifest = load_manifest(root)
    lock = json.loads((package / "lake-manifest.json").read_text())
    if receipt is None:
        receipt = json.loads((evidence / "execution/RECEIPT.json").read_text())
    source_errors = verify_sources(package)
    require(not source_errors, "source identity: " + "; ".join(source_errors))
    require(receipt["schema_version"] == 2, "receipt schema version")
    require(receipt["status"] == "PASS", "replay did not pass")
    require(receipt["source_commit"] == manifest["source_commit"], "source commit")
    require(receipt["source_identity_sha256"] == source_identity(root),
            "source/script/lock SHA-256 identity")
    plan = command_plan(manifest)
    require(receipt["module_count"] == len(expected_oleans(manifest)) == 54,
            "module count")
    require(receipt["clean_project_olean_count_before"] == 0,
            "project .olean count before replay")
    require(receipt["produced_project_oleans"] == expected_oleans(manifest),
            "exact produced project .olean path set")
    commands = receipt["commands"]
    require(len(commands) == len(plan) == 56, "exact command count")
    for i, (row, (label, command, log_name)) in enumerate(zip(commands, plan)):
        require((row["label"], row["command"], row["log"]) ==
                (label, command, log_name), f"exact command structure at {i}")
        require(row["exit_code"] == 0, f"nonzero exit at {i}")
        log = evidence / "execution" / log_name
        require(log.is_file(), f"missing log at {i}")
        require(hashlib.sha256(log.read_bytes()).hexdigest() == row["log_sha256"],
                f"log SHA-256 at {i}")
    declarations = re.findall(r"^#print axioms\s+(\S+)",
                              (package / "AxiomAudit.lean").read_text(), re.M)
    audit = (evidence / "execution" / plan[-1][2]).read_text()
    printed = re.findall(r"^'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit, re.M)
    require(len(declarations) == len(printed) == 6 and
            [name for name, _ in printed] == declarations,
            "exact audited declarations")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    require(all({x.strip() for x in axioms.split(",")} == allowed
                for _, axioms in printed) and "sorryAx" not in audit,
            "unexpected axiom dependencies")
    before = receipt["dependency_checkouts_before"]
    after = receipt["dependency_checkouts_after"]
    validate_checkouts(before, lock, "before")
    validate_checkouts(after, lock, "after")
    validate_cache(receipt["dependency_cache_before"], before, "before")
    validate_cache(receipt["dependency_cache_after"], after, "after")
    require([(r["name"], r["checkout_head"]) for r in before] ==
            [(r["name"], r["checkout_head"]) for r in after],
            "dependency HEAD changed during replay")


def main() -> None:
    try:
        check_receipt()
    except (ValueError, KeyError, TypeError) as error:
        raise SystemExit(f"FAIL: {error}") from error
    print("PASS: exact source/script hashes, nine locked clean checkout HEADs, "
          "54 project .oleans, 56 exact zero-exit commands/logs, six trust-zero axioms")


if __name__ == "__main__":
    main()
