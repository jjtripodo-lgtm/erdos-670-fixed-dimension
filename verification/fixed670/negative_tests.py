#!/usr/bin/env python3
"""Mutation tests: each altered replay claim must be rejected."""

from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path

from verify_execution import ROOT, check_receipt


def main() -> None:
    original = json.loads((ROOT / "verification/fixed670/execution/RECEIPT.json").read_text())
    check_receipt(ROOT, original)
    cases = {
        "failed_status": lambda r: r.update(status="FAILED"),
        "source_hash": lambda r: r["source_identity_sha256"].update(
            {"lean-fixed670/replay.py": "0" * 64}),
        "missing_command": lambda r: r["commands"].pop(4),
        "changed_command": lambda r: r["commands"][0]["command"].append("--update"),
        "failed_exit": lambda r: r["commands"][2].update(exit_code=1),
        "changed_log": lambda r: r["commands"][3].update(log_sha256="0" * 64),
        "missing_olean": lambda r: r["produced_project_oleans"].pop(),
        "extra_olean": lambda r: r["produced_project_oleans"].append(".lake/build/lib/lean/Extra.olean"),
        "wrong_head": lambda r: r["dependency_checkouts_before"][0].update(
            checkout_head="0" * 40),
        "dirty_checkout": lambda r: r["dependency_checkouts_after"][1].update(
            git_status_porcelain=" M lakefile.toml"),
        "false_cache_authentication": lambda r: r["dependency_cache_before"].update(
            cache_provenance_authenticated=True),
    }
    for name, mutation in cases.items():
        receipt = deepcopy(original)
        mutation(receipt)
        try:
            check_receipt(ROOT, receipt)
        except (ValueError, KeyError, TypeError):
            continue
        raise SystemExit(f"FAIL: mutation accepted: {name}")
    print(f"PASS: baseline receipt accepted; {len(cases)} malformed or falsified claims rejected")


if __name__ == "__main__":
    main()
