"""Exact source, command, output and dependency contract for the #670 replay."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_order(manifest: dict) -> list[str]:
    rows = manifest["modules"]
    modules = [row["module"] for row in rows]
    if len(modules) != manifest["module_count"] or len(set(modules)) != len(modules):
        raise ValueError("module count or uniqueness differs")
    if len(modules) != 54:
        raise ValueError("this candidate's exact closure must have 54 modules")
    positions = {module: i for i, module in enumerate(modules)}
    for i, row in enumerate(rows):
        for dep in row["imports"]:
            if dep.startswith("Erdos488.") and positions.get(dep, i) >= i:
                raise ValueError(f"module order is not topological: {dep} before {row['module']}")
    if modules[-1] != manifest["root_module"]:
        raise ValueError("final source module is not last")
    return modules


def command_plan(manifest: dict) -> list[tuple[str, list[str], str]]:
    modules = module_order(manifest)
    rows = [(m, ["lake", "--no-cache", "build", m]) for m in modules]
    rows += [
        ("final_default_build", ["lake", "--no-cache", "build"]),
        ("final_axiom_audit", ["lake", "env", "lean", "--trust=0", "AxiomAudit.lean"]),
    ]
    return [(label, cmd, f"{i:02d}_{label.split('.')[-1]}.log")
            for i, (label, cmd) in enumerate(rows)]


def expected_oleans(manifest: dict) -> list[str]:
    return sorted(".lake/build/lib/lean/" + m.replace(".", "/") + ".olean"
                  for m in module_order(manifest))


SOURCE_IDENTITY_PATHS = [
    "lean-fixed670/AxiomAudit.lean",
    "lean-fixed670/lake-manifest.json",
    "lean-fixed670/lakefile.toml",
    "lean-fixed670/lean-toolchain",
    "lean-fixed670/prepare_dependencies.py",
    "lean-fixed670/replay.py",
    "lean-fixed670/replay_contract.py",
    "lean-fixed670/verify_sources.py",
    "verification/fixed670/FROZEN_FILES_SHA256.json",
    "verification/fixed670/SOURCE_MANIFEST.json",
    "verification/fixed670/upstream-lake-manifest.json",
    "verification/fixed670/upstream-lean-toolchain",
    "verification/fixed670/verify_execution.py",
]


def source_identity(candidate_root: Path) -> dict[str, str]:
    return {name: sha256(candidate_root / name) for name in SOURCE_IDENTITY_PATHS}


def dependency_checkouts(package: Path, lock: dict) -> tuple[list[dict], dict]:
    packages_dir = package / ".lake" / "packages"
    expected = lock["packages"]
    if len(expected) != 9 or len({row["name"] for row in expected}) != 9:
        raise ValueError("expected exactly nine distinct locked public dependencies")
    checked = []
    for row in expected:
        name = row["name"]
        checkout = packages_dir / name
        if not checkout.is_dir():
            raise ValueError(f"missing locked checkout: {name}; see README setup")
        head = subprocess.run(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                              check=True, capture_output=True, text=True).stdout.strip()
        status = subprocess.run(["git", "-C", str(checkout), "status", "--porcelain",
                                 "--untracked-files=all"], check=True,
                                capture_output=True, text=True).stdout
        if head != row["rev"]:
            raise ValueError(f"locked checkout HEAD mismatch: {name}")
        if status:
            raise ValueError(f"locked checkout has tracked or nonignored untracked changes: {name}")
        cached = sum(1 for _ in (checkout / ".lake" / "build").rglob("*.olean"))
        checked.append({"name": name, "locked_rev": row["rev"],
                        "checkout_head": head, "git_status_porcelain": "",
                        "cached_olean_count_before": cached,
                        "path": f".lake/packages/{name}"})
    return checked, {
        "packages_root_is_symlink": packages_dir.is_symlink(),
        "upstream_compiled_oleans_before": sum(r["cached_olean_count_before"] for r in checked),
        "cache_provenance_authenticated": False,
        "scope": "Git HEAD and nonignored dirty-state checked; compiled-cache provenance not authenticated",
    }


def load_manifest(candidate_root: Path) -> dict:
    return json.loads((candidate_root / "verification/fixed670/SOURCE_MANIFEST.json").read_text())
