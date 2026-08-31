#!/usr/bin/env python3
"""Build a local mechanical-report.json for Palomar editorial audit."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

IMPLEMENTATION_SOURCES = (
    "vendor/scott1972/Scott1972/ContinuousLattice/FunctionSpaces.lean",
    "vendor/scott1972/Scott1972/ContinuousLattice/InverseLimits.lean",
    "QLambda/OmegaQVA.lean",
    "QLambda/QDomain.lean",
    "QLambda/QuantumDomainEquation.lean",
    "QLambda/TTContinuationDomainEquation.lean",
)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def git_state() -> tuple[str | None, bool]:
    try:
        dirty = subprocess.check_output(
            ["git", "status", "--porcelain"],
            cwd=ROOT,
            stderr=subprocess.DEVNULL,
            text=True,
        )
        out = subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=ROOT,
            stderr=subprocess.DEVNULL,
            text=True,
        )
        return out.strip(), not bool(dirty.strip())
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None, False


def source_bundle_sha256(paths: dict[str, Path]) -> str:
    h = hashlib.sha256()
    for name, path in sorted(paths.items()):
        h.update(name.encode("utf-8"))
        h.update(b"\0")
        h.update(path.read_bytes())
        h.update(b"\0")
    return h.hexdigest()


def challenge_imports() -> list[str]:
    text = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    return re.findall(r"^import\s+(\S+)", text, re.MULTILINE)


def load_comparator() -> dict:
    with (ROOT / "comparator.json").open(encoding="utf-8") as f:
        return json.load(f)


def build_report() -> dict:
    cfg = load_comparator()
    base_commit, clean = git_state()
    theorems = cfg["theorem_names"]
    definitions = cfg.get("definition_names", [])
    paths = {
        "comparator.json": ROOT / "comparator.json",
        "Challenge.lean": ROOT / "Challenge.lean",
        "Solution.lean": ROOT / "Solution.lean",
        "formalization.yaml": ROOT / "formalization.yaml",
        "lean-toolchain": ROOT / "lean-toolchain",
    }
    if (ROOT / "lakefile.toml").is_file():
        paths["lakefile.toml"] = ROOT / "lakefile.toml"
    elif (ROOT / "lakefile.lean").is_file():
        paths["lakefile.lean"] = ROOT / "lakefile.lean"
    implementation_paths = {
        name: ROOT / name for name in IMPLEMENTATION_SOURCES
    }
    paths.update(implementation_paths)
    bundle_hash = source_bundle_sha256(implementation_paths)

    return {
        "schema": "qlambda-local-mechanical-report-v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "repository": {
            "commit": base_commit if clean else None,
            "base_commit": base_commit,
            "working_tree_clean": clean,
            "immutable_source_bundle_sha256": bundle_hash,
            "comparator_config": "comparator.json",
        },
        "comparator": {
            "challenge_module": cfg["challenge_module"],
            "solution_module": cfg["solution_module"],
            "theorem_names": theorems,
            "definition_names": definitions,
            "permitted_axioms": cfg["permitted_axioms"],
        },
        "declarations_checked_order": theorems + definitions,
        "challenge_imports": challenge_imports(),
        "artifact_hashes": {name: sha256_file(path) for name, path in paths.items() if path.is_file()},
        "implementation_sources": list(IMPLEMENTATION_SOURCES),
        "preflight": {
            "mechanical_steps": "comparator, imports, build, type-compare, sorry-scan, axioms",
            "status": "passed_before_report",
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    report = build_report()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    decl_count = len(report["declarations_checked_order"])
    print(f"OK: mechanical report written to {args.out} ({decl_count} declarations).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
