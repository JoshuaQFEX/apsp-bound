#!/usr/bin/env python3
"""Prepare a portable verification subproject inside the pinned upstream clone.

Author: Joshua Wharton, QFEX, joshua@qfex.com.
This prepares source files only; it does not claim to run the Lean checks.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import runpy
import subprocess

HERE = Path(__file__).resolve().parent
UPSTREAM = "225c37476e31bdb27594953cc1f7738496fb4afc"
PINS = {
    "ThreeSumApsp": "e1a4e6508154ea59f030480661590a9fe3018011",
    "mathlib": "0df444a360eaa60ab8c11dca51a86af692955474",
}
BASE_SOURCES = {
    "LowRowMachine.lean": "b245ce32186f551eedd12e0ab2d3a95002faa82826bfea5284fce6d5ad5518fa",
    "LowRowSemantics.lean": "e0913d2c4df268e376f11c1585b6aa90e24d6b186a399aa1c2b052f93943ac56",
}

def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)

def install(source: Path, destination: Path) -> None:
    data = source.read_bytes()
    require(not destination.exists() or destination.read_bytes() == data,
            f"Refusing to overwrite different existing source: {destination}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(data)

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="Git checkout of thin-matrix-results at the exact pin")
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    commit = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    require(commit == UPSTREAM, f"Expected upstream commit {UPSTREAM}; found {commit}")
    runpy.run_path(str(HERE / "verify_upstream_integrity.py"))
    integrity = json.loads((HERE / "integrity_manifest.json").read_text())
    for record in integrity["files"]:
        name = record["name"]
        require((checkout / "lean" / name).read_bytes() ==
                (HERE / "pinned_upstream" / name).read_bytes(),
                f"Pinned upstream source differs: {name}")
    for name, expected in BASE_SOURCES.items():
        data = (HERE.parent / name).read_bytes()
        require(hashlib.sha256(data).hexdigest() == expected,
                f"The checked base source differs: {name}")
    machine = checkout / "machine"
    manifest = json.loads((machine / "lake-manifest.json").read_text())
    actual = {entry["name"]: entry.get("rev") for entry in manifest["packages"]}
    for name, expected in PINS.items():
        require(actual.get(name) == expected, f"Unexpected pinned dependency: {name}")
    require((machine / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1",
            "Unexpected upstream Lean toolchain")

    project = machine / "apsp-low-row-refinement"
    project.mkdir(exist_ok=True)
    for source in sorted((HERE / "project").iterdir()):
        if source.is_file():
            install(source, project / source.name)
    install(machine / "lake-manifest.json", project / "lake-manifest.json")
    install(machine / "lake-manifest.json", project / "pinned-lake-manifest.json")
    for name in BASE_SOURCES:
        install(HERE.parent / name, project / name)
    for source in sorted((HERE / "upstream").glob("*.lean")):
        install(source, project / source.name)
    for name in ("LowRowRefinement.lean", "LowRowRefinementAudit.lean"):
        install(HERE / name, project / name)

    # Reuse an existing pinned package cache without touching the upstream
    # project's sources or build outputs. A fresh clone can fetch its own.
    cached_packages = machine / ".lake" / "packages"
    local_packages = project / ".lake" / "packages"
    if cached_packages.is_dir() and not local_packages.exists():
        local_packages.parent.mkdir(exist_ok=True)
        local_packages.symlink_to(cached_packages, target_is_directory=True)
    print(f"Prepared source project: {project}")
    print("Next: enter that directory, run `lake update`, then `bash build_refinement.sh`.")

if __name__ == "__main__":
    main()
