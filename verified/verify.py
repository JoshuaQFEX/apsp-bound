#!/usr/bin/env python3
"""Build and check the exact APSP challenge theorem and its transitive axioms.

Joshua Wharton <joshua@qfex.com>, QFEX.
The inherited program, compiler, and proof retain their original notices.
"""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent
END_STATEMENT_SHA256 = "4291e3f05781cea42f9d672ff73ceac1f6d1a0c3021038e94372fa8f7e1ad987"
PRIOR_VERIFIED_BOUND = Fraction("2.99556085")


def run(args: list[str], *, capture: bool = False) -> str:
    result = subprocess.run(
        args, cwd=ROOT, check=True, text=True,
        stdout=subprocess.PIPE if capture else None,
    )
    return result.stdout if capture else ""


def source_snapshot() -> dict[str, str]:
    files = list((ROOT / "Submission").rglob("*.lean"))
    files += [ROOT / name for name in (
        "Submission.lean", "manifest.json", "lean-toolchain",
        "lakefile.toml", "lake-manifest.json", "verify.py", "scripts/build_sequential.py",
        "scripts/build_cached_groups.py",
    )]
    return {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(files)
    }


def check_dependency_sources() -> None:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = ROOT / manifest["packagesDir"]
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise SystemExit(f"Unexpected dependency kind: {package['name']}")
        directory = packages / package["name"]
        actual = run(["git", "-C", str(directory), "rev-parse", "HEAD"], capture=True).strip()
        if actual != package["rev"]:
            raise SystemExit(f"Dependency revision differs from pin: {package['name']}")
        dirty = run([
            "git", "-C", str(directory), "status", "--porcelain", "--untracked-files=normal",
        ], capture=True).strip()
        if dirty:
            raise SystemExit(f"Dependency source checkout is modified: {package['name']}")


def main() -> None:
    lake = shutil.which("lake")
    if lake is None:
        raise SystemExit("lake is not on PATH; install the pinned Lean toolchain first")
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.33.1":
        raise SystemExit("Unexpected Lean toolchain pin")
    version = run([lake, "env", "lean", "--version"], capture=True).strip()
    if not version.startswith("Lean (version 4.33.1,"):
        raise SystemExit(f"Unexpected Lean runtime: {version}")
    statement = ROOT / "Submission" / "EndStatement.lean"
    if hashlib.sha256(statement.read_bytes()).hexdigest() != END_STATEMENT_SHA256:
        raise SystemExit("EndStatement.lean differs from the canonical challenge statement")
    manifest = json.loads((ROOT / "manifest.json").read_text())
    if manifest.get("problem") != "apsp":
        raise SystemExit("The manifest must target APSP")
    bound = Fraction(manifest["bound"])
    if not 0 < bound < PRIOR_VERIFIED_BOUND:
        raise SystemExit("The proposed bound does not improve 2.99556085")

    check_dependency_sources()
    before = source_snapshot()
    run([lake, "build"])
    # The type ascription checks the exact Problem.SolvedInTime proposition,
    # including program, inputs, outputs, widths, and rational runtime bound.
    # The audit then traverses all dependencies of that actual theorem.
    audit = f'''import Submission
import Lean.Util.CollectAxioms

theorem exactChallengeCheck :
    EndStatement.APSP.SolvedInTime (({bound.numerator} : Rat) / {bound.denominator}) :=
  Race.bound

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let dependencies ← Lean.collectAxioms `exactChallengeCheck
  for axiomName in dependencies do
    unless allowed.contains axiomName do
      throwError "Unexpected axiom {{axiomName}} in the exact APSP theorem"
  logInfo m!"Exact APSP theorem passed. Transitive axioms: {{dependencies}}"

#print axioms exactChallengeCheck
'''
    with tempfile.TemporaryDirectory(prefix="apsp-exact-audit-") as directory:
        audit_path = Path(directory) / "Audit.lean"
        audit_path.write_text(audit)
        run([lake, "env", "lean", str(audit_path)])
    if source_snapshot() != before:
        raise SystemExit("Proof sources changed during verification; rerun on a fixed snapshot")
    check_dependency_sources()
    print(f"PASS: EndStatement.APSP.SolvedInTime ({bound.numerator}/{bound.denominator})")
    print(f"Canonical statement SHA-256: {END_STATEMENT_SHA256}")
    print(f"Source files checked: {len(before)}")
    print(version)


if __name__ == "__main__":
    main()
