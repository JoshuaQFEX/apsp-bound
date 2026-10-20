#!/usr/bin/env python3
"""Check the recorded imports and proof adaptation against pinned snapshots.

Author: Joshua Wharton, QFEX, joshua@qfex.com.
This source-integrity check is separate from the Lean kernel proofs.
The allowed proof edit replaces a rewrite by transport across its equality.
Every mathematical definition and theorem statement is preserved exactly.
"""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
manifest = json.loads((root / "integrity_manifest.json").read_text())

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def without_imports(data: bytes) -> bytes:
    return b"".join(line for line in data.splitlines(keepends=True)
                    if not line.startswith(b"import "))

def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)

equality_transport = """  have h := (congrArg
    (fun a : Cyclic q => CoeffBound a (q*(2^(7*L+m)*A)*(2^(7*L+m)*A)))
    (mul_eq_convolution (q := q)
      (fun k => e.left.eval sources raw (e.leftDegree,k))
      (fun k => e.right.eval sources raw (e.rightDegree,k)))).mp h
"""
permitted_adaptations = {
    ("CoefficientBounds.lean", "  rw [mul_eq_convolution] at h\n", equality_transport)
}
adaptation_count = 0
for record in manifest["files"]:
    name = record["name"]
    original = (root / "pinned_upstream" / name).read_bytes()
    vendored = (root / "upstream" / name).read_bytes()
    require(digest(original) == record["upstream_sha256"], f'{name}: upstream hash mismatch')
    require(digest(vendored) == record["vendored_sha256"], f'{name}: vendored hash mismatch')
    original_body = without_imports(original)
    require(digest(original_body) == record["non_import_content_sha256"],
            f'{name}: upstream non-import content hash mismatch')
    expected_body = original_body
    for adaptation in record.get("proof_adaptations", []):
        old, new = adaptation["old"], adaptation["new"]
        require((name, old, new) in permitted_adaptations,
                f'{name}: unapproved proof adaptation')
        require(expected_body.count(old.encode()) == 1,
                f'{name}: proof adaptation must match exactly once')
        expected_body = expected_body.replace(old.encode(), new.encode(), 1)
        adaptation_count += 1
    require(expected_body == without_imports(vendored),
            f'{name}: unrecorded non-import change')
    if record["byte_identical"]:
        require(original == vendored, f'{name}: not byte-identical')

compatibility = manifest["compatibility_layer"]
require(digest((root / compatibility["path"]).read_bytes()) == compatibility["sha256"],
        'Compatibility helper hash mismatch')
require(next(r for r in manifest["files"]
             if r["name"] == "SparseLocalForms.lean")["byte_identical"],
        'SparseLocalForms must remain byte-identical')
print(f'Upstream integrity check passed for {len(manifest["files"])} pinned modules; '
      f'{adaptation_count} explicitly whitelisted proof adaptation; '
      'SparseLocalForms is byte-identical.')
