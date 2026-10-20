#!/usr/bin/env bash
# Author: Joshua Wharton, QFEX, joshua@qfex.com.
# Recheck pinned dependencies and each local leaf with ordinary Lake builds.
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$project_dir"
mkdir -p verification
exec > >(tee verification/refinement-build.log) 2>&1

python3 - <<'PY'
import json
from pathlib import Path
def revisions(path):
    return {entry['name']: entry.get('rev')
            for entry in json.loads(Path(path).read_text())['packages']}
expected = revisions('pinned-lake-manifest.json')
actual = revisions('lake-manifest.json')
if actual != expected:
    raise RuntimeError('The dependency revisions differ from the pinned upstream manifest')
print('Pinned dependency manifest matches.')
PY

lake env lean --version
export LEAN_NUM_THREADS=1
mapfile -t cache_roots < mathlib_cache_roots.txt
lake exe cache get "${cache_roots[@]}"

while IFS= read -r module; do
  printf 'Checking challenge dependency %s\n' "$module"
  lake build "@ThreeSumApsp/+$module"
done < challenge_import_order.txt

while IFS= read -r module; do
  printf 'Checking refinement module %s\n' "$module"
  lake build "+$module"
done < local_import_order.txt

# Re-run the audit explicitly so an existing build cache cannot hide its
# transitive-axiom report. The namespace audit itself rejects empty scope.
lake env lean -j1 LowRowRefinementAudit.lean
printf 'REFINEMENT BUILD AND TRANSITIVE-AXIOM AUDIT PASSED\n'
