# Reproduce the selected-row machine proof

`DenseCanonicalSelectionRound.lean` is the new source file. Its source SHA-256
is `bcada4d629f7eda95fafeff960b637c50e14cbdf24ace8e239e127b635351e2b`.
It imports `DenseScoreTablePass` from the pinned upstream machine project
and `ThreeSumApsp.Lang.Lib.Copy` and `ThreeSumApsp.Lang.Calls` from the pinned
official dependency. No module from the refined numerical-certificate
project is imported by this component.

## Clean checkout

With Git and elan installed, start in a directory containing
`DenseCanonicalSelectionRound.lean` and run:

```sh
git clone https://github.com/shreshth-s/thin-matrix-results.git thin-matrix-results
git -C thin-matrix-results checkout --detach 225c37476e31bdb27594953cc1f7738496fb4afc
cp DenseCanonicalSelectionRound.lean thin-matrix-results/machine/
cd thin-matrix-results/machine
lake update
lake build +DenseScoreTablePass @ThreeSumApsp/+ThreeSumApsp.Lang.Lib.Copy
lake env lean -j1 DenseCanonicalSelectionRound.lean -o DenseCanonicalSelectionRound.olean
```

The upstream `machine/lean-toolchain` selects Lean 4.33.1. Its existing
`lakefile.toml` fixes these dependencies:

| Dependency | Exact revision | Subdirectory |
| --- | --- | --- |
| `anthropics/formal-math` | `e1a4e6508154ea59f030480661590a9fe3018011` | `3sum-apsp` |
| `leanprover-community/mathlib4` | `0df444a360eaa60ab8c11dca51a86af692955474` | Repository root |

`lake update` resolves those pinned revisions and writes the dependency
manifest. The `lake build` command builds only the score-table module, the
official copied-array primitive, and their imports. The final
command checks the new file with one Lean thread and emits its `.olean`.
It prints the eight theorem axiom-dependency reports saved in
`DenseCanonicalSelectionRound.verification.txt` and must exit with code 0.

The upstream default build also contains unrelated machine components. They
are not required for this leaf proof. The reproduction commands leave
upstream source and configuration unchanged apart from adding this new file.

## Preparation workspace

The separate preparation workspace used a `lakefile.toml` pointing to extracted copies of the same
upstream source and official dependency and reused the existing pinned
Mathlib cache. It is a workspace-specific build configuration, not the
portable dependency recipe above, and is not included in this directory.
The successful check used:

```sh
lake env lean -j1 DenseCanonicalSelectionRound.lean -o .lake/build/lib/lean/DenseCanonicalSelectionRound.olean
```

The completed controller proof includes exact score storage, selection of
a remaining argmin, copying its complete row into the base buffer, flag
deletion, memory framing, polynomial resource needs, and append stability.
It does not implement the oracle that supplies the cached input rows, or
claim a complete proof of APSP at exponent 2.9929479187094.
