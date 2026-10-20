# Machine components for the faster conditional bound

**Joshua Wharton · QFEX · joshua@qfex.com**

These files prove actual executions and resource bounds for components of the construction targeting exponent **2.9929479187094**. They do not prove the complete APSP theorem at that exponent. The separate complete theorem at **2.995560766** is in [`../verified/`](../verified/README.md).

## Checked components

| Component | Proved behavior | Proved source-time allowance |
| --- | --- | --- |
| [Selected-row controller](DenseCanonicalSelectionRound.lean) | Computes candidate scores, selects a remaining argmin, copies its complete row into the base buffer, clears its flag, and preserves other memory | `22*P*I + 62*P + 16*I + 87` |
| [Twelve local row encoders](LowRowMachine.lean) | Executes a specified normal or opposite local form on bounded integer arrays, including the shifted third input of the normal fifth row, with exact output and framing | `64*N + 8` per row call |

The controller is a fixed six-procedure Light program. For `P > 0`, its time is at most `25*(P*I + 6*P + I)`. Its closed task theorem includes polynomial resource bounds. The task supplies the cached rows, masks, and a disjoint buffer layout. It proves an argmin, without asserting identity with the functional controller's particular tie-breaking routine.

The row encoder is one fixed twelve-procedure program, with a proved contract for each procedure. A call writes one specified row. It needs words bounded by `8*U + 2`, no additional scratch cells, and no nested calls. Inputs may alias each other; the destination is separate from every input. For `N = width*q`, each row call's allowance is bounded by `5*(14*q*width) + 8`.

[LowRowSemantics.lean](LowRowSemantics.lean) proves all twelve explicit formulas and the flattened-address identity for the auxiliary-degree shift. The checked [upstream refinement](refinement/README.md) proves that the actual machine task outputs the imported `SparseLocalForms.localRow`, including its materialized `denseLocalRow` form. It also proves that each row call's execution allowance is at most five times the upstream `materializeScalarCost`, plus eight. The later `BinaryLowEncoder.rowBlock` and physical cache integration remain unfinished.

## Verification and reproduction

The controller source and both low-row proof modules compiled under Lean 4.33.1 with exit code 0. The controller's eight printed theorem dependencies contain only standard axioms. The [low-row namespace audit](LowRowAudit.lean) checked all 99 declarations and allowed only `propext`, `Classical.choice`, and `Quot.sound`.

The later [refinement audit](refinement/LowRowRefinementAudit.lean) checked 746 machine, refinement, and upstream declarations with the same permitted axioms. Its [reproduction notes](refinement/README.md) document the transparent Lean-version adaptations and the nonfatal upstream simplifier diagnostics retained in the successful transcript.

- [Controller reproduction commands and pins](REPRODUCE.md)
- [Controller verification transcript](DenseCanonicalSelectionRound.verification.txt)
- [Low-row reproduction commands and pins](LOW_ROW_REPRODUCE.md)
- [Low-row execution transcript](LowRowMachine.verification.txt), [semantic transcript](LowRowSemantics.verification.txt), and [namespace audit transcript](LowRowAudit.verification.txt)
- [Imported-row refinement, portable setup, and successful transcript](refinement/README.md)

The upstream algorithms and official Light primitives retain their original attribution. These new component proofs are attributed to Joshua Wharton, QFEX, and were prepared with AI assistance.

## Remaining full theorem

[MACHINE_OBLIGATIONS.md](MACHINE_OBLIGATIONS.md) records the precise unresolved `Solves`, `PolyNeed`, and lifted-runtime contracts. The shared cache, fast cyclic arithmetic, complete factor/restart controller, and bit-scaled min-plus caller still need operational implementations and cost proofs. The caller must also connect these local component contracts to the imported mathematical construction. The existing numerical and ledger proofs do not discharge those obligations.
