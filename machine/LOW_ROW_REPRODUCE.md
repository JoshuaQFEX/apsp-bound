# Reproduce the verified local-row encoder

Author: Joshua Wharton, QFEX, joshua@qfex.com.

`LowRowMachine.lean` and `LowRowSemantics.lean` both passed the Lean 4.33.1
kernel check and emitted compiled `.olean` files. `LowRowAudit.lean` passed
its audit of all **99** declarations in `Light.LowRowMachine`; their
transitive axiom dependencies contain only `propext`, `Classical.choice`,
and `Quot.sound`.

## What is proved

The program contains twelve fixed procedures: the six normal and six
opposite local coefficient forms. Each procedure writes a complete array
of `n` integer coefficients. The normal fifth row uses the third input
from the preceding auxiliary degree, contributing zero in degree zero.
Negative constants are constructed by actual subtraction in the Light
syntax. Their construction, the input loads, arithmetic, stores, tests,
and loop control are included in the source-language step allowance.

| Declaration | Closed conclusion |
| --- | --- |
| `Light.LowRowMachine.solves` | The one-procedure program satisfies the concrete array task. |
| `Light.LowRowMachine.solves_in` | The same contract holds inside any program containing this actual body at the chosen index. |
| `Light.LowRowMachine.allProgram_solves` | One fixed twelve-procedure program implements every normal/opposite row. |
| `Light.LowRowMachine.need_polynomial` | The resource requirement is polynomial. |
| `Light.LowRowMachine.solvedIn` | The task has source allowance `64*n + 8`. |
| `Light.LowRowMachine.ledger_overhead` | At `n = width*q`, the allowance is at most `5*(14*q*width) + 8`. |
| `Light.LowRowMachine.normal_formulas` and `opposite_formulas` | The output is exactly the twelve displayed algebraic forms. |
| `Light.LowRowMachine.thirdRead_flatten` | Subtracting `q` moves to the previous auxiliary degree and preserves the cyclic residue. |
| `Light.LowRowMachine.shifted_source_in_range` | The preceding-degree source address stays inside the coefficient array. |

The caller supplies four arrays of length `n` with entries bounded in
absolute value by `U`, a cyclic-vector length `q` with `q <= n`, and an
output buffer of `n` cells. The output buffer is separate from every input;
the inputs may alias one another. The task proves every output value and
preservation of all memory outside the output buffer. It requires word
magnitude `8*U + 2`, **zero additional scratch cells**, and no nested calls.
The output buffer itself is included in the task's concrete layout
precondition, rather than treated as free allocation.

For the intended flattened layout, `n = width*q` with positive `width`
and `q`. The shifted row reads `((degree-1)*q + residue)` when the degree
is positive. Opposite rows do not use the fourth input value; its required
valid array can alias any of the other input arrays.

## Scope of the refinement

An independent source review checked that these formulas match
`SparseLocalForms.normal_localPolynomial` and
`SparseLocalForms.opposite_localPolynomial` at the pinned thin-matrix
revision below. The checked files prove the formulas and operational
executions directly. They do **not** import and prove an equality with
`ThinMatrix.SparseLocalForms.localRow` or `BinaryLowEncoder.rowBlock`.
That named refinement theorem remains a separate integration step.

This component does not construct the shared cache, implement the HIGH
cyclic multiplier, assemble the equality oracle, or prove the complete
APSP bound `2.9929479187094`. Its `Light.Solves` contract has no assumed
execution or assumed cost-domination premise.

## Exact source and object hashes

| File | SHA-256 |
| --- | --- |
| `LowRowMachine.lean` | `b245ce32186f551eedd12e0ab2d3a95002faa82826bfea5284fce6d5ad5518fa` |
| `LowRowSemantics.lean` | `e0913d2c4df268e376f11c1585b6aa90e24d6b186a399aa1c2b052f93943ac56` |
| `LowRowAudit.lean` | `131405e4f36643c3e065c27663296469eca9a4574dfec92847ce479443eaa1a4` |
| `LowRowMachine.olean` | `e295c928f2840eecea0b94ff0710bb4dfe09d9bacd44910ee815f834aec300d5` |
| `LowRowSemantics.olean` | `0e4780b2120803ca5824185cc019077d8d81c9572d98ec56a5b4830280339103` |

Object hashes record this successful build. Source hashes and pinned
dependencies identify the reproducible proof; regenerated object hashes
may depend on build metadata.

## Clean pinned reproduction

With Git and elan installed, start beside the three new Lean files:

```sh
git clone https://github.com/shreshth-s/thin-matrix-results.git thin-matrix-results
git -C thin-matrix-results checkout --detach 225c37476e31bdb27594953cc1f7738496fb4afc
cp LowRowMachine.lean LowRowSemantics.lean LowRowAudit.lean thin-matrix-results/machine/
cd thin-matrix-results/machine
lake update
lake build @ThreeSumApsp/+ThreeSumApsp.Lang.Lib.Pass @ThreeSumApsp/+ThreeSumApsp.Lang.Lib.ArrayAt @ThreeSumApsp/+ThreeSumApsp.Lang.PolyBounded @ThreeSumApsp/+ThreeSumApsp.Lang.Tactics @mathlib/+Mathlib.Tactic.FinCases
mkdir -p .lake/build/lib/lean
lake env lean -j1 -o .lake/build/lib/lean/LowRowMachine.olean LowRowMachine.lean
lake env lean -j1 -o .lake/build/lib/lean/LowRowSemantics.olean LowRowSemantics.lean
lake env lean -j1 LowRowAudit.lean
```

All three final commands must exit with code 0. The audit prints:

```text
Axiom audit passed for 99 declarations. Allowed axioms: propext, Classical.choice, Quot.sound.
```

The pinned machine project selects `leanprover/lean4:v4.33.1` and fixes:

| Dependency | Revision | Subdirectory |
| --- | --- | --- |
| `anthropics/formal-math` | `e1a4e6508154ea59f030480661590a9fe3018011` | `3sum-apsp` |
| `leanprover-community/mathlib4` | `0df444a360eaa60ab8c11dca51a86af692955474` | Repository root |

Only the official Light dependency, Mathlib, and the three new files are
needed for this component. The source comparison with the upstream cache
forms uses thin-matrix commit
`225c37476e31bdb27594953cc1f7738496fb4afc`.

## Successful local check

The isolated workspace uses path dependencies containing the same pinned
sources and reuses the existing Mathlib cache. The successful commands
were run from `apsp_work/full_machine/extension`, with the Lean 4.33.1
binary directory on `PATH`. They are recorded, with exit codes, axiom
reports, and hashes, in:

- `LowRowMachine.verification.txt`
- `LowRowSemantics.verification.txt`
- `LowRowAudit.verification.txt`

Only one new Lean check ran at a time. An earlier resource interruption
did not produce a successful semantic-module check; the saved semantic
transcript records the later successful run.
