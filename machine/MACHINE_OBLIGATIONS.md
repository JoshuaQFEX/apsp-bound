# Machine proof status for the refined APSP exponent

Author: Joshua Wharton, QFEX <joshua@qfex.com>

Target: `EndStatement.APSP.SolvedInTime (29929479187094 / 10000000000000)`.

This note concerns the exponent **2.9929479187094**. A proof of a different,
slower exponent does not discharge this target.

## Pinned sources inspected

- [Current thin-matrix source](https://github.com/shreshth-s/thin-matrix-results/tree/225c37476e31bdb27594953cc1f7738496fb4afc),
  including all 138 Lean files and the separate actual-machine project.
- [Canonical formal-math dependency](https://github.com/anthropics/formal-math/tree/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp).
- The earlier mathematical certificate used thin-matrix commit
  `8a21eaae81599913dba562727e03a9b48c36a5b9`.

The current source adds compiled score selection and certification, including
an actual scan of the current candidate mask. Its machine adapters still
state the three obligations below as hypotheses. The newer source does not
provide an improved min-plus solver satisfying them.

## Exact remaining theorem inputs

The current [canonical adapter](https://github.com/shreshth-s/thin-matrix-results/blob/225c37476e31bdb27594953cc1f7738496fb4afc/machine/CanonicalMachineAdapter.lean)
has the following inputs, where `P` is a finite Light program, `p` its entry
procedure, `Tn` a natural-valued runtime, and `need` a resource bound:

```lean
hs : Light.Solves Light.mpTask P p Tn need
hn : Light.PolyNeed need
hb : ∀ κ : Nat, ∃ (k : Nat) (C : Real), ∀ᶠ n : Nat in atTop,
  Light.timeUpTo (Light.Sec3.apTime Tn) n ((n : Real) ^ (κ : Real)) ≤
    C * completeCost k n
```

Its old target constant is `299294792 / 100000000`; the final adaptation must
use the refined rational exponent and the proved refined ledger. Changing
that rational constant alone would not construct `hs`, `hn`, or `hb`.

### `hs`: an actual min-plus program

[`Light.Solves`](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Tasks.lean)
requires operational executions of the program body. Specifically, it must
work for every appended program, every input satisfying the task's memory
precondition, and every admissible word, address, and call-depth limit.
The required postcondition computes every min-plus matrix entry and
preserves memory outside the permitted output and scratch regions.

The input is two signed-integer matrices of size `n*n`, with entries bounded
by `U`. The task provides concrete input and output addresses. Arrays outside
the stipulated input regions may contain arbitrary values. A functional
theorem about vectors, an oracle-correctness premise, or a work-counter field
does not supply these executions.

### `hn`: polynomial resource bounds

All of the required word magnitude, additional cells, and call depth must
be bounded by one polynomial in the task parameters `n` and `U`. This must
cover transient arithmetic values and address calculations, not merely the
final answers. The constant and degree may depend on the fixed algorithm
parameters; huge fixed parameter denominators are not by themselves an
obstruction to this condition.

### `hb`: the runtime of the full host and its input-magnitude range

The existing, verified APSP host may be reused once `hs` and `hn` hold. Its
exact source allowance is

```lean
Nat.clog 2 n * (Tn n (3 * (n * U)) + 23 * (n*n) + 29)
  + 53 * (n*n) + 17*n + 65
```

The final bound must include these calls at `3*n*U`, the outer logarithmic
factor, and the supremum taken by `timeUpTo` over the relevant natural input
bounds. It must be uniform for each fixed polynomial input-weight exponent
`κ`. An estimate only for the idealized equality-oracle work does not cover
this statement.

## Machine integration status

| Layer | Existing material | Still required for this target |
| --- | --- | --- |
| Local tensor rows | Checked Light executions of all twelve forms, shifted addressing, framing, transient bounds, equality to imported `localRow`/`denseLocalRow`, and an execution-to-scalar-counter comparison | Integration with `BinaryLowEncoder.rowBlock` and the physical cache constructor |
| Shared cache | Functional cache construction/query and charged recurrences | Finite program constructing and reusing the physical arrays, with framing and charged execution |
| Fast cyclic arithmetic | Functional binary FFT implementation and its charged costs | Actual bounded-word implementation, including coefficient intermediates, normalization, allocation, and execution bounds |
| Composite selection | Actual score scans, argmin, pool minimum, mask count, and certification components | Complete loop over factors/restarts; oracle calls; modulus/history updates; initialization and exact cache lifetime |
| Min-plus caller | Functional bit-scaling and signed/optional matrix reductions | Actual caller matching `mpTask`, including all arrays, scans, control flow, and word bounds |
| APSP host | Closed official repeated-squaring host and compiler | Instantiate it with the completed min-plus solver and bound its precise lifted runtime |

The functional `Counted` and `Result` structures admit higher-order Lean
callbacks and record work as ordinary fields. They are not a target-program
syntax. A generic compiler cannot obtain executable code and execution bounds
from these fields alone. The explicit local low-encoder forms have now been
implemented by the checked Light program and imported-row refinement below.

The active binary cyclic multiplication path uses `BinaryArrayFFT`.
Completing the older Toom multiplication path alone would not verify that
active implementation. The signed polynomial coefficients in a local
low-encoder row can be handled with ordinary bounded Light arithmetic, but
that observation does not establish bounds for every FFT intermediate.

## New isolated controller component

`DenseCanonicalSelectionRound.lean` implements a fixed six-procedure
Light program that computes every candidate score, chooses a remaining
minimum-score candidate, copies its complete row into the base buffer, and
clears exactly its remaining flag. It uses the official verified copying
routine and the upstream verified score/argmin routines.

This addresses a precise limitation of the upstream `DenseSelectionRound`:
that routine updates the base by a coordinatewise minimum with its previous
contents. The canonical greedy algorithm instead replaces the base by the
chosen row. The new routine does not need the old base to be initialized.

Its proved source allowance is

```text
22*P*I + 62*P + 16*I + 87
```

and the cost comparison is `time <= 25*(P*I + 6*P + I)` for `P > 0`, including
the zero-incidence case. Here `P*I + 6*P + I` is the existing charged
controller-visits expression. The exact theorem proves an argmin
postcondition and row replacement; equality with the functional algorithm's
particular tie-breaking implementation is not asserted.

The file has now compiled successfully with Lean 4.33.1. The closed
`Light.DenseCanonicalSelectionRound.task_solved`, `need_polynomial`, and
`solvedIn` declarations prove its `Solves`, `PolyNeed`, and `SolvedIn`
contracts. Its eight printed theorem dependency reports contain only
`propext`, `Classical.choice`, and `Quot.sound` (some use a strict subset).
The exact command and transcript are in
`DenseCanonicalSelectionRound.verification.txt`; clean pinned
reproduction instructions are in `REPRODUCE.md`.
The input row table, original active mask, nonempty remaining mask, bounds,
and ordered disjoint buffer layout remain explicit task preconditions. It
does not construct the equality-oracle table or the complete selection loop.

## Checked local-row component

`LowRowMachine.lean` supplies a fixed twelve-procedure Light program with
closed execution and polynomial-resource theorems. It proves all specified
output coefficients, preserves memory outside the destination, uses no
additional scratch cells, and has allowance `64*N + 8` per row call and word need
`8*U + 2`. The source arrays may alias one another; the output must be
disjoint from them. The shifted third input of the normal fifth row reads
the previous auxiliary degree while preserving the cyclic residue.

`LowRowSemantics.lean` proves the explicit formulas and flattening identities.
Both modules compiled successfully. `LowRowAudit.lean` checked all 99
declarations and found only the standard three axioms. Reproduction commands
and source hashes are in `LOW_ROW_REPRODUCE.md` and the accompanying
verification transcripts.

The checked `refinement/LowRowRefinement.lean` now connects the actual machine
task to the imported upstream `SparseLocalForms.localRow` and `denseLocalRow`.
It proves an execution allowance of at most five times the upstream
`materializeScalarCost`, plus eight. The subsequent audit checked 746
declarations with only the standard three axioms. Its README and successful
transcript document the exact source adaptations and nonfatal upstream
simplifier diagnostics.

Integration with `BinaryLowEncoder.rowBlock`, the physical shared cache, and
its HIGH/LOW query assembly remains unfinished. The component condition
`q <= N` covers the intended `N = width*q` with `width >= 1`.

## Numerical slack and arithmetic integration

The refined real certificate reserves `2e-14` beyond the requested exponent
saving. Its rational gate proves that an arithmetic epsilon of `1e-13`,
multiplied by the last-phase scale, plus a `1e-15` reserve fits within this
margin. The original arithmetic epsilon of `1e-8` does not fit the refined
margin. The gate is the already compiled declaration
`ApspBound.Analytic.arithmeticAllowanceFits` in
`../lean/ApspBound/Certificate.lean`:

```lean
theorem arithmeticAllowanceFits :
    (1 / 10^13 : ℝ) * v + (1 / 10^15 : ℝ) < uniformSlack := by
  norm_num [v, eta, b, R, S, uniformSlack]
```

The saved `../lean/verification.txt` records the successful full
certificate build and `Audit.lean`'s successful audit of all 232 declarations
in the `ApspBound` namespace. `Audit.lean` inspects their transitive axiom
dependencies, allowing only `propext`, `Classical.choice`, and `Quot.sound`;
this includes `arithmeticAllowanceFits`.

Applying the new gate to the actual arithmetic implementation still
requires a consistent parameterized cost proof for that implementation.

The already checked real logarithm, entropy, strict-inequality, and finite
polylogarithmic-ledger theorems solve the analytic part. They neither assume
nor prove the existence of a faster machine program. Closing the three
explicit obligations above is the remaining route to the requested
canonical theorem.
