# Lean numerical and cost-ledger formalization

**Joshua Wharton · QFEX · [joshua@qfex.com](mailto:joshua@qfex.com)**

This project formalizes the exact parameter certificate and the asymptotic mathematical cost ledger for the exponent **2.9929479187094**. The logarithms in the theorem are Mathlib's actual `Real.log`, and the rational parameter values agree with the parent directory's [parameters.json](../parameters.json).

The separate [`../verified/` project](../verified/README.md) contains the complete exact-model APSP development at exponent **2.995560766**. Its theorem has a different exponent and uses the inherited fully implemented algorithm; it does not establish the faster bound studied here. The [`../machine/` directory](../machine/README.md) records checked components and the remaining implementation obligations for the faster construction.

## Build and audit

Install Lean through [Elan](https://github.com/leanprover/elan), then run from this directory:

```bash
lake exe cache get Mathlib.Analysis.SpecialFunctions.Log.Deriv Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring Mathlib.Tactic.Positivity Mathlib.Tactic.FinCases
lake build
lake env lean Audit.lean
```

The toolchain is pinned to **Lean 4.33.1**. Mathlib is pinned to commit **`0df444a360eaa60ab8c11dca51a86af692955474`**, with its transitive dependencies recorded in [lake-manifest.json](lake-manifest.json). The first command downloads precompiled dependency objects; all proof modules in this numerical Lean project are built from source by the second command.

[Audit.lean](Audit.lean) examines every declaration in the `ApspBound` namespace and rejects any transitive axiom outside `propext`, `Classical.choice`, and `Quot.sound`. These are the standard logical axioms used by this Mathlib development. The audit rejects `sorryAx`, native decision axioms, and any additional project axiom. The rational checks use `decide +kernel`; the real estimates use proof-producing Mathlib tactics.

The [GitHub workflow](../.github/workflows/lean.yml) rebuilds the development, runs this audit, and reproduces the independent Python certificate.

## Structure

| Module | Role |
| --- | --- |
| [Definitions](ApspBound/Definitions.lean) | Exact parameters, real entropy, phase savings, and tile geometry |
| [Numerical](ApspBound/Numerical.lean) | Rational witness identities and all 47 affine inequalities over rational enclosures |
| [LogBounds](ApspBound/LogBounds.lean) | Seven real logarithm bounds and three entropy enclosures, proved using a 40-term positive atanh series |
| [Certificate](ApspBound/Certificate.lean) | Connection between the rational and real expressions; closed real numerical feasibility and bounds throughout both phases |
| [Asymptotics](ApspBound/Asymptotics.lean) | General results absorbing fixed logarithmic powers and upward rounding into a strict exponent gap |
| [AsymptoticLedger](ApspBound/AsymptoticLedger.lean) | Application to all six cost categories across the fixed stages at the exact refined exponent |

The Python optimizer and numerical checker are independent corroboration. Neither is called by Lean or trusted as a source of proof.

## Exact asymptotic theorem

`ApspBound.Ledger.refinedExponentBigO` states that, for every fixed natural number `k`, the explicitly defined `completeCost k` is

$$O\!\left(n^{29929479187094/10000000000000}\right)
= O\!\left(n^{2.9929479187094}\right).$$

`completeCost` includes a quadratic scan, incidence bookkeeping, all six phase costs at each of the `R+1` stages, upward integer rounding, and fixed logarithmic padding. Here `R = 10^12` is fixed independently of `n`. The proof handles the finite stage family symbolically and does not enumerate a trillion cases.

The numerical and cost-ledger theorems have no hypotheses asserting unproved logarithm bounds or numerical feasibility. The actual execution cost of an APSP program is a separate obligation.

## Scope of the formalization

This numerical project **does not prove the challenge's complete `EndStatement.APSP` theorem at exponent 2.9929479187094**. The connection from the aligned embedding, polynomial cache, composite-incidence reduction, and min-plus/APSP reductions to the step count of a correct fixed-width word-RAM program remains outside these modules.

The explicit interfaces `costBoundOfDomination` and `costBoundOfEventualDomination` explain how a future program proof can use the established ledger bound. Their cost-domination premises remain visible; these modules supply no complete execution witness for the faster bound.

This distinction already exists in the upstream [machine adapter](https://github.com/shreshth-s/thin-matrix-results/blob/8a21eaae81599913dba562727e03a9b48c36a5b9/machine/CanonicalMachineAdapter.lean) and [machine documentation](https://github.com/shreshth-s/thin-matrix-results/blob/8a21eaae81599913dba562727e03a9b48c36a5b9/machine/README.md). Its adapter requires a correct min-plus machine program, a polynomial word-width requirement, and a bound comparing actual machine execution to the cost ledger. Those obligations are not discharged by changing numerical constants.

An additional detail matters when extending the upstream charged-work development: its [ArithmeticSlack module](https://github.com/shreshth-s/thin-matrix-results/blob/8a21eaae81599913dba562727e03a9b48c36a5b9/lean/ArithmeticSlack.lean) reserves an arithmetic exponent overhead and a margin larger than this refinement's available slack. Those values must also be reduced and their downstream proofs checked before that stronger interface can be reused. This project does not claim that substituting the new witness alone proves the upstream whole-program theorem.

## Attribution

The new rational witness and its formalization are attributed to **Joshua Wharton, QFEX**. The implementation follows and adapts parts of the finite affine certificate, real-logarithm proof arrangement, and asymptotic composition from **shreshth-s/thin-matrix-results**, pinned to commit `8a21eaae81599913dba562727e03a9b48c36a5b9`. The relevant original modules are [AlignedCertificate](https://github.com/shreshth-s/thin-matrix-results/blob/8a21eaae81599913dba562727e03a9b48c36a5b9/lean/AlignedCertificate.lean), [RealCertificate](https://github.com/shreshth-s/thin-matrix-results/blob/8a21eaae81599913dba562727e03a9b48c36a5b9/lean/RealCertificate.lean), and [AsymptoticCosts](https://github.com/shreshth-s/thin-matrix-results/blob/8a21eaae81599913dba562727e03a9b48c36a5b9/lean/AsymptoticCosts.lean). File headers record this derivation.

The underlying algorithm and earlier results retain the attribution given in the parent [research note](../apsp_refinement.pdf) and [README](../README.md). AI assistance was used in preparing and reviewing this development.
