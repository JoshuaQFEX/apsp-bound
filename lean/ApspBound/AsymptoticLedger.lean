/-
Copyright (c) 2026 Joshua Wharton, QFEX.
Author: Joshua Wharton <joshua@qfex.com>

The aligned-stage ledger is adapted from shreshth-s/thin-matrix-results,
lean/AsymptoticCosts.lean at commit
8a21eaae81599913dba562727e03a9b48c36a5b9, instantiated with the refined
parameters and analytically certified strict inequalities in this project.

This module proves an asymptotic theorem about an explicit mathematical
cost ledger. It does not assert that an APSP implementation has this cost,
nor that such an implementation satisfies the challenge's machine model.
-/
import ApspBound.Certificate
import ApspBound.Asymptotics

namespace ApspBound.Ledger

noncomputable section
open Filter Asymptotics Analytic Asymptotic
open scoped BigOperators

theorem targetIdentity : exponent = 3 - delta := by
  norm_num [exponent, delta]

theorem targetAboveTwo : 2 < exponent := by
  norm_num [exponent]

/-- The stage index includes all selected and candidate stages and their
common endpoint. R is a fixed integer, independent of the input size n. -/
def stageSaving (j : Fin (R + 1)) (i : Fin 6) : ℝ :=
  if j.val ≤ S then scalarSaving ((j.val : ℝ) * eta) i
  else cyclicSaving (((j.val - S : ℕ) : ℝ) * eta) i

/-- The endpoint certificate controls all R+1 stages without enumerating
R. The certificate's real-parameter inequalities have no hypotheses. -/
theorem stageSaving_gt_delta_withSlack (j : Fin (R + 1)) (i : Fin 6) :
    delta + uniformSlack < stageSaving j i := by
  have hη : 0 ≤ eta := by norm_num [eta, b, R]
  have hjR : j.val ≤ R := Nat.le_of_lt_succ j.isLt
  unfold stageSaving
  split_ifs with hj
  · apply scalarSaving_gt_delta_withSlack _ (mul_nonneg (Nat.cast_nonneg _) hη) _ i
    change (j.val : ℝ) * eta ≤ (S : ℝ) * eta
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hη
  · apply cyclicSaving_gt_delta_withSlack _ (mul_nonneg (Nat.cast_nonneg _) hη) _ i
    change ((j.val - S : ℕ) : ℝ) * eta ≤ ((R - S : ℕ) : ℝ) * eta
    apply mul_le_mul_of_nonneg_right _ hη
    exact_mod_cast Nat.sub_le_sub_right hjR S

theorem stageSaving_gt_delta (j : Fin (R + 1)) (i : Fin 6) :
    delta < stageSaving j i := by
  linarith [stageSaving_gt_delta_withSlack j i, uniformSlackPositive]

theorem stageExponentStrict (j : Fin (R + 1)) (i : Fin 6) :
    3 - stageSaving j i < exponent := by
  rw [targetIdentity]
  linarith [stageSaving_gt_delta j i]

theorem bookkeepingExponentStrict : 3 - (b - eta) < exponent := by
  rw [targetIdentity]
  linarith [bookkeeping_gt_delta]

/-- Every fixed polylogarithmic padding fits in each certified scalar tile. -/
theorem scalarTileFitsEventually (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ u)
    (k : ℕ) (C : ℝ) : ∀ᶠ n : ℕ in atTop,
    C * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ ((b + x) * T)
      ≤ (n : ℝ) ^ (1 + x / 2) := by
  apply eventualPowerFit _ k C
  have hg := scalarGeometry_pos x hx0 hx1
  change 0 < 1 + x / 2 - (b + x) * T at hg
  linarith

/-- The same strict geometry argument applies to the frozen cyclic tile. -/
theorem cyclicTileFitsEventually (k : ℕ) (C : ℝ) : ∀ᶠ n : ℕ in atTop,
    C * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (e * T)
      ≤ (n : ℝ) ^ (1 + u / 2) := by
  apply eventualPowerFit _ k C
  have hg := cyclicGeometry_pos
  change 0 < 1 + u / 2 - e * T at hg
  linarith

/-- The complete algebraic ledger: a quadratic scan, incidence bookkeeping,
and all six costs at each stage. Arbitrary fixed k admits any additional
fixed logarithmic power. R+10 and (R+1)^2 reproduce the upstream ledger's
fixed padding; this definition does not prove that padding bounds a program. -/
def completeCost (k n : ℕ) : ℝ :=
  ((R : ℝ) + 1) ^ 2 * (Real.log (n : ℝ)) ^ (k + R + 10) *
    (roundedPower 2 n + roundedPower (3 - (b - eta)) n +
      ∑ j : Fin (R + 1), ∑ i : Fin 6,
        roundedPower (3 - stageSaving j i) n)

/-- Closed asymptotic consequence of the real numerical certificate. The
strict savings absorb fixed logarithmic powers and all upward rounding. -/
theorem completeCostBigO (k : ℕ) :
    completeCost k =O[atTop] (fun n : ℕ => (n : ℝ) ^ exponent) := by
  let K := k + R + 10
  have hd : 0 < exponent := lt_trans (by norm_num) targetAboveTwo
  have hscan := roundedLogPowBigO targetAboveTwo hd K
  have hbook := roundedLogPowBigO bookkeepingExponentStrict hd K
  have hstages : (fun n : ℕ => ∑ j : Fin (R + 1), ∑ i : Fin 6,
      (Real.log (n : ℝ)) ^ K * roundedPower (3 - stageSaving j i) n)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ exponent) := by
    apply Asymptotics.IsBigO.fun_sum
    intro j _
    apply Asymptotics.IsBigO.fun_sum
    intro i _
    exact roundedLogPowBigO (stageExponentStrict j i) hd K
  have h := ((hscan.add hbook).add hstages).const_mul_left (((R : ℝ) + 1) ^ 2)
  change (fun n : ℕ => ((R : ℝ) + 1) ^ 2 * (Real.log (n : ℝ)) ^ (k + R + 10) *
    (roundedPower 2 n + roundedPower (3 - (b - eta)) n +
      ∑ j : Fin (R + 1), ∑ i : Fin 6,
        roundedPower (3 - stageSaving j i) n)) =O[atTop] _
  simpa only [K, mul_add, Finset.mul_sum, mul_assoc] using h

/-- The exact requested exponent as a rational literal. -/
theorem refinedExponentBigO (k : ℕ) :
    completeCost k =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (29929479187094 / 10000000000000 : ℝ)) := by
  simpa only [exponent] using completeCostBigO k

theorem completeCostNonnegative (k n : ℕ) (hn : 1 ≤ n) :
    0 ≤ completeCost k n := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hl := Real.log_nonneg hnR
  unfold completeCost roundedPower
  positivity

/-- A future algorithm proof can use this exact cost-domination interface.
The hypothesis is an explicit remaining obligation, not an APSP theorem. -/
theorem costBoundOfDomination (time : ℕ → ℝ) (k : ℕ)
    (hdom : time =O[atTop] completeCost k) :
    time =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (29929479187094 / 10000000000000 : ℝ)) :=
  hdom.trans (refinedExponentBigO k)

/-- Eventual pointwise domination of a natural-number step count also
suffices. No machine, implementation, or domination witness is supplied. -/
theorem costBoundOfEventualDomination (time : ℕ → ℕ) (k : ℕ) (C : ℝ)
    (hdom : ∀ᶠ n : ℕ in atTop, (time n : ℝ) ≤ C * completeCost k n) :
    (fun n => (time n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (29929479187094 / 10000000000000 : ℝ)) := by
  apply costBoundOfDomination _ k
  apply IsBigO.of_bound C
  filter_upwards [hdom, eventually_ge_atTop (1 : ℕ)] with n hb hn
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (time n)),
    Real.norm_of_nonneg (completeCostNonnegative k n hn)] using hb

end
end ApspBound.Ledger
