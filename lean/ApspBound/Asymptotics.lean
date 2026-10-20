/-
Copyright (c) 2026 Joshua Wharton, QFEX.
Author: Joshua Wharton <joshua@qfex.com>

Asymptotic composition for the APSP numerical refinement. The proof strategy
for absorbing logarithmic powers and integer rounding follows
shreshth-s/thin-matrix-results, lean/AsymptoticCosts.lean, commit
8a21eaae81599913dba562727e03a9b48c36a5b9, with the finite-ledger interface
generalized here. No claim about the execution cost of an algorithm is made.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ApspBound.Asymptotic

noncomputable section
open Filter Asymptotics
open scoped BigOperators

/-- Any strict saving in the exponent absorbs every fixed logarithmic power. -/
theorem logPowMulRpowBigO {a d : ℝ} (had : a < d) (k : ℕ) :
    (fun n : ℕ => (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ a)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ d) := by
  have hlogR : (fun x : ℝ => (Real.log x) ^ k)
      =O[atTop] (fun x : ℝ => x ^ (d - a)) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := d - a) (k : ℝ) (sub_pos.mpr had)).isBigO
  have hlog := hlogR.natCast_atTop
  have hp : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a) :=
    isBigO_refl _ _
  simpa only [Asymptotics.isBigO_iff, Real.norm_eq_abs, Pi.mul_apply] using
    IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (d - a) a d hlog hp (by linarith)

/-- The saving is strong enough for little-o, including an arbitrary fixed
logarithmic power. -/
theorem logPowMulRpowLittleO {a d : ℝ} (had : a < d) (k : ℕ) :
    (fun n : ℕ => (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ a)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ d) := by
  have hlogR : (fun x : ℝ => (Real.log x) ^ k)
      =o[atTop] (fun x : ℝ => x ^ (d - a)) := by
    simpa only [Real.rpow_natCast] using
      isLittleO_log_rpow_rpow_atTop (s := d - a) (k : ℝ) (sub_pos.mpr had)
  have hlog := hlogR.natCast_atTop
  have hp : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a) :=
    isBigO_refl _ _
  have hmul := hlog.mul_isBigO hp
  have heq : (fun n : ℕ => (n : ℝ) ^ (d - a) * (n : ℝ) ^ a)
      =ᶠ[atTop] (fun n : ℕ => (n : ℝ) ^ d) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1)
      (show 1 ≤ (n : ℝ) by exact_mod_cast hn)
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  simpa only [Asymptotics.isLittleO_iff, Real.norm_eq_abs] using
    hmul.congr' Filter.EventuallyEq.rfl heq

/-- A strict exponent gap eventually accommodates every fixed multiplier
and logarithmic padding, with constant one on the larger power. -/
theorem eventualPowerFit {a d : ℝ} (had : a < d) (k : ℕ) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ a ≤ (n : ℝ) ^ d := by
  have h := (logPowMulRpowLittleO had k).const_mul_left C
  have hb := h.bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb] with n hn
  calc
    C * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ a
        ≤ ‖C * ((Real.log (n : ℝ)) ^ k * (n : ℝ) ^ a)‖ := by
          simpa only [mul_assoc, Real.norm_eq_abs] using
            le_abs_self (C * ((Real.log (n : ℝ)) ^ k * (n : ℝ) ^ a))
    _ ≤ 1 * ‖(n : ℝ) ^ d‖ := hn
    _ = (n : ℝ) ^ d := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) d), one_mul]

/-- Real-valued natural ceiling. The ceiling is taken before returning to ℝ. -/
def roundedPower (a : ℝ) (n : ℕ) : ℝ := (Nat.ceil ((n : ℝ) ^ a) : ℝ)

theorem roundedPowerNonnegative (a : ℝ) (n : ℕ) : 0 ≤ roundedPower a n :=
  Nat.cast_nonneg _

/-- Upward integer rounding adds at most one. The positive target exponent
absorbs this unit as well as the fixed logarithmic power. -/
theorem roundedLogPowBigO {a d : ℝ} (had : a < d) (hd : 0 < d) (k : ℕ) :
    (fun n : ℕ => (Real.log (n : ℝ)) ^ k * roundedPower a n)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ d) := by
  have ha := logPowMulRpowBigO had k
  have hz := logPowMulRpowBigO (a := 0) hd k
  have hsum := ha.add hz
  have hdom : (fun n : ℕ => (Real.log (n : ℝ)) ^ k * roundedPower a n)
      =O[atTop] (fun n : ℕ => (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ a +
        (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (0 : ℝ)) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hl : 0 ≤ (Real.log (n : ℝ)) ^ k :=
      pow_nonneg (Real.log_nonneg hnR) _
    have hc := (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) a)).le
    rw [Real.norm_of_nonneg (mul_nonneg hl (roundedPowerNonnegative a n))]
    simpa [roundedPower, Real.rpow_zero, mul_add] using mul_le_mul_of_nonneg_left hc hl
  exact hdom.trans hsum

/-- A finite cost ledger with an independently chosen constant, logarithmic
power and power exponent for each entry. None of these choices depends on n. -/
def finiteLedger {ι : Type*} [Fintype ι] (C : ι → ℝ) (k : ι → ℕ)
    (a : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i, C i * ((Real.log (n : ℝ)) ^ k i * roundedPower (a i) n)

/-- Every fixed finite ledger whose entry exponents are strictly below d
is O(n^d), including all its ceilings and logarithmic factors. This theorem
does not require an explicitly supplied uniform numerical slack. -/
theorem finiteLedgerBigO {ι : Type*} [Fintype ι] (C : ι → ℝ) (k : ι → ℕ)
    (a : ι → ℝ) {d : ℝ} (hd : 0 < d) (ha : ∀ i, a i < d) :
    finiteLedger C k a =O[atTop] (fun n : ℕ => (n : ℝ) ^ d) := by
  classical
  unfold finiteLedger
  apply Asymptotics.IsBigO.fun_sum
  intro i _
  exact (roundedLogPowBigO (ha i) hd (k i)).const_mul_left (C i)

/-- For a nonnegative-cost ledger, its value is nonnegative for every n ≥ 1. -/
theorem finiteLedgerNonnegative {ι : Type*} [Fintype ι] (C : ι → ℝ) (k : ι → ℕ)
    (a : ι → ℝ) (hC : ∀ i, 0 ≤ C i) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ finiteLedger C k a n := by
  classical
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hC i) (mul_nonneg
    (pow_nonneg (Real.log_nonneg hnR) _) (roundedPowerNonnegative (a i) n))

/-- This interface records exactly the remaining cost proof an algorithm
must supply: eventual domination of its actual natural-number step count.
No such domination is asserted by this module. -/
theorem costBoundOfEventualDomination {ι : Type*} [Fintype ι]
    (C : ι → ℝ) (k : ι → ℕ) (a : ι → ℝ) {d : ℝ}
    (hd : 0 < d) (ha : ∀ i, a i < d) (hC : ∀ i, 0 ≤ C i)
    (time : ℕ → ℕ) (B : ℝ)
    (hdom : ∀ᶠ n : ℕ in atTop, (time n : ℝ) ≤ B * finiteLedger C k a n) :
    (fun n => (time n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ d) := by
  have hledger : (fun n => (time n : ℝ)) =O[atTop] finiteLedger C k a := by
    apply IsBigO.of_bound B
    filter_upwards [hdom, eventually_ge_atTop (1 : ℕ)] with n hb hn
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (time n)),
      Real.norm_of_nonneg (finiteLedgerNonnegative C k a hC n hn)] using hb
  exact hledger.trans (finiteLedgerBigO C k a hd ha)

end
end ApspBound.Asymptotic
