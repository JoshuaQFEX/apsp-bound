/-
Copyright (c) 2026 Joshua Wharton, QFEX.
Author: Joshua Wharton <joshua@qfex.com>

Closed analytic feasibility certificate for the exponent 2.9929479187094.
The affine interval-to-real bridge follows the corresponding construction in
shreshth-s/thin-matrix-results, commit 8a21eaae81599913dba562727e03a9b48c36a5b9.
Every logarithm bound is proved in LogBounds; no analytic enclosure is assumed.
This module proves cost inequalities, not a complete APSP word-RAM program.
-/
import ApspBound.Definitions
import ApspBound.Numerical
import ApspBound.LogBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ApspBound.Analytic

theorem logFour : Real.log 4 = 2 * Real.log 2 := by
  convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num

theorem logTwoPositive : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem TEnclosure :
    (12059361352073940511273 / 10^21 : ℝ) < T ∧
    T < (12059361352073940511274 / 10^21 : ℝ) := by
  have h0 := logTwo
  have hc := entropyC
  have hp : 0 < 2 * Real.log 2 := mul_pos (by norm_num) logTwoPositive
  have hlo : ((12059361352073940511273 / 10^21 : ℝ) - c + 1) * (2 * Real.log 2)
      < c * entropy (1 / c) := by
    norm_num [c] at hc ⊢
    linarith [h0.1, h0.2, hc.1, hc.2]
  have hhi : c * entropy (1 / c)
      < ((12059361352073940511274 / 10^21 : ℝ) - c + 1) * (2 * Real.log 2) := by
    norm_num [c] at hc ⊢
    linarith [h0.1, h0.2, hc.1, hc.2]
  have hl := (lt_div_iff₀ hp).2 hlo
  have hh := (div_lt_iff₀ hp).2 hhi
  dsimp [T, CK]
  rw [logFour]
  constructor <;> linarith

theorem GEnclosure :
    (86576374110896937279 / 10^21 : ℝ) < G ∧
    G < (86576374110896937280 / 10^21 : ℝ) := by
  have h0 := logTwo
  have hc := entropyC
  have hd := entropyD
  dsimp [G]
  rw [logFour]
  constructor
  · apply (lt_div_iff₀ logTwoPositive).2
    norm_num [c, theta] at hc hd ⊢
    linarith [h0.1, h0.2, hc.1, hc.2, hd.1, hd.2]
  · apply (div_lt_iff₀ logTwoPositive).2
    norm_num [c, theta] at hc hd ⊢
    linarith [h0.1, h0.2, hc.1, hc.2, hd.1, hd.2]

theorem q1Enclosure :
    (348125802190376753494 / 10^21 : ℝ) < q1 ∧
    q1 < (348125802190376753495 / 10^21 : ℝ) := by
  have h0 := logTwo
  have ht := entropyTheta
  dsimp [q1]
  constructor
  · apply (lt_div_iff₀ logTwoPositive).2
    linarith [h0.1, h0.2, ht.1, ht.2]
  · apply (div_lt_iff₀ logTwoPositive).2
    linarith [h0.1, h0.2, ht.1, ht.2]

noncomputable def evalReal (a : Numerical.Affine) : ℝ :=
  (a.constant : ℝ) + (a.tCoeff : ℝ) * T + (a.gCoeff : ℝ) * G + (a.qCoeff : ℝ) * q1

theorem signedLowerReal (coefficient lo hi : Rat) (x : ℝ)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (Numerical.signedLower coefficient lo hi : ℝ) ≤ (coefficient : ℝ) * x := by
  by_cases h : 0 ≤ coefficient
  · simp only [Numerical.signedLower, if_pos h, Rat.cast_mul]
    apply mul_le_mul_of_nonneg_left hlo
    exact_mod_cast h
  · simp only [Numerical.signedLower, if_neg h, Rat.cast_mul]
    apply mul_le_mul_of_nonpos_left hhi
    have hn : coefficient ≤ 0 := le_of_not_ge h
    exact_mod_cast hn

theorem actualParameterEnclosures :
    (Numerical.tLo : ℝ) ≤ T ∧ T ≤ (Numerical.tHi : ℝ) ∧
    (Numerical.gLo : ℝ) ≤ G ∧ G ≤ (Numerical.gHi : ℝ) ∧
    (Numerical.qLo : ℝ) ≤ q1 ∧ q1 ≤ (Numerical.qHi : ℝ) := by
  have ht := TEnclosure
  have hg := GEnclosure
  have hq := q1Enclosure
  norm_num [Numerical.tLo, Numerical.tHi, Numerical.gLo, Numerical.gHi,
    Numerical.qLo, Numerical.qHi]
  norm_num at ht hg hq
  exact ⟨ht.1.le, ht.2.le, hg.1.le, hg.2.le, hq.1.le, hq.2.le⟩

theorem lowerLeActual (a : Numerical.Affine) :
    (Numerical.lower a : ℝ) ≤ evalReal a := by
  rcases actualParameterEnclosures with ⟨ht0, ht1, hg0, hg1, hq0, hq1⟩
  have ht := signedLowerReal a.tCoeff _ _ T ht0 ht1
  have hg := signedLowerReal a.gCoeff _ _ G hg0 hg1
  have hq := signedLowerReal a.qCoeff _ _ q1 hq0 hq1
  unfold Numerical.lower evalReal
  push_cast
  linarith

theorem allActualRealCostsWithSlack :
    ∀ check ∈ Numerical.checks,
      (check.target : ℝ) + uniformSlack < evalReal check.expression := by
  intro check hmember
  have hb : decide (check.target + Numerical.uniformSlack < Numerical.lower check.expression)
      = true :=
    (List.all_eq_true.mp Numerical.numericalMarginsWithSlack) check hmember
  have hr : check.target + Numerical.uniformSlack < Numerical.lower check.expression :=
    of_decide_eq_true hb
  have hm : (check.target : ℝ) + uniformSlack <
      (Numerical.lower check.expression : ℝ) := by
    have hcast : ((check.target + Numerical.uniformSlack : Rat) : ℝ) <
        (Numerical.lower check.expression : ℝ) := by exact_mod_cast hr
    norm_num [Numerical.uniformSlack, uniformSlack] at hcast ⊢
    exact hcast
  exact lt_of_lt_of_le hm (lowerLeActual check.expression)

theorem uniformSlackPositive : 0 < uniformSlack := by norm_num [uniformSlack]

theorem allActualRealCosts :
    ∀ check ∈ Numerical.checks, (check.target : ℝ) < evalReal check.expression := by
  intro check hmember
  have h := allActualRealCostsWithSlack check hmember
  linarith [uniformSlackPositive]

/-- All 47 inequalities at the actual real-logarithm parameters, without hypotheses. -/
theorem analyticNumericalCertificate :
    Numerical.checks.length = 47 ∧
    ∀ check ∈ Numerical.checks,
      (check.target : ℝ) + uniformSlack < evalReal check.expression :=
  ⟨Numerical.checkCount, allActualRealCostsWithSlack⟩

theorem realStageIdentities :
    u + v = b ∧ (R : ℝ) * eta = b ∧ (S : ℝ) * eta = u ∧
    e = b + u ∧ exponent = 3 - delta ∧ exponent < previousExponent := by
  norm_num [u, v, e, eta, b, R, S, exponent, delta, previousExponent]

theorem bookkeeping_gt_delta_withSlack : delta + uniformSlack < b - eta := by
  norm_num [delta, uniformSlack, b, eta, R]

theorem bookkeeping_gt_delta : delta < b - eta :=
  lt_trans (lt_add_of_pos_right delta uniformSlackPositive) bookkeeping_gt_delta_withSlack

theorem scalarSaving_zero_withSlack (i : Fin 6) :
    delta + uniformSlack < scalarSaving 0 i := by
  have ht := TEnclosure
  have hg := GEnclosure
  have hq := q1Enclosure
  fin_cases i <;>
    norm_num [scalarSaving, q2, E, Ebox, delta, uniformSlack, b, theta, eta, R] <;>
    linarith [ht.1, ht.2, hg.1, hg.2, hq.1, hq.2]

theorem scalarSaving_u_withSlack (i : Fin 6) :
    delta + uniformSlack < scalarSaving u i := by
  have ht := TEnclosure
  have hg := GEnclosure
  have hq := q1Enclosure
  fin_cases i <;>
    norm_num [scalarSaving, q2, E, Ebox, delta, uniformSlack, b, theta, eta, u, R, S] <;>
    linarith [ht.1, ht.2, hg.1, hg.2, hq.1, hq.2]

theorem cyclicSaving_zero_withSlack (i : Fin 6) :
    delta + uniformSlack < cyclicSaving 0 i := by
  have ht := TEnclosure
  have hg := GEnclosure
  have hq := q1Enclosure
  fin_cases i <;>
    norm_num [cyclicSaving, q2, E, Ebox, delta, uniformSlack, b, theta, eta, u, e, R, S] <;>
    linarith [ht.1, ht.2, hg.1, hg.2, hq.1, hq.2]

theorem cyclicSaving_v_withSlack (i : Fin 6) :
    delta + uniformSlack < cyclicSaving v i := by
  have ht := TEnclosure
  have hg := GEnclosure
  have hq := q1Enclosure
  fin_cases i <;>
    norm_num [cyclicSaving, q2, E, Ebox, delta, uniformSlack, b, theta, eta, u, v, e, R, S] <;>
    linarith [ht.1, ht.2, hg.1, hg.2, hq.1, hq.2]

private theorem affineAbove (a d m x target : ℝ)
    (h0 : target < a) (hm : target < a + d * m)
    (hx0 : 0 ≤ x) (hxm : x ≤ m) : target < a + d * x := by
  by_cases hd : 0 ≤ d
  · have hdx := mul_nonneg hd hx0
    linarith
  · have hdx := mul_le_mul_of_nonpos_left hxm (le_of_not_ge hd)
    linarith

private noncomputable def scalarSlope (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => G - 1
  | 1 => -q1
  | 2 => -q2
  | 3 => -1 / 2 - E
  | 4 => -1 / 2 - Ebox
  | _ => -3 / 2

private noncomputable def cyclicSlope (i : Fin 6) : ℝ :=
  match i.val with
  | 2 => 0
  | _ => -1

private theorem scalarAffine (x : ℝ) (i : Fin 6) :
    scalarSaving x i = scalarSaving 0 i + scalarSlope i * x := by
  fin_cases i <;> norm_num [scalarSaving, scalarSlope] <;> ring

private theorem cyclicAffine (z : ℝ) (i : Fin 6) :
    cyclicSaving z i = cyclicSaving 0 i + cyclicSlope i * z := by
  fin_cases i <;> norm_num [cyclicSaving, cyclicSlope] <;> ring

theorem scalarSaving_gt_delta_withSlack (x : ℝ) (hx0 : 0 ≤ x) (hxu : x ≤ u) (i : Fin 6) :
    delta + uniformSlack < scalarSaving x i := by
  have h0 := scalarSaving_zero_withSlack i
  have hu := scalarSaving_u_withSlack i
  rw [scalarAffine u i] at hu
  rw [scalarAffine x i]
  exact affineAbove _ _ _ _ _ h0 hu hx0 hxu

theorem cyclicSaving_gt_delta_withSlack (z : ℝ) (hz0 : 0 ≤ z) (hzv : z ≤ v) (i : Fin 6) :
    delta + uniformSlack < cyclicSaving z i := by
  have h0 := cyclicSaving_zero_withSlack i
  have hv := cyclicSaving_v_withSlack i
  rw [cyclicAffine v i] at hv
  rw [cyclicAffine z i]
  exact affineAbove _ _ _ _ _ h0 hv hz0 hzv

theorem scalarSaving_gt_delta (x : ℝ) (hx0 : 0 ≤ x) (hxu : x ≤ u) (i : Fin 6) :
    delta < scalarSaving x i := by
  have h := scalarSaving_gt_delta_withSlack x hx0 hxu i
  linarith [uniformSlackPositive]

theorem cyclicSaving_gt_delta (z : ℝ) (hz0 : 0 ≤ z) (hzv : z ≤ v) (i : Fin 6) :
    delta < cyclicSaving z i := by
  have h := cyclicSaving_gt_delta_withSlack z hz0 hzv i
  linarith [uniformSlackPositive]

theorem scalarGeometry_pos (x : ℝ) (hx0 : 0 ≤ x) (hxu : x ≤ u) :
    0 < scalarGeometry x := by
  have ht := TEnclosure
  have h0 : 0 < 1 - b * T := by
    norm_num [b] at *
    linarith [ht.1, ht.2]
  have hu : 0 < 1 - b * T + (1 / 2 - T) * u := by
    norm_num [u, eta, b, R, S] at *
    linarith [ht.1, ht.2]
  have h := affineAbove _ _ _ _ _ h0 hu hx0 hxu
  dsimp [scalarGeometry]
  nlinarith only [h]

theorem cyclicGeometry_pos : 0 < cyclicGeometry := by
  have ht := TEnclosure
  norm_num [cyclicGeometry, e, u, eta, b, R, S]
  linarith [ht.1, ht.2]

/-- Numerical room for a smaller exact-arithmetic allowance. This proves only
the parameter inequality; it does not port a multiplication implementation. -/
theorem arithmeticAllowanceFits :
    (1 / 10^13 : ℝ) * v + (1 / 10^15 : ℝ) < uniformSlack := by
  norm_num [v, eta, b, R, S, uniformSlack]

end ApspBound.Analytic

#print axioms ApspBound.Analytic.analyticNumericalCertificate
#print axioms ApspBound.Analytic.scalarSaving_gt_delta_withSlack
#print axioms ApspBound.Analytic.cyclicSaving_gt_delta_withSlack
