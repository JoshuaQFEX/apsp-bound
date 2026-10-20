/-
Copyright (c) 2026 Joshua Wharton, QFEX.
Author: Joshua Wharton <joshua@qfex.com>

Analytic numerical certificate for the conditional APSP exponent refinement.
The range-reduction identity and proof arrangement follow the open upstream
ThinMatrix.RealCertificate module from shreshth-s/thin-matrix-results, with new rational
parameters and 40-term enclosures. The analytical remainder bound itself is
proved in Mathlib.Analysis.SpecialFunctions.Log.Deriv.

Each numerical bound is proved inside Lean from the real logarithm. The Python
generator only selects rational endpoints; it is not in the proof's trust base.
-/
import ApspBound.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

namespace ApspBound.Analytic
open scoped BigOperators
noncomputable section

/-- The applications below use 40 terms of this proved positive atanh-series enclosure.
The omitted nonnegative tail is bounded by a rational geometric majorant. -/
theorem atanhLogBounds (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
        ≤ Real.log ((1 + z) / (1 - z)) ∧
    Real.log ((1 + z) / (1 - z)) ≤
      2 * ((∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
        z ^ (2 * n + 1) / (1 - z ^ 2)) := by
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 n
  constructor <;> linarith

theorem logTwoFine :
    (693147180559945309417232121458 / 10^30 : ℝ) < Real.log (2 : ℝ) ∧
    Real.log (2 : ℝ) < (693147180559945309417232121459 / 10^30 : ℝ) := by
  have h := atanhLogBounds (1 / 3 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logC16 :
    (405574466206381144535140895700 / 10^30 : ℝ) < Real.log (16000000000000000 / 10665500244065729 : ℝ) ∧
    Real.log (16000000000000000 / 10665500244065729 : ℝ) < (405574466206381144535140895701 / 10^30 : ℝ) := by
  have h := atanhLogBounds (5334499755934271 / 26665500244065729 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logCComp2 :
    (594695794157380769260934210624 / 10^30 : ℝ) < Real.log (19331000488131458 / 10665500244065729 : ℝ) ∧
    Real.log (19331000488131458 / 10665500244065729 : ℝ) < (594695794157380769260934210625 / 10^30 : ℝ) := by
  have h := atanhLogBounds (8665500244065729 / 29996500732197187 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logD16 :
    (338047137752077978432345089172 / 10^30 : ℝ) < Real.log (373880870520509476 / 266637506101643225 : ℝ) ∧
    Real.log (373880870520509476 / 266637506101643225 : ℝ) < (338047137752077978432345089173 / 10^30 : ℝ) := by
  have h := atanhLogBounds (107243364418866251 / 640518376622152701 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logDComp2 :
    (601428838713867539932064942021 / 10^30 : ℝ) < Real.log (973079806776445531 / 533275012203286450 : ℝ) ∧
    Real.log (973079806776445531 / 533275012203286450 : ℝ) < (601428838713867539932064942022 / 10^30 : ℝ) := by
  have h := atanhLogBounds (439804794573159081 / 1506354818979731981 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logTheta16 :
    (43792151246919381980159120037 / 10^30 : ℝ) < Real.log (6529782369872631 / 6250000000000000 : ℝ) ∧
    Real.log (6529782369872631 / 6250000000000000 : ℝ) < (43792151246919381980159120038 / 10^30 : ℝ) := by
  have h := atanhLogBounds (279782369872631 / 12779782369872631 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logThetaComp2 :
    (625619852105642143314436314929 / 10^30 : ℝ) < Real.log (93470217630127369 / 50000000000000000 : ℝ) ∧
    Real.log (93470217630127369 / 50000000000000000 : ℝ) < (625619852105642143314436314930 / 10^30 : ℝ) := by
  have h := atanhLogBounds (43470217630127369 / 143470217630127369 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- The public logarithm enclosure used in the rational cost ledger. -/
theorem logTwo :
    (693147180559945309417232 / 10^24 : ℝ) < Real.log 2 ∧
    Real.log 2 < (693147180559945309417233 / 10^24 : ℝ) := by
  have h := logTwoFine
  norm_num at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- Range-reduction identity used to place both entropy logarithms in [1,2]
for the chosen parameters. -/
theorem entropyScaled (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    entropy p = (1+3*p)*Real.log 2 - p*Real.log (16*p)
      - (1-p)*Real.log (2*(1-p)) := by
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
  have hmul := Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (ne_of_gt hp)
  have hcomp := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (ne_of_gt (sub_pos.mpr hp1))
  have ha : Real.log p = Real.log (16*p) - 4*Real.log 2 := by
    rw [h16] at hmul
    linarith
  have hb : Real.log (1-p) = Real.log (2*(1-p)) - Real.log 2 := by
    linarith
  rw [entropy, ha, hb]
  ring

theorem entropyC :
    (311152414738582918394308 / 10^24 : ℝ) < entropy (1/c) ∧
    entropy (1/c) < (311152414738582918394309 / 10^24 : ℝ) := by
  have hs := entropyScaled (1/c) (by norm_num [c, theta]) (by norm_num [c, theta])
  have h0 := logTwoFine
  have h1 := logC16
  have h2 := logCComp2
  norm_num [c, theta] at hs ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

theorem entropyD :
    (297038479999443775766554 / 10^24 : ℝ) < entropy ((1-theta)/c) ∧
    entropy ((1-theta)/c) < (297038479999443775766555 / 10^24 : ℝ) := by
  have hs := entropyScaled ((1-theta)/c) (by norm_num [c, theta]) (by norm_num [c, theta])
  have h0 := logTwoFine
  have h1 := logD16
  have h2 := logDComp2
  norm_num [c, theta] at hs ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

theorem entropyTheta :
    (241302418268428879845954 / 10^24 : ℝ) < entropy (theta) ∧
    entropy (theta) < (241302418268428879845955 / 10^24 : ℝ) := by
  have hs := entropyScaled (theta) (by norm_num [c, theta]) (by norm_num [c, theta])
  have h0 := logTwoFine
  have h1 := logTheta16
  have h2 := logThetaComp2
  norm_num [c, theta] at hs ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

/-- The four real-logarithm enclosures, with no enclosure hypotheses. -/
theorem analyticEnclosures :
    ((693147180559945309417232 / 10^24 : ℝ) < Real.log 2 ∧
      Real.log 2 < (693147180559945309417233 / 10^24 : ℝ)) ∧
    ((311152414738582918394308 / 10^24 : ℝ) < entropy (1/c) ∧
      entropy (1/c) < (311152414738582918394309 / 10^24 : ℝ)) ∧
    ((297038479999443775766554 / 10^24 : ℝ) < entropy ((1-theta)/c) ∧
      entropy ((1-theta)/c) < (297038479999443775766555 / 10^24 : ℝ)) ∧
    ((241302418268428879845954 / 10^24 : ℝ) < entropy theta ∧
      entropy theta < (241302418268428879845955 / 10^24 : ℝ)) :=
  ⟨logTwo, entropyC, entropyD, entropyTheta⟩

#print axioms atanhLogBounds
#print axioms analyticEnclosures

end
end ApspBound.Analytic
