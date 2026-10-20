/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Parameter and numerical refinements (c) 2026 Joshua Wharton, QFEX.
Author of modifications: Joshua Wharton <joshua@qfex.com>
-/
module

public import Submission.ThreeSumApsp.Pruned.Costs
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Refined numbers for `c = 20`, `θ = 5656907/50000000`

The logarithms are proved from forty terms of the positive atanh series, with
Mathlib's geometric remainder bound. Python selected the rational endpoints;
it supplies no assumptions to Lean. The public bounds are
`Γ > 0.06602549498`, `q < 0.43397449436`, and `19 ln 3 / ln 4 < 15.057143757`.
The coarser, unchanged `κ < 2.9` certificate retains ample slack.

This module refines the certificate by Hrishik Sai Bojnal (fringewidth), built
on Li Xuanji's deterministic batched APSP proof and the Anthropic development.
-/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

namespace ThreeSumApsp
open scoped BigOperators

private theorem refinedAtanhLogBounds (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
        ≤ Real.log ((1 + z) / (1 - z)) ∧
    Real.log ((1 + z) / (1 - z)) ≤
      2 * ((∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
        z ^ (2 * n + 1) / (1 - z ^ 2)) := by
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 n
  constructor <;> linarith

private theorem fineLogTwo :
    (693147180559945309417232 / 10^24 : ℝ) < Real.log (2 : ℝ) ∧
    Real.log (2 : ℝ) < (693147180559945309417233 / 10^24 : ℝ) := by
  have h := refinedAtanhLogBounds (1 / 3 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem fineLogThreeHalf :
    (405465108108164381978013 / 10^24 : ℝ) < Real.log (3 / 2 : ℝ) ∧
    Real.log (3 / 2 : ℝ) < (405465108108164381978014 / 10^24 : ℝ) := by
  have h := refinedAtanhLogBounds (1 / 5 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem fineLogCompTwice :
    (573081133314703071200848 / 10^24 : ℝ) < Real.log (44343093 / 25000000 : ℝ) ∧
    Real.log (44343093 / 25000000 : ℝ) < (573081133314703071200849 / 10^24 : ℝ) := by
  have h := refinedAtanhLogBounds (19343093 / 69343093 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem fineLogNearOne :
    (5936980151365743127724 / 10^24 : ℝ) < Real.log (955656907 / 950000000 : ℝ) ∧
    Real.log (955656907 / 950000000 : ℝ) < (5936980151365743127725 / 10^24 : ℝ) := by
  have h := refinedAtanhLogBounds (5656907 / 1905656907 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem fineLogTheta16 :
    (593442993228432596191592 / 10^24 : ℝ) < Real.log (5656907 / 3125000 : ℝ) ∧
    Real.log (5656907 / 3125000 : ℝ) < (593442993228432596191593 / 10^24 : ℝ) := by
  have h := refinedAtanhLogBounds (2531907 / 8781907 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem fineLogHighOver16 :
    (177787237078024965467822 / 10^24 : ℝ) < Real.log (955656907 / 800000000 : ℝ) ∧
    Real.log (955656907 / 800000000 : ℝ) < (177787237078024965467823 / 10^24 : ℝ) := by
  have h := refinedAtanhLogBounds (155656907 / 1755656907 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem refinedLogSixteen : Real.log 16 = 4 * Real.log 2 := by
  convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num

private lemma logB_a : Real.log (44343093 / 50000000 : ℝ) ∈
    Set.Icc (-12006604724524223822 / 10^20 : ℝ) (-12006604724524223821 / 10^20 : ℝ) := by
  have hr := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by norm_num : (44343093 / 50000000 : ℝ) ≠ 0)
  norm_num at hr
  have h1 := fineLogCompTwice
  have h2 := fineLogTwo
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma logB_b : Real.log (955656907 / 950000000 : ℝ) ∈
    Set.Icc (593698015136574312 / 10^20 : ℝ) (593698015136574313 / 10^20 : ℝ) := by
  have h1 := fineLogNearOne
  have h2 := fineLogTwo
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma logB_c : Real.log (955656907 / 50000000 : ℝ) ∈
    Set.Icc (295037595931780620313 / 10^20 : ℝ) (295037595931780620314 / 10^20 : ℝ) := by
  have hr := Real.log_mul (by norm_num : (16 : ℝ) ≠ 0)
    (by norm_num : (955656907 / 800000000 : ℝ) ≠ 0)
  rw [refinedLogSixteen] at hr
  norm_num at hr
  have h1 := fineLogHighOver16
  have h2 := fineLogTwo
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma logB_3 : Real.log (3 : ℝ) ∈
    Set.Icc (109861228866810969139 / 10^20 : ℝ) (109861228866810969140 / 10^20 : ℝ) := by
  have hr := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by norm_num : (3 / 2 : ℝ) ≠ 0)
  norm_num at hr
  have h1 := fineLogThreeHalf
  have h2 := fineLogTwo
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma logB_theta : Real.log (5656907 / 50000000 : ℝ) ∈
    Set.Icc (-217914572901134864148 / 10^20 : ℝ) (-217914572901134864147 / 10^20 : ℝ) := by
  have hr := Real.log_mul (by norm_num : (16 : ℝ) ≠ 0)
    (by norm_num : (5656907 / 50000000 : ℝ) ≠ 0)
  rw [refinedLogSixteen] at hr
  norm_num at hr
  have h1 := fineLogTheta16
  have h2 := fineLogTwo
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma logB_9 : Real.log (9 : ℝ) ∈
    Set.Icc (219722457733621938278 / 10^20 : ℝ) (219722457733621938281 / 10^20 : ℝ) := by
  rw [Real.log_nine]
  have h := logB_3
  constructor <;> linarith [h.1, h.2]

private lemma logB_4 : Real.log (4 : ℝ) ∈
    Set.Icc (138629436111989061882 / 10^20 : ℝ) (138629436111989061885 / 10^20 : ℝ) := by
  rw [Real.log_four]
  have h := fineLogTwo
  constructor <;> linarith [h.1, h.2]

private lemma logB_19 : Real.log 19 ∈ Set.Icc 2.94443897 2.94443899 :=
  ⟨le_trans (by numerics) (log_mem 4 8).1, (log_mem 4 8).2.trans (by numerics)⟩

private lemma logB_20 : Real.log 20 ∈ Set.Icc 2.99573226 2.99573228 :=
  ⟨le_trans (by numerics) (log_mem 4 8).1, (log_mem 4 8).2.trans (by numerics)⟩

/-- Cancellation of the large entropy terms, exactly at the new rational point. -/
private lemma GammaOf_B_eq :
    GammaOf 20 (5656907 / 50000000) * Real.log 4
      = 44343093 / 50000000 * Real.log (44343093 / 50000000)
        + 19 * Real.log (955656907 / 950000000)
        + 5656907 / 50000000 * Real.log (955656907 / 50000000)
        - 5656907 / 50000000 * Real.log 9 := by
  rw [GammaOf_mul_log_four (by norm_num) (by norm_num) (by norm_num)]
  have h1 : (1 : ℝ) - 5656907 / 50000000 = 44343093 / 50000000 := by norm_num
  have h2 : (20 : ℝ) - 1 + 5656907 / 50000000 = 955656907 / 50000000 := by norm_num
  have h3 : (20 : ℝ) - 1 = 19 := by norm_num
  rw [h1, h2, h3, show (955656907 / 950000000 : ℝ) = (955656907 / 50000000) / 19 by
    norm_num, Real.log_div (x := 955656907 / 50000000) (y := 19) (by norm_num) (by norm_num)]
  ring

/-- The certified lower bound used for preprocessing boxes. -/
theorem GammaOf_B : (0.06602549498 : ℝ) < GammaOf 20 (5656907 / 50000000) := by
  refine lt_of_mul_lt_mul_right ?_ log_four_pos.le
  rw [GammaOf_B_eq]
  have h1 := logB_a; have h2 := logB_b; have h3 := logB_c; have h4 := logB_9
  have h5 := logB_4
  simp only [Set.mem_Icc] at *
  linarith

/-- A coarse upper bound required by the unchanged tensor geometry. -/
theorem GammaOf_B_lt : GammaOf 20 (5656907 / 50000000) < (0.0661 : ℝ) := by
  refine lt_of_mul_lt_mul_right ?_ log_four_pos.le
  rw [GammaOf_B_eq]
  have h1 := logB_a; have h2 := logB_b; have h3 := logB_c; have h4 := logB_9
  have h5 := logB_4
  simp only [Set.mem_Icc] at *
  linarith

theorem GammaOf_B_pos : 0 < GammaOf 20 (5656907 / 50000000) :=
  lt_trans (by norm_num) GammaOf_B

/-- The certified upper bound used for queries. -/
theorem qOf_B : qOf (5656907 / 50000000) < (0.43397449436 : ℝ) := by
  unfold qOf entropy
  rw [div_lt_iff₀ log_four_pos]
  have h1 := logB_theta; have h2 := logB_a; have h3 := logB_9; have h4 := logB_4
  norm_num only [show (1 : ℝ) - 5656907 / 50000000 = 44343093 / 50000000 by norm_num]
  simp only [Set.mem_Icc] at *
  linarith

/-- The certified upper bound used for pruned encodings. -/
theorem bExp_B : 19 * Real.log 3 / Real.log 4 < (15.057143757 : ℝ) := by
  rw [div_lt_iff₀ log_four_pos]
  have h3 := logB_3; have h5 := logB_4
  simp only [Set.mem_Icc] at *
  linarith

/-- The unchanged, coarse binomial coefficient bound. -/
theorem kappa_B : 20 * entropy (1 / 20) / Real.log 4 < (2.9 : ℝ) := by
  rw [div_lt_iff₀ log_four_pos, PrunedAux.mul_entropy_inv (by norm_num)]
  have h1 := logB_19; have h2 := logB_20; have h5 := logB_4
  simp only [Set.mem_Icc] at *
  norm_num
  linarith

end ThreeSumApsp
