/-
Copyright (c) 2026 Joshua Wharton, QFEX.
Author: Joshua Wharton <joshua@qfex.com>

Exact parameters and real-valued cost formulas for the published APSP
numerical refinement. The parameters are rational; entropy uses Real.log.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ApspBound.Analytic

noncomputable def c : ℝ := 10665500244065729 / 1000000000000000
noncomputable def theta : ℝ := 6529782369872631 / 100000000000000000
noncomputable def b : ℝ := 46046352103722105 / 1000000000000000000
def R : ℕ := 1000000000000
def S : ℕ := 768979037380
noncomputable def delta : ℝ := 70520812906 / 10000000000000
noncomputable def uniformSlack : ℝ := 2 / 100000000000000
noncomputable def exponent : ℝ := 29929479187094 / 10000000000000
noncomputable def previousExponent : ℝ := 299294792 / 100000000
noncomputable def eta : ℝ := b / (R : ℝ)
noncomputable def u : ℝ := (S : ℝ) * eta
noncomputable def v : ℝ := ((R - S : ℕ) : ℝ) * eta
noncomputable def e : ℝ := b + u

noncomputable def entropy (x : ℝ) : ℝ :=
  -x * Real.log x - (1 - x) * Real.log (1 - x)

noncomputable def CK : ℝ := c * entropy (1 / c) / Real.log 4
noncomputable def T : ℝ := c - 1 + CK
noncomputable def G : ℝ :=
  (c * entropy (1 / c) - c * entropy ((1 - theta) / c) - theta * Real.log 4) /
    Real.log 2
noncomputable def q1 : ℝ := entropy theta / Real.log 2
noncomputable def q2 : ℝ := q1 + 2 * theta
noncomputable def E : ℝ := T + q1
noncomputable def Ebox : ℝ := T - G

/-- Savings below cubic time, in the six cost categories of the written reduction. -/
noncomputable def scalarSaving (x : ℝ) (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => b - x + (b + x) * G - eta
  | 1 => b - (b + x) * q1 - eta
  | 2 => b - (b + x) * q2 - eta
  | 3 => 1 + b - x / 2 - (b + x) * E - eta
  | 4 => 1 + b - x / 2 - (b + x) * Ebox - eta
  | _ => 1 - 3 * x / 2 - eta

noncomputable def cyclicSaving (z : ℝ) (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => b - u - z + e * G - eta
  | 1 => b - z - e * q1 - eta
  | 2 => b - e * q2 - eta
  | 3 => 1 + b - u / 2 - z - e * E - eta
  | 4 => 1 + b - u / 2 - z - e * Ebox - eta
  | _ => 1 - 3 * u / 2 - z - eta

noncomputable def scalarGeometry (x : ℝ) : ℝ := 1 + x / 2 - (b + x) * T
noncomputable def cyclicGeometry : ℝ := 1 + u / 2 - e * T

end ApspBound.Analytic
