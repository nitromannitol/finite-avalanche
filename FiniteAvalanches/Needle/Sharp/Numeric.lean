import FiniteAvalanches.Needle.ConnectedSetApplication
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Needle107Numeric
open scoped BigOperators

lemma log_two_lower : (69 / 100 : ℝ) ≤ Real.log 2 := by
  linarith only [Real.log_two_gt_d9]

lemma log_ten_lower : (23 / 10 : ℝ) ≤ Real.log 10 := by
  have hfive := Real.sum_range_le_log_div (x := (1/9 : ℝ)) (by norm_num)
    (by norm_num) 1
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, Nat.cast_one, pow_one] at hfive
  have htwo := Real.log_two_gt_d9
  have hlog : Real.log 10 = 3 * Real.log 2 + Real.log (5/4 : ℝ) := by
    rw [show (10 : ℝ) = 2^3 * (5/4) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  linarith only [hfive, htwo, hlog]

/-- The numerical last step in the current source proof, without any network premise. -/
theorem source_dyadic_bound (h : ℕ) (hh : 10 ≤ h) :
    32 + 64 * (Real.log h / Real.log 2) ≤ 107 * Real.log h := by
  have hcast : (10 : ℝ) ≤ h := by exact_mod_cast hh
  have hL : (23 / 10 : ℝ) ≤ Real.log h :=
    log_ten_lower.trans (Real.log_le_log (by norm_num) hcast)
  have h2 := log_two_lower
  have hd : Real.log h / Real.log 2 ≤ (100/69 : ℝ) * Real.log h := by
    apply (div_le_iff₀ (by linarith only [h2])).mpr
    nlinarith only [mul_nonneg (by linarith only [hL] : 0 ≤ Real.log h)
      (by linarith only [h2] : 0 ≤ Real.log 2 - 69/100)]
  linarith only [hd, hL]

/-- Literal comparison required to specialize the existing production bound is false. -/
theorem existing_log_constant_obstruction (h : ℕ) (hh : 10 ≤ h) :
    ¬ (3840 * Real.log ((h : ℝ) + 2) ≤ 107 * Real.log h) := by
  have hcast : (10 : ℝ) ≤ h := by exact_mod_cast hh
  have hpos : 0 < Real.log h := Real.log_pos (by linarith only [hcast])
  have hmono : Real.log h ≤ Real.log ((h : ℝ) + 2) :=
    Real.log_le_log (by linarith only [hcast]) (by linarith)
  intro he
  linarith only [he, hmono, hpos]

/-- Even an optimal harmonic-to-log conversion cannot repair the coefficient 960. -/
theorem harmonic_coefficient_obstruction (h : ℕ) (hh : 10 ≤ h) :
    ¬ (960 * Real.log h ≤ 107 * Real.log h) := by
  have hcast : (10 : ℝ) ≤ h := by exact_mod_cast hh
  have hpos : 0 < Real.log h := Real.log_pos (by linarith only [hcast])
  intro he
  linarith only [he, hpos]

end Needle107Numeric
