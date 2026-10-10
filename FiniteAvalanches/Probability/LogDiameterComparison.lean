import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Comparison of logarithmic decay at two natural-number scales. -/

namespace FiniteAvalanches

/-- Increasing the diameter decreases a negative logarithmic power. Enlarging
the coefficient to `max C 1` makes this comparison valid for every real `C`. -/
theorem mul_log_rpow_neg_le_max_of_nat_le (a C : ℝ) (ha : 0 ≤ a)
    {r d : ℕ} (hrd : r ≤ d) :
    C * Real.rpow (Real.log ((d : ℝ) + 2)) (-a) ≤
      max C 1 * Real.rpow (Real.log ((r : ℝ) + 2)) (-a) := by
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hr1 : 1 < (r : ℝ) + 2 := by linarith only [hr0]
  have hd1 : 1 < (d : ℝ) + 2 := by linarith only [hd0]
  have hrdReal : (r : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hrd
  have hscale : (r : ℝ) + 2 ≤ (d : ℝ) + 2 := by linarith only [hrdReal]
  have hlog : Real.log ((r : ℝ) + 2) ≤ Real.log ((d : ℝ) + 2) :=
    Real.log_le_log (zero_lt_one.trans hr1) hscale
  have hpow : Real.rpow (Real.log ((d : ℝ) + 2)) (-a) ≤
      Real.rpow (Real.log ((r : ℝ) + 2)) (-a) :=
    Real.rpow_le_rpow_of_nonpos (Real.log_pos hr1) hlog (neg_nonpos.mpr ha)
  calc
    _ ≤ max C 1 * Real.rpow (Real.log ((d : ℝ) + 2)) (-a) :=
      mul_le_mul_of_nonneg_right (le_max_left C 1)
        (Real.rpow_nonneg (Real.log_pos hd1).le (-a))
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow
      (zero_le_one.trans (le_max_right C 1))

end FiniteAvalanches
