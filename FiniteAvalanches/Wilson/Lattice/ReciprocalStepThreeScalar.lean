import FiniteAvalanches.Probability.Multiscale.Scales

/-! The exact square query count and sixth-power localization cost. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.ReciprocalStepThree
open FiniteAvalanches.Probability.Multiscale

/-- At scales at least two, the full square count costs only 128 in the estimate. -/
theorem query_sixth_power_bound (r : ℝ) (hr : 2 ≤ r) :
    (6 * r + 3) ^ 2 * Real.sqrt ((3 * r + 2) / r ^ 6) ≤
      128 * r ^ (-(1 / 2 : ℝ)) := by
  have hr0 : 0 < r := by linarith
  have hc : (6 * r + 3) ^ 2 ≤ 64 * r ^ 2 := by nlinarith
  have hw : Real.sqrt ((3 * r + 2) / r ^ 6) ≤
      2 * Real.sqrt (r / r ^ 6) := by
    calc
      _ ≤ Real.sqrt (4 * (r / r ^ 6)) := Real.sqrt_le_sqrt (by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr0.le _))
      _ = 2 * Real.sqrt (r / r ^ 6) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
  calc
    _ ≤ (64 * r ^ 2) * (2 * Real.sqrt (r / r ^ 6)) :=
      mul_le_mul hc hw (Real.sqrt_nonneg _) (by positivity)
    _ = 128 * (r ^ 2 * Real.sqrt (r / r ^ 6)) := by ring
    _ = 128 * r ^ (-(1 / 2 : ℝ)) := by rw [query_beurling_power r hr0]

/-- Multiplication by the existing universal localization constant preserves uniformity. -/
theorem query_sixth_power_bound_mul (D r : ℝ) (hD : 0 ≤ D) (hr : 2 ≤ r) :
    (6 * r + 3) ^ 2 * D * Real.sqrt ((3 * r + 2) / r ^ 6) ≤
      (128 * D) * r ^ (-(1 / 2 : ℝ)) := by
  calc
    _ = D * ((6 * r + 3) ^ 2 * Real.sqrt ((3 * r + 2) / r ^ 6)) := by ring
    _ ≤ D * (128 * r ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (query_sixth_power_bound r hr) hD
    _ = _ := by ring

end FiniteAvalanches.Wilson.Lattice.ReciprocalStepThree
