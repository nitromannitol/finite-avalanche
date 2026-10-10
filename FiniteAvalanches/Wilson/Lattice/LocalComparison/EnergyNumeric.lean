import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
namespace LocalEnergyNumeric
open scoped BigOperators

theorem log_half_le_harmonic_half (r : ℕ) :
    Real.log (r : ℝ)/2 ≤ ∑ j ∈ Finset.Icc 1 r, 1/(2*(j : ℝ)) := by
  have h := log_le_harmonic_floor (r : ℝ) (Nat.cast_nonneg r)
  simp only [Nat.floor_natCast,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at h
  calc
    Real.log (r : ℝ)/2 ≤ (∑ j ∈ Finset.Icc 1 r, (j : ℝ)⁻¹)/2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = ∑ j ∈ Finset.Icc 1 r, 1/(2*(j : ℝ)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      simp only [div_eq_mul_inv,mul_inv_rev,one_mul]

theorem thirty_two_le_log_half (r : ℕ) (hr : 10^30 ≤ r) : 32 ≤ Real.log (r : ℝ)/2 := by
  have hpow : 2^96 ≤ r := (by norm_num : 2^96 ≤ (10:ℕ)^30).trans hr
  have hpowReal : (2:ℝ)^96 ≤ r := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < 2^96) hpowReal
  rw [Real.log_pow] at hlog
  have htwo : (2/3:ℝ) ≤ Real.log 2 := by
    exact (by norm_num : (2/3:ℝ) ≤ 0.6931471803).trans Real.log_two_gt_d9.le
  norm_num at hlog
  linarith only [hlog,htwo]

end LocalEnergyNumeric
