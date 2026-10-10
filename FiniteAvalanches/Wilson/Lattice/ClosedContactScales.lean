import FiniteAvalanches.Wilson.Lattice.CofiniteContactScales

/-! A strict larger integer test radius preserves the original binary error scales. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.ClosedContactScales
open CofiniteContactScales

theorem sourceScale_add_one_le_next (κ i : ℕ) (hκ : 30 ≤ κ) :
    sourceScale κ i + 1 ≤ sourceScale κ (i + 1) := by
  have h := four_mul_sourceScale_le κ i hκ
  have hr := sourceScale_two_le κ i hκ
  omega

theorem source_threshold_lt_padded (κ n : ℕ) (hκ : 30 ≤ κ) :
    (1 / 16 : ℝ) * Real.log (sourceScale κ n : ℝ) <
      (1 / 16 : ℝ) * Real.log (sourceScale κ n + 1 : ℕ) := by
  apply mul_lt_mul_of_pos_left _ (by norm_num)
  apply Real.log_lt_log
  · exact_mod_cast (by have h := sourceScale_two_le κ n hκ; omega : 0 < sourceScale κ n)
  · exact_mod_cast Nat.lt_succ_self (sourceScale κ n)

/-- A universal D>=1 covers the warm-up-only case n=1. -/
theorem initial_error_ge_one (D : ℝ) (hD : 1 ≤ D) :
    1 ≤ 2 * D * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hfour : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    norm_num
  have hm := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≤ 4) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  rw [hfour] at hm
  have hnon : 0 ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  nlinarith only [hD, hm, hnon]

end FiniteAvalanches.Wilson.Lattice.ClosedContactScales
