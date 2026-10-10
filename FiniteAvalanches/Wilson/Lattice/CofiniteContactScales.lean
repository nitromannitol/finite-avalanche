import FiniteAvalanches.Probability.Multiscale.Arithmetic

/-! Literal binary scales and the complete preceding-scale error block. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CofiniteContactScales
open FiniteAvalanches.Probability.Multiscale
open scoped BigOperators

/-- The manuscript's scale, including r_0 = 2. -/
def sourceScale (κ i : ℕ) : ℕ := 2 ^ ((6 * κ) ^ i)

theorem sourceScale_two_le (κ i : ℕ) (hκ : 30 ≤ κ) : 2 ≤ sourceScale κ i :=
  le_self_pow₀ (by norm_num) (by positivity : (6 * κ) ^ i ≠ 0)

theorem sourceScale_mono (κ : ℕ) (hκ : 30 ≤ κ) : Monotone (sourceScale κ) := by
  intro i j hij
  exact pow_le_pow_right₀ (by norm_num) (pow_le_pow_right₀ (by omega : 1 ≤ 6 * κ) hij)

theorem sourceScale_succ (κ i : ℕ) :
    sourceScale κ (i + 1) = (sourceScale κ i ^ 6) ^ κ := by
  simp only [sourceScale]
  rw [pow_succ, ← pow_mul, ← pow_mul]

theorem ten_pow_le_sourceScale (κ n : ℕ) (hκ : 30 ≤ κ) (hn : 1 ≤ n) :
    10 ^ κ ≤ sourceScale κ n := by
  have h : 10 ^ κ ≤ sourceScale κ 1 := by
    rw [sourceScale_succ]
    norm_num only [sourceScale, pow_zero, pow_one]
    exact Nat.pow_le_pow_left (by norm_num : 10 ≤ 2 ^ 6) κ
  exact h.trans (sourceScale_mono κ hκ hn)

theorem sourceScale_six_le_next (κ i : ℕ) (hκ : 30 ≤ κ) :
    sourceScale κ i ^ 6 ≤ sourceScale κ (i + 1) := by
  rw [sourceScale_succ]
  exact Nat.le_self_pow (by omega : κ ≠ 0) _

/-- Every escape radius in the actual union fits the stated diameter scale. -/
theorem sourceScale_six_le_diameter_scale (κ n i : ℕ) (hκ : 30 ≤ κ)
    (hn : 1 ≤ n) (hi : i ≤ 2 * n - 2) :
    sourceScale κ i ^ 6 ≤ sourceScale κ (2 * n - 1) :=
  (sourceScale_six_le_next κ i hκ).trans (sourceScale_mono κ hκ (by omega))

theorem sourceHeight_ten_le (κ i : ℕ) (hκ : 30 ≤ κ) :
    10 ≤ sourceScale κ i ^ 6 := by
  have h := Nat.pow_le_pow_left (sourceScale_two_le κ i hκ) 6
  norm_num at h
  omega

theorem four_mul_sourceScale_le (κ i : ℕ) (hκ : 30 ≤ κ) :
    4 * sourceScale κ i ≤ sourceScale κ (i + 1) := by
  have hr := sourceScale_two_le κ i hκ
  have hs : 4 ≤ sourceScale κ i ^ 2 := by nlinarith only [hr]
  have hm := Nat.mul_le_mul_right (sourceScale κ i) hs
  calc
    _ ≤ sourceScale κ i ^ 3 := by simpa only [pow_succ, pow_zero, one_mul] using hm
    _ ≤ (sourceScale κ i ^ 6) ^ κ := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by omega) (by omega : 3 ≤ 6 * κ)
    _ = sourceScale κ (i + 1) := (sourceScale_succ κ i).symm

theorem source_error_halves (κ i : ℕ) (hκ : 30 ≤ κ) :
    (sourceScale κ (i + 1) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      (sourceScale κ i : ℝ) ^ (-(1 / 2 : ℝ)) / 2 := by
  have hr : 0 < (sourceScale κ i : ℝ) := by
    exact_mod_cast (by have h := sourceScale_two_le κ i hκ; omega : 0 < sourceScale κ i)
  have hg : 4 * (sourceScale κ i : ℝ) ≤ (sourceScale κ (i + 1) : ℝ) := by
    exact_mod_cast four_mul_sourceScale_le κ i hκ
  have hfour : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    norm_num
  calc
    _ ≤ (4 * (sourceScale κ i : ℝ)) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hg (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) hr.le, hfour]
      ring

/-- Indices n-1,...,2n-2, with the n=1 warm-up error at radius two. -/
theorem source_error_sum (κ n : ℕ) (hκ : 30 ≤ κ) :
    (∑ i : Fin n, (sourceScale κ (n - 1 + i.val) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      2 * (sourceScale κ (n - 1) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hb := sum_Ico_le_two_mul_of_le_half
    (fun i => (sourceScale κ i : ℝ) ^ (-(1 / 2 : ℝ)))
    (fun i => Real.rpow_nonneg (Nat.cast_nonneg _) _) (source_error_halves κ · hκ) (n - 1) n
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at hb
  simpa only [← Fin.sum_univ_eq_sum_range] using hb

end FiniteAvalanches.Wilson.Lattice.CofiniteContactScales
