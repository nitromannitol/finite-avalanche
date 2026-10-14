import FiniteAvalanches.Probability.Multiscale.ScaleExponent
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

namespace FiniteAvalanches.Probability.CurrentScale

/-- An elementary natural power bound for the incoming forcing term. -/
theorem square_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show 4 + (m + 1) = (4 + m) + 1 by omega, pow_succ (2 : ℕ) (4 + m)]
    have hm : 4 ≤ 4 + m := by omega
    have hprev := ih hm
    nlinarith only [hprev, hm]

/-- The actual source superexponential error is dominated by b times b^-i. -/
theorem scale_error_le_geometric (b i : ℕ) (hb : 6 ≤ b) (hi : 2 ≤ i) :
    Real.rpow (scale b (i - 1) : ℝ) (-(1 / 2 : ℝ)) ≤
      (b : ℝ) / (b : ℝ) ^ i := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hk : 4 ≤ b ^ (i - 1) := by
    have hp : b ≤ b ^ (i - 1) := by
      simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ b)
        (by omega : 1 ≤ i - 1)
    omega
  have hs : ((b : ℝ) ^ (i - 1)) ^ 2 ≤ (scale b (i - 1) : ℝ) := by
    exact_mod_cast square_le_two_pow (b ^ (i - 1)) hk
  have hroot : (b : ℝ) ^ (i - 1) ≤ Real.sqrt (scale b (i - 1) : ℝ) := by
    have h := Real.sqrt_le_sqrt hs
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hb0.le _)] using h
  have hpos : 0 < (b : ℝ) ^ (i - 1) := pow_pos hb0 _
  rw [Real.rpow_eq_pow, Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]
  calc
    _ ≤ ((b : ℝ) ^ (i - 1))⁻¹ := inv_anti₀ hpos hroot
    _ = (b : ℝ) / (b : ℝ) ^ i := by
      have he : i = (i - 1) + 1 := by omega
      rw [he, Nat.add_sub_cancel, pow_succ]
      field_simp

/-- Both exact forcing terms have one coefficient before every scale index. -/
theorem source_forcing_le_geometric (b : ℕ) (hb : 6 ≤ b) (A : ℝ) (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 < D ∧ ∀ i : ℕ, 2 ≤ i →
      16 / Real.log (scale b i : ℝ) +
        A * Real.rpow (scale b (i - 1) : ℝ) (-(1 / 2 : ℝ)) ≤
          D / (b : ℝ) ^ i := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨16 / Real.log 2 + A * b,
    add_pos_of_pos_of_nonneg (div_pos (by norm_num) hlog) (mul_nonneg hA hb0.le), ?_⟩
  intro i hi
  have he := mul_le_mul_of_nonneg_left (scale_error_le_geometric b i hb hi) hA
  have hp : (b : ℝ) ^ i ≠ 0 := (pow_pos hb0 i).ne'
  rw [log_scale]
  calc
    _ ≤ 16 / ((b : ℝ) ^ i * Real.log 2) + A * ((b : ℝ) / (b : ℝ) ^ i) :=
      add_le_add le_rfl he
    _ = (16 / Real.log 2 + A * b) / (b : ℝ) ^ i := by
      field_simp [hp, hlog.ne']

end FiniteAvalanches.Probability.CurrentScale
