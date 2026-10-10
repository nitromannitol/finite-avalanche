import FiniteAvalanches.Probability.Multiscale.StepSixArithmetic

/-! Diameter conversion using the binary scales themselves. -/

set_option autoImplicit false

namespace FiniteAvalanches.Probability.Multiscale.StepSixIncoming

open FiniteAvalanches.Probability.Multiscale

/-- The next binary block bounds every admissible index. -/
theorem binary_block_maximal (P n j : ℕ) (hP : 1 ≤ P) (R : ℝ)
    (hnext : R < 16 * (lateScale 2 P (2 * n + 1) : ℝ))
    (hj : 16 * (lateScale 2 P (2 * j - 1) : ℝ) ≤ R) : j ≤ n := by
  by_contra h
  have hidx : 2 * n + 1 ≤ 2 * j - 1 := by omega
  have hr : (lateScale 2 P (2 * n + 1) : ℝ) ≤ lateScale 2 P (2 * j - 1) := by
    exact_mod_cast lateScale_mono 2 P (by norm_num) hP hidx
  linarith

/-- The largest index for the exact condition `16 r_(2n-1) ≤ R`. -/
theorem exists_binary_block (P : ℕ) (hP : 2 ≤ P) (R : ℝ)
    (hlarge : 16 * (lateScale 2 P 1 : ℝ) ≤ R) :
    ∃ n : ℕ, 1 ≤ n ∧ 16 * (lateScale 2 P (2 * n - 1) : ℝ) ≤ R ∧
      R < 16 * (lateScale 2 P (2 * n + 1) : ℝ) ∧
      ∀ j : ℕ, 16 * (lateScale 2 P (2 * j - 1) : ℝ) ≤ R → j ≤ n := by
  have hex : ∃ n : ℕ, R < 16 * (lateScale 2 P (2 * n + 1) : ℝ) := by
    obtain ⟨n, hn⟩ := exists_nat_gt R
    have hi := StepSix.index_add_two_le_binary_scale P (2 * n + 1) hP
    have hcast : (n : ℝ) ≤ lateScale 2 P (2 * n + 1) := by
      exact_mod_cast (show n ≤ lateScale 2 P (2 * n + 1) by omega)
    exact ⟨n, by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
  let n := Nat.find hex
  have hnext : R < 16 * (lateScale 2 P (2 * n + 1) : ℝ) := Nat.find_spec hex
  have hn : 1 ≤ n := by
    by_contra h
    have hz : n = 0 := by omega
    simp only [hz, mul_zero, zero_add] at hnext
    linarith
  have hprev := Nat.find_min hex (show n - 1 < Nat.find hex by dsimp [n]; omega)
  have heq : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  rw [heq] at hprev
  exact ⟨n, hn, le_of_not_gt hprev, hnext,
    fun j hj => binary_block_maximal P n j (by omega) R hnext hj⟩

/-- The upper threshold uses `r_(2n+1)`, with no localization power. -/
theorem log_radius_le_next_binary_block (P n : ℕ) (hP : 2 ≤ P)
    (R : ℝ) (hR : 0 ≤ R) (hnext : R < 16 * (lateScale 2 P (2 * n + 1) : ℝ)) :
    Real.log (R + 2) ≤ (Real.log 18 + Real.log 2) * (P : ℝ) ^ (2 * n + 2) := by
  have hr : (1 : ℝ) ≤ lateScale 2 P (2 * n + 1) := by
    exact_mod_cast (show 1 ≤ lateScale 2 P (2 * n + 1) from
      (by norm_num : 1 ≤ (2 : ℕ)).trans (le_lateScale 2 P _ (by norm_num) (by omega)))
  have hlog := Real.log_le_log (by linarith : 0 < R + 2)
    (show R + 2 ≤ 18 * (lateScale 2 P (2 * n + 1) : ℝ) by linarith)
  rw [Real.log_mul (by norm_num : (18 : ℝ) ≠ 0) (by linarith :
      (lateScale 2 P (2 * n + 1) : ℝ) ≠ 0), log_lateScale] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hpow : (P : ℝ) ^ (2 * n + 1) ≤ (P : ℝ) ^ (2 * n + 2) :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ P by omega)) (by omega)
  have hone : (1 : ℝ) ≤ (P : ℝ) ^ (2 * n + 2) :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ P by omega))
  have hl2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hl18 : 0 ≤ Real.log (18 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith only [hlog, mul_le_mul_of_nonneg_left hpow hl2,
    mul_le_mul_of_nonneg_left hone hl18]

/-- A positive uniform constant also covers every diameter below `16 r_1`. -/
theorem binary_log_constant_pos (P : ℕ) (p M : ℝ) (hp : p ≤ 1 / 2) (hM : 0 ≤ M) :
    0 < (Real.log (16 * (lateScale 2 P 1 : ℝ) + 2)) ^ contactExponent p P +
      M * (Real.log 18 + Real.log 2) ^ contactExponent p P / (1 - p) := by
  have hr : (0 : ℝ) ≤ lateScale 2 P 1 := Nat.cast_nonneg _
  have hB : 0 < Real.log (16 * (lateScale 2 P 1 : ℝ) + 2) := Real.log_pos (by linarith)
  have hq : 0 < 1 - p := by linarith
  have hA : 0 ≤ Real.log 18 + Real.log 2 :=
    add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num))
  exact add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hB _)
    (div_nonneg (mul_nonneg hM (Real.rpow_nonneg hA _)) hq.le)

/-- Scalar block bounds at the exact binary admissibility imply logarithmic decay. -/
theorem le_log_power_of_binary_blocks (P : ℕ) (p M : ℝ)
    (hP : 2 ≤ P) (hp : 0 < p) (hp' : p ≤ 1 / 2) (hM : 0 ≤ M)
    (R y : ℝ) (hR : 0 ≤ R) (hy : y ≤ 1)
    (hblock : ∀ n : ℕ, 1 ≤ n → 16 * (lateScale 2 P (2 * n - 1) : ℝ) ≤ R →
      y ≤ M * (1 - p) ^ n) :
    y ≤ ((Real.log (16 * (lateScale 2 P 1 : ℝ) + 2)) ^ contactExponent p P +
      M * (Real.log 18 + Real.log 2) ^ contactExponent p P / (1 - p)) *
      (Real.log (R + 2)) ^ (-contactExponent p P) := by
  have ha := contactExponent_pos p P hp hp' hP
  have hA : 0 < Real.log 18 + Real.log 2 :=
    add_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  have hterm : 0 ≤ (Real.log (R + 2)) ^ (-contactExponent p P) :=
    Real.rpow_nonneg (Real.log_pos (by linarith)).le _
  by_cases hlarge : 16 * (lateScale 2 P 1 : ℝ) ≤ R
  · obtain ⟨n, hn, hprev, hnext, _⟩ := exists_binary_block P hP R hlarge
    have hb := hblock n hn hprev
    have hc := geometric_le_log_power p (Real.log 18 + Real.log 2)
      (Real.log (R + 2)) P n hp hp' hP hA (Real.log_pos (by linarith))
      (log_radius_le_next_binary_block P n hP R hR hnext)
    have hx := mul_le_mul_of_nonneg_left hc hM
    have hnterm : 0 ≤ (Real.log (16 * (lateScale 2 P 1 : ℝ) + 2)) ^
        contactExponent p P :=
      Real.rpow_nonneg (Real.log_nonneg (by
        have h0 : (0 : ℝ) ≤ lateScale 2 P 1 := Nat.cast_nonneg _
        linarith)) _
    simp only [div_eq_mul_inv] at hx ⊢
    nlinarith only [hb, hx, mul_nonneg hnterm hterm]
  · have hc := one_le_log_power (contactExponent p P) R
      (16 * (lateScale 2 P 1 : ℝ)) ha.le hR (le_of_not_ge hlarge)
    have hq : 0 < 1 - p := by linarith
    have hnterm : 0 ≤ M * (Real.log 18 + Real.log 2) ^ contactExponent p P /
        (1 - p) := div_nonneg (mul_nonneg hM (Real.rpow_nonneg hA.le _)) hq.le
    nlinarith only [hy, hc, mul_nonneg hnterm hterm]

end FiniteAvalanches.Probability.Multiscale.StepSixIncoming
