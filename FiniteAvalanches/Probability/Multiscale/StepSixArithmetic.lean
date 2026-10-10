import FiniteAvalanches.Probability.Multiscale.Logarithm
import FiniteAvalanches.Probability.Multiscale.Scales

/-! Diameter conversion at the literal binary scales. -/

set_option autoImplicit false

namespace FiniteAvalanches.Probability.Multiscale.StepSix

open FiniteAvalanches.Probability.Multiscale

/-- Binary scales escape every finite index even at their initial value two. -/
theorem index_add_two_le_binary_scale (P i : ℕ) (hP : 2 ≤ P) :
    i + 2 ≤ lateScale 2 P i := by
  induction i with
  | zero => simp only [lateScale, pow_zero, pow_one]; omega
  | succ i ih =>
    have hr : 2 ≤ lateScale 2 P i := le_lateScale 2 P i (by norm_num) (by omega)
    have hsquare : lateScale 2 P i + 1 ≤ lateScale 2 P i ^ 2 := by nlinarith
    have hstep : lateScale 2 P i + 1 ≤ lateScale 2 P (i + 1) := by
      rw [lateScale_succ]
      exact hsquare.trans (pow_le_pow_right₀ (by omega) hP)
    omega

/-- The largest admissible binary block has the exact next-block upper bound. -/
theorem exists_binary_block (P : ℕ) (hP : 2 ≤ P) (R : ℝ)
    (hlarge : 16 * (lateHeight 2 P 1 : ℝ) ≤ R) :
    ∃ n : ℕ, 1 ≤ n ∧ 16 * (lateHeight 2 P (2 * n - 1) : ℝ) ≤ R ∧
      R < 16 * (lateHeight 2 P (2 * n + 1) : ℝ) ∧
      ∀ j : ℕ, 16 * (lateHeight 2 P (2 * j - 1) : ℝ) ≤ R → j ≤ n := by
  have hex : ∃ n : ℕ, R < 16 * (lateHeight 2 P (2 * n + 1) : ℝ) := by
    obtain ⟨n, hn⟩ := exists_nat_gt R
    have hi := index_add_two_le_binary_scale P (2 * n + 1) hP
    have hnat : n ≤ lateHeight 2 P (2 * n + 1) := by
      have hr : 1 ≤ lateScale 2 P (2 * n + 1) := by omega
      exact (show n ≤ lateScale 2 P (2 * n + 1) by omega).trans
        (le_self_pow₀ hr (by norm_num : (6 : ℕ) ≠ 0))
    have hcast : (n : ℝ) ≤ lateHeight 2 P (2 * n + 1) := by exact_mod_cast hnat
    exact ⟨n, by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
  let n := Nat.find hex
  have hnext : R < 16 * (lateHeight 2 P (2 * n + 1) : ℝ) := Nat.find_spec hex
  have hn : 1 ≤ n := by
    by_contra h
    have hz : n = 0 := by omega
    simp only [hz, mul_zero, zero_add] at hnext
    linarith
  have hprev := Nat.find_min hex (show n - 1 < Nat.find hex by dsimp [n]; omega)
  have heq : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  rw [heq] at hprev
  exact ⟨n, hn, le_of_not_gt hprev, hnext,
    fun j hj => late_block_maximal 2 P n j (by norm_num) (by omega) R hnext hj⟩

/-- A scalar block bound yields the logarithmic diameter bound with a fixed
constant, including every radius below the first admissible block. -/
theorem le_log_power_of_binary_blocks (P : ℕ) (p M : ℝ)
    (hP : 2 ≤ P) (hp : 0 < p) (hp' : p ≤ 1 / 2) (hM : 0 ≤ M)
    (R y : ℝ) (hR : 0 ≤ R) (hy : y ≤ 1)
    (hblock : ∀ n : ℕ, 1 ≤ n → 16 * (lateHeight 2 P (2 * n - 1) : ℝ) ≤ R →
      y ≤ M * (1 - p) ^ n) :
    y ≤ ((Real.log (16 * (lateHeight 2 P 1 : ℝ) + 2)) ^ contactExponent p P +
      M * (Real.log 18 + 6 * Real.log 2) ^ contactExponent p P / (1 - p)) *
      (Real.log (R + 2)) ^ (-contactExponent p P) := by
  have ha := contactExponent_pos p P hp hp' hP
  have hA : 0 < Real.log 18 + 6 * Real.log 2 := by
    have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hl18 := Real.log_pos (by norm_num : (1 : ℝ) < 18)
    linarith
  have hterm : 0 ≤ (Real.log (R + 2)) ^ (-contactExponent p P) :=
    Real.rpow_nonneg (Real.log_pos (by linarith)).le _
  by_cases hlarge : 16 * (lateHeight 2 P 1 : ℝ) ≤ R
  · obtain ⟨n, hn, hprev, hnext, _⟩ := exists_binary_block P hP R hlarge
    have hb := hblock n hn hprev
    have hc := geometric_le_log_power p (Real.log 18 + 6 * Real.log 2)
      (Real.log (R + 2)) P n hp hp' hP hA (Real.log_pos (by linarith))
      (log_radius_le_next_block 2 P n (by norm_num) hP R hR hnext)
    have hx := mul_le_mul_of_nonneg_left hc hM
    have hnterm : 0 ≤ (Real.log (16 * (lateHeight 2 P 1 : ℝ) + 2)) ^
        contactExponent p P :=
      Real.rpow_nonneg (Real.log_nonneg (by
        have h0 : (0 : ℝ) ≤ lateHeight 2 P 1 := Nat.cast_nonneg _
        linarith)) _
    simp only [div_eq_mul_inv] at hx ⊢
    nlinarith only [hb, hx, mul_nonneg hnterm hterm]
  · have hc := one_le_log_power (contactExponent p P) R
      (16 * (lateHeight 2 P 1 : ℝ)) ha.le hR (le_of_not_ge hlarge)
    have hq : 0 < 1 - p := by linarith
    have hnterm : 0 ≤ M * (Real.log 18 + 6 * Real.log 2) ^ contactExponent p P /
        (1 - p) := div_nonneg (mul_nonneg hM (Real.rpow_nonneg hA.le _)) hq.le
    nlinarith only [hy, hc, mul_nonneg hnterm hterm]

end FiniteAvalanches.Probability.Multiscale.StepSix
