module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

@[expose] public section

/-! Elementary arithmetic for the manuscript's fixed late block. These results
contain no forest law, geometric success assertion, or independence premise. -/

set_option autoImplicit false

namespace FiniteAvalanches.Probability.Multiscale

/-- The literal integer scale in Section 4. -/
def lateScale (s P i : ℕ) : ℕ := s ^ (P ^ i)

/-- The literal localization radius in Section 4. -/
def lateHeight (s P i : ℕ) : ℕ := lateScale s P i ^ 6

@[simp] theorem lateScale_cast (s P i : ℕ) :
    (lateScale s P i : ℝ) = (s : ℝ) ^ (P ^ i) := by
  simp [lateScale]

@[simp] theorem lateHeight_cast (s P i : ℕ) :
    (lateHeight s P i : ℝ) = ((lateScale s P i : ℝ)) ^ 6 := by
  simp [lateHeight]

theorem lateScale_succ (s P i : ℕ) :
    lateScale s P (i + 1) = lateScale s P i ^ P := by
  simp only [lateScale, pow_succ, pow_mul]

theorem le_lateScale (s P i : ℕ) (hs : 1 ≤ s) (hP : 1 ≤ P) :
    s ≤ lateScale s P i := by
  exact le_self_pow₀ hs (by positivity : P ^ i ≠ 0)

theorem four_mul_lateScale_le (s P i : ℕ) (hs : 4 ≤ s) (hP : 2 ≤ P) :
    4 * lateScale s P i ≤ lateScale s P (i + 1) := by
  have hr : 4 ≤ lateScale s P i := hs.trans (le_lateScale s P i (by omega) (by omega))
  rw [lateScale_succ]
  calc
    4 * lateScale s P i ≤ lateScale s P i ^ 2 := by nlinarith
    _ ≤ lateScale s P i ^ P := pow_le_pow_right₀ (by omega) hP

/-- The localization error halves at each literal scale. -/
theorem lateScale_neg_half_succ_le (s P i : ℕ) (hs : 4 ≤ s) (hP : 2 ≤ P) :
    (lateScale s P (i + 1) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      (lateScale s P i : ℝ) ^ (-(1 / 2 : ℝ)) / 2 := by
  have hr : 0 < (lateScale s P i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < s) (le_lateScale s P i (by omega) (by omega)))
  have hg : 4 * (lateScale s P i : ℝ) ≤ (lateScale s P (i + 1) : ℝ) := by
    exact_mod_cast four_mul_lateScale_le s P i hs hP
  have hfour : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    norm_num
  calc
    (lateScale s P (i + 1) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        (4 * (lateScale s P i : ℝ)) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hg (by norm_num)
    _ = (lateScale s P i : ℝ) ^ (-(1 / 2 : ℝ)) / 2 := by
      rw [Real.mul_rpow (by norm_num) hr.le, hfour]
      ring

/-- A halving recurrence has a finite interval sum at most twice its initial value. -/
theorem sum_Ico_le_two_mul_of_le_half (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i)
    (hstep : ∀ i, e (i + 1) ≤ e i / 2) (m n : ℕ) :
    ∑ i ∈ Finset.Ico m (m + n), e i ≤ 2 * e m := by
  have h : ∀ k, ∑ j ∈ Finset.range k, e (m + j) ≤ 2 * e m - 2 * e (m + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep (m + k)
      simp only [← Nat.add_assoc]
      linarith
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  exact (h n).trans (by linarith [he (m + n)])

/-- Exact late-block localization sum, including the empty block `m = 0`. -/
theorem sum_lateScale_neg_half_le (s P m : ℕ) (hs : 4 ≤ s) (hP : 2 ≤ P) :
    ∑ i ∈ Finset.Ico m (2 * m), (lateScale s P i : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      2 * (lateScale s P m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  simpa only [two_mul] using sum_Ico_le_two_mul_of_le_half
    (fun i => (lateScale s P i : ℝ) ^ (-(1 / 2 : ℝ)))
    (fun i => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun i => lateScale_neg_half_succ_le s P i hs hP) m m

/-- The exact logarithm used for the contact threshold. -/
theorem log_lateScale (s P i : ℕ) :
    Real.log (lateScale s P i : ℝ) = (P : ℝ) ^ i * Real.log s := by
  rw [lateScale_cast, Real.log_pow, Nat.cast_pow]

/-- The exponential localization remainder is bounded by the reciprocal logarithm. -/
theorem neg_half_le_two_div_log (x : ℝ) (hx : 1 < x) :
    x ^ (-(1 / 2 : ℝ)) ≤ 2 / Real.log x := by
  have hl := Real.log_pos hx
  have he := Real.add_one_le_exp (Real.log x / 2)
  rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
  have hp := Real.exp_pos (Real.log x / 2)
  have hn : Real.exp (Real.log x * -(1 / 2 : ℝ)) = (Real.exp (Real.log x / 2))⁻¹ := by
    rw [show Real.log x * -(1 / 2 : ℝ) = -(Real.log x / 2) by ring, Real.exp_neg]
  rw [hn]
  apply (le_div_iff₀ hl).mpr
  have hi : (Real.exp (Real.log x / 2))⁻¹ * Real.exp (Real.log x / 2) = 1 := inv_mul_cancel₀ hp.ne'
  nlinarith [inv_pos.mpr hp]

end FiniteAvalanches.Probability.Multiscale
