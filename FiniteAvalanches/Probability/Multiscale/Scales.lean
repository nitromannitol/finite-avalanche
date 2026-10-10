module

public import FiniteAvalanches.Probability.Multiscale.Arithmetic

@[expose] public section

/-! Choosing the manuscript's scales once, before the root shape or diameter. -/

set_option autoImplicit false

namespace FiniteAvalanches.Probability.Multiscale

theorem lateScale_mono (s P : ℕ) (hs : 1 ≤ s) (hP : 1 ≤ P) :
    Monotone (lateScale s P) := by
  intro i j hij
  exact pow_le_pow_right₀ hs (pow_le_pow_right₀ hP hij)

theorem lateHeight_mono (s P : ℕ) (hs : 1 ≤ s) (hP : 1 ≤ P) :
    Monotone (lateHeight s P) := by
  intro i j hij
  exact pow_le_pow_left₀ (Nat.zero_le _) (lateScale_mono s P hs hP hij) 6

/-- The next-block upper threshold makes the chosen index genuinely maximal. -/
theorem late_block_maximal (s P m n : ℕ) (hs : 1 ≤ s) (hP : 1 ≤ P) (R : ℝ)
    (hnext : R < 16 * (lateHeight s P (2 * m + 1) : ℝ))
    (hn : 16 * (lateHeight s P (2 * n - 1) : ℝ) ≤ R) : n ≤ m := by
  by_contra h
  have hidx : 2 * m + 1 ≤ 2 * n - 1 := by omega
  have hh : (lateHeight s P (2 * m + 1) : ℝ) ≤ lateHeight s P (2 * n - 1) := by
    exact_mod_cast lateHeight_mono s P hs hP hidx
  linarith

/-- A fixed positive exponent gap suffices for every larger real scale. -/
theorem power_gap_le (D : ℝ) (P s : ℕ) (hD : 0 ≤ D) (hs : 2 ≤ s)
    (hgap : (2 : ℝ) ^ D ≤ (s : ℝ) ^ ((P : ℝ) - 6 * D))
    (u : ℝ) (hu : (s : ℝ) ≤ u) (hPD : 6 * D ≤ P) :
    (u ^ 6 + 2) ^ D ≤ u ^ P := by
  have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hu2 : 2 ≤ u := hs'.trans hu
  have hu0 : 0 < u := by linarith
  have hu6 : 2 ≤ u ^ 6 := (show (2 : ℝ) ≤ 2 ^ 6 by norm_num).trans
    (pow_le_pow_left₀ (by norm_num) hu2 6)
  have hg : (2 : ℝ) ^ D ≤ u ^ ((P : ℝ) - 6 * D) := hgap.trans
    (Real.rpow_le_rpow (by positivity) hu (sub_nonneg.mpr hPD))
  calc
    (u ^ 6 + 2) ^ D ≤ (2 * u ^ 6) ^ D :=
      Real.rpow_le_rpow (by positivity) (by linarith) hD
    _ = (2 : ℝ) ^ D * u ^ (6 * D) := by
      rw [Real.mul_rpow (by norm_num) (pow_nonneg hu0.le _), ← Real.rpow_natCast,
        ← Real.rpow_mul hu0.le]
      norm_num
    _ ≤ u ^ ((P : ℝ) - 6 * D) * u ^ (6 * D) :=
      mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hu0.le _)
    _ = u ^ P := by rw [← Real.rpow_add hu0, sub_add_cancel, Real.rpow_natCast]

/-- The complete fixed-base selection in the manuscript, with an integer base
and a real carrier for the universal power-gap condition. -/
theorem exists_late_scale_base (D c : ℝ) (rStar P : ℕ)
    (hD : 2 ≤ D) (hc : 0 < c) (hP : 6 * D < (P : ℝ)) :
    ∃ s : ℕ, 10 ≤ s ∧ rStar ≤ s ∧ (c / 2) * Real.log s ≥ 1 ∧
      ∀ u : ℝ, (s : ℝ) ≤ u → (u ^ 6 + 2) ^ D ≤ u ^ P := by
  let e : ℝ := (P : ℝ) - 6 * D
  have he : 0 < e := sub_pos.mpr hP
  let b : ℝ := max 10 (max rStar (max (Real.exp (2 / c))
    (Real.exp (D * Real.log 2 / e))))
  obtain ⟨s, hs⟩ := exists_nat_gt b
  have hs10 : (10 : ℝ) ≤ s := (le_max_left _ _).trans hs.le
  have hsr : (rStar : ℝ) ≤ s :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hs.le)
  have hs2 : 2 ≤ s := by exact_mod_cast (show (2 : ℝ) ≤ s by linarith)
  have hs0 : 0 < (s : ℝ) := by linarith
  have hsc : Real.exp (2 / c) ≤ s :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hs.le))
  have hsg : Real.exp (D * Real.log 2 / e) ≤ s :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hs.le))
  have hlc : 2 / c ≤ Real.log s := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hsc
  have hlg : D * Real.log 2 / e ≤ Real.log s := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hsg
  have hgap : (2 : ℝ) ^ D ≤ (s : ℝ) ^ ((P : ℝ) - 6 * D) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hs0]
    apply Real.exp_le_exp.mpr
    have hg := (div_le_iff₀ he).mp hlg
    dsimp [e] at hg
    nlinarith only [hg]
  refine ⟨s, by exact_mod_cast hs10, by exact_mod_cast hsr, ?_, ?_⟩
  · have hl := (div_le_iff₀ hc).mp hlc
    nlinarith only [hl]
  · intro u hu
    exact power_gap_le D P s (by linarith) hs2 hgap u hu hP.le

/-- Both integer parameters can be fixed before any root pair or diameter. -/
theorem exists_late_scales (D c : ℝ) (rStar : ℕ) (hD : 2 ≤ D) (hc : 0 < c) :
    ∃ P s : ℕ, 6 * D < (P : ℝ) ∧ 3 ≤ P ∧ 10 ≤ s ∧ rStar ≤ s ∧
      1 ≤ (c / 2) * Real.log s ∧
      ∀ u : ℝ, (s : ℝ) ≤ u → (u ^ 6 + 2) ^ D ≤ u ^ P := by
  obtain ⟨P, hP⟩ := exists_nat_gt (6 * D)
  obtain ⟨s, hs, hr, ht, hg⟩ := exists_late_scale_base D c rStar P hD hc hP
  have hP3 : 3 ≤ P := by exact_mod_cast (show (3 : ℝ) ≤ P by linarith)
  exact ⟨P, s, hP, hP3, hs, hr, ht, hg⟩

/-- Every consecutive pair obeys the revealed-root separation requirement. -/
theorem lateScale_gap (D : ℝ) (P s : ℕ) (hs : 1 ≤ s) (hP : 1 ≤ P)
    (hgap : ∀ u : ℝ, (s : ℝ) ≤ u → (u ^ 6 + 2) ^ D ≤ u ^ P) (i : ℕ) :
    ((lateHeight s P i : ℝ) + 2) ^ D ≤ (lateScale s P (i + 1) : ℝ) := by
  have hi : (s : ℝ) ≤ lateScale s P i := by exact_mod_cast le_lateScale s P i hs hP
  have h := hgap (lateScale s P i : ℝ) hi
  simpa only [lateHeight_cast, lateScale_succ, Nat.cast_pow] using h

/-- The same fixed base makes every trial threshold at least one. -/
theorem one_le_late_threshold (s P i : ℕ) (c : ℝ) (hs : 1 ≤ s) (hP : 1 ≤ P)
    (hc : 0 ≤ c) (hbase : 1 ≤ (c / 2) * Real.log s) :
    1 ≤ (c / 2) * Real.log (lateScale s P i : ℝ) := by
  have hs0 : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hi : (s : ℝ) ≤ lateScale s P i := by exact_mod_cast le_lateScale s P i hs hP
  exact hbase.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hs0 hi) (by positivity))

/-- The query starting radius satisfies the exact Beurling separation margin. -/
theorem beurling_margin_le_lateHeight (s P i : ℕ) (hs : 4 ≤ s) (hP : 1 ≤ P) :
    4 * (3 * lateScale s P i + 1) + 4 ≤ lateHeight s P i := by
  have hr : 4 ≤ lateScale s P i := hs.trans (le_lateScale s P i (by omega) hP)
  have hsq : 16 ≤ lateScale s P i ^ 2 := by
    simpa using pow_le_pow_left₀ (Nat.zero_le 4) hr 2
  calc
    4 * (3 * lateScale s P i + 1) + 4 ≤ 16 * lateScale s P i := by omega
    _ ≤ lateScale s P i ^ 3 := by
      simpa only [pow_succ] using Nat.mul_le_mul_right (lateScale s P i) hsq
    _ ≤ lateHeight s P i := pow_le_pow_right₀ (by omega) (by norm_num : 3 ≤ 6)

/-- The total single-batch error exponent is exactly negative one half. -/
theorem query_beurling_power (r : ℝ) (hr : 0 < r) :
    r ^ 2 * Real.sqrt (r / r ^ 6) = r ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow hr.le (pow_nonneg hr.le _),
    ← Real.rpow_natCast r 6, ← Real.rpow_mul hr.le]
  norm_num
  rw [← Real.rpow_natCast r 2, ← Real.rpow_natCast r 3, ← Real.rpow_sub hr]
  norm_num
  rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
  norm_num

/-- Exact square-window cardinality and the `3r + 2` Beurling numerator
are absorbed by a single radius-independent constant. -/
theorem query_beurling_bound (r : ℝ) (hr : 1 ≤ r) :
    (6 * r + 3) ^ 2 * Real.sqrt ((3 * r + 2) / r ^ 6) ≤
      81 * Real.sqrt 5 * r ^ (-(1 / 2 : ℝ)) := by
  have hr0 : 0 < r := by linarith
  have hcount : (6 * r + 3) ^ 2 ≤ 81 * r ^ 2 := by nlinarith
  have hwalk : Real.sqrt ((3 * r + 2) / r ^ 6) ≤
      Real.sqrt 5 * Real.sqrt (r / r ^ 6) := by
    calc
      Real.sqrt ((3 * r + 2) / r ^ 6) ≤ Real.sqrt (5 * (r / r ^ 6)) :=
        Real.sqrt_le_sqrt (by
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr0.le _))
      _ = Real.sqrt 5 * Real.sqrt (r / r ^ 6) := Real.sqrt_mul (by norm_num) _
  calc
    (6 * r + 3) ^ 2 * Real.sqrt ((3 * r + 2) / r ^ 6) ≤
        (81 * r ^ 2) * (Real.sqrt 5 * Real.sqrt (r / r ^ 6)) :=
      mul_le_mul hcount hwalk (Real.sqrt_nonneg _) (by positivity)
    _ = 81 * Real.sqrt 5 * (r ^ 2 * Real.sqrt (r / r ^ 6)) := by ring
    _ = 81 * Real.sqrt 5 * r ^ (-(1 / 2 : ℝ)) := by rw [query_beurling_power r hr0]

end FiniteAvalanches.Probability.Multiscale
