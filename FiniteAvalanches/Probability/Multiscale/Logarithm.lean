module

public import FiniteAvalanches.Probability.Multiscale.Arithmetic

@[expose] public section

/-! Diameter conversion for the fixed late block. The exponent is shared by
all radii; no lattice law or conditional geometry is represented here. -/

set_option autoImplicit false

namespace FiniteAvalanches.Probability.Multiscale

/-- The one exponent appearing in the current reciprocal proof. -/
noncomputable def contactExponent (p : ℝ) (P : ℕ) : ℝ := -Real.log (1 - p) / (2 * Real.log P)

theorem contactExponent_pos (p : ℝ) (P : ℕ) (hp : 0 < p) (hp' : p ≤ 1 / 2)
    (hP : 2 ≤ P) : 0 < contactExponent p P := by
  have hq : 0 < 1 - p := by linarith
  have hql : Real.log (1 - p) < 0 := Real.log_neg hq (by linarith)
  have hPl : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  exact div_pos (neg_pos.mpr hql) (mul_pos (by norm_num) hPl)

/-- The comparison used to absorb both deterministic error terms. -/
theorem inv_nat_lt_one_sub (p : ℝ) (P : ℕ) (hp : p ≤ 1 / 2) (hP : 3 ≤ P) :
    (P : ℝ)⁻¹ < 1 - p := by
  have hPr : (3 : ℝ) ≤ P := by exact_mod_cast hP
  have hpos : (0 : ℝ) < P := by linarith
  have h := (inv_lt_inv₀ hpos (by norm_num : (0 : ℝ) < 2)).mpr
    (show (2 : ℝ) < P by linarith)
  norm_num at h
  linarith

/-- Exact power identity behind the factor two in the logarithmic exponent. -/
theorem late_power_neg_exponent (p : ℝ) (P m : ℕ) (hp : 0 < p) (hp' : p ≤ 1 / 2)
    (hP : 2 ≤ P) :
    ((P : ℝ) ^ (2 * m + 2)) ^ (-contactExponent p P) = (1 - p) ^ (m + 1) := by
  have hq : 0 < 1 - p := by linarith
  have hPr : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hPl : Real.log (P : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < P by omega))).ne'
  rw [Real.rpow_def_of_pos (pow_pos hPr _), Real.log_pow]
  have he : (↑(2 * m + 2) * Real.log (P : ℝ)) * -contactExponent p P =
      (↑(m + 1) : ℝ) * Real.log (1 - p) := by
    simp only [contactExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    ring
  rw [he, Real.exp_nat_mul, Real.exp_log hq]

/-- Converting any upper logarithmic bound at the next block to the shared exponent. -/
theorem geometric_le_log_power (p A x : ℝ) (P m : ℕ)
    (hp : 0 < p) (hp' : p ≤ 1 / 2) (hP : 2 ≤ P) (hA : 0 < A) (hx : 0 < x)
    (hbound : x ≤ A * (P : ℝ) ^ (2 * m + 2)) :
    (1 - p) ^ m ≤ A ^ contactExponent p P / (1 - p) * x ^ (-contactExponent p P) := by
  have ha := contactExponent_pos p P hp hp' hP
  have hq : 0 < 1 - p := by linarith
  have hPr : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hcompare := Real.rpow_le_rpow_of_nonpos hx hbound (neg_nonpos.mpr ha.le)
  have hcancel : A ^ contactExponent p P * A ^ (-contactExponent p P) = 1 := by
    rw [← Real.rpow_add hA, add_neg_cancel, Real.rpow_zero]
  calc
    (1 - p) ^ m = A ^ contactExponent p P / (1 - p) *
        (A * (P : ℝ) ^ (2 * m + 2)) ^ (-contactExponent p P) := by
      rw [Real.mul_rpow hA.le (pow_nonneg hPr.le _), late_power_neg_exponent p P m hp hp' hP,
        pow_succ]
      field_simp
      nlinarith only [hcancel]
    _ ≤ A ^ contactExponent p P / (1 - p) * x ^ (-contactExponent p P) :=
      mul_le_mul_of_nonneg_left hcompare (by positivity)

/-- Literal next-block threshold gives the bound directly with `log (R + 2)`. -/
theorem log_radius_le_next_block (s P m : ℕ) (hs : 2 ≤ s) (hP : 2 ≤ P)
    (R : ℝ) (hR : 0 ≤ R) (hnext : R < 16 * (lateHeight s P (2 * m + 1) : ℝ)) :
    Real.log (R + 2) ≤ (Real.log 18 + 6 * Real.log s) * (P : ℝ) ^ (2 * m + 2) := by
  have hs' : 1 ≤ s := by omega
  have hP' : 1 ≤ P := by omega
  have hr : (1 : ℝ) ≤ lateScale s P (2 * m + 1) := by
    exact_mod_cast hs'.trans (le_lateScale s P (2 * m + 1) hs' hP')
  have hh : (1 : ℝ) ≤ lateHeight s P (2 * m + 1) := by
    rw [lateHeight_cast]
    exact one_le_pow₀ hr
  have hlog := Real.log_le_log (by linarith : 0 < R + 2)
    (show R + 2 ≤ 18 * (lateHeight s P (2 * m + 1) : ℝ) by linarith)
  rw [Real.log_mul (by norm_num : (18 : ℝ) ≠ 0) (by linarith :
      (lateHeight s P (2 * m + 1) : ℝ) ≠ 0), lateHeight_cast, Real.log_pow,
      log_lateScale] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hpow : (P : ℝ) ^ (2 * m + 1) ≤ (P : ℝ) ^ (2 * m + 2) :=
    pow_le_pow_right₀ (by exact_mod_cast hP') (by omega)
  have hone : (1 : ℝ) ≤ (P : ℝ) ^ (2 * m + 2) := one_le_pow₀ (by exact_mod_cast hP')
  have hls : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg (by exact_mod_cast hs')
  have hl18 : 0 ≤ Real.log (18 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith only [hlog, mul_le_mul_of_nonneg_left hpow hls,
    mul_le_mul_of_nonneg_left hone hl18]

/-- The scales escape every bounded real radius. -/
theorem index_add_two_le_lateScale (s P i : ℕ) (hs : 4 ≤ s) (hP : 2 ≤ P) :
    i + 2 ≤ lateScale s P i := by
  induction i with
  | zero => simp only [lateScale, pow_zero, pow_one]; omega
  | succ i ih =>
    have hg := four_mul_lateScale_le s P i hs hP
    omega

/-- Actual maximal block, rather than an asymptotic choice of its index. -/
theorem exists_late_block (s P : ℕ) (hs : 4 ≤ s) (hP : 2 ≤ P) (R : ℝ)
    (hlarge : 16 * (lateHeight s P 1 : ℝ) ≤ R) :
    ∃ m : ℕ, 1 ≤ m ∧ 16 * (lateHeight s P (2 * m - 1) : ℝ) ≤ R ∧
      R < 16 * (lateHeight s P (2 * m + 1) : ℝ) := by
  have hex : ∃ n : ℕ, R < 16 * (lateHeight s P (2 * n + 1) : ℝ) := by
    obtain ⟨n, hn⟩ := exists_nat_gt R
    have hi := index_add_two_le_lateScale s P (2 * n + 1) hs hP
    have hnat : n ≤ lateHeight s P (2 * n + 1) := by
      have hr : 1 ≤ lateScale s P (2 * n + 1) := by omega
      exact (show n ≤ lateScale s P (2 * n + 1) by omega).trans
        (le_self_pow₀ hr (by norm_num : (6 : ℕ) ≠ 0))
    have hcast : (n : ℝ) ≤ lateHeight s P (2 * n + 1) := by exact_mod_cast hnat
    exact ⟨n, by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
  let m := Nat.find hex
  have hnext : R < 16 * (lateHeight s P (2 * m + 1) : ℝ) := Nat.find_spec hex
  have hm : 1 ≤ m := by
    by_contra h
    have hz : m = 0 := by omega
    simp only [hz, mul_zero, zero_add] at hnext
    linarith
  refine ⟨m, hm, ?_, hnext⟩
  have hprev := Nat.find_min hex (show m - 1 < Nat.find hex by dsimp [m]; omega)
  have heq : 2 * (m - 1) + 1 = 2 * m - 1 := by omega
  rw [heq] at hprev
  exact le_of_not_gt hprev

/-- Small radii, including nonintegral radii and `R = 0`, need no asymptotic estimate. -/
theorem one_le_log_power (a R R₀ : ℝ) (ha : 0 ≤ a) (hR : 0 ≤ R) (hle : R ≤ R₀) :
    1 ≤ (Real.log (R₀ + 2)) ^ a * (Real.log (R + 2)) ^ (-a) := by
  have hx : 0 < Real.log (R + 2) := Real.log_pos (by linarith)
  have hy : 0 < Real.log (R₀ + 2) := Real.log_pos (by linarith)
  have hxy := Real.log_le_log (by linarith : 0 < R + 2) (by linarith : R + 2 ≤ R₀ + 2)
  have hcmp := Real.rpow_le_rpow_of_nonpos hx hxy (neg_nonpos.mpr ha)
  have hid : (Real.log (R₀ + 2)) ^ a * (Real.log (R₀ + 2)) ^ (-a) = 1 := by
    rw [← Real.rpow_add hy, add_neg_cancel, Real.rpow_zero]
  rw [← hid]
  exact mul_le_mul_of_nonneg_left hcmp (Real.rpow_nonneg hy.le a)

/-- A scalar conversion of the checked block bound. This is arithmetic, not a
conditional version of the manuscript's forest theorem. Its constant is chosen
before the real radius and before the scalar being bounded. -/
theorem le_log_power_of_late_blocks (s P : ℕ) (p M : ℝ)
    (hs : 4 ≤ s) (hP : 2 ≤ P) (hp : 0 < p) (hp' : p ≤ 1 / 2) (hM : 0 ≤ M)
    (R y : ℝ) (hR : 0 ≤ R) (hy : y ≤ 1)
    (hblock : ∀ m : ℕ, 1 ≤ m → 16 * (lateHeight s P (2 * m - 1) : ℝ) ≤ R →
      y ≤ M * (1 - p) ^ m) :
    y ≤ ((Real.log (16 * (lateHeight s P 1 : ℝ) + 2)) ^ contactExponent p P +
      M * (Real.log 18 + 6 * Real.log s) ^ contactExponent p P / (1 - p)) *
      (Real.log (R + 2)) ^ (-contactExponent p P) := by
  have ha := contactExponent_pos p P hp hp' hP
  have hq : 0 < 1 - p := by linarith
  have hA : 0 < Real.log 18 + 6 * Real.log s := by
    have hls : 0 < Real.log (s : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < s by omega))
    have hl18 := Real.log_pos (by norm_num : (1 : ℝ) < 18)
    linarith
  have hterm : 0 ≤ (Real.log (R + 2)) ^ (-contactExponent p P) :=
    Real.rpow_nonneg (Real.log_pos (by linarith)).le _
  by_cases hlarge : 16 * (lateHeight s P 1 : ℝ) ≤ R
  · obtain ⟨m, hm, hprev, hnext⟩ := exists_late_block s P hs hP R hlarge
    have hb := hblock m hm hprev
    have hc := geometric_le_log_power p (Real.log 18 + 6 * Real.log s)
      (Real.log (R + 2)) P m hp hp' hP hA (Real.log_pos (by linarith))
      (log_radius_le_next_block s P m (by omega) hP R hR hnext)
    have hx := mul_le_mul_of_nonneg_left hc hM
    have hn : 0 ≤ (Real.log (16 * (lateHeight s P 1 : ℝ) + 2)) ^ contactExponent p P :=
      Real.rpow_nonneg (Real.log_nonneg (by
        have h0 : (0 : ℝ) ≤ lateHeight s P 1 := Nat.cast_nonneg _
        linarith)) _
    simp only [div_eq_mul_inv] at hx ⊢
    nlinarith only [hb, hx, mul_nonneg hn hterm]
  · have hc := one_le_log_power (contactExponent p P) R
      (16 * (lateHeight s P 1 : ℝ)) ha.le hR (le_of_not_ge hlarge)
    have hn : 0 ≤ M * (Real.log 18 + 6 * Real.log s) ^ contactExponent p P / (1 - p) :=
      div_nonneg (mul_nonneg hM (Real.rpow_nonneg hA.le _)) hq.le
    nlinarith only [hy, hc, mul_nonneg hn hterm]

/-- The explicit uniform constant is positive and depends only on fixed parameters. -/
theorem late_log_constant_pos (s P : ℕ) (p M : ℝ) (hp : p ≤ 1 / 2) (hM : 0 ≤ M) :
    0 < (Real.log (16 * (lateHeight s P 1 : ℝ) + 2)) ^ contactExponent p P +
      M * (Real.log 18 + 6 * Real.log s) ^ contactExponent p P / (1 - p) := by
  have hh : (0 : ℝ) ≤ lateHeight s P 1 := Nat.cast_nonneg _
  have hB : 0 < Real.log (16 * (lateHeight s P 1 : ℝ) + 2) := Real.log_pos (by linarith)
  have hq : 0 < 1 - p := by linarith
  have hls := Real.log_natCast_nonneg s
  have hl18 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 18)
  have hA : 0 ≤ Real.log 18 + 6 * Real.log s := by linarith
  exact add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hB _)
    (div_nonneg (mul_nonneg hM (Real.rpow_nonneg hA _)) hq.le)

end FiniteAvalanches.Probability.Multiscale
