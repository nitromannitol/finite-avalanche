import FiniteAvalanches.Probability.Multiscale.StepSixIncomingArithmetic
import FiniteAvalanches.Probability.Multiscale.Estimates

/-! Reciprocal decay with the localization error at the preceding scale. -/

set_option autoImplicit false

namespace FiniteAvalanches.Probability.Multiscale.StepSixIncoming

open MeasureTheory FiniteAvalanches.Probability FiniteAvalanches.Probability.Multiscale

/-- The first exploration history has radius two. -/
theorem binary_initial_scale (P : ℕ) : lateScale 2 P 0 = 2 := by
  simp only [lateScale, pow_zero, pow_one]

/-- The predecessor index costs a uniform factor two, including `n = 1`. -/
theorem inverse_pow_pred_le_two_geometric (P n : ℕ) (p : ℝ)
    (hP : 3 ≤ P) (hn : 1 ≤ n) (hp : p ≤ 1 / 2) :
    ((P : ℝ) ^ (n - 1))⁻¹ ≤ 2 * (1 - p) ^ n := by
  by_cases hfirst : n = 1
  · subst n
    norm_num only [Nat.sub_self, pow_zero, pow_one, inv_one]
    linarith
  · have hPr : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
    have hgeom : ((P : ℝ) ^ (n - 1))⁻¹ ≤ (1 - p) ^ (n - 1) := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (inv_nonneg.mpr hPr.le)
        (inv_nat_lt_one_sub p P hp hP).le _
    have hq : 0 ≤ 1 - p := by linarith
    have hhalf : 1 ≤ 2 * (1 - p) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hhalf (pow_nonneg hq (n - 1))
    have heq : n - 1 + 1 = n := by omega
    have hpow : (1 - p) ^ n = (1 - p) ^ (n - 1) * (1 - p) := by
      calc
        _ = (1 - p) ^ (n - 1 + 1) := congrArg (fun j : ℕ => (1 - p) ^ j) heq.symm
        _ = _ := pow_succ _ _
    rw [hpow]
    nlinarith only [hgeom, hmul]

/-- The preceding localization error is absorbed uniformly in the trial rate. -/
theorem previous_scale_neg_half_le (P n : ℕ) (p : ℝ)
    (hP : 3 ≤ P) (hn : 1 ≤ n) (hp : p ≤ 1 / 2) :
    (lateScale 2 P (n - 1) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      (4 / Real.log 2) * (1 - p) ^ n := by
  have hr : (1 : ℝ) < lateScale 2 P (n - 1) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < (2 : ℕ))
      (le_lateScale 2 P _ (by norm_num) (by omega))
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hPr : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  calc
    (lateScale 2 P (n - 1) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        2 / Real.log (lateScale 2 P (n - 1) : ℝ) := neg_half_le_two_div_log _ hr
    _ = (2 / Real.log 2) * ((P : ℝ) ^ (n - 1))⁻¹ := by
      rw [log_lateScale]
      norm_num only [Nat.cast_ofNat]
      field_simp
    _ ≤ (2 / Real.log 2) * (2 * (1 - p) ^ n) :=
      mul_le_mul_of_nonneg_left (inverse_pow_pred_le_two_geometric P n p hP hn hp)
        (by positivity)
    _ = (4 / Real.log 2) * (1 - p) ^ n := by ring

/-- The exact strict threshold and preceding-scale error yield one block bound. -/
theorem integral_reciprocal_le_binary_geometric {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : Ω → ℕ) (hL : Measurable L)
    (hpos : ∀ᵐ ω ∂μ, 1 ≤ L ω) (P n : ℕ) (p D : ℝ)
    (hP : 3 ≤ P) (hn : 1 ≤ n) (hp : p ≤ 1 / 2) (hD : 0 ≤ D)
    (hbad : μ.real {ω | (L ω : ℝ) < (1 / 16 : ℝ) * Real.log (lateScale 2 P n : ℝ)} ≤
      (1 - p) ^ n + 2 * D * (lateScale 2 P (n - 1) : ℝ) ^ (-(1 / 2 : ℝ))) :
    (∫ ω, (L ω : ℝ)⁻¹ ∂μ) ≤
      (1 + (8 * D + 16) / Real.log 2) * (1 - p) ^ n := by
  have hr : (1 : ℝ) < lateScale 2 P n := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < (2 : ℕ))
      (le_lateScale 2 P n (by norm_num) (by omega))
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hPr : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hsplit := integral_reciprocal_le_lt μ L hL hpos
    ((1 / 16 : ℝ) * Real.log (lateScale 2 P n : ℝ))
    (mul_pos (by norm_num) (Real.log_pos hr))
  have herror := mul_le_mul_of_nonneg_left (previous_scale_neg_half_le P n p hP hn hp)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD)
  have hgeom : ((P : ℝ) ^ n)⁻¹ ≤ (1 - p) ^ n := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hPr.le)
      (inv_nat_lt_one_sub p P hp hP).le n
  have hid : ((1 / 16 : ℝ) * Real.log (lateScale 2 P n : ℝ))⁻¹ =
      (16 / Real.log 2) * ((P : ℝ) ^ n)⁻¹ := by
    rw [log_lateScale]
    norm_num only [Nat.cast_ofNat]
    field_simp
  have hthreshold := mul_le_mul_of_nonneg_left hgeom
    (by positivity : 0 ≤ (16 : ℝ) / Real.log 2)
  rw [← hid] at hthreshold
  have hrem : 2 * D * (lateScale 2 P (n - 1) : ℝ) ^ (-(1 / 2 : ℝ)) +
      ((1 / 16 : ℝ) * Real.log (lateScale 2 P n : ℝ))⁻¹ ≤
      ((8 * D + 16) / Real.log 2) * (1 - p) ^ n := by
    calc
      _ ≤ 2 * D * ((4 / Real.log 2) * (1 - p) ^ n) +
          (16 / Real.log 2) * (1 - p) ^ n := add_le_add herror hthreshold
      _ = _ := by ring
  nlinarith only [hsplit, hbad, hrem]

universe u

/-- One positive exponent and constant precede all probability spaces and
diameters. The small-count estimate is the explicit conditional input. -/
theorem exists_reciprocal_log_bound_of_small_counts (ε : ℝ) (κ : ℕ) (D : ℝ)
    (hε : 0 < ε) (hε' : ε ≤ 1) (hκ : 30 ≤ κ) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (diam : ℝ) (μ : Measure Ω)
        [IsProbabilityMeasure μ] (L : Ω → ℕ),
        0 ≤ diam → Measurable L → (∀ᵐ ω ∂μ, 1 ≤ L ω) →
        (∀ n : ℕ, 1 ≤ n → 16 * ((2 : ℝ) ^ ((6 * κ) ^ (2 * n - 1))) ≤ diam →
          μ.real {ω | (L ω : ℝ) < (1 / 16 : ℝ) * Real.log ((2 : ℝ) ^ ((6 * κ) ^ n))} ≤
            (1 - ε / 2) ^ n + 2 * D *
              ((2 : ℝ) ^ ((6 * κ) ^ (n - 1))) ^ (-(1 / 2 : ℝ))) →
        (∫ ω, (L ω : ℝ)⁻¹ ∂μ) ≤ C * (Real.log (diam + 2)) ^ (-a) := by
  let P := 6 * κ
  let p := ε / 2
  let M := 1 + (8 * max D 0 + 16) / Real.log 2
  let C := (Real.log (16 * (lateScale 2 P 1 : ℝ) + 2)) ^ contactExponent p P +
    M * (Real.log 18 + Real.log 2) ^ contactExponent p P / (1 - p)
  have hP : 3 ≤ P := by dsimp [P]; omega
  have hp : 0 < p := by dsimp [p]; positivity
  have hp' : p ≤ 1 / 2 := by dsimp [p]; linarith
  have hD : 0 ≤ max D 0 := le_max_right D 0
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have ha := contactExponent_pos p P hp hp' (by omega)
  have hC : 0 < C := binary_log_constant_pos P p M hp' hM
  refine ⟨contactExponent p P, C, ha, hC, ?_⟩
  intro Ω mΩ diam μ hμ L hdiam hL hpos hbad
  apply le_log_power_of_binary_blocks P p M (by omega) hp hp' hM diam
    (∫ ω, (L ω : ℝ)⁻¹ ∂μ) hdiam (integral_reciprocal_le_one μ L hL hpos)
  intro n hn hscale
  have hscale' : 16 * ((2 : ℝ) ^ ((6 * κ) ^ (2 * n - 1))) ≤ diam := by
    simpa only [lateScale_cast, P, Nat.cast_ofNat] using hscale
  have hb : μ.real {ω | (L ω : ℝ) < (1 / 16 : ℝ) * Real.log (lateScale 2 P n : ℝ)} ≤
      (1 - p) ^ n + 2 * D * (lateScale 2 P (n - 1) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simpa only [lateScale_cast, P, p, Nat.cast_ofNat] using hbad n hn hscale'
  have hDcmp : 2 * D * (lateScale 2 P (n - 1) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      2 * max D 0 * (lateScale 2 P (n - 1) : ℝ) ^ (-(1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_left D 0) (by norm_num))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact integral_reciprocal_le_binary_geometric μ L hL hpos P n p (max D 0)
    hP hn hp' hD (hb.trans (add_le_add le_rfl hDcmp))

end FiniteAvalanches.Probability.Multiscale.StepSixIncoming
