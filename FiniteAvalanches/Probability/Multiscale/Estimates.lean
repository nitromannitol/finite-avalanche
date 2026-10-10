module

public import FiniteAvalanches.Probability.Multiscale.Logarithm
public import FiniteAvalanches.Probability.Survival
public import FiniteAvalanches.Probability.Reciprocal

@[expose] public section

/-! Probability and reciprocal consumers of the literal late-block arithmetic.
The conditional success and localization premises below are ordinary local
probability inequalities. They are not asserted for Wilson forests here. -/

set_option autoImplicit false

namespace FiniteAvalanches.Probability.Multiscale

open MeasureTheory FiniteAvalanches.Probability

section Probability
variable {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Summing the literal localization errors over the finite late block. -/
theorem localization_union_le (E : ℕ → Set Ω) (s P m : ℕ) (C : ℝ)
    (hs : 4 ≤ s) (hP : 2 ≤ P) (hC : 0 ≤ C)
    (hE : ∀ i ∈ Finset.Ico m (2 * m),
      μ.real (E i) ≤ C * (lateScale s P i : ℝ) ^ (-(1 / 2 : ℝ))) :
    μ.real (⋃ i ∈ Finset.Ico m (2 * m), E i) ≤
      2 * C * (lateScale s P m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  calc
    μ.real (⋃ i ∈ Finset.Ico m (2 * m), E i) ≤
        ∑ i ∈ Finset.Ico m (2 * m), μ.real (E i) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ Finset.Ico m (2 * m),
        C * (lateScale s P i : ℝ) ^ (-(1 / 2 : ℝ)) := Finset.sum_le_sum hE
    _ = C * ∑ i ∈ Finset.Ico m (2 * m),
        (lateScale s P i : ℝ) ^ (-(1 / 2 : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (2 * (lateScale s P m : ℝ) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (sum_lateScale_neg_half_le s P m hs hP) hC
    _ = 2 * C * (lateScale s P m : ℝ) ^ (-(1 / 2 : ℝ)) := by ring

/-- Integrating a conditional error estimate on a general probability space. -/
theorem measureReal_le_of_condExp_indicator_le (history : MeasurableSpace Ω)
    (hm : history ≤ m₀) (E : Set Ω) (hE : MeasurableSet[m₀] E) (b : ℝ)
    (herror : ∀ᵐ ω ∂μ, (μ[E.indicator (fun _ => (1 : ℝ)) | history]) ω ≤ b) :
    μ.real E ≤ b := by
  calc
    μ.real E = ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
      rw [integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one]
    _ = ∫ ω, (μ[E.indicator (fun _ => (1 : ℝ)) | history]) ω ∂μ :=
      (integral_condExp hm).symm
    _ ≤ ∫ _ : Ω, b ∂μ := integral_mono_ae integrable_condExp (integrable_const b) herror
    _ = b := by simp

/-- Literal summed localization bound derived from integrated conditional errors. -/
theorem localization_union_le_of_condExp (E : ℕ → Set Ω)
    (history : ℕ → MeasurableSpace Ω) (hm : ∀ i, history i ≤ m₀)
    (hE : ∀ i, MeasurableSet (E i)) (s P m : ℕ) (C : ℝ)
    (hs : 4 ≤ s) (hP : 2 ≤ P) (hC : 0 ≤ C)
    (herror : ∀ i ∈ Finset.Ico m (2 * m), ∀ᵐ ω ∂μ,
      (μ[(E i).indicator (fun _ => (1 : ℝ)) | history i]) ω ≤
        C * (lateScale s P i : ℝ) ^ (-(1 / 2 : ℝ))) :
    μ.real (⋃ i ∈ Finset.Ico m (2 * m), E i) ≤
      2 * C * (lateScale s P m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  apply localization_union_le μ E s P m C hs hP hC
  intro i hi
  exact measureReal_le_of_condExp_indicator_le μ (history i) (hm i) (E i) (hE i)
    (C * (lateScale s P i : ℝ) ^ (-(1 / 2 : ℝ))) (herror i hi)

/-- Conditional success and localization combine without a finite history
carrier, a bounded stopping time, or independence of the successes. -/
theorem small_count_le_of_condExp (B S E : ℕ → Set Ω)
    (history : ℕ → MeasurableSpace Ω) (hm : ∀ j, history j ≤ m₀)
    (hB : ∀ j, MeasurableSet[history j] (B j)) (hS : ∀ j, MeasurableSet (S j))
    (s P m : ℕ) (p C : ℝ) (hs : 4 ≤ s) (hP : 2 ≤ P) (hp : p ≤ 1) (hC : 0 ≤ C)
    (hnext : ∀ j < m, B (j + 1) ⊆ B j \ S j)
    (hsuccess : ∀ j < m, ∀ᵐ ω ∂μ, ω ∈ B j →
      p ≤ (μ[(S j).indicator (fun _ => (1 : ℝ)) | history j]) ω)
    (hE : ∀ i ∈ Finset.Ico m (2 * m),
      μ.real (E i) ≤ C * (lateScale s P i : ℝ) ^ (-(1 / 2 : ℝ)))
    (L : Ω → ℕ) (t : ℝ)
    (hbad : {ω | (L ω : ℝ) < t} ⊆ B m ∪ ⋃ i ∈ Finset.Ico m (2 * m), E i) :
    μ.real {ω | (L ω : ℝ) < t} ≤ (1 - p) ^ m +
      2 * C * (lateScale s P m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hsurvive := survival_le_pow_of_condExp μ history hm B S hB hS p hp m hnext hsuccess
  have herror := localization_union_le μ E s P m C hs hP hC hE
  exact (measureReal_mono hbad).trans
    ((measureReal_union_le _ _).trans (add_le_add hsurvive herror))

/-- The bounded-diameter branch uses the actual reciprocal expectation bound. -/
theorem integral_reciprocal_le_one (L : Ω → ℕ) (hL : Measurable L)
    (hpos : ∀ᵐ ω ∂μ, 1 ≤ L ω) :
    (∫ ω, (L ω : ℝ)⁻¹ ∂μ) ≤ 1 := by
  calc
    (∫ ω, (L ω : ℝ)⁻¹ ∂μ) ≤ ∫ _ : Ω, (1 : ℝ) ∂μ :=
      integral_mono_ae (integrable_reciprocal μ L hL hpos) (integrable_const 1)
        (hpos.mono (fun ω hω => inv_le_one_of_one_le₀ (by exact_mod_cast hω)))
    _ = 1 := by simp

/-- Real Bochner expectation at the exact contact threshold, with the two
remainders absorbed into the same geometric failure rate. -/
theorem integral_reciprocal_le_geometric (L : Ω → ℕ) (hL : Measurable L)
    (hpos : ∀ᵐ ω ∂μ, 1 ≤ L ω) (s P m : ℕ) (p c C : ℝ)
    (hs : 4 ≤ s) (hP : 3 ≤ P) (hp : p ≤ 1 / 2) (hc : 0 < c) (hC : 0 ≤ C)
    (hbad : μ.real {ω | (L ω : ℝ) < (c / 2) * Real.log (lateScale s P m : ℝ)} ≤
      (1 - p) ^ m + 2 * C * (lateScale s P m : ℝ) ^ (-(1 / 2 : ℝ))) :
    (∫ ω, (L ω : ℝ)⁻¹ ∂μ) ≤
      (1 + (4 * C + 2 / c) / Real.log s) * (1 - p) ^ m := by
  have hs1 : 1 ≤ s := by omega
  have hP1 : 1 ≤ P := by omega
  have hr : (1 : ℝ) < lateScale s P m := by
    exact_mod_cast lt_of_lt_of_le (show 1 < s by omega) (le_lateScale s P m hs1 hP1)
  have hls : 0 < Real.log (s : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < s by omega))
  have hPr : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hpow := pow_pos hPr m
  have hlog := Real.log_pos hr
  have hsplit := integral_reciprocal_le_lt μ L hL hpos
    ((c / 2) * Real.log (lateScale s P m : ℝ)) (mul_pos (by positivity) hlog)
  have herror := neg_half_le_two_div_log (lateScale s P m : ℝ) hr
  rw [log_lateScale] at herror
  have hid : 2 * C * (2 / ((P : ℝ) ^ m * Real.log s)) +
      ((c / 2) * Real.log (lateScale s P m : ℝ))⁻¹ =
      ((4 * C + 2 / c) / Real.log s) * ((P : ℝ) ^ m)⁻¹ := by
    rw [log_lateScale]
    field_simp
    ring
  have hrem : 2 * C * (lateScale s P m : ℝ) ^ (-(1 / 2 : ℝ)) +
      ((c / 2) * Real.log (lateScale s P m : ℝ))⁻¹ ≤
      ((4 * C + 2 / c) / Real.log s) * ((P : ℝ) ^ m)⁻¹ := by
    rw [← hid]
    exact add_le_add (mul_le_mul_of_nonneg_left herror
      (show 0 ≤ 2 * C from mul_nonneg (by norm_num) hC)) le_rfl
  have hgeom : ((P : ℝ) ^ m)⁻¹ ≤ (1 - p) ^ m := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hPr.le) (inv_nat_lt_one_sub p P hp hP).le m
  have hcoef : 0 ≤ (4 * C + 2 / c) / Real.log s := by positivity
  have habsorb := mul_le_mul_of_nonneg_left hgeom hcoef
  nlinarith only [hsplit, hbad, hrem, habsorb]

end Probability
end FiniteAvalanches.Probability.Multiscale
