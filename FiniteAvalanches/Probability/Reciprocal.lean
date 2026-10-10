module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-! Reciprocal contact counts use real Bochner expectations, with integrability proved below. -/

set_option autoImplicit false

namespace FiniteAvalanches.Probability

open MeasureTheory

/-- The exact integer-threshold split used for a positive finite contact count. -/
theorem reciprocal_le_indicator (l k : ℕ) (hl : 1 ≤ l) :
    (l : ℝ)⁻¹ ≤ (if l ≤ k then (1 : ℝ) else 0) + ((k : ℝ) + 1)⁻¹ := by
  have hlarge : 1 ≤ (l : ℝ) := by exact_mod_cast hl
  split_ifs with h
  · exact (inv_le_one_of_one_le₀ hlarge).trans
      (le_add_of_nonneg_right (inv_nonneg.mpr (by positivity)))
  · have hkl : k + 1 ≤ l := Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
    have hkl' : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hkl
    simpa only [zero_add] using
      (inv_le_inv₀ (by positivity : (0 : ℝ) < l) (by positivity : (0 : ℝ) < k + 1)).mpr
        hkl'

/-- Real thresholds keep the small-count event strict, including equality on its complement. -/
theorem reciprocal_le_indicator_lt (l : ℕ) (hl : 1 ≤ l) (t : ℝ) (ht : 0 < t) :
    (l : ℝ)⁻¹ ≤ (if (l : ℝ) < t then (1 : ℝ) else 0) + t⁻¹ := by
  have hlarge : 1 ≤ (l : ℝ) := by exact_mod_cast hl
  split_ifs with h
  · exact (inv_le_one_of_one_le₀ hlarge).trans
      (le_add_of_nonneg_right (inv_nonneg.mpr ht.le))
  · simpa only [zero_add] using
      (inv_le_inv₀ (lt_of_lt_of_le zero_lt_one hlarge) ht).mpr (le_of_not_gt h)

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A measurable positive integer count has an integrable real reciprocal. -/
theorem integrable_reciprocal (L : Ω → ℕ) (hL : Measurable L)
    (hpos : ∀ᵐ ω ∂μ, 1 ≤ L ω) :
    Integrable (fun ω => (L ω : ℝ)⁻¹) μ := by
  have hcast : Measurable (fun ω => (L ω : ℝ)) :=
    MeasurableEmbedding.natCast.measurable.comp hL
  apply (integrable_const (1 : ℝ)).mono_nonneg hcast.inv.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => inv_nonneg.mpr (Nat.cast_nonneg _)))
  refine hpos.mono fun ω hω => ?_
  have hlarge : (1 : ℝ) ≤ (L ω : ℝ) := by exact_mod_cast hω
  exact inv_le_one_of_one_le₀ hlarge

/-- Bochner expectation split at the manuscript's event `L ≤ k`. -/
theorem integral_reciprocal_le (L : Ω → ℕ) (hL : Measurable L)
    (hpos : ∀ᵐ ω ∂μ, 1 ≤ L ω) (k : ℕ) :
    (∫ ω, (L ω : ℝ)⁻¹ ∂μ) ≤ μ.real {ω | L ω ≤ k} + ((k : ℝ) + 1)⁻¹ := by
  classical
  have hbad : MeasurableSet {ω | L ω ≤ k} := measurableSet_le hL measurable_const
  have hind := (integrable_const (1 : ℝ) (μ := μ)).indicator hbad
  have hconst := integrable_const (((k : ℝ) + 1)⁻¹) (μ := μ)
  calc
    (∫ ω, (L ω : ℝ)⁻¹ ∂μ) ≤
        ∫ ω, {ω | L ω ≤ k}.indicator (fun _ => (1 : ℝ)) ω + ((k : ℝ) + 1)⁻¹ ∂μ :=
      integral_mono_ae (integrable_reciprocal μ L hL hpos) (hind.add hconst)
        (hpos.mono (fun ω hω => by
          simpa only [Set.indicator_apply, Set.mem_setOf_eq] using
            (reciprocal_le_indicator (L ω) k hω)))
    _ = μ.real {ω | L ω ≤ k} + ((k : ℝ) + 1)⁻¹ := by
      rw [integral_add hind hconst, integral_indicator_const (1 : ℝ) hbad, integral_const]
      simp only [smul_eq_mul, mul_one, probReal_univ, one_mul]

/-- Bochner expectation split at the strict real threshold proposed for the fixed scales. -/
theorem integral_reciprocal_le_lt (L : Ω → ℕ) (hL : Measurable L)
    (hpos : ∀ᵐ ω ∂μ, 1 ≤ L ω) (t : ℝ) (ht : 0 < t) :
    (∫ ω, (L ω : ℝ)⁻¹ ∂μ) ≤ μ.real {ω | (L ω : ℝ) < t} + t⁻¹ := by
  classical
  have hcast : Measurable (fun ω => (L ω : ℝ)) :=
    MeasurableEmbedding.natCast.measurable.comp hL
  have hbad : MeasurableSet {ω | (L ω : ℝ) < t} := measurableSet_lt hcast measurable_const
  have hind := (integrable_const (1 : ℝ) (μ := μ)).indicator hbad
  have hconst := integrable_const t⁻¹ (μ := μ)
  calc
    (∫ ω, (L ω : ℝ)⁻¹ ∂μ) ≤
        ∫ ω, {ω | (L ω : ℝ) < t}.indicator (fun _ => (1 : ℝ)) ω + t⁻¹ ∂μ :=
      integral_mono_ae (integrable_reciprocal μ L hL hpos) (hind.add hconst)
        (hpos.mono (fun ω hω => by
          simpa only [Set.indicator_apply, Set.mem_setOf_eq] using
            (reciprocal_le_indicator_lt (L ω) hω t ht)))
    _ = μ.real {ω | (L ω : ℝ) < t} + t⁻¹ := by
      rw [integral_add hind hconst, integral_indicator_const (1 : ℝ) hbad, integral_const]
      simp only [smul_eq_mul, mul_one, probReal_univ, one_mul]

/-- The real reciprocal expectation agrees with the nonnegative extended-real integral. -/
theorem ofReal_integral_reciprocal (L : Ω → ℕ) (hL : Measurable L)
    (hpos : ∀ᵐ ω ∂μ, 1 ≤ L ω) :
    ENNReal.ofReal (∫ ω, (L ω : ℝ)⁻¹ ∂μ) =
      ∫⁻ ω, ENNReal.ofReal ((L ω : ℝ)⁻¹) ∂μ := by
  exact ofReal_integral_eq_lintegral_ofReal (integrable_reciprocal μ L hL hpos)
    (Filter.Eventually.of_forall (fun ω => inv_nonneg.mpr (Nat.cast_nonneg _)))

end Probability

end FiniteAvalanches.Probability

