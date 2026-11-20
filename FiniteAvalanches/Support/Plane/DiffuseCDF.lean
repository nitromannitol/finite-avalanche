import FiniteAvalanches.Support.Plane.CantorDiffuse
import Mathlib.Probability.CDF

/-!
# Distribution functions of diffuse measures

A probability measure on the real line with null singletons has a continuous
cumulative distribution function.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set MeasureTheory ProbabilityTheory

/-- The cumulative distribution function of a diffuse real probability measure
is continuous. -/
theorem continuous_cdf_of_null_singletons (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ {x} = 0) : Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hzero : ENNReal.ofReal (cdf μ x - Function.leftLim (cdf μ) x) = 0 := by
    rw [← StieltjesFunction.measure_singleton, measure_cdf, hμ x]
  have hle : cdf μ x ≤ Function.leftLim (cdf μ) x := by
    have h := ENNReal.ofReal_eq_zero.mp hzero
    linarith
  have heq : Function.leftLim (cdf μ) x = cdf μ x :=
    le_antisymm ((cdf μ).mono.leftLim_le le_rfl) hle
  apply continuousAt_iff_continuous_left_right.mpr
  exact ⟨continuousWithinAt_Iio_iff_Iic.mp
    ((cdf μ).mono.continuousWithinAt_Iio_iff_leftLim_eq.mpr heq),
    (cdf μ).right_continuous x⟩

/-- The cumulative distribution function of a probability on the unit interval,
with values in the unit interval. -/
noncomputable def unitIntervalCDF (μ : Measure unitInterval) (t : unitInterval) : unitInterval :=
  ⟨cdf (μ.map Subtype.val) t.val,
    cdf_nonneg (μ.map Subtype.val) t.val, cdf_le_one (μ.map Subtype.val) t.val⟩

/-- The distribution function of a diffuse probability on the unit interval is
continuous and monotone. -/
theorem unitIntervalCDF_continuous_monotone (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (hμ : ∀ t : unitInterval, μ {t} = 0) :
    Continuous (unitIntervalCDF μ) ∧ Monotone (unitIntervalCDF μ) := by
  let ν : Measure ℝ := μ.map Subtype.val
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map continuous_subtype_val.measurable.aemeasurable
  have hν : ∀ x : ℝ, ν {x} = 0 := by
    intro x
    rw [show ν = μ.map Subtype.val from rfl,
      Measure.map_apply continuous_subtype_val.measurable (measurableSet_singleton x)]
    by_cases hx : x ∈ unitInterval
    · let t : unitInterval := ⟨x, hx⟩
      have heq : (Subtype.val : unitInterval → ℝ) ⁻¹' {x} = {t} := by
        ext s
        simp only [mem_preimage, mem_singleton_iff]
        exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      rw [heq, hμ t]
    · have heq : (Subtype.val : unitInterval → ℝ) ⁻¹' {x} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        exact hx (by simpa only [mem_preimage, mem_singleton_iff] using ht ▸ t.property)
      simp only [heq, measure_empty]
  refine ⟨?_, ?_⟩
  · exact ((continuous_cdf_of_null_singletons ν hν).comp continuous_subtype_val).subtype_mk _
  · intro s t hst
    exact monotone_cdf ν hst

/-- The distribution function of a diffuse probability fixes the endpoints. -/
theorem unitIntervalCDF_endpoints (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (hμ : ∀ t : unitInterval, μ {t} = 0) :
    unitIntervalCDF μ 0 = 0 ∧ unitIntervalCDF μ 1 = 1 := by
  constructor <;> apply Subtype.ext
  · change cdf (μ.map Subtype.val) (0 : ℝ) = 0
    rw [show (0 : ℝ) = ((0 : unitInterval) : ℝ) from rfl, unitInterval.cdf_eq_real]
    rw [show Icc (0 : unitInterval) 0 = {0} by simp, measureReal_def, hμ 0]
    simp
  · change cdf (μ.map Subtype.val) (1 : ℝ) = 1
    rw [show (1 : ℝ) = ((1 : unitInterval) : ℝ) from rfl, unitInterval.cdf_eq_real]
    rw [show Icc (0 : unitInterval) 1 = univ from Icc_bot_top, measureReal_def, measure_univ]
    simp

/-- The distribution function is constant between two ordered points exactly
when the half-open interval between them has zero measure. -/
theorem unitIntervalCDF_eq_iff_measure_Ioc_eq_zero
    (μ : Measure unitInterval) [IsProbabilityMeasure μ] {s t : unitInterval} (hst : s ≤ t) :
    unitIntervalCDF μ s = unitIntervalCDF μ t ↔ μ (Ioc s t) = 0 := by
  let ν : Measure ℝ := μ.map Subtype.val
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map continuous_subtype_val.measurable.aemeasurable
  have hmeasure : μ (Ioc s t) = ENNReal.ofReal (cdf ν t.val - cdf ν s.val) := by
    have h := (cdf ν).measure_Ioc s.val t.val
    rw [measure_cdf] at h
    rw [show ν = μ.map Subtype.val from rfl,
      Measure.map_apply continuous_subtype_val.measurable measurableSet_Ioc,
      preimage_subtype_val_Ioc] at h
    exact h
  rw [hmeasure, ENNReal.ofReal_eq_zero, sub_nonpos]
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    exact le_of_eq hv.symm
  · intro h
    apply Subtype.ext
    exact le_antisymm (monotone_cdf ν hst) h

end FiniteAvalanches.Electrical.StatementGeometry
