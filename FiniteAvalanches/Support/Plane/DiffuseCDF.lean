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

end FiniteAvalanches.Electrical.StatementGeometry
