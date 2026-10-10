import FiniteAvalanches.Sandpile.ExtendedObservables

/-! Real tail bounds and extended-valued event masses have the same meaning. -/
namespace FiniteAvalanches.Probability
open FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open scoped ENNReal Classical
noncomputable section

/-- Real and extended inequalities agree for finite event masses and a nonnegative bound. -/
theorem real_tail_sum_iff (μ : Measure StableField) [IsFiniteMeasure μ]
    (A B : Set StableField) (b : ℝ) (hb : 0 ≤ b) :
    (μ A).toReal + (μ B).toReal ≤ b ↔ μ A + μ B ≤ ENNReal.ofReal b := by
  rw [← ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top μ B)]
  simpa only [ENNReal.toReal_ofReal hb] using
    (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr
      ⟨measure_ne_top μ A, measure_ne_top μ B⟩)
      (show ENNReal.ofReal b ≠ ⊤ from ENNReal.ofReal_ne_top))

/-- The actual radius and total-count events, for every real nonnegative threshold. -/
theorem real_avalanche_tail_iff (μ : Measure StableField) [IsProbabilityMeasure μ]
    (o : Site2) (R C a : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    (μ {η | ENNReal.ofReal R < extendedCount (radius η o)}).toReal +
      (μ {η | ENNReal.ofReal R < extendedCount (totalTopplings η o)}).toReal ≤
        C * Real.log (R + 2) ^ (-a) ↔
    μ {η | ENNReal.ofReal R < extendedCount (radius η o)} +
      μ {η | ENNReal.ofReal R < extendedCount (totalTopplings η o)} ≤
        ENNReal.ofReal (C * Real.log (R + 2) ^ (-a)) := by
  apply real_tail_sum_iff
  exact mul_nonneg hC (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)

end
end FiniteAvalanches.Probability
