import FiniteAvalanches.Probability.Radius.Limits
import FiniteAvalanches.Sandpile.ExtendedObservables

/-! Real thresholds use the literal extended radius, including infinity. The
floor is proved to give the identical event, rather than changing the threshold. -/
namespace FiniteAvalanches.Probability
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

theorem real_radius_tail_eq_floor (o : Site2) (R : ℝ) (hR : 0 ≤ R) :
    {η : StableField | ENNReal.ofReal R < extendedCount (radius η o)} =
      {η | (⌊R⌋₊ : WithTop ℕ) < radius η o} := by
  ext η
  change ENNReal.ofReal R < extendedCount (radius η o) ↔ (⌊R⌋₊ : WithTop ℕ) < radius η o
  cases h : radius η o using WithTop.recTopCoe with
  | top => exact iff_of_true ENNReal.ofReal_lt_top (WithTop.coe_lt_top (⌊R⌋₊ : ℕ))
  | coe n =>
    exact (ofReal_lt_extendedCount_coe R hR n).trans
      ((Nat.floor_lt hR).symm.trans WithTop.coe_lt_coe.symm)

theorem isClopen_real_radius_tail (o : Site2) (R : ℝ) (hR : 0 ≤ R) :
    IsClopen {η : StableField | ENNReal.ofReal R < extendedCount (radius η o)} := by
  rw [real_radius_tail_eq_floor o R hR]
  exact isClopen_radius_gt o ⌊R⌋₊

theorem tendsto_real_radius_tail_of_marginals (μ : Measure StableField)
    (hμ : ∀ (F : Finset Site2) (p : F → Fin 4), Tendsto
      (fun N : ℕ => FiniteWired.finiteFieldLaw N {η | F.restrict η = p})
      atTop (nhds (μ {η | F.restrict η = p}))) (o : Site2) (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun N : ℕ => FiniteWired.finiteFieldLaw N
      {η | ENNReal.ofReal R < extendedCount (radius η o)}) atTop
      (nhds (μ {η | ENNReal.ofReal R < extendedCount (radius η o)})) := by
  simp_rw [real_radius_tail_eq_floor o R hR]
  exact tendsto_radius_gt_of_marginals μ hμ o ⌊R⌋₊

theorem tendsto_real_radius_tail_of_weak (μ : MeasureTheory.ProbabilityMeasure StableField)
    (hμ : Tendsto finiteFieldProbability atTop (nhds μ)) (o : Site2) (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun N : ℕ => FiniteWired.finiteFieldLaw N
      {η | ENNReal.ofReal R < extendedCount (radius η o)}) atTop
      (nhds ((μ : Measure StableField) {η | ENNReal.ofReal R < extendedCount (radius η o)})) := by
  simp_rw [real_radius_tail_eq_floor o R hR]
  exact tendsto_radius_gt_of_weak μ hμ o ⌊R⌋₊

end
end FiniteAvalanches.Probability
