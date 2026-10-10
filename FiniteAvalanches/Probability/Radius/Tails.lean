import FiniteAvalanches.Probability.Radius.Limits

/-! Supporting transfer of independently established finite-field tail bounds.
The convergence and finite estimates are honest inputs, not claimed source
results. Vanishing tails give literal finite legal stabilization at every source
whose estimates are supplied; no translation invariance is silently assumed. -/
namespace FiniteAvalanches.Probability
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

theorem radius_tail_le_of_marginals (μ : Measure StableField)
    (hμ : ∀ (F : Finset Site2) (p : F → Fin 4), Tendsto
      (fun N : ℕ => FiniteWired.finiteFieldLaw N {η | F.restrict η = p})
      atTop (nhds (μ {η | F.restrict η = p}))) (o : Site2) (R : ℕ) (b : ℝ≥0∞)
    (hB : ∀ᶠ N : ℕ in atTop,
      FiniteWired.finiteFieldLaw N {η | (R : WithTop ℕ) < radius η o} ≤ b) :
    μ {η | (R : WithTop ℕ) < radius η o} ≤ b :=
  le_of_tendsto (tendsto_radius_gt_of_marginals μ hμ o R) hB

theorem radius_tail_le_of_weak (μ : MeasureTheory.ProbabilityMeasure StableField)
    (hμ : Tendsto finiteFieldProbability atTop (nhds μ)) (o : Site2) (R : ℕ) (b : ℝ≥0∞)
    (hB : ∀ᶠ N : ℕ in atTop,
      FiniteWired.finiteFieldLaw N {η | (R : WithTop ℕ) < radius η o} ≤ b) :
    (μ : Measure StableField) {η | (R : WithTop ℕ) < radius η o} ≤ b :=
  le_of_tendsto (tendsto_radius_gt_of_weak μ hμ o R) hB

theorem radius_tail_real_le_of_weak (μ : MeasureTheory.ProbabilityMeasure StableField)
    (hμ : Tendsto finiteFieldProbability atTop (nhds μ)) (o : Site2) (R : ℕ) (b : ℝ)
    (hB : ∀ᶠ N : ℕ in atTop,
      (FiniteWired.finiteFieldLaw N).real {η | (R : WithTop ℕ) < radius η o} ≤ b) :
    (μ : Measure StableField).real {η | (R : WithTop ℕ) < radius η o} ≤ b :=
  le_of_tendsto
    ((ENNReal.tendsto_toReal (measure_ne_top (μ : Measure StableField) _)).comp
      (tendsto_radius_gt_of_weak μ hμ o R)) hB

theorem ae_finiteStabilizable_of_radius_tail_bound (μ : Measure StableField) (o : Site2)
    (b : ℕ → ℝ≥0∞) (hb : Tendsto b atTop (nhds 0))
    (hB : ∀ R : ℕ, μ {η | (R : WithTop ℕ) < radius η o} ≤ b R) :
    ∀ᵐ η ∂μ, FiniteStabilizable η o := by
  rw [ae_iff]
  apply le_antisymm _ bot_le
  apply ge_of_tendsto' hb
  intro R
  apply (measure_mono _).trans (hB R)
  intro η hη
  change ¬ FiniteStabilizable η o at hη
  change (R : WithTop ℕ) < radius η o
  rw [(radius_eq_top_iff η o).mpr hη]
  exact WithTop.coe_lt_top R

theorem ae_all_finiteStabilizable_of_radius_tail_bounds (μ : Measure StableField)
    (b : Site2 → ℕ → ℝ≥0∞) (hb : ∀ o, Tendsto (b o) atTop (nhds 0))
    (hB : ∀ (o : Site2) (R : ℕ), μ {η | (R : WithTop ℕ) < radius η o} ≤ b o R) :
    ∀ᵐ η ∂μ, ∀ o : Site2, FiniteStabilizable η o :=
  ae_all_iff.mpr (fun o => ae_finiteStabilizable_of_radius_tail_bound μ o (b o) (hb o) (hB o))

theorem ae_finiteStabilizable_of_weak_tail_bounds
    (μ : MeasureTheory.ProbabilityMeasure StableField)
    (hμ : Tendsto finiteFieldProbability atTop (nhds μ)) (o : Site2)
    (b : ℕ → ℝ≥0∞) (hb : Tendsto b atTop (nhds 0))
    (hB : ∀ R : ℕ, ∀ᶠ N : ℕ in atTop,
      FiniteWired.finiteFieldLaw N {η | (R : WithTop ℕ) < radius η o} ≤ b R) :
    ∀ᵐ η ∂(μ : Measure StableField), FiniteStabilizable η o :=
  ae_finiteStabilizable_of_radius_tail_bound (μ : Measure StableField) o b hb
    (fun R => radius_tail_le_of_weak μ hμ o R (b R) (hB R))

theorem ae_all_finiteStabilizable_of_weak_tail_bounds
    (μ : MeasureTheory.ProbabilityMeasure StableField)
    (hμ : Tendsto finiteFieldProbability atTop (nhds μ))
    (b : Site2 → ℕ → ℝ≥0∞) (hb : ∀ o, Tendsto (b o) atTop (nhds 0))
    (hB : ∀ (o : Site2) (R : ℕ), ∀ᶠ N : ℕ in atTop,
      FiniteWired.finiteFieldLaw N {η | (R : WithTop ℕ) < radius η o} ≤ b o R) :
    ∀ᵐ η ∂(μ : Measure StableField), ∀ o : Site2, FiniteStabilizable η o :=
  ae_all_iff.mpr (fun o => ae_finiteStabilizable_of_weak_tail_bounds μ hμ o (b o) (hb o) (hB o))

end
end FiniteAvalanches.Probability
