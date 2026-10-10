import FiniteAvalanches.Probability.Radius.Cylinders
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Supporting finite-to-infinite passage. Convergence hypotheses are explicit;
neither existence of a local limit nor any source tail estimate is asserted here.
Every approximating law is the actual zero extension of the original finite law. -/
namespace FiniteAvalanches.Probability
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

/-- The actual finite field law, merely packaged with its proved mass-one certificate. -/
def finiteFieldProbability (N : ℕ) : MeasureTheory.ProbabilityMeasure StableField :=
  ⟨FiniteWired.finiteFieldLaw N, inferInstance⟩

theorem finiteFieldProbability_toMeasure (N : ℕ) :
    (finiteFieldProbability N : Measure StableField) = FiniteWired.finiteFieldLaw N := rfl

theorem measure_finite_coordinate_event (μ : Measure StableField) (F : Finset Site2)
    (E : Set StableField)
    (hE : ∀ η η' : StableField, (∀ x ∈ F, η' x = η x) → (η' ∈ E ↔ η ∈ E)) :
    μ E = ∑ p ∈ (F.restrict '' E).toFinite.toFinset, μ {η | F.restrict η = p} := by
  have hf : Measurable (F.restrict : StableField → F → Fin 4) :=
    measurable_pi_lambda _ (fun x => measurable_pi_apply x.val)
  have hs := sum_measure_preimage_singleton (μ := μ) (F.restrict '' E).toFinite.toFinset
    (fun p _ => (measurableSet_singleton p).preimage hf)
  have hp (p : F → Fin 4) : (F.restrict : StableField → F → Fin 4) ⁻¹' {p} =
      {η : StableField | F.restrict η = p} := by
    ext η
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  simp_rw [hp] at hs
  rw [Set.Finite.coe_toFinset] at hs
  exact (congrArg μ (finite_coordinate_event_eq_cylinder F E hE)).trans hs.symm

theorem tendsto_finite_coordinate_event (μ : Measure StableField) (F : Finset Site2)
    (E : Set StableField)
    (hE : ∀ η η' : StableField, (∀ x ∈ F, η' x = η x) → (η' ∈ E ↔ η ∈ E))
    (hμ : ∀ p : F → Fin 4, Tendsto
      (fun N : ℕ => FiniteWired.finiteFieldLaw N {η | F.restrict η = p})
      atTop (nhds (μ {η | F.restrict η = p}))) :
    Tendsto (fun N : ℕ => FiniteWired.finiteFieldLaw N E) atTop (nhds (μ E)) := by
  simp_rw [measure_finite_coordinate_event _ F E hE]
  exact tendsto_finsetSum _ (fun p _ => hμ p)

theorem tendsto_radius_le_of_marginals (μ : Measure StableField)
    (hμ : ∀ (F : Finset Site2) (p : F → Fin 4), Tendsto
      (fun N : ℕ => FiniteWired.finiteFieldLaw N {η | F.restrict η = p})
      atTop (nhds (μ {η | F.restrict η = p}))) (o : Site2) (R : ℕ) :
    Tendsto (fun N : ℕ => FiniteWired.finiteFieldLaw N
      {η | radius η o ≤ (R : WithTop ℕ)}) atTop
      (nhds (μ {η | radius η o ≤ (R : WithTop ℕ)})) :=
  tendsto_finite_coordinate_event μ _ _
    (fun _ _ => radius_le_iff_of_agree_box o R) (hμ _)

theorem tendsto_radius_gt_of_marginals (μ : Measure StableField)
    (hμ : ∀ (F : Finset Site2) (p : F → Fin 4), Tendsto
      (fun N : ℕ => FiniteWired.finiteFieldLaw N {η | F.restrict η = p})
      atTop (nhds (μ {η | F.restrict η = p}))) (o : Site2) (R : ℕ) :
    Tendsto (fun N : ℕ => FiniteWired.finiteFieldLaw N
      {η | (R : WithTop ℕ) < radius η o}) atTop
      (nhds (μ {η | (R : WithTop ℕ) < radius η o})) := by
  apply tendsto_finite_coordinate_event μ (boxSites (siteRadius 0 o + R + 1)) _
  · intro η η' heq
    change (R : WithTop ℕ) < radius η' o ↔ (R : WithTop ℕ) < radius η o
    simpa only [not_le] using not_congr (radius_le_iff_of_agree_box o R heq)
  · exact hμ _

theorem tendsto_radius_le_of_weak (μ : MeasureTheory.ProbabilityMeasure StableField)
    (hμ : Tendsto finiteFieldProbability atTop (nhds μ)) (o : Site2) (R : ℕ) :
    Tendsto (fun N : ℕ => FiniteWired.finiteFieldLaw N
      {η | radius η o ≤ (R : WithTop ℕ)}) atTop
      (nhds ((μ : Measure StableField) {η | radius η o ≤ (R : WithTop ℕ)})) :=
  MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ
    (by rw [(isClopen_radius_le o R).frontier_eq]; exact measure_empty)

theorem tendsto_radius_gt_of_weak (μ : MeasureTheory.ProbabilityMeasure StableField)
    (hμ : Tendsto finiteFieldProbability atTop (nhds μ)) (o : Site2) (R : ℕ) :
    Tendsto (fun N : ℕ => FiniteWired.finiteFieldLaw N
      {η | (R : WithTop ℕ) < radius η o}) atTop
      (nhds ((μ : Measure StableField) {η | (R : WithTop ℕ) < radius η o})) :=
  MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ
    (by rw [(isClopen_radius_gt o R).frontier_eq]; exact measure_empty)

end
end FiniteAvalanches.Probability
