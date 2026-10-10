import FiniteAvalanches.External.SandpileLimit

namespace FiniteAvalanches.External.SandpileLimit

open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
  FiniteAvalanches.Probability
open scoped ENNReal Classical

noncomputable section

theorem IsInfiniteVolumeLaw.tendsto_boxes {μ : ProbabilityMeasure StableField}
    (h : IsInfiniteVolumeLaw μ) : Tendsto finiteFieldProbability atTop (nhds μ) :=
  Tendsto.congr (fun n => finiteFieldProbabilityOn_boxSites n)
    (h (fun n => boxSites n) isExhaustion_boxSites)

theorem tendsto_cylinder_of_tendsto_boxes (μ : ProbabilityMeasure StableField)
    (hμ : Tendsto finiteFieldProbability atTop (nhds μ)) (F : Finset Site2) (ζ : StableField) :
    Tendsto (fun N : ℕ => FiniteWired.finiteFieldLaw N {η | ∀ x ∈ F, η x = ζ x}) atTop
      (nhds ((μ : Measure StableField) {η | ∀ x ∈ F, η x = ζ x})) := by
  have hE : ∀ η η' : StableField, (∀ x ∈ F, η' x = η x) →
      (η' ∈ {η : StableField | ∀ x ∈ F, η x = ζ x} ↔ η ∈ {η : StableField | ∀ x ∈ F, η x = ζ x}) := by
    intro η η' h
    simp only [Set.mem_setOf_eq]
    exact forall₂_congr (fun x hx => by rw [h x hx])
  exact MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ
    (by rw [(isClopen_finite_coordinate_event F _ hE).frontier_eq]; exact measure_empty)

theorem IsInfiniteVolumeLaw.unique {μ ν : ProbabilityMeasure StableField}
    (hμ : IsInfiniteVolumeLaw μ) (hν : IsInfiniteVolumeLaw ν) : μ = ν :=
  Subtype.ext (local_limit_unique (μ : Measure StableField) (ν : Measure StableField)
    (tendsto_cylinder_of_tendsto_boxes μ hμ.tendsto_boxes)
    (tendsto_cylinder_of_tendsto_boxes ν hν.tendsto_boxes))

theorem existsUnique_infiniteVolumeLaw : ∃! μ : ProbabilityMeasure StableField, IsInfiniteVolumeLaw μ := by
  obtain ⟨μ, hμ, -⟩ := exists_infiniteVolumeLaw
  exact ⟨μ, hμ, fun ν hν => hν.unique hμ⟩

end

end FiniteAvalanches.External.SandpileLimit
