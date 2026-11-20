import FiniteAvalanches.Wilson.Lattice.WiredCylinderLimit
import FiniteAvalanches.Wilson.Lattice.LawUniqueness

/-! Existence, uniqueness and weak convergence of the Wilson cylinder law. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- A probability measure has the finite joint distributions of the recurrent
Wilson sampler for all finite query lists. -/
def IsWilsonCylinderLaw (R : RootPair) (ν : ProbabilityMeasure ForestField) : Prop :=
  ∀ (x : ℕ → Site 2) (n : ℕ) (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool),
    (∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z) →
    (∀ z ∈ D, ∃ i < n, x i = z) →
    (ν : Measure ForestField) (jointEvent E D pe pc) =
      wilsonRows (samplerEvent R ((List.range n).map x) E D pe pc)

/-- Finite joint edge and color coordinates admit a single finite query list. -/
theorem exists_finite_queries (E : Finset LatticeEdge) (D : Finset (Site 2)) :
    ∃ (x : ℕ → Site 2) (n : ℕ),
      (∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z) ∧
      (∀ z ∈ D, ∃ i < n, x i = z) := by
  let F : Finset (Site 2) := D ∪ E.biUnion (fun e => e.val.toFinset)
  let L := F.toList
  let x : ℕ → Site 2 := fun i => L.getD i 0
  have hmem (z : Site 2) (hz : z ∈ F) : ∃ i < L.length, x i = z := by
    have hzL : z ∈ L := Finset.mem_toList.mpr hz
    obtain ⟨i, hi, hiz⟩ := List.mem_iff_getElem.mp hzL
    exact ⟨i, hi, (List.getD_eq_getElem L 0 hi).trans hiz⟩
  refine ⟨x, L.length, ?_, ?_⟩
  · intro e he z hz
    apply hmem z
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, Sym2.mem_toFinset.mpr hz⟩)
  · intro z hz
    exact hmem z (Finset.mem_union_left _ hz)

/-- The finite joint distributions determine at most one probability measure. -/
theorem isWilsonCylinderLaw_unique (R : RootPair) {μ ν : ProbabilityMeasure ForestField}
    (hμ : IsWilsonCylinderLaw R μ) (hν : IsWilsonCylinderLaw R ν) : μ = ν := by
  apply probabilityMeasure_eq_of_jointEvent
  intro E D pe pc
  obtain ⟨x, n, hE, hD⟩ := exists_finite_queries E D
  exact (hμ x n E D pe pc hE hD).trans (hν x n E D pe pc hE hD).symm

/-- The recurrent Wilson sampler determines a unique probability measure on
the complete edge and color field. -/
theorem existsUnique_wilsonCylinderLaw (R : RootPair) :
    ∃! ν : ProbabilityMeasure ForestField, IsWilsonCylinderLaw R ν := by
  obtain ⟨ν, hν⟩ := exists_probabilityMeasure_jointEvent_eq_sampler R
  exact ⟨ν, hν, fun μ hμ => isWilsonCylinderLaw_unique R hμ hν⟩

/-- The finite wired forest fields converge weakly to the unique measure with
the Wilson sampler's joint cylinder distributions. -/
theorem finiteForestProbability_tendsto_of_cylinderLaw (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν) :
    Tendsto (finiteForestProbability R) atTop (nhds ν) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ hμ
  apply isWilsonCylinderLaw_unique R ?_ hν
  intro x n E D pe pc hE hD
  exact clusterPoint_jointEvent_eq_sampler R μ hμ x n E D pe pc hE hD

end
end FiniteAvalanches.Wilson.Lattice
