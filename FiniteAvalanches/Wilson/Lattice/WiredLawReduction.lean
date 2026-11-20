import FiniteAvalanches.Wilson.Lattice.WiredCylinderLaw

/-! Reduction of the recurrent Wilson law to its rooted-forest support. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- Every finite query list is the range of its zero-based enumeration. -/
theorem list_eq_range_getD (L : List (Site 2)) :
    ((List.range L.length).map (fun i => L.getD i 0)) = L := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem L 0 hi']

/-- The cylinder-law characterization holds for every literal finite query list. -/
theorem IsWilsonCylinderLaw.jointEvent_eq_sampler (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν)
    (L : List (Site 2)) (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, z ∈ L) (hD : ∀ z ∈ D, z ∈ L) :
    (ν : Measure ForestField) (jointEvent E D pe pc) = wilsonRows (samplerEvent R L E D pe pc) := by
  let x : ℕ → Site 2 := fun i => L.getD i 0
  have hmem (z : Site 2) (hz : z ∈ L) : ∃ i < L.length, x i = z := by
    obtain ⟨i, hi, hiz⟩ := List.mem_iff_getElem.mp hz
    exact ⟨i, hi, (List.getD_eq_getElem L 0 hi).trans hiz⟩
  have h := hν x L.length E D pe pc
    (fun e he z hz => hmem z (hE e he z hz)) (fun z hz => hmem z (hD z hz))
  simpa only [x, list_eq_range_getD] using h

/-- Any Wilson law has the sampler's complete joint cylinder distributions. -/
theorem IsWilsonLaw.isCylinderLaw (R : RootPair) (ν : ProbabilityMeasure ForestField)
    (hν : IsWilsonLaw R ν) : IsWilsonCylinderLaw R ν := by
  intro x n E D pe pc hE hD
  apply hν.2 ((List.range n).map x) E D pe pc
  · intro e he z hz
    obtain ⟨i, hi, rfl⟩ := hE e he z hz
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := hD z hz
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- The Wilson law assertion follows once the cylinder law is shown to be
supported on the prescribed rooted colored forests. -/
theorem wilsonLaw_existsUnique_of_cylinder_support (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν)
    (hsupport : ∀ᵐ ω ∂(ν : Measure ForestField), is_colored_forest R ω) :
    (∃! μ : ProbabilityMeasure ForestField, IsWilsonLaw R μ) ∧
    ∀ μ : ProbabilityMeasure ForestField, IsWilsonLaw R μ →
      Tendsto (finiteForestProbability R) atTop (nhds μ) := by
  have hlaw : IsWilsonLaw R ν := ⟨hsupport, IsWilsonCylinderLaw.jointEvent_eq_sampler R ν hν⟩
  constructor
  · exact ⟨ν, hlaw, fun μ hμ => isWilsonLaw_unique R hμ hlaw⟩
  · intro μ hμ
    exact finiteForestProbability_tendsto_of_cylinderLaw R μ (IsWilsonLaw.isCylinderLaw R μ hμ)

end
end FiniteAvalanches.Wilson.Lattice
