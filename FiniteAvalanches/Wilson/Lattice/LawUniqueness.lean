import FiniteAvalanches.Wilson.Lattice.Sampler
import Mathlib.Data.Finset.Sum
import Mathlib.MeasureTheory.Constructions.Cylinders

/-! Finite joint patterns determine the two-color Wilson law. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Trees.Lattice MeasureTheory
open scoped Classical

noncomputable section

private theorem measure_eq_of_bool_patterns {ι : Type*} (μ ν : Measure (ι → Bool))
    [IsFiniteMeasure μ]
    (h : ∀ (F : Finset ι) (p : F → Bool),
      μ {η | F.restrict η = p} = ν {η | F.restrict η = p}) : μ = ν := by
  have hm (F : Finset ι) : Measure.map F.restrict μ = Measure.map F.restrict ν := by
    apply Measure.ext_of_singleton
    intro p
    have hf : Measurable (F.restrict : (ι → Bool) → F → Bool) :=
      measurable_pi_lambda _ (fun x => measurable_pi_apply x.val)
    rw [Measure.map_apply hf (measurableSet_singleton p),
      Measure.map_apply hf (measurableSet_singleton p)]
    exact h F p
  apply Measure.ext_of_generateFrom_of_iUnion
    (measurableCylinders (fun _ : ι => Bool)) (fun _ : ℕ => (Set.univ : Set (ι → Bool)))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (Set.iUnion_const _) (fun _ => univ_mem_measurableCylinders _) (fun _ => measure_ne_top μ _)
  intro S hS
  obtain ⟨F, A, hA, rfl⟩ := (mem_measurableCylinders S).mp hS
  have hf : Measurable (F.restrict : (ι → Bool) → F → Bool) :=
    measurable_pi_lambda _ (fun x => measurable_pi_apply x.val)
  simpa only [Measure.map_apply hf hA, MeasureTheory.cylinder] using congrArg (fun m => m A) (hm F)

/-- Probability measures on edge and color fields are determined by their joint patterns. -/
theorem probabilityMeasure_eq_of_jointEvent (μ ν : ProbabilityMeasure ForestField)
    (h : ∀ B D pe pc, (μ : Measure ForestField) (jointEvent B D pe pc) =
      (ν : Measure ForestField) (jointEvent B D pe pc)) : μ = ν := by
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : LatticeEdge ⊕ Site 2 => Bool)).symm
  apply ProbabilityMeasure.toMeasure_injective
  apply e.map_measurableEquiv_injective
  apply measure_eq_of_bool_patterns
  intro F p
  let q : LatticeEdge ⊕ Site 2 → Bool := fun i => if hi : i ∈ F then p ⟨i, hi⟩ else false
  have hm : MeasurableSet {η : (LatticeEdge ⊕ Site 2) → Bool | F.restrict η = p} := by
    exact (measurable_pi_lambda _ (fun x => measurable_pi_apply x.val)) (measurableSet_singleton p)
  rw [Measure.map_apply e.measurable hm, Measure.map_apply e.measurable hm]
  have he : e ⁻¹' {η | F.restrict η = p} =
      jointEvent F.toLeft F.toRight (fun x => q (Sum.inl x)) (fun x => q (Sum.inr x)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, jointEvent, Finset.mem_toLeft,
      Finset.mem_toRight]
    constructor
    · intro hω
      constructor
      · intro x hx
        simpa [q, hx, e, Finset.restrict_def, MeasurableEquiv.sumPiEquivProdPi,
          Equiv.sumPiEquivProdPi] using congrFun hω ⟨Sum.inl x, hx⟩
      · intro x hx
        simpa [q, hx, e, Finset.restrict_def, MeasurableEquiv.sumPiEquivProdPi,
          Equiv.sumPiEquivProdPi] using congrFun hω ⟨Sum.inr x, hx⟩
    · rintro ⟨hl, hr⟩
      funext x
      rcases x with ⟨x, hx⟩
      cases x with
      | inl x => simpa [q, hx, e, Finset.restrict_def, MeasurableEquiv.sumPiEquivProdPi,
          Equiv.sumPiEquivProdPi] using hl x hx
      | inr x => simpa [q, hx, e, Finset.restrict_def, MeasurableEquiv.sumPiEquivProdPi,
          Equiv.sumPiEquivProdPi] using hr x hx
  rw [he]
  exact h _ _ _ _

/-- The finite-pattern characterization specifies at most one Wilson law. -/
theorem isWilsonLaw_unique (R : RootPair) {μ ν : ProbabilityMeasure ForestField}
    (hμ : IsWilsonLaw R μ) (hν : IsWilsonLaw R ν) : μ = ν := by
  apply probabilityMeasure_eq_of_jointEvent
  intro B D pe pc
  let F : Finset (Site 2) := D ∪ B.biUnion (fun e => e.val.toFinset)
  let L := F.toList
  have hB : ∀ e ∈ B, ∀ x ∈ e.val, x ∈ L := by
    intro e he x hx
    apply Finset.mem_toList.mpr
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, Sym2.mem_toFinset.mpr hx⟩)
  have hD : ∀ x ∈ D, x ∈ L := by
    intro x hx
    exact Finset.mem_toList.mpr (Finset.mem_union_left _ hx)
  exact (hμ.2 L B D pe pc hB hD).trans (hν.2 L B D pe pc hB hD).symm

end
end FiniteAvalanches.Wilson.Lattice
