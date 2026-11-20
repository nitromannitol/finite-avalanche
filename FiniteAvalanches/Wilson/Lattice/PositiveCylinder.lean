import FiniteAvalanches.Wilson.Lattice.FiniteUstWeakLimit

/-! Finite edge-inclusion events determine a lattice edge-field law. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- The event that all edges in a finite family are selected. -/
def edgeInclusionEvent (E : Finset LatticeEdge) : Set EdgeField :=
  {ω | ∀ e ∈ E, ω e = true}

/-- Inclusion events are the all-true finite cylinders. -/
theorem edgeInclusionEvent_eq_cylinder (E : Finset LatticeEdge) :
    edgeInclusionEvent E = FiniteAvalanches.Trees.Lattice.cylinder E (fun _ => true) := by
  ext ω
  simp only [edgeInclusionEvent, Set.mem_setOf_eq, FiniteAvalanches.Trees.Lattice.cylinder,
    Finset.restrict_def, funext_iff, Subtype.forall]

/-- Intersections of inclusion events correspond to unions of edge families. -/
theorem edgeInclusionEvent_union (E F : Finset LatticeEdge) :
    edgeInclusionEvent (E ∪ F) = edgeInclusionEvent E ∩ edgeInclusionEvent F := by
  ext ω
  simp only [edgeInclusionEvent, Set.mem_setOf_eq, Finset.mem_union, Set.mem_inter_iff]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

/-- Finite inclusion events generate the full product measurable space. -/
theorem edgeInclusionEvent_generateFrom :
    MeasurableSpace.generateFrom (Set.range edgeInclusionEvent) =
      (inferInstance : MeasurableSpace EdgeField) := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨E, rfl⟩
    rw [edgeInclusionEvent_eq_cylinder]
    exact measurableSet_cylinder _ _
  · rw [MeasurableSpace.pi_eq_generateFrom_projections]
    apply MeasurableSpace.generateFrom_le
    rintro _ ⟨e, A, _, rfl⟩
    have hp : MeasurableSet[MeasurableSpace.generateFrom (Set.range edgeInclusionEvent)]
        (edgeInclusionEvent {e}) :=
      MeasurableSpace.measurableSet_generateFrom ⟨{e}, rfl⟩
    by_cases ht : true ∈ A <;> by_cases hf : false ∈ A
    · have hA : A = Set.univ := by ext b; cases b <;> simp_all
      rw [hA, Set.preimage_univ]
      exact MeasurableSet.univ
    · have hA : A = {true} := by ext b; cases b <;> simp_all
      have he : (Function.eval e ⁻¹' A : Set EdgeField) = edgeInclusionEvent {e} := by
        ext ω
        simp [hA, edgeInclusionEvent]
      rw [he]
      exact hp
    · have hA : A = {false} := by ext b; cases b <;> simp_all
      have he : (Function.eval e ⁻¹' A : Set EdgeField) = (edgeInclusionEvent {e})ᶜ := by
        ext ω
        simp only [hA, Set.mem_preimage, Function.eval, Set.mem_singleton_iff,
          Set.mem_compl_iff, edgeInclusionEvent, Set.mem_setOf_eq, Finset.mem_singleton,
          forall_eq]
        cases h : ω e <;> simp
      rw [he]
      exact hp.compl
    · have hA : A = ∅ := by ext b; cases b <;> simp_all
      rw [hA, Set.preimage_empty]
      exact @MeasurableSet.empty EdgeField (MeasurableSpace.generateFrom (Set.range edgeInclusionEvent))

/-- Finite edge-inclusion events form a pi-system. -/
theorem isPiSystem_edgeInclusionEvent : IsPiSystem (Set.range edgeInclusionEvent) := by
  rintro _ ⟨E, rfl⟩ _ ⟨F, rfl⟩ _
  exact ⟨E ∪ F, edgeInclusionEvent_union E F⟩

/-- Probability laws on edge fields are determined by finite inclusion probabilities. -/
theorem probabilityMeasure_edgeField_eq_of_inclusion (μ ν : ProbabilityMeasure EdgeField)
    (h : ∀ E : Finset LatticeEdge,
      (μ : Measure EdgeField) (edgeInclusionEvent E) =
        (ν : Measure EdgeField) (edgeInclusionEvent E)) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  have huniv : Set.univ ∈ Set.range edgeInclusionEvent := by
    refine ⟨∅, ?_⟩
    ext ω
    simp [edgeInclusionEvent]
  apply Measure.ext_of_generateFrom_of_iUnion (Set.range edgeInclusionEvent)
    (fun _ : ℕ => (Set.univ : Set EdgeField)) edgeInclusionEvent_generateFrom.symm
    isPiSystem_edgeInclusionEvent (Set.iUnion_const _) (fun _ => huniv)
    (fun _ => measure_ne_top _ _)
  rintro _ ⟨E, rfl⟩
  exact h E

end
end FiniteAvalanches.Wilson.Lattice
