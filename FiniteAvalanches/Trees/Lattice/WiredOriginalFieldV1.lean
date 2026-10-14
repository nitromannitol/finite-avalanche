import FiniteAvalanches.Trees.Lattice.FiniteFixedCut

                                                                                    
                                                         

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice.CurrentOriginalField

open LatticeProb FiniteAvalanches.Sandpile TreeMeasurability11 Filter MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- A coordinate is selected exactly when its original wired copy is selected. -/
def originalWiredField {N : ℕ} (t : (WiredTrees.graph N).SpanningTree) : EdgeField :=
  fun f => decide (∃ e : FiniteWired.Edge N, e ∈ t.val ∧ originalCopyEdge e = f)

theorem originalCopyEdge_injective (N : ℕ) :
    Function.Injective (@originalCopyEdge N) := by
  intro e f h
  cases e with
  | inl e =>
    exact (FixedCutLimit12.originalCopyEdge_eq_internal e f h.symm).symm
  | inr e =>
    cases f with
    | inl f =>
      have hf := FixedCutLimit12.originalCopyEdge_eq_internal f (.inr e) h
      cases hf
    | inr f =>
      have hs := Sym2.eq_iff.mp (congrArg Subtype.val h)
      rcases hs with hs | hs
      · have hx := FiniteWired.site_injective N hs.1
        have hd : e.val.2 = f.val.2 := by
          apply FiniteWired.step_injective
          rw [hs.1] at hs
          exact add_left_cancel hs.2
        exact congrArg Sum.inr (Subtype.ext (Prod.ext hx hd))
      · exact False.elim (e.property
          (hs.2 ▸ fun i => (f.val.1 i).property))

theorem originalWiredField_eq_true {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (f : LatticeEdge) : originalWiredField t f = true ↔
      ∃ e : FiniteWired.Edge N, e ∈ t.val ∧ originalCopyEdge e = f := by
  simp only [originalWiredField, decide_eq_true_eq]

theorem originalWiredField_copy_iff {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (e : FiniteWired.Edge N) :
    originalWiredField t (originalCopyEdge e) = true ↔ e ∈ t.val := by
  rw [originalWiredField_eq_true]
  constructor
  · rintro ⟨f, hf, he⟩
    exact (originalCopyEdge_injective N he) ▸ hf
  · intro he
    exact ⟨e, he, rfl⟩

/-- An exit remains the actual original nearest-neighbor coordinate, with its copy ID. -/
theorem originalWiredField_exit_iff {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (e : FiniteWired.ExitEdge N) :
    originalWiredField t (originalCopyEdge (.inr e)) = true ↔ .inr e ∈ t.val :=
  originalWiredField_copy_iff t (.inr e)

theorem wiredField_exit_eq_false {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (e : FiniteWired.ExitEdge N) : wiredField t (originalCopyEdge (.inr e)) = false := by
  apply wiredField_eq_false_of_no_internal
  intro i hi
  have he := FixedCutLimit12.originalCopyEdge_eq_internal i (.inr e) hi.symm
  cases he

                                                                                      
theorem originalWiredField_eq_wiredField_internal {N : ℕ}
    (t : (WiredTrees.graph N).SpanningTree) (i : FiniteWired.InteriorEdge N) :
    originalWiredField t (interiorEdge i) = wiredField t (interiorEdge i) := by
  have he : originalWiredField t (interiorEdge i) = true ↔
      wiredField t (interiorEdge i) = true := by
    have hi := originalWiredField_copy_iff t (.inl i)
    change originalWiredField t (interiorEdge i) = true ↔ .inl i ∈ t.val at hi
    exact hi.trans (wiredField_internal_iff t i).symm
  cases h1 : originalWiredField t (interiorEdge i) <;>
    cases h2 : wiredField t (interiorEdge i) <;> simp_all

                                                                                         
theorem eventually_internal_representative (f : LatticeEdge) :
    ∀ᶠ N : ℕ in atTop, ∃ i : FiniteWired.InteriorEdge N, interiorEdge i = f := by
  rcases f with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | hf u v =>
    filter_upwards [eventually_ge_atTop (max (siteRadius 0 u) (siteRadius 0 v))] with N hN
    have hu : FiniteWired.inBox N u := (mem_box_sites N u).mp
      ((site_radius_zero_le_iff u N).mp ((le_max_left _ _).trans hN))
    have hv : FiniteWired.inBox N v := (mem_box_sites N v).mp
      ((site_radius_zero_le_iff v N).mp ((le_max_right _ _).trans hN))
    obtain ⟨k, h | h⟩ := he
    · exact ⟨⟨(FiniteWired.activeOfSite N u hu, FiniteWired.activeOfSite N v hv), k, h⟩,
        Subtype.ext rfl⟩
    · exact ⟨⟨(FiniteWired.activeOfSite N v hv, FiniteWired.activeOfSite N u hu), k, h⟩,
        Subtype.ext Sym2.eq_swap⟩

/-- One cofinal threshold works for the whole finite coordinate family and every tree. -/
theorem eventually_finite_field_agreement (F : Finset LatticeEdge) :
    ∀ᶠ N : ℕ in atTop, ∀ t : (WiredTrees.graph N).SpanningTree,
      ∀ f ∈ F, originalWiredField t f = wiredField t f := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert f F _ ih =>
    filter_upwards [eventually_internal_representative f, ih] with N hf hF t e he
    rcases Finset.mem_insert.mp he with rfl | he
    · obtain ⟨i, hi⟩ := hf
      rw [← hi]
      exact originalWiredField_eq_wiredField_internal t i
    · exact hF t e he

/-- Exact finite cylinders coincide cofinally, on the same actual copied-tree carrier. -/
theorem eventually_cylinder_preimage_eq (F : Finset LatticeEdge) (p : F → Bool) :
    ∀ᶠ N : ℕ in atTop,
      {t : (WiredTrees.graph N).SpanningTree | originalWiredField t ∈ cylinder F p} =
      {t : (WiredTrees.graph N).SpanningTree | wiredField t ∈ cylinder F p} := by
  filter_upwards [eventually_finite_field_agreement F] with N hN
  have he (t : (WiredTrees.graph N).SpanningTree) :
      F.restrict (originalWiredField t) = F.restrict (wiredField t) := by
    funext f
    exact hN t f.val f.property
  ext t
  change F.restrict (originalWiredField t) = p ↔ F.restrict (wiredField t) = p
  rw [he t]

end
end FiniteAvalanches.Trees.Lattice.CurrentOriginalField
