import FiniteAvalanches.Wilson.Lattice.WiredSamplerEdges

/-! Original lattice observations inside finite wired boxes. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- A lattice edge with both endpoints in the box has an original interior copy. -/
theorem exists_interiorEdge_of_inBox (B : ℕ) (e : LatticeEdge)
    (hbox : ∀ z ∈ e.val, FiniteWired.inBox B z) :
    ∃ i : FiniteWired.InteriorEdge B, interiorEdge i = e := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | _ u v =>
    have hu : FiniteWired.inBox B u := hbox u (by simp)
    have hv : FiniteWired.inBox B v := hbox v (by simp)
    change (lattice 2).Adj u v at he
    obtain ⟨j, hj | hj⟩ := he
    · let i : FiniteWired.InteriorEdge B :=
        ⟨(FiniteWired.activeOfSite B u hu, FiniteWired.activeOfSite B v hv),
          ⟨j, by simpa only [FiniteWired.site_activeOfSite] using hj⟩⟩
      refine ⟨i, Subtype.ext ?_⟩
      simp only [interiorEdge, FiniteWired.site_activeOfSite, i]
    · let i : FiniteWired.InteriorEdge B :=
        ⟨(FiniteWired.activeOfSite B v hv, FiniteWired.activeOfSite B u hu),
          ⟨j, by simpa only [FiniteWired.site_activeOfSite] using hj⟩⟩
      refine ⟨i, Subtype.ext ?_⟩
      simp only [interiorEdge, FiniteWired.site_activeOfSite, i]
      exact Sym2.eq_swap

/-- Each endpoint of an interior copy is an endpoint of its lattice edge. -/
theorem interiorEdge_endpoint_mem {B : ℕ} (i : FiniteWired.InteriorEdge B) :
    FiniteWired.site i.val.1 ∈ (interiorEdge i).val ∧
      FiniteWired.site i.val.2 ∈ (interiorEdge i).val := by
  simp only [interiorEdge, Sym2.mem_iff, eq_self, true_or, or_true, and_self]

/-- An interior edge indicator is the indicator of its original copied edge. -/
theorem finiteEdgeField_internal_eq (R : RootPair) (B : ℕ)
    (F : FiniteForest R B) (i : FiniteWired.InteriorEdge B) :
    finiteEdgeField R B F (interiorEdge i) = decide (Sum.inl i ∈ F.val) := by
  unfold finiteEdgeField
  apply Bool.decide_congr
  constructor
  · rintro ⟨j, hj, he⟩
    exact (interiorEdge_injective B he) ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

end
end FiniteAvalanches.Wilson.Lattice
