import FiniteAvalanches.Wilson.Lattice.WiredDualFaceLaw
import FiniteAvalanches.Wilson.Lattice.LatticeBranchHorizon

/-! Fixed dual observations eventually avoid the wired boundary. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- Every fixed finite set of dual edges eventually crosses interior wired copies. -/
theorem eventually_dualEdges_have_interior_copies (E : Finset LatticeEdge) :
    ∀ᶠ B : ℕ in atTop, ∀ e ∈ E, ∃ i : FiniteWired.InteriorEdge B,
      wiredCopyDualEdge (.inl i) = e := by
  have h : ∀ᶠ B : ℕ in atTop, ∀ e : E,
      FiniteWired.inBox B (crossingEdgeEquiv e.val).val.out.1 ∧
      FiniteWired.inBox B (crossingEdgeEquiv e.val).val.out.2 :=
    eventually_all.mpr (fun e =>
      (eventually_finiteWired_inBox (crossingEdgeEquiv e.val).val.out.1).and
        (eventually_finiteWired_inBox (crossingEdgeEquiv e.val).val.out.2))
  filter_upwards [h] with B hB e he
  have hbox : ∀ z ∈ (crossingEdgeEquiv e).val, FiniteWired.inBox B z := by
    intro z hz
    have hz' : z = (crossingEdgeEquiv e).val.out.1 ∨
        z = (crossingEdgeEquiv e).val.out.2 := by
      rw [← (crossingEdgeEquiv e).val.out_eq] at hz
      exact Sym2.mem_iff.mp hz
    rcases hz' with rfl | rfl
    · exact (hB ⟨e, he⟩).1
    · exact (hB ⟨e, he⟩).2
  obtain ⟨i, hi⟩ := exists_interiorEdge_of_inBox B (crossingEdgeEquiv e) hbox
  refine ⟨i, ?_⟩
  change crossingEdgeEquiv.symm (interiorEdge i) = e
  rw [hi, Equiv.symm_apply_apply]

/-- Complementary-tree bijections identify each fixed dual cylinder for all
sufficiently large wired boxes. -/
theorem eventually_finite_dual_cylinder_eq_dualFaceLaw
    (φ : ∀ B, (WiredTrees.graph B).SpanningTree ≃ (wiredDualFaceGraph B).SpanningTree)
    (hφ : ∀ B t, (φ B t).val = t.valᶜ) (E : Finset LatticeEdge) (p : E → Bool) :
    ∀ᶠ B : ℕ in atTop,
      finiteLaw B (dualField ⁻¹' cylinder E p) = wiredDualFaceLaw B (cylinder E p) := by
  filter_upwards [eventually_dualEdges_have_interior_copies E] with B hB
  exact finite_dual_cylinder_eq_dualFaceLaw_of_tree_equiv B (φ B) (hφ B) E p hB

end
end FiniteAvalanches.Wilson.Lattice
