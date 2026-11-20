import FiniteAvalanches.Wilson.Lattice.WiredLimitDualTree

/-! Finite dual detours around selected primal edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- A selected primal edge has a finite simple dual detour whose every crossed
primal edge is absent. -/
theorem exists_dual_detour_of_tree (ω : EdgeField) (hdual : IsTree (dualField ω))
    (e : LatticeEdge) (he : ω e = true) :
    let d := crossingEdgeEquiv.symm e
    ∃ p : (toGraph (dualField ω)).Walk d.val.out.1 d.val.out.2,
      p.IsPath ∧ d.val ∉ p.edges ∧
      ∀ f : LatticeEdge, f.val ∈ p.edges → ω (crossingEdgeEquiv f) = false := by
  let d := crossingEdgeEquiv.symm e
  let p := FiniteAvalanches.Trees.RootedPaths.path hdual d.val.out.1 d.val.out.2
  have hzero : dualField ω d = false := by
    rw [dualField_apply_crossing]
    simp only [d, Equiv.apply_symm_apply, he, Bool.not_true]
  refine ⟨p, FiniteAvalanches.Trees.RootedPaths.path_isPath hdual _ _, ?_, ?_⟩
  · intro hp
    have hmem : d.val ∈ (toGraph (dualField ω)).edgeSet := p.edges_subset_edgeSet hp
    have hone := (edge_mem_toGraph_iff (dualField ω) d).mp hmem
    rw [hzero] at hone
    contradiction
  · intro f hf
    have hmem : f.val ∈ (toGraph (dualField ω)).edgeSet := p.edges_subset_edgeSet hf
    have hone := (edge_mem_toGraph_iff (dualField ω) f).mp hmem
    rw [dualField_apply_crossing] at hone
    cases hv : ω (crossingEdgeEquiv f) <;> simp_all

/-- Almost surely, every selected primal edge has a finite simple dual detour. -/
theorem wiredLimit_ae_dual_detours (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν)) :
    ∀ᵐ ω ∂(ν : Measure EdgeField), ∀ e : LatticeEdge, ω e = true →
      let d := crossingEdgeEquiv.symm e
      ∃ p : (toGraph (dualField ω)).Walk d.val.out.1 d.val.out.2,
        p.IsPath ∧ d.val ∉ p.edges ∧
        ∀ f : LatticeEdge, f.val ∈ p.edges → ω (crossingEdgeEquiv f) = false := by
  filter_upwards [wiredLimit_ae_tree_and_dual_tree ν hν] with ω hω e he
  exact exists_dual_detour_of_tree ω hω.2 e he

end
end FiniteAvalanches.Wilson.Lattice
