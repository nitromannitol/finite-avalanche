import FiniteAvalanches.Trees.Lattice.SourceObjects
import FiniteAvalanches.Trees.Lattice.EuclideanPaths
import FiniteAvalanches.Trees.Lattice.Dual

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice.PastTail
open LatticeProb SimpleGraph FiniteAvalanches.Trees.Lattice
open scoped Classical
noncomputable section

/-- The outgoing edge is the only selected edge crossing the literal vertex past. -/
theorem selected_crossing_iff_outgoing (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v x y : Site 2) (hxy : (lattice 2).Adj x y)
    (hx : x ∈ vertexPast ω hT hOne v) (hy : y ∉ vertexPast ω hT hOne v) :
    ω ⟨s(x, y), hxy⟩ = true ↔
      (⟨s(x, y), hxy⟩ : LatticeEdge) = outgoingEdge ω hT hOne v := by
  constructor
  · intro hsel
    by_contra hne
    have he : s(x, y) ≠ (outgoingEdge ω hT hOne v).val :=
      fun h => hne (Subtype.ext h)
    have hadj : (cutGraph ω (outgoingEdge ω hT hOne v)).Adj x y :=
      SimpleGraph.deleteEdges_adj.mpr ⟨⟨hxy, hsel⟩, by simpa only [Set.mem_singleton_iff] using he⟩
    apply hy
    rw [vertexPast_eq_cutComponent] at hx ⊢
    exact (mem_cutComponent_iff ω _ v y).mpr
      (hadj.symm.reachable.trans ((mem_cutComponent_iff ω _ v x).mp hx))
  · intro he
    rw [he]
    exact outgoingEdge_selected ω hT hOne v

/-- All other literal boundary edges are absent; their actual crossing dual edges
are selected in the complementary dual field. -/
theorem crossing_dual_selected (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) (p : Site 2 × Fin 2)
    (hcross : (p.1 ∈ vertexPast ω hT hOne v ∧
      p.1 + unit p.2 ∉ vertexPast ω hT hOne v) ∨
      (p.1 ∉ vertexPast ω hT hOne v ∧ p.1 + unit p.2 ∈ vertexPast ω hT hOne v))
    (hne : baseEdge p ≠ outgoingEdge ω hT hOne v) :
    dualField ω (baseEdge (dualBaseInv p)) = true := by
  have hfalse : ω (baseEdge p) = false := by
    cases hsel : ω (baseEdge p) with
    | false => rfl
    | true =>
      exfalso
      rcases hcross with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact hne ((selected_crossing_iff_outgoing ω hT hOne v _ _
          ⟨p.2, Or.inl rfl⟩ hx hy).mp hsel)
      · have h := (selected_crossing_iff_outgoing ω hT hOne v _ _
          (show (lattice 2).Adj (p.1 + unit p.2) p.1 from
            (show (lattice 2).Adj p.1 (p.1 + unit p.2) from ⟨p.2, Or.inl rfl⟩).symm)
          hy hx).mp (by simpa only [baseEdge, Sym2.eq_swap] using hsel)
        exact hne (by simpa only [baseEdge, Sym2.eq_swap] using h)
  have hd := dualField_baseEdge ω (dualBaseInv p)
  change dualField ω (baseEdge (dualBaseInv p)) = !ω (baseEdge (dualBase (dualBaseInv p))) at hd
  rw [dualBase_right_inv, hfalse] at hd
  exact hd

end
end FiniteAvalanches.Trees.Lattice.PastTail
