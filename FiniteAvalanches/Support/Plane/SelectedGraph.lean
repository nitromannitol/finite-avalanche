import FiniteAvalanches.Support.Plane.ReachabilityPath
import FiniteAvalanches.Support.Schoenflies.Graph.Walk

/-!
# The selected nonloop graph

Removing loop edges preserves reachability between vertices of a copied graph.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open scoped Classical Graph

/-- The multigraph formed by the selected nonloop copied edges. -/
def CopiedGraph.selectedGraph {V E : Type} [Fintype V] [Fintype E]
    (G : CopiedGraph V E) (A : Finset E) : Graph V E where
  vertexSet := univ
  edgeSet := {e | e ∈ A ∧ G.left e ≠ G.right e}
  IsLink := fun e x y => e ∈ A ∧ G.left e ≠ G.right e ∧
    ((G.left e = x ∧ G.right e = y) ∨ (G.right e = x ∧ G.left e = y))
  isLink_symm := by
    intro e _
    constructor
    intro x y h
    rcases h with ⟨he, hn, h | h⟩
    · exact ⟨he, hn, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨he, hn, Or.inl ⟨h.2, h.1⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w h h'
    rcases h.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h'.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · rintro ⟨he, hn⟩
      exact ⟨G.left e, G.right e, he, hn, Or.inl ⟨rfl, rfl⟩⟩
    · rintro ⟨_, _, he, hn, _⟩
      exact ⟨he, hn⟩
  left_mem_of_isLink := by simp

/-- Every copied walk gives a walk after discarding its loop steps. -/
theorem CopiedGraph.selectedGraph_reaches {V E : Type} [Fintype V] [Fintype E]
    (G : CopiedGraph V E) (A : Finset E) {u v : V} (h : G.reaches A u v) :
    (G.selectedGraph A).Reaches u v := by
  induction h with
  | refl => exact Graph.Reaches.refl (mem_univ _)
  | @tail w v _ hedge ih =>
    obtain ⟨e, he, hends⟩ := hedge
    by_cases hn : G.left e = G.right e
    · have hwv : w = v := by rcases hends with ⟨hl, hr⟩ | ⟨hr, hl⟩ <;> simp_all
      subst v
      exact ih
    · exact ih.trans (Graph.Reaches.of_isLink ⟨he, hn, hends⟩)

end FiniteAvalanches.Electrical.StatementGeometry
