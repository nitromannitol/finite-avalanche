module

public import FiniteAvalanches.Trees.Past

@[expose] public section

/-! A marked set meets a union of rooted pasts exactly when its connecting subtree meets the roots. -/
namespace FiniteAvalanches.Trees.RootedPaths
variable {V : Type*} {T : SimpleGraph V} (hT : T.IsTree)

/-- When the root is marked, the connecting subtree is the union of paths to marked vertices. -/
theorem mem_connectingSubtree_iff_ancestor {r : V} {S : Set V} (hr : r ∈ S) (b : V) :
    b ∈ connectingSubtree hT S ↔ ∃ x ∈ S, ancestor hT r b x := by
  constructor
  · rintro ⟨x, hx, y, hy, hb⟩
    rcases path_subset_union hT x y r hb with hb | hb
    · refine ⟨x, hx, ?_⟩
      rw [path_reverse hT x r, SimpleGraph.Walk.support_reverse] at hb
      exact List.mem_reverse.mp hb
    · exact ⟨y, hy, hb⟩
  · rintro ⟨x, hx, hb⟩
    exact ⟨r, hr, x, hx, hb⟩

end FiniteAvalanches.Trees.RootedPaths

namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Trees.RootedPaths
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : Multigraph V E)

/-- The actual outgoing-edge pasts meet the marked set precisely at connecting-subtree vertices. -/
theorem past_union_meets_iff_span (t : G.SpanningTree) (r : V)
    (S : Set V) (hr : r ∈ S) (B : Set {v : V // v ≠ r}) :
    (∃ x ∈ S, ∃ b ∈ B, x ∈ G.past t r b.val b.property) ↔
      ∃ b ∈ B, b.val ∈ G.span t S := by
  simp only [past_eq_descendants, descendants, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, b, hb, ha⟩
    exact ⟨b, hb, (mem_connectingSubtree_iff_ancestor
      (G.toSimple_isTree t.property) hr b.val).mpr ⟨x, hx, ha⟩⟩
  · rintro ⟨b, hb, ha⟩
    obtain ⟨x, hx, ha⟩ := (mem_connectingSubtree_iff_ancestor
      (G.toSimple_isTree t.property) hr b.val).mp ha
    exact ⟨x, hx, b, hb, ha⟩

end FiniteAvalanches.Trees.Multigraph
