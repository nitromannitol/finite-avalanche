module

public import FiniteAvalanches.Trees.Induced
public import FiniteAvalanches.Trees.JoiningCounts

/-! Unique paths and connecting subtrees under literal induced-copy restriction. -/
@[expose] public section

namespace FiniteAvalanches.Trees.Multigraph
open scoped Classical
open FiniteAvalanches.Trees.RootedPaths
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E]
    (G : Multigraph V E)

/-- The original vertex inclusion, on the actual copied-edge support graph. -/
def restrictedInclusion (C : Set V) (t : Finset (G.RestrictedEdge C)) :
    (G.restrictedGraph C).toSimple t →g G.toSimple (G.liftedEdges C t) where
  toFun := Subtype.val
  map_rel' := by
    intro x y h
    obtain ⟨e, he, hxy⟩ := h
    refine ⟨e.val, Finset.mem_image_of_mem Subtype.val he, ?_⟩
    rcases hxy with hxy | hxy
    · exact Or.inl ⟨congrArg Subtype.val hxy.1, congrArg Subtype.val hxy.2⟩
    · exact Or.inr ⟨congrArg Subtype.val hxy.1, congrArg Subtype.val hxy.2⟩

/-- Mapping the entire unique path gives the actual original component path. -/
theorem restricted_path_map (C : Set V) (t : (G.restrictedGraph C).SpanningTree)
    (x y : C) :
    (path ((G.restrictedGraph C).toSimple_isTree t.property) x y).map
      (G.restrictedInclusion C t.val) =
      G.componentPath (G.restrictedTreeEquiv C t) x y := by
  apply (G.existsUnique_component_path (G.restrictedTreeEquiv C t) x y).choose_spec.2
  exact (path_isPath ((G.restrictedGraph C).toSimple_isTree t.property) x y).map
    (show Function.Injective (G.restrictedInclusion C t.val) from Subtype.val_injective)

theorem restricted_path_support (C : Set V) (t : (G.restrictedGraph C).SpanningTree)
    (x y : C) :
    (G.componentPath (G.restrictedTreeEquiv C t) x y).support =
      (path ((G.restrictedGraph C).toSimple_isTree t.property) x y).support.map Subtype.val := by
  have h := congrArg (fun p => p.support) (G.restricted_path_map C t x y)
  exact h.symm.trans (SimpleGraph.Walk.support_map _ _)

/-- The full connecting subtree is preserved on its original vertex carrier. -/
theorem componentSpan_eq_image_span (C : Set V) (t : (G.restrictedGraph C).SpanningTree)
    (S : Set V) (hSC : S ⊆ C) :
    G.componentSpan (G.restrictedTreeEquiv C t) S hSC =
      Subtype.val '' (G.restrictedGraph C).span t {x : C | x.val ∈ S} := by
  ext v
  constructor
  · rintro ⟨x, hx, y, hy, hv⟩
    rw [G.restricted_path_support C t ⟨x, hSC hx⟩ ⟨y, hSC hy⟩] at hv
    obtain ⟨z, hz, he⟩ := List.mem_map.mp hv
    exact ⟨z, ⟨⟨x, hSC hx⟩, hx, ⟨y, hSC hy⟩, hy, hz⟩, he⟩
  · rintro ⟨z, ⟨x, hx, y, hy, hz⟩, rfl⟩
    refine ⟨x.val, hx, y.val, hy, ?_⟩
    rw [G.restricted_path_support C t ⟨x.val, hSC hx⟩ ⟨y.val, hSC hy⟩]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩


end
end FiniteAvalanches.Trees.Multigraph
