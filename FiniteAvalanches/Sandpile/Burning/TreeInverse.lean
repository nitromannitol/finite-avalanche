module

public import FiniteAvalanches.Sandpile.Burning.GlobalInverse

@[expose] public section

/-! The reconstructed field has the original tree distances globally. Equal
candidate sets and equal ranks recover every outgoing original copy, then the
whole spanning-tree subset. Both inverses will form an actual carrier equivalence. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V)

theorem tree_distances_burning_tree_heights (t : (copiedTreeGraph G).SpanningTree) :
    treeDistance G s (burningTree G s (treeHeights G s t) (tree_heights_noForbidden G s t)) =
      treeDistance G s t := by
  funext w
  by_cases hw : w = s
  · subst w
    rw [tree_distance_sink, tree_distance_sink]
  · let v : SourceVertex s := ⟨w, Finset.mem_erase.mpr ⟨hw, Finset.mem_univ _⟩⟩
    exact (tree_distance_burning_tree G s (treeHeights G s t)
      (tree_heights_noForbidden G s t) v).trans (burn_time_tree_heights G s t v)

theorem reconstructed_parent_copies (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    treeParentCopies G s t v = parentCopies G s (treeHeights G s t)
      (burnTime G s (treeHeights G s t) (tree_heights_noForbidden G s t) v) v := by
  have hc := original_tree_parent_copies G s (treeHeights G s t) (tree_heights_noForbidden G s t) v
  unfold treeParentCopies at hc
  rw [tree_distances_burning_tree_heights] at hc
  exact hc

theorem reconstructed_tree_base (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    treeBase G s t v = activeDegree G (Finset.univ.erase s)
      (burnRemainder G s (treeHeights G s t)
        (burnTime G s (treeHeights G s t) (tree_heights_noForbidden G s t) v)) v := by
  have hc := original_tree_base G s (treeHeights G s t) (tree_heights_noForbidden G s t) v
  unfold treeBase at hc
  rw [tree_distances_burning_tree_heights] at hc
  exact hc

/-- Every recovered parent is the same original E copy, including parallel copies. -/
theorem reconstructed_parent_copy (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    (globalParentCopy G s (treeHeights G s t) (tree_heights_noForbidden G s t) v).val =
      (treeParent G s t v).val := by
  let e := (globalParentCopy G s (treeHeights G s t) (tree_heights_noForbidden G s t) v).val
  have hc := reconstructed_parent_copies G s t v
  have he : e ∈ treeParentCopies G s t v := by
    rw [hc]
    exact (globalParentCopy G s (treeHeights G s t) (tree_heights_noForbidden G s t) v).property
  have hr := global_parent_rank_reconstruct G s (treeHeights G s t) (tree_heights_noForbidden G s t) v
  have heq := copy_rank_congr hc (show e = e from rfl) he
    (globalParentCopy G s (treeHeights G s t) (tree_heights_noForbidden G s t) v).property
  rw [← heq, ← reconstructed_tree_base, tree_height_rank_eq] at hr
  apply copy_rank_injective (treeParentCopies G s t v) e _ he (treeParent G s t v).property
  omega

omit [DecidableEq V] in
theorem copied_tree_card (T : FiniteAvalanches.Trees.Multigraph V E)
    (t : T.SpanningTree) : t.val.card + 1 = Fintype.card V := by
  have hc := (T.toSimple_isTree t.property).card_edgeFinset
  rw [copied_edge_finset, Finset.card_image_of_injOn
    (T.edge_injOn_of_is_forest t.property.2.2.2)] at hc
  exact hc

/-- Second global inverse: equality of the full original-copy spanning tree. -/
theorem burning_tree_tree_heights (t : (copiedTreeGraph G).SpanningTree) :
    burningTree G s (treeHeights G s t) (tree_heights_noForbidden G s t) = t := by
  apply Subtype.ext
  have hs : parentEdgeSet G s (treeHeights G s t) (tree_heights_noForbidden G s t) ⊆ t.val := by
    intro e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    rw [reconstructed_parent_copy]
    exact ((copiedTreeGraph G).parentEdge_spec t s v.val (source_vertex_ne_sink s v)).1
  apply Finset.eq_of_subset_of_card_le hs
  have hc := copied_tree_card (copiedTreeGraph G) t
  have hh := copied_tree_card (copiedTreeGraph G)
    (burningTree G s (treeHeights G s t) (tree_heights_noForbidden G s t))
  change _ ≤ (parentEdgeSet G s (treeHeights G s t) (tree_heights_noForbidden G s t)).card
  change (parentEdgeSet G s (treeHeights G s t) (tree_heights_noForbidden G s t)).card + 1 = _ at hh
  omega

/-- The actual finite copied-edge burning bijection, not a recurrence or probability law. -/
def burningEquiv : {h : SourceHeights G s // noForbidden G (Finset.univ.erase s) h} ≃
    (copiedTreeGraph G).SpanningTree where
  toFun h := burningTree G s h.val h.property
  invFun t := ⟨treeHeights G s t, tree_heights_noForbidden G s t⟩
  left_inv h := Subtype.ext (tree_heights_burning_tree G s h.val h.property)
  right_inv t := burning_tree_tree_heights G s t

end
end FiniteAvalanches.Sandpile.Burning
