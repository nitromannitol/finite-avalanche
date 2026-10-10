module

public import FiniteAvalanches.Sandpile.Burning.TreeReconstruction

@[expose] public section

/-! The two proved restrictions and the literal lift are global inverses on
original copies. The shape is the actual union of outgoing-edge pasts. The
source exclusion and held inclusion of every event member are derived first. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V) (K : Finset (SourceVertex s)) (A : Finset V)

/-- Ordinary original-copy spanning trees having the literal prescribed union of pasts. -/
abbrev HeldPastTreeFiber :=
  {t : (copiedTreeGraph G).SpanningTree // treePastUnion G s t K = A}

theorem held_past_fiber_avoids_sink (t : HeldPastTreeFiber G s K A) : s ∉ A :=
  t.property ▸ tree_past_union_avoids_sink G s t.val K

theorem held_past_fiber_contains_held (t : HeldPastTreeFiber G s K A) :
    K.image Subtype.val ⊆ A := t.property ▸ held_subset_tree_past_union G s t.val K

variable (hs : s ∉ A) (hBA : K.image Subtype.val ⊆ A)

/-- Literal complement-first restrictions, with both certificates proved from the event. -/
def restrictPastTrees (t : HeldPastTreeFiber G s K A) :
    (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree ×
      (copiedTreeGraph (heldGraph G s A (K.image Subtype.val) hs hBA)).SpanningTree := by
  rcases t with ⟨t, ht⟩
  have hd := past_complement_tree_certificate G s t K
  rw [ht] at hd
  have hc : ∀ e ∈ t.val, (G.left e ∉ A ∧ G.right e ∉ A) ∨
      retained G A (K.image Subtype.val) e := by
    intro e he
    simpa only [ht] using past_tree_edge_partition G s t K e he
  exact (⟨restrictCopies G (Finset.univ \ A) t.val, hd⟩,
    ⟨restrictHeldCopies G A (K.image Subtype.val) t.val,
      held_restriction_is_tree G s A _ hs hBA t hc hd⟩)

/-- Literal lift, with its actual past event proved rather than supplied. -/
def liftPastTrees
    (p : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree ×
      (copiedTreeGraph (heldGraph G s A (K.image Subtype.val) hs hBA)).SpanningTree) :
    HeldPastTreeFiber G s K A :=
  ⟨liftHeldTrees G s A (K.image Subtype.val) hs hBA p.1 p.2,
    lifted_tree_past_union G s A (K.image Subtype.val) hs hBA p.1 p.2 K rfl⟩

theorem lift_restrict_past_trees (t : HeldPastTreeFiber G s K A) :
    liftPastTrees G s K A hs hBA (restrictPastTrees G s K A hs hBA t) = t := by
  apply Subtype.ext
  apply Subtype.ext
  change (restrictCopies G (Finset.univ \ A) t.val.val).image Subtype.val ∪
    (restrictHeldCopies G A (K.image Subtype.val) t.val.val).image Subtype.val = t.val.val
  apply original_copies_partition
  intro e he
  simpa only [t.property] using past_tree_edge_partition G s t.val K e he

theorem restrict_lift_past_trees
    (p : (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree ×
      (copiedTreeGraph (heldGraph G s A (K.image Subtype.val) hs hBA)).SpanningTree) :
    restrictPastTrees G s K A hs hBA (liftPastTrees G s K A hs hBA p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    exact restrict_lift_complement G s A (K.image Subtype.val) hs hBA p.1 p.2
  · apply Subtype.ext
    exact restrict_lift_held G s A (K.image Subtype.val) hs hBA p.1 p.2

/-- The global copied-edge tree restriction/lifting bijection. Formation of the
held graph uses the necessary shape conditions, which every event member proves. -/
def heldPastTreeEquiv :
    HeldPastTreeFiber G s K A ≃
      ((copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree ×
        (copiedTreeGraph (heldGraph G s A (K.image Subtype.val) hs hBA)).SpanningTree) where
  toFun := restrictPastTrees G s K A hs hBA
  invFun := liftPastTrees G s K A hs hBA
  left_inv := lift_restrict_past_trees G s K A hs hBA
  right_inv := restrict_lift_past_trees G s K A hs hBA

theorem card_held_past_fiber : Nat.card (HeldPastTreeFiber G s K A) =
    Nat.card (copiedTreeGraph (inducedGraph G (Finset.univ \ A))).SpanningTree *
      Nat.card (copiedTreeGraph (heldGraph G s A (K.image Subtype.val) hs hBA)).SpanningTree := by
  rw [Nat.card_congr (heldPastTreeEquiv G s K A hs hBA), Nat.card_prod]

theorem held_past_fiber_empty_held (t : HeldPastTreeFiber G s ∅ A) : A = ∅ := by
  exact t.property.symm.trans (tree_past_union_empty G s t.val)

end
end FiniteAvalanches.Sandpile.Burning
