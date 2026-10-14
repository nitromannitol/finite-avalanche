import FiniteAvalanches.Trees.RootedForests

/-! Pairs of trees on complementary supports are exactly the copied rooted
two-forests with the prescribed first-root component. -/

namespace FiniteAvalanches.Trees.Multigraph

open scoped Classical
noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

theorem internalEdges_erase (C : Set V) (s : Finset E) (e : E) :
    G.internalEdges C (s.erase e) = (G.internalEdges C s).erase e := by
  ext f
  simp only [internalEdges, Finset.mem_filter, Finset.mem_erase]
  tauto

theorem is_forest_union_of_supported {C : Set V} {s t : Finset E}
    (hs : G.supported C s) (ht : G.supported Cᶜ t)
    (hfs : G.is_forest s) (hft : G.is_forest t) : G.is_forest (s ∪ t) := by
  have hside := G.supported_union_same_side hs ht
  intro e he hr
  have hside' : ∀ f ∈ (s ∪ t).erase e, G.left f ∈ C ↔ G.right f ∈ C :=
    fun f hf => hside f (Finset.mem_erase.mp hf).2
  rcases Finset.mem_union.mp he with he | he
  · have h := G.reaches_internalEdges hside' (hs e he).1 hr
    rw [G.internalEdges_erase, G.internalEdges_union hs ht] at h
    exact hfs e he h
  · have h := G.reaches_internalEdges
      (C := Cᶜ) (fun f hf => not_congr (hside' f hf)) (ht e he).1 hr
    have hint : G.internalEdges Cᶜ (s ∪ t) = t := by
      rw [Finset.union_comm]
      exact G.internalEdges_union ht (by simpa only [compl_compl] using hs)
    rw [G.internalEdges_erase, hint] at h
    exact hft e he h

/-- The entire edge-copy subset, with roots `a,b` and first component exactly `C`. -/
abbrev TwoForestOn (C : Set V) (a b : V) :=
  {F : Finset E // G.is_rooted_forest ({a, b} : Set V) F ∧
    ∀ x, G.reaches F x a ↔ x ∈ C}

theorem twoForest_same_side {C : Set V} {a b : V} (F : G.TwoForestOn C a b) :
    ∀ e ∈ F.val, G.left e ∈ C ↔ G.right e ∈ C := by
  intro e he
  constructor
  · intro hl
    apply (F.property.2 (G.right e)).mp
    exact (Relation.ReflTransGen.single ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩).trans
      ((F.property.2 (G.left e)).mpr hl)
  · intro hr
    apply (F.property.2 (G.left e)).mp
    exact (Relation.ReflTransGen.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩).trans
      ((F.property.2 (G.right e)).mpr hr)

theorem twoForest_reaches_second {C : Set V} {a b : V} (F : G.TwoForestOn C a b)
    {x : V} (hx : x ∉ C) : G.reaches F.val x b := by
  obtain ⟨r, hr, hxr, _⟩ := F.property.1.2 x
  rcases Set.mem_insert_iff.mp hr with rfl | hr
  · exact False.elim (hx ((F.property.2 x).mp hxr))
  · rw [Set.mem_singleton_iff] at hr
    exact hr ▸ hxr

theorem twoForest_reaches_second_iff {C : Set V} {a b : V}
    (hb : b ∉ C) (F : G.TwoForestOn C a b) (x : V) :
    G.reaches F.val x b ↔ x ∉ C := by
  constructor
  · intro h hx
    exact hb ((G.reaches_mem_iff (G.twoForest_same_side F) h).mp hx)
  · exact G.twoForest_reaches_second F

/-- Union retains the original labels of both component trees. -/
def treePairToTwoForest {C : Set V} {a b : V} (ha : a ∈ C) (hb : b ∉ C)
    (p : G.ComponentTree C × G.ComponentTree Cᶜ) : G.TwoForestOn C a b := by
  let s := p.1.val
  let t := p.2.val
  have hs := p.1.property
  have ht := p.2.property
  have hside := G.supported_union_same_side hs.2.1 ht.2.1
  refine ⟨s ∪ t, ⟨G.is_forest_union_of_supported hs.2.1 ht.2.1 hs.2.2.2 ht.2.2.2,
    ?_⟩, ?_⟩
  · intro x
    by_cases hx : x ∈ C
    · refine ⟨a, Set.mem_insert _ _, G.reaches_mono Finset.subset_union_left
        (hs.2.2.1 x hx a ha), ?_⟩
      intro r hr hxr
      rcases Set.mem_insert_iff.mp hr with rfl | hr
      · rfl
      · have hrc := (G.reaches_mem_iff hside hxr).mp hx
        exact False.elim (hb ((Set.mem_singleton_iff.mp hr) ▸ hrc))
    · refine ⟨b, Set.mem_insert_of_mem _ (Set.mem_singleton _),
        G.reaches_mono Finset.subset_union_right (ht.2.2.1 x hx b hb), ?_⟩
      intro r hr hxr
      rcases Set.mem_insert_iff.mp hr with rfl | hr
      · exact False.elim (hx ((G.reaches_mem_iff hside hxr).mpr ha))
      · exact Set.mem_singleton_iff.mp hr
  · intro x
    constructor
    · intro h
      exact (G.reaches_mem_iff hside h).mpr ha
    · intro hx
      exact G.reaches_mono Finset.subset_union_left (hs.2.2.1 x hx a ha)

/-- Restriction of the selected copies recovers each whole component tree. -/
def twoForestToTreePair {C : Set V} {a b : V} (ha : a ∈ C) (hb : b ∉ C)
    (F : G.TwoForestOn C a b) : G.ComponentTree C × G.ComponentTree Cᶜ := by
  have hside := G.twoForest_same_side F
  refine ⟨⟨G.internalEdges C F.val, G.is_tree_internalEdges ⟨a, ha⟩ hside ?_
    F.property.1.1⟩,
    ⟨G.internalEdges Cᶜ F.val, G.is_tree_internalEdges ⟨b, hb⟩
      (fun e he => not_congr (hside e he)) ?_ F.property.1.1⟩⟩
  · intro x hx y hy
    exact ((F.property.2 x).mpr hx).trans (G.reaches_symm ((F.property.2 y).mpr hy))
  · intro x hx y hy
    exact (G.twoForest_reaches_second F hx).trans
      (G.reaches_symm (G.twoForest_reaches_second F hy))

theorem split_tree_pair_union {C : Set V} {a b : V} (ha : a ∈ C) (hb : b ∉ C)
    (p : G.ComponentTree C × G.ComponentTree Cᶜ) :
    G.twoForestToTreePair ha hb (G.treePairToTwoForest ha hb p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    exact G.internalEdges_union p.1.property.2.1 p.2.property.2.1
  · apply Subtype.ext
    change G.internalEdges Cᶜ (p.1.val ∪ p.2.val) = p.2.val
    rw [Finset.union_comm]
    exact G.internalEdges_union p.2.property.2.1
      (by simpa only [compl_compl] using p.1.property.2.1)

theorem union_split_twoForest {C : Set V} {a b : V} (ha : a ∈ C) (hb : b ∉ C)
    (F : G.TwoForestOn C a b) :
    G.treePairToTwoForest ha hb (G.twoForestToTreePair ha hb F) = F := by
  apply Subtype.ext
  exact G.internalEdges_union_compl (G.twoForest_same_side F)

def componentTreePairEquiv {C : Set V} {a b : V} (ha : a ∈ C) (hb : b ∉ C) :
    G.ComponentTree C × G.ComponentTree Cᶜ ≃ G.TwoForestOn C a b where
  toFun := G.treePairToTwoForest ha hb
  invFun := G.twoForestToTreePair ha hb
  left_inv := G.split_tree_pair_union ha hb
  right_inv := G.union_split_twoForest ha hb

theorem card_twoForestOn {C : Set V} {a b : V} (ha : a ∈ C) (hb : b ∉ C) :
    Nat.card (G.TwoForestOn C a b) =
      Nat.card (G.ComponentTree C) * Nat.card (G.ComponentTree Cᶜ) := by
  rw [← Nat.card_congr (G.componentTreePairEquiv ha hb), Nat.card_prod]

end
end FiniteAvalanches.Trees.Multigraph
