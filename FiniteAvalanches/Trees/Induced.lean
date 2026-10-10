module

public import FiniteAvalanches.Trees.Ancestors

@[expose] public section

/-! Trees on an induced graph and trees on the original supported vertex set
have the same individual edge copies. Both directions lift finite walks and
the deletion-forest certificate; no connectivity or nonempty support is assumed. -/
namespace FiniteAvalanches.Trees.Multigraph
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] (G : Multigraph V E)

abbrev RestrictedEdge (C : Set V) := {e : E // G.left e ∈ C ∧ G.right e ∈ C}

def restrictedGraph (C : Set V) : Multigraph C (G.RestrictedEdge C) where
  left e := ⟨G.left e.val, e.property.1⟩
  right e := ⟨G.right e.val, e.property.2⟩
  loopless e h := G.loopless e.val (congrArg Subtype.val h)

/-- Forget only the subtype proof, preserving the original E-copy itself. -/
def liftedEdges (C : Set V) (t : Finset (G.RestrictedEdge C)) : Finset E :=
  t.image Subtype.val

theorem lifted_supported (C : Set V) (t : Finset (G.RestrictedEdge C)) :
    G.supported C (G.liftedEdges C t) := by
  intro e he
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
  exact f.property

theorem restricted_reaches_iff (C : Set V) (t : Finset (G.RestrictedEdge C)) (x y : C) :
    (G.restrictedGraph C).reaches t x y ↔ G.reaches (G.liftedEdges C t) x.val y.val := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hadj ih =>
      obtain ⟨e, he, hxy⟩ := hadj
      apply ih.tail
      refine ⟨e.val, Finset.mem_image_of_mem Subtype.val he, ?_⟩
      rcases hxy with hxy | hxy
      · exact Or.inl ⟨congrArg Subtype.val hxy.1, congrArg Subtype.val hxy.2⟩
      · exact Or.inr ⟨congrArg Subtype.val hxy.1, congrArg Subtype.val hxy.2⟩
  · intro h
    have go : ∀ a b, G.reaches (G.liftedEdges C t) a b →
        ∀ (ha : a ∈ C) (hb : b ∈ C),
          (G.restrictedGraph C).reaches t ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a b h
      induction h with
      | refl => intro ha hb; exact .refl
      | @tail b c _ hadj ih =>
        intro ha hc
        obtain ⟨e, he, hxy⟩ := hadj
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
        have hb : b ∈ C := by
          rcases hxy with hxy | hxy
          · exact hxy.1 ▸ f.property.1
          · exact hxy.1 ▸ f.property.2
        apply (ih ha hb).tail
        refine ⟨f, hf, ?_⟩
        rcases hxy with hxy | hxy
        · exact Or.inl ⟨Subtype.ext hxy.1, Subtype.ext hxy.2⟩
        · exact Or.inr ⟨Subtype.ext hxy.1, Subtype.ext hxy.2⟩
    exact go x.val y.val h x.property y.property

theorem lifted_erase (C : Set V) (t : Finset (G.RestrictedEdge C)) (e : G.RestrictedEdge C) :
    G.liftedEdges C (t.erase e) = (G.liftedEdges C t).erase e.val :=
  Finset.image_erase Subtype.val_injective t e

theorem restricted_forest_iff (C : Set V) (t : Finset (G.RestrictedEdge C)) :
    (G.restrictedGraph C).is_forest t ↔ G.is_forest (G.liftedEdges C t) := by
  constructor
  · intro ht e he hr
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    apply ht f hf
    apply (G.restricted_reaches_iff C (t.erase f) _ _).mpr
    rw [G.lifted_erase]
    exact hr
  · intro ht e he hr
    apply ht e.val (Finset.mem_image_of_mem Subtype.val he)
    rw [← G.lifted_erase]
    exact (G.restricted_reaches_iff C (t.erase e) _ _).mp hr

theorem restricted_tree_iff (C : Set V) (t : Finset (G.RestrictedEdge C)) :
    (G.restrictedGraph C).is_tree Set.univ t ↔ G.is_tree C (G.liftedEdges C t) := by
  constructor
  · rintro ⟨⟨x, _⟩, _, hc, hf⟩
    refine ⟨⟨x.val, x.property⟩, G.lifted_supported C t, ?_,
      (G.restricted_forest_iff C t).mp hf⟩
    intro x hx y hy
    exact (G.restricted_reaches_iff C t ⟨x, hx⟩ ⟨y, hy⟩).mp
      (hc _ (Set.mem_univ _) _ (Set.mem_univ _))
  · rintro ⟨⟨x, hx⟩, _, hc, hf⟩
    refine ⟨⟨⟨x, hx⟩, Set.mem_univ _⟩, ?_, ?_, (G.restricted_forest_iff C t).mpr hf⟩
    · intro e he
      exact ⟨Set.mem_univ _, Set.mem_univ _⟩
    · intro x hx y hy
      exact (G.restricted_reaches_iff C t x y).mpr (hc _ x.property _ y.property)

/-- Every supported original subset has its literal subtype restriction. -/
def restrictedEdges (C : Set V) (s : Finset E) (hs : G.supported C s) :
    Finset (G.RestrictedEdge C) :=
  s.attach.image (fun e => ⟨e.val, hs e.val e.property⟩)

theorem lift_restricted_edges (C : Set V) (s : Finset E) (hs : G.supported C s) :
    G.liftedEdges C (G.restrictedEdges C s hs) = s := by
  unfold liftedEdges restrictedEdges
  rw [Finset.image_image]
  exact Finset.attach_image_val

/-- Actual induced-tree carrier transport, including empty/disconnected/singleton supports. -/
def restrictedTreeEquiv (C : Set V) :
    (G.restrictedGraph C).SpanningTree ≃ G.ComponentTree C where
  toFun t := ⟨G.liftedEdges C t.val, (G.restricted_tree_iff C t.val).mp t.property⟩
  invFun t := ⟨G.restrictedEdges C t.val t.property.2.1, by
    apply (G.restricted_tree_iff C _).mpr
    rw [G.lift_restricted_edges]
    exact t.property⟩
  left_inv t := by
    apply Subtype.ext
    apply Finset.image_injective Subtype.val_injective
    exact G.lift_restricted_edges C (G.liftedEdges C t.val) (G.lifted_supported C t.val)
  right_inv t := Subtype.ext (G.lift_restricted_edges C t.val t.property.2.1)

theorem restricted_tree_equiv_edges (C : Set V) (t : (G.restrictedGraph C).SpanningTree) :
    (G.restrictedTreeEquiv C t).val = t.val.image Subtype.val := rfl

theorem card_restricted_trees (C : Set V) :
    Nat.card (G.restrictedGraph C).SpanningTree = Nat.card (G.ComponentTree C) :=
  Nat.card_congr (G.restrictedTreeEquiv C)

end
end FiniteAvalanches.Trees.Multigraph
