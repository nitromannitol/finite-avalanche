module

public import FiniteAvalanches.Trees.Measure

@[expose] public section

/-! The actual support/inside-tree partition of trees with nonroot marked common ancestor. -/
open scoped Classical
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Trees.RootedPaths
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : Multigraph V E)

/-- Supports with the same positive two-component count as the source shape sum. -/
abbrev PositiveSupport (r : V) (S : Set V) :=
  {C : Set V // S ⊆ C ∧ r ∉ C ∧
    0 < Fintype.card (G.ComponentTree C) ∧ 0 < Fintype.card (G.ComponentTree Cᶜ)}

/-- Ordinary unmarked trees whose common ancestor is active. -/
abbrev ActiveAncestorTree (r : V) (S : Set V) (hS : S.Nonempty) :=
  {u : G.SpanningTree // G.ancestorOf u r S hS ≠ r}

theorem internalEdges_erase_of_crosses {C : Set V} (s : Finset E) {e : E}
    (he : G.crosses C e) : G.internalEdges C (s.erase e) = G.internalEdges C s := by
  ext f
  simp only [internalEdges, Finset.mem_filter, Finset.mem_erase]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · rintro ⟨hf, hl, hr⟩
    refine ⟨⟨?_, hf⟩, hl, hr⟩
    rintro rfl
    rcases he with he | he
    · exact he.2 hr
    · exact he.1 hl

/-- The outgoing copy and its actual deletion components, extracted from an active ancestor. -/
noncomputable def ancestorCut (r : V) (S : Set V) (hS : S.Nonempty)
    (u : G.ActiveAncestorTree r S hS) :
    G.CutTree (G.descendants u.val r (G.ancestorOf u.val r S hS)) := by
  let a := G.ancestorOf u.val r S hS
  let e := G.parentEdge u.val r a u.property
  have he := G.parentEdge_spec u.val r a u.property
  have hc := G.cut_components_componentAfter u.val e he.1 a
    (path (G.toSimple_isTree u.val.property) a r).snd he.2
  rw [show G.componentAfter u.val.val e a = G.descendants u.val r a from
    G.past_eq_descendants u.val r a u.property] at hc
  exact ⟨(u.val.val, e), u.val.property, hc⟩

theorem ancestorCut_edges (r : V) (S : Set V) (hS : S.Nonempty)
    (u : G.ActiveAncestorTree r S hS) : (G.ancestorCut r S hS u).val.1 = u.val.val := rfl

noncomputable def insideTree (r : V) (S : Set V) (hS : S.Nonempty)
    (u : G.ActiveAncestorTree r S hS) :
    G.ComponentTree (G.descendants u.val r (G.ancestorOf u.val r S hS)) := by
  let p := G.ancestorCut r S hS u
  have ht := (G.split _ p).property.1
  change G.is_tree _ (G.internalEdges _ (p.val.1.erase p.val.2)) at ht
  rw [G.internalEdges_erase_of_crosses p.val.1 p.property.2.2.1] at ht
  exact ⟨G.internalEdges _ u.val.val, ht⟩

noncomputable def outsideTree (r : V) (S : Set V) (hS : S.Nonempty)
    (u : G.ActiveAncestorTree r S hS) :
    G.ComponentTree (G.descendants u.val r (G.ancestorOf u.val r S hS))ᶜ :=
  ⟨(G.split _ (G.ancestorCut r S hS u)).val.2.1,
    (G.split _ (G.ancestorCut r S hS u)).property.2.1⟩

noncomputable def supportOf (r : V) (S : Set V) (hS : S.Nonempty)
    (u : G.ActiveAncestorTree r S hS) : G.PositiveSupport r S := by
  let C := G.descendants u.val r (G.ancestorOf u.val r S hS)
  have hSC : S ⊆ C := (commonAncestor_spec (G.toSimple_isTree u.val.property) r S hS).1
  have hr : r ∉ C := by
    intro h
    exact u.property (ancestor_antisymm (G.toSimple_isTree u.val.property) h
      (ancestor_root _ r _))
  have hC : 0 < Fintype.card (G.ComponentTree C) :=
    Fintype.card_pos_iff.mpr ⟨G.insideTree r S hS u⟩
  have hD : 0 < Fintype.card (G.ComponentTree Cᶜ) :=
    Fintype.card_pos_iff.mpr ⟨G.outsideTree r S hS u⟩
  exact ⟨C, hSC, hr, hC, hD⟩

abbrev TreeFiber (r : V) (S : Set V) (hS : S.Nonempty) :=
  (C : G.PositiveSupport r S) × (t : G.ComponentTree C.val) ×
    G.AncestorPastTree C.val S r hS t

def forgetFiber (r : V) (S : Set V) (hS : S.Nonempty)
    (p : G.TreeFiber r S hS) : G.ActiveAncestorTree r S hS :=
  ⟨p.2.2.val, G.ancestor_ne_root_of_event p.1.property.2.1 hS p.2.2⟩

theorem forgetFiber_bijective (r : V) (S : Set V) (hS : S.Nonempty) :
    Function.Bijective (G.forgetFiber r S hS) := by
  constructor
  · rintro ⟨C, t, u⟩ ⟨D, d, v⟩ he
    have huv : u.val = v.val := congrArg Subtype.val he
    have hCD : C = D := by
      apply Subtype.ext
      exact u.property.1.symm.trans (huv ▸ v.property.1)
    subst D
    have htd : t = d := by
      apply Subtype.ext
      exact u.property.2.symm.trans (huv ▸ v.property.2)
    subst d
    have huv' : u = v := Subtype.ext huv
    subst v
    rfl
  · intro u
    let C := G.supportOf r S hS u
    let t := G.insideTree r S hS u
    refine ⟨⟨C, t, ⟨u.val, rfl, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- Every active-ancestor tree has one actual support and one actual inside restriction. -/
noncomputable def treeFiberEquiv (r : V) (S : Set V) (hS : S.Nonempty) :
    G.TreeFiber r S hS ≃ G.ActiveAncestorTree r S hS :=
  Equiv.ofBijective _ (G.forgetFiber_bijective r S hS)

end FiniteAvalanches.Trees.Multigraph
