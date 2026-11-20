import FiniteAvalanches.Sandpile.Burning.SpanningTree

/-! A cut-parity criterion for connectivity of complementary finite graphs. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Trees
open scoped Classical

noncomputable section

variable {V W E : Type*} [Fintype V] [Fintype W] [Fintype E] [DecidableEq E]

/-- Original copies crossing both specified cuts. -/
def commonCutCopies (G : Multigraph V E) (H : Multigraph W E) (C : Set V) (D : Set W) : Finset E :=
  Finset.univ.filter (fun e => G.crosses C e ∧ H.crosses D e)

/-- If every primal cut meets every dual cut evenly, a dual graph is connected
on the complement of any primal spanning tree. -/
theorem dual_complement_connected_of_even_cuts (G : Multigraph V E) (H : Multigraph W E)
    (hH : ∀ x y, H.reaches Finset.univ x y)
    (hparity : ∀ C : Set V, ∀ D : Set W, Even (commonCutCopies G H C D).card)
    (t : G.SpanningTree) (x y : W) : H.reaches t.valᶜ x y := by
  by_contra hxy
  let D : Set W := {v | H.reaches t.valᶜ x v}
  have hx : x ∈ D := Relation.ReflTransGen.refl
  have hy : y ∉ D := hxy
  have hsub : ∀ e, H.crosses D e → e ∈ t.val := by
    intro e he
    by_contra hn
    have hm : e ∈ t.valᶜ := Finset.mem_compl.mpr hn
    rcases he with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · apply hr
      exact hl.tail ⟨e, hm, Or.inl ⟨rfl, rfl⟩⟩
    · apply hl
      exact hr.tail ⟨e, hm, Or.inr ⟨rfl, rfl⟩⟩
  have hex : ∃ e, H.crosses D e := by
    by_contra h
    have hside : ∀ e ∈ (Finset.univ : Finset E), H.left e ∈ D ↔ H.right e ∈ D := by
      intro e _
      constructor
      · intro hl
        by_contra hr
        exact h ⟨e, Or.inl ⟨hl, hr⟩⟩
      · intro hr
        by_contra hl
        exact h ⟨e, Or.inr ⟨hl, hr⟩⟩
    exact hy ((H.reaches_mem_iff hside (hH x y)).mp hx)
  obtain ⟨e, he⟩ := hex
  have het : e ∈ t.val := hsub e he
  let C := G.componentAfter t.val e (G.left e)
  have hcut := G.cut_components_componentAfter t e het (G.left e) (G.right e) (Or.inl ⟨rfl, rfl⟩)
  have heq : commonCutCopies G H C D = {e} := by
    ext f
    simp only [commonCutCopies, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hg, hh⟩
      by_contra hfe
      have hmem : f ∈ t.val.erase e := Finset.mem_erase.mpr ⟨hfe, hsub f hh⟩
      have hs := hcut.2.2.1 f hmem
      rcases hg with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact hr (hs.mp hl)
      · exact hl (hs.mpr hr)
    · intro hfe
      subst f
      exact ⟨hcut.2.1, he⟩
  have hp := hparity C D
  rw [heq] at hp
  norm_num at hp

/-- A finite copied spanning tree has one fewer copy than vertices. -/
theorem copiedSpanningTree_card (G : Multigraph V E) (t : G.SpanningTree) :
    t.val.card + 1 = Fintype.card V := by
  letI : DecidableEq V := Classical.decEq _
  have htree := G.toSimple_isTree t.property
  have hcard := htree.card_edgeFinset
  rw [FiniteAvalanches.Sandpile.Burning.copied_edge_finset] at hcard
  rw [Finset.card_image_iff.mpr (G.edge_injOn_of_is_forest t.property.2.2.2)] at hcard
  exact hcard

/-- Under cut parity and the finite Euler count, the complement of a primal
spanning tree is a dual spanning tree. -/
theorem dual_complement_tree_of_even_cuts [Nonempty W] (G : Multigraph V E) (H : Multigraph W E)
    (hH : ∀ x y, H.reaches Finset.univ x y)
    (hparity : ∀ C : Set V, ∀ D : Set W, Even (commonCutCopies G H C D).card)
    (hEuler : Fintype.card E + 2 = Fintype.card V + Fintype.card W)
    (t : G.SpanningTree) : H.is_tree Set.univ t.valᶜ := by
  letI : DecidableEq W := Classical.decEq _
  have hconn := dual_complement_connected_of_even_cuts G H hH hparity t
  have htcard := copiedSpanningTree_card G t
  have hcompl : t.valᶜ.card + t.val.card = Fintype.card E := by
    simpa only [Finset.card_univ] using Finset.card_compl_add_card t.val
  have hcard : t.valᶜ.card + 1 = Fintype.card W := by omega
  exact FiniteAvalanches.Sandpile.Burning.copied_tree_of_connected_card H
    (Classical.choice inferInstance) t.valᶜ hconn hcard

/-- Complement swaps the two finite tree carriers under cut parity and the
finite Euler count. -/
def dualTreeEquivOfEvenCuts [Nonempty V] [Nonempty W] (G : Multigraph V E) (H : Multigraph W E)
    (hG : ∀ x y, G.reaches Finset.univ x y) (hH : ∀ x y, H.reaches Finset.univ x y)
    (hparity : ∀ C : Set V, ∀ D : Set W, Even (commonCutCopies G H C D).card)
    (hEuler : Fintype.card E + 2 = Fintype.card V + Fintype.card W) :
    G.SpanningTree ≃ H.SpanningTree where
  toFun t := ⟨t.valᶜ, dual_complement_tree_of_even_cuts G H hH hparity hEuler t⟩
  invFun t := ⟨t.valᶜ, dual_complement_tree_of_even_cuts H G hG (by
    intro D C
    have heq : commonCutCopies H G D C = commonCutCopies G H C D := by
      ext e
      simp only [commonCutCopies, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
    rw [heq]
    exact hparity C D) (by omega) t⟩
  left_inv t := by
    apply Subtype.ext
    simp only [compl_compl]
  right_inv t := by
    apply Subtype.ext
    simp only [compl_compl]

end
end FiniteAvalanches.Wilson.Lattice
