module

public import FiniteAvalanches.Sandpile.Burning.TreeGraph
public import FiniteAvalanches.Trees.Past

@[expose] public section

/-! Original burning copies have already been proved connected and counted.
The finite connected-cardinality criterion now proves their actual canonical
spanning-tree certificate, including parallel copies and singleton graphs. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem copied_edge_finset (G : FiniteAvalanches.Trees.Multigraph V E) (t : Finset E) :
    (G.toSimple t).edgeFinset = t.image G.edge := by
  ext a
  induction a using Sym2.ind with
  | h x y =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      FiniteAvalanches.Trees.Multigraph.toSimple, FiniteAvalanches.Trees.Multigraph.adjacent,
      Finset.mem_image, FiniteAvalanches.Trees.Multigraph.edge, Sym2.eq_iff]
    constructor
    · rintro ⟨e, he, h | h⟩
      · exact ⟨e, he, Or.inl h⟩
      · exact ⟨e, he, Or.inr ⟨h.2, h.1⟩⟩
    · rintro ⟨e, he, h | h⟩
      · exact ⟨e, he, Or.inl h⟩
      · exact ⟨e, he, Or.inr ⟨h.2, h.1⟩⟩

omit [DecidableEq V] in
theorem copied_forest_of_simple (G : FiniteAvalanches.Trees.Multigraph V E)
    (t : Finset E) (ha : (G.toSimple t).IsAcyclic)
    (hi : Set.InjOn G.edge (t : Set E)) : G.is_forest t := by
  intro e he hr
  have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ha)
    (v := G.left e) (w := G.right e) ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  rw [SimpleGraph.isBridge_iff] at hb
  apply hb
  apply ((G.toSimple_reachable _ _ _).mpr hr).mono
  intro x y hxy
  obtain ⟨f, hf, hxy⟩ := hxy
  refine ⟨⟨f, (Finset.mem_erase.mp hf).2, hxy⟩, ?_⟩
  intro hbad
  have hfe : G.edge f = G.edge e := by
    have hpair : G.edge f = s(x,y) := by
      rcases hxy with h | h
      · simp [FiniteAvalanches.Trees.Multigraph.edge, h.1, h.2]
      · simp [FiniteAvalanches.Trees.Multigraph.edge, h.1, h.2, Sym2.eq_swap]
    have hs : s(x,y) = G.edge e := by
      exact Set.mem_singleton_iff.mp hbad.1
    exact hpair.trans hs
  exact (Finset.mem_erase.mp hf).1 (hi (Finset.mem_erase.mp hf).2 he hfe)

/-- A literal connected copied-edge graph with one fewer copy than vertices is a tree. -/
theorem copied_tree_of_connected_card (G : FiniteAvalanches.Trees.Multigraph V E)
    (s : V) (t : Finset E) (hc : ∀ x y, G.reaches t x y)
    (ht : t.card + 1 = Fintype.card V) : G.is_tree Set.univ t := by
  letI : Nonempty V := ⟨s⟩
  have hconn : (G.toSimple t).Connected :=
    SimpleGraph.Connected.mk fun x y => (G.toSimple_reachable t x y).mpr (hc x y)
  have hl := hconn.card_vert_le_card_edgeSet_add_one
  have he : Nat.card (G.toSimple t).edgeSet = (t.image G.edge).card := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, copied_edge_finset]
  have hle := Finset.card_image_le (s := t) (f := G.edge)
  rw [Nat.card_eq_fintype_card, he] at hl
  have hcard : (t.image G.edge).card = t.card := by omega
  have hsimple : (G.toSimple t).IsTree :=
    SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hconn, by
      rw [he, hcard, Nat.card_eq_fintype_card]; exact ht⟩
  exact ⟨⟨s, Set.mem_univ _⟩, (by intro e he; simp),
    (by intro x hx y hy; exact hc x y),
    copied_forest_of_simple G t hsimple.2 (Finset.card_image_iff.mp hcard)⟩

variable [LinearOrder E] (G : Multigraph V E) (s : V)

theorem parent_copies_is_tree (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) :
    (copiedTreeGraph G).is_tree Set.univ (parentEdgeSet G s h hn) := by
  apply copied_tree_of_connected_card (copiedTreeGraph G) s _
    (parent_copies_connected G s h hn)
  rw [parent_edge_set_card]
  have hc : Fintype.card (SourceVertex s) = (Finset.univ.erase s : Finset V).card :=
    Fintype.card_coe _
  rw [hc, Finset.card_erase_add_one (Finset.mem_univ s), Finset.card_univ]

/-- The actual selected original copies, with their derived canonical certificate. -/
def burningTree (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) : (copiedTreeGraph G).SpanningTree :=
  ⟨parentEdgeSet G s h hn, parent_copies_is_tree G s h hn⟩

end
end FiniteAvalanches.Sandpile.Burning
