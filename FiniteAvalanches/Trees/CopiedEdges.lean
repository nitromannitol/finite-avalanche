module

public import FiniteAvalanches.Trees.Joining
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

/-! Rooted geometry of literal copied-edge trees. -/
open scoped Classical

namespace FiniteAvalanches.Trees.Multigraph
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : Multigraph V E)

/-- Forget endpoints' orientation, while retaining the original copy in the domain. -/
def edge (e : E) : Sym2 V := s(G.left e, G.right e)

/-- The simple graph of an actual edge subset. Copy injectivity on forests is proved below. -/
def toSimple (t : Finset E) : SimpleGraph V where
  Adj := G.adjacent t
  symm := ⟨fun _ _ h => G.adjacent_symm h⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨e, _, h | h⟩
    · exact G.loopless e (h.1.trans h.2.symm)
    · exact G.loopless e (h.2.trans h.1.symm)⟩

omit [DecidableEq E] in
theorem toSimple_reachable (t : Finset E) (x y : V) :
    (G.toSimple t).Reachable x y ↔ G.reaches t x y :=
  SimpleGraph.reachable_iff_reflTransGen _ _

theorem edge_injOn_of_is_forest {t : Finset E} (ht : G.is_forest t) :
    Set.InjOn G.edge (t : Set E) := by
  intro e he f hf hef
  by_contra hne
  apply ht e he
  apply Relation.ReflTransGen.single
  refine ⟨f, Finset.mem_erase.mpr ⟨Ne.symm hne, hf⟩, ?_⟩
  rcases Sym2.eq_iff.mp hef with h | h
  · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · exact Or.inr ⟨h.1.symm, h.2.symm⟩

theorem toSimple_isAcyclic {t : Finset E} (ht : G.is_forest t) :
    (G.toSimple t).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro x y hxy
  rcases hxy with ⟨e, he, h | h⟩
  all_goals
    rw [SimpleGraph.isBridge_iff]
    intro hr
    apply ht e he
    have hm : (G.toSimple t).deleteEdges {s(x,y)} ≤ G.toSimple (t.erase e) := by
      intro a b hab
      obtain ⟨⟨f, hf, hfab⟩, hne⟩ := hab
      refine ⟨f, Finset.mem_erase.mpr ⟨?_, hf⟩, hfab⟩
      intro hfe
      subst f
      apply hne
      rw [SimpleGraph.fromEdgeSet_adj]
      refine ⟨?_, ?_⟩
      · simp only [Set.mem_singleton_iff, Sym2.eq_iff]
        aesop
      · rcases hfab with hfab | hfab
        · exact fun hab => G.loopless e (hfab.1.trans (hab.trans hfab.2.symm))
        · exact fun hab => G.loopless e (hfab.2.trans (hab.symm.trans hfab.1.symm))
    have hr' := (G.toSimple_reachable (t.erase e) x y).mp (hr.mono hm)
    first
    | simpa only [← h.1, ← h.2] using hr'
    | exact G.reaches_symm (by simpa only [← h.1, ← h.2] using hr')

theorem toSimple_isTree {t : Finset E} (ht : G.is_tree Set.univ t) :
    (G.toSimple t).IsTree := by
  have hne : Nonempty V := ⟨ht.1.choose⟩
  letI : Nonempty V := hne
  refine ⟨SimpleGraph.Connected.mk ?_, G.toSimple_isAcyclic ht.2.2.2⟩
  intro x y
  exact (G.toSimple_reachable t x y).mpr (ht.2.2.1 x (Set.mem_univ _) y (Set.mem_univ _))

end FiniteAvalanches.Trees.Multigraph
