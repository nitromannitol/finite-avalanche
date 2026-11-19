import FiniteAvalanches.Wilson.Lattice.WiredArrowUniqueness
import FiniteAvalanches.Wilson.CyclePopping.ForestRank

/-! Orient every wired rooted forest toward its original roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical

noncomputable section

/-- Every nonroot has a direction using a forest copy and decreasing the
copied-edge distance to the root set. -/
theorem exists_forest_rootward_direction (R : RootPair) (N : ℕ) (F : FiniteForest R N)
    (v : FiniteWired.Vertex N) (hv : v ∉ (wiredRoots R N).val) :
    ∃ d : FiniteWired.Direction,
      (∃ x : FiniteWired.Active N, v = some x ∧ FiniteWired.directionEdge x d ∈ F.val) ∧
      forestRootRank (WiredTrees.graph N) (wiredRoots R N).val F (wiredHead N v d) <
        forestRootRank (WiredTrees.graph N) (wiredRoots R N).val F v := by
  cases v with
  | none => exact (hv (Or.inr trivial)).elim
  | some x =>
    obtain ⟨y, ⟨e, he, hend⟩, hy⟩ :=
      forestRootRank_descends (WiredTrees.graph N) (wiredRoots R N).val F hv
    have hi : Components.incident x e := by
      rcases hend with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    obtain ⟨d, hd⟩ := Components.exists_direction_of_incident x e hi
    have hdir := wiredHead_direction_endpoints x d
    have hdy : wiredHead N (some x) d = y := by
      rw [hd] at hdir
      change ((FiniteWired.endpoints e).1 = some x ∧ (FiniteWired.endpoints e).2 = y) ∨
        ((FiniteWired.endpoints e).2 = some x ∧ (FiniteWired.endpoints e).1 = y) at hend
      have hn := FiniteWired.endpoints_ne e
      rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases hdir with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> aesop
    exact ⟨d, ⟨x, rfl, hd ▸ he⟩, hdy ▸ hy⟩

/-- Select one descending forest direction at each nonroot. -/
def forestDirection (R : RootPair) (N : ℕ) (F : FiniteForest R N)
    (v : FiniteWired.Vertex N) : FiniteWired.Direction :=
  if hv : v ∉ (wiredRoots R N).val then
    Classical.choose (exists_forest_rootward_direction R N F v hv)
  else (0, false)

/-- The selected nonroot direction uses a forest copy and decreases root distance. -/
theorem forestDirection_spec (R : RootPair) (N : ℕ) (F : FiniteForest R N)
    (v : FiniteWired.Vertex N) (hv : v ∉ (wiredRoots R N).val) :
    (∃ x : FiniteWired.Active N, v = some x ∧
      FiniteWired.directionEdge x (forestDirection R N F v) ∈ F.val) ∧
    forestRootRank (WiredTrees.graph N) (wiredRoots R N).val F
        (wiredHead N v (forestDirection R N F v)) <
      forestRootRank (WiredTrees.graph N) (wiredRoots R N).val F v := by
  simp only [forestDirection, dif_pos hv]
  exact Classical.choose_spec (exists_forest_rootward_direction R N F v hv)

/-- The descending directions have no cycle away from the roots. -/
def forestDirections (R : RootPair) (N : ℕ) (F : FiniteForest R N) :
    GoodArrows (wiredRoots R N).val (wiredHead N) := by
  refine ⟨forestDirection R N F, ?_⟩
  intro c hc
  obtain ⟨v, hv, hmin⟩ := c.exists_min_image
    (forestRootRank (WiredTrees.graph N) (wiredRoots R N).val F) hc.nonempty
  have hlt := (forestDirection_spec R N F v (hc.avoids_roots v hv)).2
  exact (not_lt_of_ge (hmin _ (hc.maps_to v hv))) hlt

/-- Orienting and then forgetting directions returns the original copied forest. -/
theorem wiredArrowForest_forestDirections (R : RootPair) (N : ℕ) (F : FiniteForest R N) :
    wiredArrowForest R N (forestDirections R N F) = F := by
  apply rootedForest_eq_of_subset (WiredTrees.graph N) (wiredRoots R N).val F
  intro e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  have hxR := (Finset.mem_filter.mp hx).2
  obtain ⟨y, hy, he⟩ := (forestDirection_spec R N F (some x) hxR).1
  have hxy : y = x := Option.some.inj hy.symm
  subst y
  exact he

end
end FiniteAvalanches.Wilson.Lattice
