import FiniteAvalanches.Trees.Lattice.InfiniteLawProperties
import FiniteAvalanches.Trees.PathCopies
import FiniteAvalanches.Sandpile.Components.CutSites
import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace FiniteAvalanches.Trees.Lattice
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- All original lattice-edge coordinates incident to a finite vertex set. -/
def incidentCoordinates (C : Finset (Site 2)) : Finset LatticeEdge :=
  C.biUnion fun x => (nbrFinset x).attach.image
    fun (y : {y : Site 2 // y ∈ nbrFinset x}) =>
      (⟨s(x, y.val), (FiniteWired.mem_neighbors_iff x y.val).mp y.property⟩ : LatticeEdge)

theorem mem_incidentCoordinates {C : Finset (Site 2)} {x y : Site 2}
    (hx : x ∈ C) (hxy : (lattice 2).Adj x y) :
    (⟨s(x, y), hxy⟩ : LatticeEdge) ∈ incidentCoordinates C := by
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, Finset.mem_image.mpr ?_⟩
  exact ⟨⟨y, (FiniteWired.mem_neighbors_iff x y).mpr hxy⟩,
    Finset.mem_attach _ _, rfl⟩

private theorem wired_internal_adj {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (x y : FiniteWired.Active N) :
    ((WiredTrees.graph N).toSimple t.val).Adj (some x) (some y) ↔
      (toGraph (wiredField t)).Adj (FiniteWired.site x) (FiniteWired.site y) := by
  constructor
  · rintro ⟨j, hj, h⟩
    cases j with
    | inl j =>
      have hadj : (toGraph (wiredField t)).Adj
          (FiniteWired.site j.val.1) (FiniteWired.site j.val.2) :=
        ⟨(interiorEdge j).property, (wiredField_internal_iff t j).mpr hj⟩
      rcases h with h | h
      · change (some j.val.1 = some x ∧ some j.val.2 = some y) at h
        have hx := Option.some.inj h.1
        have hy := Option.some.inj h.2
        subst x; subst y
        exact hadj
      · change (some j.val.2 = some x ∧ some j.val.1 = some y) at h
        have hx := Option.some.inj h.1
        have hy := Option.some.inj h.2
        subst x; subst y
        exact hadj.symm
    | inr j =>
      simp [WiredTrees.graph, Multigraph.ofEndpoints, FiniteWired.endpoints] at h
  · rintro ⟨hxy, hpres⟩
    obtain ⟨j, hj, he⟩ := (wiredField_eq_true t ⟨s(FiniteWired.site x,
      FiniteWired.site y), hxy⟩).mp hpres
    rcases Sym2.eq_iff.mp (congrArg Subtype.val he) with h | h
    · exact ⟨.inl j, hj, Or.inl ⟨congrArg some
        (FiniteWired.site_injective N h.1), congrArg some
        (FiniteWired.site_injective N h.2)⟩⟩
    · exact ⟨.inl j, hj, Or.inr ⟨congrArg some
        (FiniteWired.site_injective N h.2), congrArg some
        (FiniteWired.site_injective N h.1)⟩⟩

private theorem wired_cut_internal_adj {N : ℕ}
    (t : (WiredTrees.graph N).SpanningTree) (i : FiniteWired.InteriorEdge N)
    (hi : Sum.inl i ∈ t.val) (x y : FiniteWired.Active N) :
    ((WiredTrees.graph N).toSimple (t.val.erase (.inl i))).Adj (some x) (some y) ↔
      ((toGraph (wiredField t)).deleteEdges {(interiorEdge i).val}).Adj
        (FiniteWired.site x) (FiniteWired.site y) := by
  have heq : s(some x, some y) = (WiredTrees.graph N).edge (.inl i) ↔
      s(FiniteWired.site x, FiniteWired.site y) = (interiorEdge i).val := by
    have hs (a b : FiniteWired.Active N) :
        FiniteWired.site a = FiniteWired.site b ↔ a = b :=
      (FiniteWired.site_injective N).eq_iff
    simp only [Multigraph.edge, WiredTrees.graph, Multigraph.ofEndpoints,
      FiniteWired.endpoints, interiorEdge, Sym2.eq_iff, Option.some.injEq, hs]
  rw [(WiredTrees.graph N).toSimple_erase_tree t (.inl i) hi]
  simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  exact and_congr (wired_internal_adj t x y) (not_congr heq)

/-- The exact original active-vertex copy of a lattice vertex set; the sink is excluded. -/
def activeLift (N : ℕ) (C : Set (Site 2)) : Set (FiniteWired.Vertex N) :=
  {v | ∃ x : FiniteWired.Active N, v = some x ∧ FiniteWired.site x ∈ C}

@[simp] theorem some_mem_activeLift (N : ℕ) (C : Set (Site 2))
    (x : FiniteWired.Active N) : some x ∈ activeLift N C ↔ FiniteWired.site x ∈ C := by
  simp [activeLift]

@[simp] theorem sink_not_mem_activeLift (N : ℕ) (C : Set (Site 2)) :
    none ∉ activeLift N C := by simp [activeLift]

private theorem exit_not_at_buffer {N : ℕ} (C : Set (Site 2))
    (hbuffer : ∀ x ∈ C, ∀ y, (lattice 2).Adj x y → FiniteWired.inBox N y)
    (j : FiniteWired.ExitEdge N) : FiniteWired.site j.val.1 ∉ C := by
  intro hx
  apply j.property
  apply hbuffer _ hx
  rcases j.val.2 with ⟨k, b⟩
  cases b
  · refine ⟨k, Or.inr ?_⟩
    simp only [FiniteWired.step, Bool.false_eq_true, ↓reduceIte]
    abel
  · exact ⟨k, Or.inl (by simp [FiniteWired.step])⟩

/-- A finite component is forced in the original wired tree by agreement on every
incident lattice coordinate and by keeping its neighboring sites away from the sink.
Neither component equality nor a rooted orientation is a hypothesis. -/
theorem componentAfter_of_incident_agreement {N : ℕ} (ω : EdgeField) (e : LatticeEdge)
    (C : ((toGraph ω).deleteEdges {e.val}).ConnectedComponent)
    (c : Site 2) (hc : c ∈ C.supp) (hbox : ∀ x ∈ C.supp, FiniteWired.inBox N x)
    (hbuffer : ∀ x ∈ C.supp, ∀ y, (lattice 2).Adj x y → FiniteWired.inBox N y)
    (t : (WiredTrees.graph N).SpanningTree) (i : FiniteWired.InteriorEdge N)
    (hei : interiorEdge i = e) (he : ω e = true)
    (hagree : wiredField t e = ω e ∧ ∀ x ∈ C.supp, ∀ y,
      ∀ hxy : (lattice 2).Adj x y, wiredField t ⟨s(x,y), hxy⟩ = ω ⟨s(x,y), hxy⟩) :
    (WiredTrees.graph N).componentAfter t.val (.inl i)
        (some (FiniteWired.activeOfSite N c (hbox c hc))) = activeLift N C.supp := by
  let G := WiredTrees.graph N
  let D := (toGraph ω).deleteEdges {e.val}
  have hi : Sum.inl i ∈ t.val := by
    apply (wiredField_internal_iff t i).mp
    rw [hei, hagree.1, he]
  have hadj {x y : FiniteWired.Active N} (hx : FiniteWired.site x ∈ C.supp) :
      (G.toSimple (t.val.erase (.inl i))).Adj (some x) (some y) ↔
        D.Adj (FiniteWired.site x) (FiniteWired.site y) := by
    rw [wired_cut_internal_adj t i hi, hei]
    simp only [D, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
    apply and_congr _ Iff.rfl
    constructor
    · rintro ⟨hxy, hp⟩
      exact ⟨hxy, (hagree.2 _ hx _ hxy) ▸ hp⟩
    · rintro ⟨hxy, hp⟩
      exact ⟨hxy, (hagree.2 _ hx _ hxy).symm ▸ hp⟩
  have hside : ∀ j ∈ t.val.erase (.inl i),
      G.left j ∈ activeLift N C.supp ↔ G.right j ∈ activeLift N C.supp := by
    intro j hj
    cases j with
    | inl j =>
      change some j.val.1 ∈ activeLift N C.supp ↔ some j.val.2 ∈ activeLift N C.supp
      rw [some_mem_activeLift, some_mem_activeLift]
      constructor
      · intro hx
        have h : (G.toSimple (t.val.erase (.inl i))).Adj
            (some j.val.1) (some j.val.2) := ⟨.inl j, hj, Or.inl ⟨rfl,rfl⟩⟩
        exact C.mem_supp_of_adj_mem_supp hx ((hadj hx).mp h)
      · intro hy
        have h : (G.toSimple (t.val.erase (.inl i))).Adj
            (some j.val.2) (some j.val.1) := ⟨.inl j, hj, Or.inr ⟨rfl,rfl⟩⟩
        exact C.mem_supp_of_adj_mem_supp hy ((hadj hy).mp h)
    | inr j =>
      change some j.val.1 ∈ activeLift N C.supp ↔ none ∈ activeLift N C.supp
      simp only [some_mem_activeLift, sink_not_mem_activeLift, iff_false]
      exact exit_not_at_buffer C.supp hbuffer j
  let φ : C.toSimpleGraph →g G.toSimple (t.val.erase (.inl i)) := {
    toFun := fun x => some (FiniteWired.activeOfSite N x.val (hbox _ x.property))
    map_rel' := by
      intro x y hxy
      exact (hadj
        (x := FiniteWired.activeOfSite N x.val (hbox _ x.property))
        (y := FiniteWired.activeOfSite N y.val (hbox _ y.property)) x.property).mpr hxy }
  ext v
  constructor
  · intro hv
    exact (G.reaches_mem_iff hside hv).mp
      ((some_mem_activeLift N C.supp _).mpr hc)
  · rintro ⟨x, rfl, hx⟩
    have hp := (C.reachable_toSimpleGraph hc hx).map φ
    have hpx : φ ⟨FiniteWired.site x, hx⟩ = some x := by
      apply congrArg some
      apply FiniteWired.site_injective N
      rfl
    rw [hpx] at hp
    exact (G.toSimple_reachable _ _ _).mp hp


end
end FiniteAvalanches.Trees.Lattice
