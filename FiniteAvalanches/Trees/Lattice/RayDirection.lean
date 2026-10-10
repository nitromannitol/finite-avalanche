import FiniteAvalanches.Trees.Lattice.EdgeCuts

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb SimpleGraph
open scoped Classical
noncomputable section

private def vertexComplementToCut (ω : EdgeField) (x y : Site 2) :
    (toGraph ω).induce ({x}ᶜ : Set (Site 2)) →g
      (toGraph ω).deleteEdges {s(x, y)} where
  toFun := Subtype.val
  map_rel' := by
    intro a b hab
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hab, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro heq
    rcases Sym2.eq_iff.mp heq with h | h
    · exact a.property (by simpa only [Set.mem_singleton_iff] using h.1)
    · exact b.property (by simpa only [Set.mem_singleton_iff] using h.2)

/-- Beyond a selected tree edge, the edge-cut component is the component
obtained by deleting its starting vertex. -/
theorem adjacent_cut_component_eq_vertex_complement (ω : EdgeField) (hT : IsTree ω)
    (x y : Site 2) (hxy : (toGraph ω).Adj x y) :
    (((toGraph ω).deleteEdges {s(x, y)}).connectedComponentMk y).supp =
      ((toGraph ω).componentComplMk
        (show y ∉ ({x} : Set (Site 2)) from fun h => hxy.ne' (Set.mem_singleton_iff.mp h))).supp := by
  let G := toGraph ω
  let D := G.deleteEdges {s(x, y)}
  have hbr : ¬ D.Reachable x y :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic) hxy
  ext z
  constructor
  · intro hz
    have hreach : D.Reachable y z := (SimpleGraph.ConnectedComponent.exact hz).symm
    obtain ⟨p⟩ := hreach
    have havoid : ∀ a ∈ p.support, a ∈ ({x}ᶜ : Set (Site 2)) := by
      intro a ha hax
      have hax' : a = x := Set.mem_singleton_iff.mp hax
      exact hbr ((hax' ▸ (p.takeUntil a ha).reachable).symm)
    let f : D.induce ({x}ᶜ : Set (Site 2)) →g G.induce ({x}ᶜ : Set (Site 2)) :=
      ⟨id, fun h => h.1⟩
    have hp := ((p.induce ({x}ᶜ : Set (Site 2)) havoid).map f).reachable
    exact ⟨havoid z p.end_mem_support, SimpleGraph.ConnectedComponent.sound hp.symm⟩
  · rintro ⟨hzx, hz⟩
    have hp := SimpleGraph.ConnectedComponent.exact hz
    exact SimpleGraph.ConnectedComponent.sound (hp.map (vertexComplementToCut ω x y))

private theorem adjacent_complement_injective (ω : EdgeField) (hT : IsTree ω)
    (x y z : Site 2) (hxy : (toGraph ω).Adj x y) (hxz : (toGraph ω).Adj x z)
    (heq : (toGraph ω).componentComplMk
        (show y ∉ ({x} : Set (Site 2)) from fun h => hxy.ne' (Set.mem_singleton_iff.mp h)) =
      (toGraph ω).componentComplMk
        (show z ∉ ({x} : Set (Site 2)) from fun h => hxz.ne' (Set.mem_singleton_iff.mp h))) :
    y = z := by
  by_contra hyz
  have hp := (SimpleGraph.ConnectedComponent.exact heq).map (vertexComplementToCut ω x y)
  have hzx : ((toGraph ω).deleteEdges {s(x, y)}).Adj z x := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hxz.symm, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact hxy.ne h.2
    · exact hyz h.1.symm
  exact ((SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic) hxy)
    (hp.trans hzx.reachable).symm

/-- Exactly one actual neighbor lies on the infinite side of its edge cut. -/
theorem existsUnique_infinite_direction (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) :
    ∃! y : Site 2, (toGraph ω).Adj x y ∧
      (((toGraph ω).deleteEdges {s(x, y)}).connectedComponentMk y).supp.Infinite := by
  have hxEnd : ∃! C : (toGraph ω).ComponentCompl ({x} : Set (Site 2)), C.supp.Infinite :=
    by
      have h := hEnd ({x} : Finset (Site 2))
      rw [Finset.coe_singleton] at h
      exact h
  obtain ⟨C, hCinf, hCunique⟩ := hxEnd
  obtain ⟨⟨y, z⟩, hyC, hzx, hyz⟩ := C.exists_adj_boundary_pair
    hT.connected.preconnected (Set.singleton_nonempty x)
  have hzx' : z = x := by simpa only [Set.mem_singleton_iff] using hzx
  subst z
  have hxy := hyz.symm
  have hyCeq : (toGraph ω).componentComplMk
      (show y ∉ ({x} : Set (Site 2)) from fun h => hxy.ne' (Set.mem_singleton_iff.mp h)) = C :=
    hyC.choose_spec
  refine ⟨y, ⟨hxy, ?_⟩, ?_⟩
  · rw [adjacent_cut_component_eq_vertex_complement ω hT x y hxy, hyCeq]
    exact hCinf
  · rintro z ⟨hxz, hzinf⟩
    rw [adjacent_cut_component_eq_vertex_complement ω hT x z hxz] at hzinf
    have hzCeq := hCunique _ hzinf
    exact adjacent_complement_injective ω hT x z y hxz hxy (hzCeq.trans hyCeq.symm)

/-- The neighbor toward the unique end, selected from proved uniqueness. -/
def infiniteDirection (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) : Site 2 :=
  Classical.choose (existsUnique_infinite_direction ω hT hEnd x).exists

theorem infiniteDirection_spec (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) :
    (toGraph ω).Adj x (infiniteDirection ω hT hEnd x) ∧
      (((toGraph ω).deleteEdges {s(x, infiniteDirection ω hT hEnd x)}).connectedComponentMk
        (infiniteDirection ω hT hEnd x)).supp.Infinite :=
  Classical.choose_spec (existsUnique_infinite_direction ω hT hEnd x).exists

theorem infiniteDirection_characterization (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x y : Site 2) :
    y = infiniteDirection ω hT hEnd x ↔ (toGraph ω).Adj x y ∧
      (((toGraph ω).deleteEdges {s(x, y)}).connectedComponentMk y).supp.Infinite := by
  constructor
  · rintro rfl; exact infiniteDirection_spec ω hT hEnd x
  · intro hy
    exact (existsUnique_infinite_direction ω hT hEnd x).unique hy
      (infiniteDirection_spec ω hT hEnd x)

/-- The starting side of the outgoing edge is finite. -/
theorem infiniteDirection_start_finite (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) :
    (((toGraph ω).deleteEdges {s(x, infiniteDirection ω hT hEnd x)}).connectedComponentMk
      x).supp.Finite := by
  obtain ⟨hxy, hyinf⟩ := infiniteDirection_spec ω hT hEnd x
  let e : LatticeEdge := ⟨s(x, infiniteDirection ω hT hEnd x), toGraph_le_lattice ω hxy⟩
  obtain ⟨_, _, hu⟩ := cutGraph_existsUnique_infinite ω hT hEnd e
  by_contra hxinf
  have heq := (hu _ hxinf).trans (hu _ hyinf).symm
  exact ((SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic) hxy)
    (SimpleGraph.ConnectedComponent.exact heq)

theorem infiniteDirection_no_backtrack (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) :
    infiniteDirection ω hT hEnd (infiniteDirection ω hT hEnd x) ≠ x := by
  intro hback
  have hInf := (infiniteDirection_spec ω hT hEnd (infiniteDirection ω hT hEnd x)).2
  rw [hback, Sym2.eq_swap] at hInf
  exact hInf (infiniteDirection_start_finite ω hT hEnd x)

end
end FiniteAvalanches.Trees.Lattice
