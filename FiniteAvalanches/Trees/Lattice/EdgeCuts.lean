import FiniteAvalanches.Trees.Lattice.Topology
import FiniteAvalanches.Trees.Lattice.WiredLaw

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice
open LatticeProb SimpleGraph
open scoped Classical
noncomputable section

/-- Delete the specified original lattice edge, retaining every lattice vertex. -/
def cutGraph (ω : EdgeField) (e : LatticeEdge) : SimpleGraph (Site 2) :=
  (toGraph ω).deleteEdges {e.val}

/-- The actual component of a vertex after deleting the specified lattice edge. -/
def cutComponent (ω : EdgeField) (e : LatticeEdge) (x : Site 2) : Set (Site 2) :=
  ((cutGraph ω e).connectedComponentMk x).supp

theorem mem_cutComponent_iff (ω : EdgeField) (e : LatticeEdge) (x y : Site 2) :
    y ∈ cutComponent ω e x ↔ (cutGraph ω e).Reachable y x :=
  SimpleGraph.ConnectedComponent.eq

private theorem finite_complement_of_unique_infinite (ω : EdgeField)
    (hT : IsTree ω) (K : Finset (Site 2))
    (C : (toGraph ω).ComponentCompl (K : Set (Site 2)))
    (hC : ∀ D : (toGraph ω).ComponentCompl (K : Set (Site 2)),
      D ≠ C → D.supp.Finite) : C.suppᶜ.Finite := by
  letI : Fact (toGraph ω).Preconnected := ⟨hT.connected.preconnected⟩
  have hfin : (⋃ D : {D : (toGraph ω).ComponentCompl (K : Set (Site 2)) // D ≠ C},
      D.val.supp).Finite := Set.finite_iUnion (fun D => hC D.val D.property)
  apply (K.finite_toSet.union hfin).subset
  intro x hx
  by_cases hxK : x ∈ (K : Set (Site 2))
  · exact Or.inl hxK
  · right
    have hne : (toGraph ω).componentComplMk hxK ≠ C := by
      intro heq
      exact hx (heq ▸ (toGraph ω).componentComplMk_mem hxK)
    exact Set.mem_iUnion.mpr
      ⟨⟨(toGraph ω).componentComplMk hxK, hne⟩,
        (toGraph ω).componentComplMk_mem hxK⟩

private def complementToCut (ω : EdgeField) (e : LatticeEdge) (K : Finset (Site 2))
    (u v : Site 2) (he : e.val = s(u, v)) (hu : u ∈ K) (hv : v ∈ K) :
    (toGraph ω).induce (K : Set (Site 2))ᶜ →g cutGraph ω e where
  toFun := Subtype.val
  map_rel' := by
    intro a b hab
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hab, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hab'
    rw [he] at hab'
    rcases Sym2.eq_iff.mp hab' with h | h
    · exact a.property (h.1.symm ▸ hu)
    · exact a.property (h.1.symm ▸ hv)

/-- Finite-vertex one-endedness gives one infinite component after any one-edge deletion. -/
theorem cutGraph_existsUnique_infinite (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (e : LatticeEdge) :
    ∃! C : (cutGraph ω e).ConnectedComponent, C.supp.Infinite := by
  rcases e with ⟨e, heL⟩
  induction e using Sym2.inductionOn with
  | hf u v =>
    let e : LatticeEdge := ⟨s(u, v), heL⟩
    let K : Finset (Site 2) := {u, v}
    obtain ⟨C, hCinf, hCunique⟩ := hEnd K
    have hCcompl : C.suppᶜ.Finite :=
      finite_complement_of_unique_infinite ω hT K C (fun D hDC => by
        by_contra hDinf
        exact hDC (hCunique D hDinf))
    obtain ⟨x, hx⟩ := C.nonempty
    let D := (cutGraph ω e).connectedComponentMk x
    have hsub : C.supp ⊆ D.supp := by
      intro y hy
      obtain ⟨hxK, hxC⟩ := hx
      obtain ⟨hyK, hyC⟩ := hy
      have hreach : ((toGraph ω).induce (K : Set (Site 2))ᶜ).Reachable
          ⟨y, hyK⟩ ⟨x, hxK⟩ :=
        SimpleGraph.ConnectedComponent.exact (hyC.trans hxC.symm)
      have hmap := hreach.map (complementToCut ω e K u v rfl (by simp only [K, Finset.mem_insert,
        Finset.mem_singleton, true_or]) (by simp only [K, Finset.mem_insert,
        Finset.mem_singleton, or_true]))
      exact SimpleGraph.ConnectedComponent.sound hmap
    refine ⟨D, hCinf.mono hsub, ?_⟩
    intro D' hDinf
    obtain ⟨y, hyD, hyC⟩ := hDinf.exists_notMem_finite hCcompl
    have hy : y ∈ C.supp := by
      simpa only [Set.mem_compl_iff, not_not] using hyC
    exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hyD (hsub hy)

private theorem cut_reachable_endpoint (ω : EdgeField) (hT : IsTree ω)
    (u v z : Site 2) :
    ((toGraph ω).deleteEdges {s(u, v)}).Reachable z u ∨
      ((toGraph ω).deleteEdges {s(u, v)}).Reachable z v := by
  let G := toGraph ω
  let D := G.deleteEdges {s(u, v)}
  have aux {a b : Site 2} (p : G.Walk a b) :
      D.Reachable a b ∨ D.Reachable a u ∨ D.Reachable a v := by
    induction p with
    | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
    | @cons a b c hab p ih =>
      by_cases had : D.Adj a b
      · rcases ih with h | h | h
        · exact Or.inl (had.reachable.trans h)
        · exact Or.inr (Or.inl (had.reachable.trans h))
        · exact Or.inr (Or.inr (had.reachable.trans h))
      · have heq : s(a, b) = s(u, v) := by
          by_contra hne
          exact had (SimpleGraph.deleteEdges_adj.mpr ⟨hab,
            by simpa only [Set.mem_singleton_iff] using hne⟩)
        rcases Sym2.eq_iff.mp heq with h | h
        · exact Or.inr (Or.inl (h.1 ▸ SimpleGraph.Reachable.refl a))
        · exact Or.inr (Or.inr (h.1 ▸ SimpleGraph.Reachable.refl a))
  obtain ⟨p⟩ := hT.connected.preconnected z u
  rcases aux p with h | h | h
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inr h

private theorem cut_components_at_endpoints (ω : EdgeField) (hT : IsTree ω)
    (u v : Site 2) (C : ((toGraph ω).deleteEdges {s(u, v)}).ConnectedComponent) :
    C = ((toGraph ω).deleteEdges {s(u, v)}).connectedComponentMk u ∨
      C = ((toGraph ω).deleteEdges {s(u, v)}).connectedComponentMk v := by
  obtain ⟨z, hz⟩ := C.nonempty_supp
  rcases cut_reachable_endpoint ω hT u v z with h | h
  · exact Or.inl (hz ▸ SimpleGraph.ConnectedComponent.sound h)
  · exact Or.inr (hz ▸ SimpleGraph.ConnectedComponent.sound h)

/-- Deleting a present edge of an actual one-ended lattice tree leaves exactly
one finite component and exactly one infinite component. -/
theorem cutGraph_existsUnique_finite_and_infinite (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (e : LatticeEdge) (he : ω e = true) :
    (∃! C : (cutGraph ω e).ConnectedComponent, C.supp.Finite) ∧
      (∃! C : (cutGraph ω e).ConnectedComponent, C.supp.Infinite) := by
  have hInf := cutGraph_existsUnique_infinite ω hT hEnd e
  refine ⟨?_, hInf⟩
  rcases e with ⟨e, heL⟩
  induction e using Sym2.inductionOn with
  | hf u v =>
    let D := (toGraph ω).deleteEdges {s(u, v)}
    let U := D.connectedComponentMk u
    let V := D.connectedComponentMk v
    have hadj : (toGraph ω).Adj u v := ⟨heL, he⟩
    have hUV : U ≠ V := by
      intro heq
      have hbr := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic) hadj
      exact hbr (SimpleGraph.ConnectedComponent.exact heq)
    obtain ⟨I, hIinf, hIunique⟩ := hInf
    have hI : I = U ∨ I = V := cut_components_at_endpoints ω hT u v I
    rcases hI with hIU | hIV
    · have hVfin : V.supp.Finite := by
        by_contra hVinf
        exact hUV (hIU.symm.trans (hIunique V hVinf).symm)
      refine ⟨V, hVfin, ?_⟩
      intro C hCfin
      rcases cut_components_at_endpoints ω hT u v C with hCU | hCV
      · exact False.elim (hIinf ((hCU.trans hIU.symm) ▸ hCfin))
      · exact hCV
    · have hUfin : U.supp.Finite := by
        by_contra hUinf
        exact hUV ((hIunique U hUinf).trans hIV)
      refine ⟨U, hUfin, ?_⟩
      intro C hCfin
      rcases cut_components_at_endpoints ω hT u v C with hCU | hCV
      · exact hCU
      · exact False.elim (hIinf ((hCV.trans hIV.symm) ▸ hCfin))

end
end FiniteAvalanches.Trees.Lattice
