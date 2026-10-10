import FiniteAvalanches.Trees.Lattice.PastBoundary

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice.PastTail
open LatticeProb SimpleGraph FiniteAvalanches.Trees.Lattice
open scoped Classical
noncomputable section

/-- The complementary side is the actual cut component at the outgoing neighbor. -/
theorem vertexPast_compl_eq_outgoing_component (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) :
    (vertexPast ω hT hOne v)ᶜ =
      cutComponent ω (outgoingEdge ω hT hOne v) (towardEnd ω hT hOne v) := by
  let D := cutGraph ω (outgoingEdge ω hT hOne v)
  let U := D.connectedComponentMk v
  let V := D.connectedComponentMk (towardEnd ω hT hOne v)
  have hU : U.supp.Finite := vertexPast_finite ω hT hOne v
  have hV : V.supp.Infinite :=
    (infiniteDirection_spec ω hT (unique_infinite_components_of_oneEnded ω hT hOne) v).2
  obtain ⟨hFin, hInf⟩ := cutGraph_existsUnique_finite_and_infinite ω hT
    (unique_infinite_components_of_oneEnded ω hT hOne) (outgoingEdge ω hT hOne v)
    (outgoingEdge_selected ω hT hOne v)
  change U.suppᶜ = V.supp
  ext z
  constructor
  · intro hz
    have hne : D.connectedComponentMk z ≠ U :=
      fun h => hz ((ConnectedComponent.mem_supp_iff U z).mpr h)
    have hzInf : (D.connectedComponentMk z).supp.Infinite :=
      fun hzFin => hne (hFin.unique hzFin hU)
    exact (ConnectedComponent.mem_supp_iff V z).mpr (hInf.unique hzInf hV)
  · intro hzV hzU
    have hUV : U = V := ConnectedComponent.eq_of_common_vertex hzU hzV
    exact hV (hUV ▸ hU)

theorem vertexPast_connected (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) :
    ((toGraph ω).induce (vertexPast ω hT hOne v)).Connected := by
  let D := cutGraph ω (outgoingEdge ω hT hOne v)
  let U := D.connectedComponentMk v
  change ((toGraph ω).induce U.supp).Connected
  have hle : D.induce U.supp ≤ (toGraph ω).induce U.supp := by
    intro a b h
    exact (SimpleGraph.deleteEdges_adj.mp h).1
  exact U.connected_toSimpleGraph.mono hle

theorem vertexPast_compl_connected (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) :
    ((toGraph ω).induce (vertexPast ω hT hOne v)ᶜ).Connected := by
  rw [vertexPast_compl_eq_outgoing_component]
  let D := cutGraph ω (outgoingEdge ω hT hOne v)
  let V := D.connectedComponentMk (towardEnd ω hT hOne v)
  change ((toGraph ω).induce V.supp).Connected
  have hle : D.induce V.supp ≤ (toGraph ω).induce V.supp := by
    intro a b h
    exact (SimpleGraph.deleteEdges_adj.mp h).1
  exact V.connected_toSimpleGraph.mono hle

theorem vertexPast_lattice_sides_connected (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) :
    ((lattice 2).induce (vertexPast ω hT hOne v)).Connected ∧
      ((lattice 2).induce (vertexPast ω hT hOne v)ᶜ).Connected :=
  ⟨(vertexPast_connected ω hT hOne v).mono (fun _ _ h => toGraph_le_lattice ω h),
    (vertexPast_compl_connected ω hT hOne v).mono (fun _ _ h => toGraph_le_lattice ω h)⟩

theorem vertexPast_contains_source (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) : v ∈ vertexPast ω hT hOne v := by
  rw [vertexPast_eq_cutComponent]
  exact (mem_cutComponent_iff ω _ v v).mpr (SimpleGraph.Reachable.refl v)

theorem towardEnd_not_mem_vertexPast (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) : towardEnd ω hT hOne v ∉ vertexPast ω hT hOne v := by
  change towardEnd ω hT hOne v ∈ (vertexPast ω hT hOne v)ᶜ
  rw [vertexPast_compl_eq_outgoing_component]
  exact (mem_cutComponent_iff ω _ _ _).mpr (SimpleGraph.Reachable.refl _)

/-- All original lattice edges with one endpoint on each side of the vertex set. -/
def latticeBoundary (A : Set (Site 2)) : Set LatticeEdge :=
  {e | ∃ x ∈ A, ∃ y ∉ A, e.val = s(x, y)}

theorem mem_latticeBoundary_iff (A : Set (Site 2)) (x y : Site 2)
    (hxy : (lattice 2).Adj x y) :
    (⟨s(x, y), hxy⟩ : LatticeEdge) ∈ latticeBoundary A ↔
      (x ∈ A ∧ y ∉ A) ∨ (y ∈ A ∧ x ∉ A) := by
  constructor
  · rintro ⟨a, ha, b, hb, he⟩
    rcases Sym2.eq_iff.mp he with h | h
    · exact Or.inl ⟨h.1.symm ▸ ha, h.2.symm ▸ hb⟩
    · exact Or.inr ⟨h.2.symm ▸ ha, h.1.symm ▸ hb⟩
  · rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
    · exact ⟨x, hx, y, hy, rfl⟩
    · exact ⟨y, hy, x, hx, Sym2.eq_swap⟩

theorem latticeBoundary_finite (A : Set (Site 2)) (hA : A.Finite) :
    (latticeBoundary A).Finite := by
  let F : Set (Sym2 (Site 2)) := ⋃ x ∈ A, (fun y => s(x, y)) '' (nbrFinset x : Set (Site 2))
  have hF : F.Finite := hA.biUnion fun x _ => (nbrFinset x).finite_toSet.image (fun y => s(x, y))
  apply (Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective) hF).subset
  rintro e ⟨x, hx, y, hy, he⟩
  have hxy : (lattice 2).Adj x y := by
    change s(x, y) ∈ (lattice 2).edgeSet
    exact he ▸ e.property
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx,
    ⟨y, (FiniteAvalanches.Sandpile.FiniteWired.mem_neighbors_iff x y).mpr hxy, he.symm⟩⟩⟩

theorem outgoingEdge_mem_boundary (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) :
    outgoingEdge ω hT hOne v ∈ latticeBoundary (vertexPast ω hT hOne v) :=
  ⟨v, vertexPast_contains_source ω hT hOne v, towardEnd ω hT hOne v,
    towardEnd_not_mem_vertexPast ω hT hOne v, rfl⟩

/-- The intersection of the full lattice boundary with the selected tree is one original edge. -/
theorem selected_boundary_eq_singleton (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) :
    {e ∈ latticeBoundary (vertexPast ω hT hOne v) | ω e = true} =
      {outgoingEdge ω hT hOne v} := by
  ext e
  constructor
  · rintro ⟨⟨x, hx, y, hy, he⟩, hsel⟩
    have hxy : (lattice 2).Adj x y := by
      change s(x, y) ∈ (lattice 2).edgeSet
      exact he ▸ e.property
    have he' : e = (⟨s(x, y), hxy⟩ : LatticeEdge) := Subtype.ext he
    exact he'.trans ((selected_crossing_iff_outgoing ω hT hOne v x y hxy hx hy).mp (he' ▸ hsel))
  · intro he
    rw [Set.mem_singleton_iff] at he
    subst e
    exact ⟨outgoingEdge_mem_boundary ω hT hOne v, outgoingEdge_selected ω hT hOne v⟩

private theorem not_boundary_of_same_membership (A : Set (Site 2)) {x y : Site 2}
    (hxy : (lattice 2).Adj x y) (hm : x ∈ A ↔ y ∈ A) :
    s(x, y) ∉ Subtype.val '' latticeBoundary A := by
  rintro ⟨e, he, hev⟩
  have he' : e = (⟨s(x, y), hxy⟩ : LatticeEdge) := Subtype.ext hev
  rw [he'] at he
  rcases (mem_latticeBoundary_iff A x y hxy).mp he with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact hy (hm.mp hx)
  · exact hx (hm.mpr hy)

private theorem boundary_avoiding_reachable_mem_iff (A : Set (Site 2)) {x y : Site 2}
    (hp : ((lattice 2).deleteEdges (Subtype.val '' latticeBoundary A)).Reachable x y) :
    x ∈ A ↔ y ∈ A := by
  obtain ⟨p⟩ := hp
  induction p with
  | nil => exact Iff.rfl
  | @cons a b c hab p ih =>
    have hm : a ∈ A ↔ b ∈ A := by
      constructor
      · intro ha
        by_contra hb
        exact (SimpleGraph.deleteEdges_adj.mp hab).2
          ⟨⟨s(a, b), (SimpleGraph.deleteEdges_adj.mp hab).1⟩, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      · intro hb
        by_contra ha
        exact (SimpleGraph.deleteEdges_adj.mp hab).2
          ⟨⟨s(a, b), (SimpleGraph.deleteEdges_adj.mp hab).1⟩, ⟨b, hb, a, ha, Sym2.eq_swap⟩, rfl⟩
    exact hm.trans ih

/-- The true past boundary is a nonempty minimal disconnecting set in the full lattice graph. -/
theorem vertexPast_boundary_is_bond (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) :
    (latticeBoundary (vertexPast ω hT hOne v)).Nonempty ∧
      ¬ ((lattice 2).deleteEdges (Subtype.val '' latticeBoundary (vertexPast ω hT hOne v))).Preconnected ∧
      ∀ D : Set LatticeEdge, D ⊂ latticeBoundary (vertexPast ω hT hOne v) →
        ((lattice 2).deleteEdges (Subtype.val '' D)).Connected := by
  let A := vertexPast ω hT hOne v
  have hconn := vertexPast_lattice_sides_connected ω hT hOne v
  refine ⟨⟨outgoingEdge ω hT hOne v, outgoingEdge_mem_boundary ω hT hOne v⟩, ?_, ?_⟩
  · intro hP
    exact towardEnd_not_mem_vertexPast ω hT hOne v
      ((boundary_avoiding_reachable_mem_iff A (hP v (towardEnd ω hT hOne v))).mp
        (vertexPast_contains_source ω hT hOne v))
  · intro D hD
    let H := (lattice 2).deleteEdges (Subtype.val '' D)
    have hInside : (H.induce A).Connected := hconn.1.mono (by
      intro a b hab
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hab, ?_⟩
      intro he
      apply not_boundary_of_same_membership A hab ⟨fun _ => b.property, fun _ => a.property⟩
      exact Set.image_mono hD.le he)
    have hOutside : (H.induce Aᶜ).Connected := hconn.2.mono (by
      intro a b hab
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hab, ?_⟩
      intro he
      apply not_boundary_of_same_membership A hab
        ⟨fun ha => False.elim (a.property ha), fun hb => False.elim (b.property hb)⟩
      exact Set.image_mono hD.le he)
    obtain ⟨e, heB, heD⟩ := Set.exists_of_ssubset hD
    obtain ⟨x, hx, y, hy, he⟩ := heB
    have hxy : (lattice 2).Adj x y := by
      change s(x, y) ∈ (lattice 2).edgeSet
      exact he ▸ e.property
    have hHxy : H.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨hxy, by
      rintro ⟨f, hf, hfe⟩
      exact heD ((Subtype.ext (hfe.trans he.symm) : f = e) ▸ hf)⟩
    apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
    refine ⟨x, fun z => ?_⟩
    by_cases hz : z ∈ A
    · exact (hInside.preconnected ⟨x, hx⟩ ⟨z, hz⟩).map
        (show H.induce A →g H from ⟨Subtype.val, fun h => h⟩)
    · exact hHxy.reachable.trans ((hOutside.preconnected ⟨y, hy⟩ ⟨z, hz⟩).map
        (show H.induce Aᶜ →g H from ⟨Subtype.val, fun h => h⟩))

/-- The actual crossing map from original primal edge IDs to face-lattice dual edge IDs. -/
def crossingDualEdge : LatticeEdge ≃ LatticeEdge :=
  edgeEquiv.symm.trans (dualBaseEquiv.symm.trans edgeEquiv)

theorem crossingDualEdge_baseEdge (p : Site 2 × Fin 2) :
    crossingDualEdge (baseEdge p) = baseEdge (dualBaseInv p) := by
  change edgeEquiv (dualBaseInv (edgeEquiv.symm (baseEdge p))) = _
  rw [show edgeEquiv.symm (baseEdge p) = p from edgeEquiv.symm_apply_apply p]
  rfl

theorem dualField_crossingDualEdge (ω : EdgeField) (e : LatticeEdge) :
    dualField ω (crossingDualEdge e) = !ω e := by
  obtain ⟨p, rfl⟩ := baseEdge_surjective e
  rw [crossingDualEdge_baseEdge, dualField_baseEdge]
  change Bool.not (ω (baseEdge (dualBase (dualBaseInv p)))) = Bool.not (ω (baseEdge p))
  rw [dualBase_right_inv]

/-- Exactly one edge of the genuine dual boundary is absent from the complementary dual field. -/
theorem dual_boundary_absent_eq_outgoing (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) :
    {d ∈ crossingDualEdge '' latticeBoundary (vertexPast ω hT hOne v) |
      dualField ω d = false} = {crossingDualEdge (outgoingEdge ω hT hOne v)} := by
  ext d
  constructor
  · rintro ⟨⟨e, heB, rfl⟩, he⟩
    rw [dualField_crossingDualEdge] at he
    have hsel : ω e = true := by
      cases hω : ω e with
      | false => rw [hω] at he; cases he
      | true => rfl
    have hout : e = outgoingEdge ω hT hOne v := by
      have hm : e ∈ {e ∈ latticeBoundary (vertexPast ω hT hOne v) | ω e = true} := ⟨heB, hsel⟩
      rw [selected_boundary_eq_singleton] at hm
      exact hm
    exact congrArg crossingDualEdge hout
  · intro hd
    rw [Set.mem_singleton_iff] at hd
    subst d
    refine ⟨⟨_, outgoingEdge_mem_boundary ω hT hOne v, rfl⟩, ?_⟩
    rw [dualField_crossingDualEdge ω (outgoingEdge ω hT hOne v), outgoingEdge_selected ω hT hOne v]
    rfl

/-- Simultaneous finite proper-bond and exact complementary-dual setup for the literal past. -/
theorem vertexPast_boundary_dual_setup (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) :
    let A := vertexPast ω hT hOne v
    let B := latticeBoundary A
    A.Finite ∧ B.Finite ∧
      ((lattice 2).induce A).Connected ∧ ((lattice 2).induce Aᶜ).Connected ∧
      B.Nonempty ∧ ¬ ((lattice 2).deleteEdges (Subtype.val '' B)).Preconnected ∧
      (∀ D : Set LatticeEdge, D ⊂ B → ((lattice 2).deleteEdges (Subtype.val '' D)).Connected) ∧
      {e ∈ B | ω e = true} = {outgoingEdge ω hT hOne v} ∧
      {d ∈ crossingDualEdge '' B | dualField ω d = false} =
        {crossingDualEdge (outgoingEdge ω hT hOne v)} := by
  obtain ⟨hInside, hOutside⟩ := vertexPast_lattice_sides_connected ω hT hOne v
  obtain ⟨hB, hCut, hMinimal⟩ := vertexPast_boundary_is_bond ω hT hOne v
  exact ⟨vertexPast_finite ω hT hOne v,
    latticeBoundary_finite _ (vertexPast_finite ω hT hOne v), hInside, hOutside,
    hB, hCut, hMinimal, selected_boundary_eq_singleton ω hT hOne v,
    dual_boundary_absent_eq_outgoing ω hT hOne v⟩

end
end FiniteAvalanches.Trees.Lattice.PastTail

set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#check @FiniteAvalanches.Trees.Lattice.PastTail.vertexPast_compl_eq_outgoing_component
#check @FiniteAvalanches.Trees.Lattice.PastTail.vertexPast_boundary_is_bond
#check @FiniteAvalanches.Trees.Lattice.PastTail.selected_boundary_eq_singleton
#check @FiniteAvalanches.Trees.Lattice.PastTail.dual_boundary_absent_eq_outgoing
#check @FiniteAvalanches.Trees.Lattice.PastTail.vertexPast_boundary_dual_setup

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`FiniteAvalanches.Trees.Lattice.PastTail.vertexPast_compl_eq_outgoing_component,
      `FiniteAvalanches.Trees.Lattice.PastTail.vertexPast_lattice_sides_connected,
      `FiniteAvalanches.Trees.Lattice.PastTail.latticeBoundary_finite,
      `FiniteAvalanches.Trees.Lattice.PastTail.selected_boundary_eq_singleton,
      `FiniteAvalanches.Trees.Lattice.PastTail.vertexPast_boundary_is_bond,
      `FiniteAvalanches.Trees.Lattice.PastTail.dual_boundary_absent_eq_outgoing,
      `FiniteAvalanches.Trees.Lattice.PastTail.vertexPast_boundary_dual_setup] do
    let axs ← collectAxioms name
    for ax in axs do
      unless allowed.contains ax do throwError "Unauthorized {ax} in {name}"
    logInfo m!"ACTUAL_PAST_BOND_CLOSURE {name}: {axs.toList}"
