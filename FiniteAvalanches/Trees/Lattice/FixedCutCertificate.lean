import FiniteAvalanches.Trees.Lattice.TreeContinuityObjects

set_option autoImplicit false
open LatticeProb SimpleGraph
open scoped Classical

namespace FixedCutCertificate11
open FiniteAvalanches.Trees.Lattice TreeMeasurability11
open FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.Lattice
noncomputable section

                                                                              
                                                         
def incidentOriginalEdges (A : Set (Site 2)) : Set LatticeEdge :=
  {e | ∃ x ∈ A, ∃ y, e.val = s(x, y)}

private theorem incidentOriginalEdges_finite (A : Set (Site 2)) (hA : A.Finite) :
    (incidentOriginalEdges A).Finite := by
  let F : Set (Sym2 (Site 2)) :=
    ⋃ x ∈ A, (fun y => s(x, y)) '' (nbrFinset x : Set (Site 2))
  have hF : F.Finite := hA.biUnion fun x _ =>
    (nbrFinset x).finite_toSet.image (fun y => s(x, y))
  apply (Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective) hF).subset
  rintro e ⟨x, hx, y, he⟩
  have hxy : (lattice 2).Adj x y := by
    change s(x, y) ∈ (lattice 2).edgeSet
    exact he ▸ e.property
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx,
    ⟨y, (FiniteAvalanches.Sandpile.FiniteWired.mem_neighbors_iff x y).mpr hxy, he.symm⟩⟩⟩

private theorem component_eq_of_adj_agreement (G H : SimpleGraph (Site 2))
    (x : Site 2)
    (h : ∀ u ∈ (G.connectedComponentMk x).supp, ∀ v, H.Adj u v ↔ G.Adj u v) :
    (H.connectedComponentMk x).supp = (G.connectedComponentMk x).supp := by
  let C := G.connectedComponentMk x
  have closed {u v : Site 2} (p : H.Walk u v) : u ∈ C.supp → v ∈ C.supp := by
    induction p with
    | nil => exact id
    | @cons u v w huv p ih =>
      intro hu
      exact ih (C.mem_supp_of_adj_mem_supp hu ((h u hu v).mp huv))
  let φ : C.toSimpleGraph →g H :=
    { toFun := Subtype.val
      map_rel' := fun {u v} huv => (h u.val u.property v.val).mpr huv }
  ext y
  constructor
  · intro hy
    have hr : H.Reachable x y := (ConnectedComponent.exact hy).symm
    exact closed hr.some (ConnectedComponent.connectedComponentMk_mem)
  · intro hy
    exact ConnectedComponent.sound
      ((C.reachable_toSimpleGraph hy ConnectedComponent.connectedComponentMk_mem).map φ)

/-- Agreement on every original incident edge fixes the entire literal component
of the deleted graph, even for an arbitrary candidate edge field. -/
theorem cutComponent_eq_of_incident_agreement (ω ω' : EdgeField) (f : LatticeEdge)
    (x : Site 2)
    (h : ∀ e ∈ incidentOriginalEdges (cutComponent ω f x), ω' e = ω e) :
    cutComponent ω' f x = cutComponent ω f x := by
  apply component_eq_of_adj_agreement
  intro u hu v
  by_cases huv : (lattice 2).Adj u v
  · have he := h ⟨s(u,v), huv⟩ ⟨u, hu, v, rfl⟩
    simp only [cutGraph, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
      toGraph_adj_iff _ huv, he]
  · have hn (η : EdgeField) : ¬(toGraph η).Adj u v :=
      fun ha => huv (toGraph_le_lattice η ha)
    simp only [cutGraph, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
      hn, false_and]

/-- For every original edge, true ray membership is exactly finiteness of the
actual source-side cut component, including absent and off-ray edges. -/
theorem ray_edge_iff_cutComponent_finite (T : EndedTree) (o : Site 2) (f : LatticeEdge) :
    (∃ n : ℕ, f.val = s((orientedRay T.val T.property.1 T.property.2 o).vertex n,
      (orientedRay T.val T.property.1 T.property.2 o).vertex (n + 1))) ↔
      (cutComponent T.val f o).Finite := by
  let r := orientedRay T.val T.property.1 T.property.2 o
  have hr := (orientedRay_characterization T.val T.property.1 T.property.2 o r).mp rfl
  constructor
  · rintro ⟨n, hn⟩
    have hstep : r.vertex (n+1) = towardEnd T.val T.property.1 T.property.2 (r.vertex n) :=
      infiniteRay_succ T.val T.property.1
        (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2) o n
    have he : f = outgoingEdge T.val T.property.1 T.property.2 (r.vertex n) := by
      apply Subtype.ext
      change f.val = s(r.vertex n, towardEnd T.val T.property.1 T.property.2 (r.vertex n))
      exact hn.trans (congrArg (fun y => s(r.vertex n, y)) hstep)
    have ho : o ∈ vertexPast T.val T.property.1 T.property.2 (r.vertex n) :=
      (vertexPast_characterization T.val T.property.1 T.property.2 _ _).mpr ⟨n, rfl⟩
    rw [vertexPast_eq_cutComponent, ← he] at ho
    have hc : (cutGraph T.val f).connectedComponentMk o =
        (cutGraph T.val f).connectedComponentMk (r.vertex n) := ho
    change ((cutGraph T.val f).connectedComponentMk o).supp.Finite
    rw [hc, he]
    exact vertexPast_finite T.val T.property.1 T.property.2 (r.vertex n)
  · intro hfin
    by_contra hno
    have ha (n : ℕ) : (cutGraph T.val f).Adj (r.vertex n) (r.vertex (n+1)) := by
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨⟨r.adjacent n, hr.2 n⟩, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact fun he => hno ⟨n, he.symm⟩
    have hreach (n : ℕ) : (cutGraph T.val f).Reachable (r.vertex n) o := by
      induction n with
      | zero => rw [hr.1]
      | succ n ih => exact (ha n).symm.reachable.trans ih
    exact r.vertices_infinite (hfin.subset (by
      rintro y ⟨n, rfl⟩
      exact (mem_cutComponent_iff T.val f o _).mpr (hreach n)))

private theorem ray_edge_selected (T : EndedTree) (o : Site 2) (f : LatticeEdge)
    (h : ∃ n : ℕ, f.val = s((orientedRay T.val T.property.1 T.property.2 o).vertex n,
      (orientedRay T.val T.property.1 T.property.2 o).vertex (n + 1))) : T.val f = true := by
  obtain ⟨n, hn⟩ := h
  let r := orientedRay T.val T.property.1 T.property.2 o
  have he : f = ⟨s(r.vertex n, r.vertex (n+1)), r.adjacent n⟩ := Subtype.ext hn
  rw [he]
  exact ((orientedRay_characterization T.val T.property.1 T.property.2 o r).mp rfl).2 n

private theorem event_iff_finite_component (T : EndedTree) (o : Site 2) (f : LatticeEdge)
    (M : ℕ) (hf : T.val f = true) (x : Site 2)
    (hfin : (cutComponent T.val f x).Finite) :
    T ∈ infiniteCutEscape o f M ↔
      o ∈ cutComponent T.val f x ∧
        ¬cutComponent T.val f x ⊆ (boxSites M : Set (Site 2)) := by
  obtain ⟨hUnique, _⟩ := cutGraph_existsUnique_finite_and_infinite T.val T.property.1
    (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2) f hf
  have hcomp : (cutComponent T.val f o).Finite ↔ o ∈ cutComponent T.val f x := by
    constructor
    · intro ho
      exact hUnique.unique ho hfin
    · intro ho
      change (cutGraph T.val f).connectedComponentMk o =
        (cutGraph T.val f).connectedComponentMk x at ho
      change ((cutGraph T.val f).connectedComponentMk o).supp.Finite
      rw [ho]; exact hfin
  have heq (ho : o ∈ cutComponent T.val f x) :
      cutComponent T.val f o = cutComponent T.val f x :=
    congrArg ConnectedComponent.supp ho
  change (_ ∧ _) ↔ _
  rw [ray_edge_iff_cutComponent_finite, hcomp]
  exact and_congr_right fun ho => by rw [heq ho]

/-- A finite set of original edge indicators, constructed at the actual source
tree, determines the literal fixed-edge ray/cut event on all actual one-ended
tree candidates. No certificate, topology or convergence witness is supplied. -/
theorem exists_finite_fixed_cut_certificate (T : EndedTree) (o : Site 2)
    (f : LatticeEdge) (M : ℕ) :
    ∃ F : Finset LatticeEdge, ∀ T' : EndedTree,
      (∀ e ∈ F, T'.val e = T.val e) →
        (T' ∈ infiniteCutEscape o f M ↔ T ∈ infiniteCutEscape o f M) := by
  by_cases hf : T.val f = true
  · obtain ⟨⟨C, hCfin, _⟩, _⟩ := cutGraph_existsUnique_finite_and_infinite T.val T.property.1
      (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2) f hf
    obtain ⟨x, hx⟩ := C.nonempty_supp
    have hfin : (cutComponent T.val f x).Finite := by
      change ((cutGraph T.val f).connectedComponentMk x).supp.Finite
      rw [hx]; exact hCfin
    let A := cutComponent T.val f x
    let edges := (incidentOriginalEdges_finite A hfin).toFinset
    refine ⟨insert f edges, ?_⟩
    intro T' hagree
    have hf' : T'.val f = true := (hagree f (Finset.mem_insert_self _ _)).trans hf
    have heq : cutComponent T'.val f x = A :=
      cutComponent_eq_of_incident_agreement T.val T'.val f x (fun e he =>
        hagree e (Finset.mem_insert_of_mem ((incidentOriginalEdges_finite A hfin).mem_toFinset.mpr he)))
    have hfin' : (cutComponent T'.val f x).Finite := heq ▸ hfin
    rw [event_iff_finite_component T' o f M hf' x hfin',
      event_iff_finite_component T o f M hf x hfin, heq]
  · refine ⟨{f}, ?_⟩
    intro T' hagree
    have hf' : T'.val f ≠ true := fun ht => hf ((hagree f (Finset.mem_singleton_self _)).symm.trans ht)
    constructor
    · intro h
      exact False.elim (hf' (ray_edge_selected T' o f h.1))
    · intro h
      exact False.elim (hf (ray_edge_selected T o f h.1))


/-- The constructed original-edge cylinder is an actual open neighborhood in
the full proper source carrier, and the fixed-cut event is constant there. -/
theorem exists_open_fixed_cut_neighborhood (T : EndedTree) (o : Site 2)
    (f : LatticeEdge) (M : ℕ) :
    ∃ U : Set EndedTree, IsOpen U ∧ T ∈ U ∧ ∀ T' ∈ U,
      (T' ∈ infiniteCutEscape o f M ↔ T ∈ infiniteCutEscape o f M) := by
  obtain ⟨F, hF⟩ := exists_finite_fixed_cut_certificate T o f M
  let U : Set EndedTree :=
    Subtype.val ⁻¹' cylinder F (F.restrict T.val)
  refine ⟨U, ?_, ?_, ?_⟩
  · exact ((isClopen_cylinder F (F.restrict T.val)).preimage continuous_subtype_val).isOpen
  · exact rfl
  · intro T' hU
    apply hF T'
    intro e he
    exact congrFun hU ⟨e, he⟩

/-- A concrete source outside B₀ uses its actual original outgoing edge, so the
zero-threshold cut event is true and a genuine finite certificate preserves it. -/
theorem zero_radius_true_ray_consumer (T : EndedTree) :
    ∃ F : Finset LatticeEdge, ∀ T' : EndedTree,
      (∀ e ∈ F, T'.val e = T.val e) →
      T' ∈ infiniteCutEscape (unit (0 : Fin 2))
        (outgoingEdge T.val T.property.1 T.property.2 (unit (0 : Fin 2))) 0 := by
  let o : Site 2 := unit (0 : Fin 2)
  let f := outgoingEdge T.val T.property.1 T.property.2 o
  have hout : o ∉ (boxSites 0 : Set (Site 2)) := by
    intro h
    have hx := ((mem_box_sites 0 o).mp h) (0 : Fin 2)
    norm_num [o, unit] at hx
  have hmem : o ∈ cutComponent T.val f o :=
    (mem_cutComponent_iff T.val f o o).mpr (Reachable.refl o)
  have htrue : T ∈ infiniteCutEscape o f 0 := by
    refine ⟨⟨0, ?_⟩, fun h => hout (h hmem)⟩
    change s(o, towardEnd T.val T.property.1 T.property.2 o) =
      s(o, infiniteRay T.val T.property.1
        (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2) o 1)
    rw [infiniteRay_succ]
    rfl
  obtain ⟨F, hF⟩ := exists_finite_fixed_cut_certificate T o f 0
  exact ⟨F, fun T' h => (hF T' h).mpr htrue⟩

/-- Absent original edges have the one-coordinate certificate, for all sources
and every integer threshold, with no invented ray on invalid fields. -/
theorem absent_edge_consumer (T : EndedTree) (o : Site 2) (f : LatticeEdge) (M : ℕ)
    (hf : T.val f = false) :
    ∀ T' : EndedTree, T'.val f = T.val f → T' ∉ infiniteCutEscape o f M := by
  intro T' hagree h
  have htrue := ray_edge_selected T' o f h.1
  rw [hagree, hf] at htrue
  exact Bool.false_ne_true htrue

/-- The actual outgoing edge is present, but is off the ray of its far endpoint.
A finite certificate preserves this negative event at every threshold. -/
theorem selected_off_ray_consumer (T : EndedTree) (v : Site 2) (M : ℕ) :
    let f := outgoingEdge T.val T.property.1 T.property.2 v
    let o := towardEnd T.val T.property.1 T.property.2 v
    T.val f = true ∧ ∃ F : Finset LatticeEdge, ∀ T' : EndedTree,
      (∀ e ∈ F, T'.val e = T.val e) → T' ∉ infiniteCutEscape o f M := by
  dsimp only
  let f := outgoingEdge T.val T.property.1 T.property.2 v
  let o := towardEnd T.val T.property.1 T.property.2 v
  have hinf : (cutComponent T.val f o).Infinite :=
    (infiniteDirection_spec T.val T.property.1
      (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2) v).2
  have hfalse : T ∉ infiniteCutEscape o f M := fun h =>
    hinf ((ray_edge_iff_cutComponent_finite T o f).mp h.1)
  obtain ⟨F, hF⟩ := exists_finite_fixed_cut_certificate T o f M
  exact ⟨outgoingEdge_selected T.val T.property.1 T.property.2 v,
    F, fun T' h ht => hfalse ((hF T' h).mp ht)⟩

/-- One actual canonical UST conull witness supplies finite certificates before
all choices of source, original edge and nonnegative integer threshold. -/
theorem actualUST_fixed_cut_certificates :
    ∀ᵐ ω ∂(squareLatticeUST : MeasureTheory.Measure EdgeField),
      ∃ hT : FiniteAvalanches.Trees.Lattice.IsTree ω, ∃ hOne : OneEnded ω,
        ∀ (o : Site 2) (f : LatticeEdge) (M : ℕ),
          ∃ F : Finset LatticeEdge, ∀ T' : EndedTree,
            (∀ e ∈ F, T'.val e = ω e) →
              (T' ∈ infiniteCutEscape o f M ↔
                (⟨ω, hT, hOne⟩ : EndedTree) ∈ infiniteCutEscape o f M) := by
  filter_upwards [squareLatticeUST_ae_tree_oneEnded] with ω hω
  exact ⟨hω.1, hω.2, fun o f M =>
    exists_finite_fixed_cut_certificate ⟨ω, hω.1, hω.2⟩ o f M⟩

end
end FixedCutCertificate11

set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.universes true
set_option pp.proofs true
set_option pp.maxSteps 1000000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    if m.toString.startsWith "FiniteAvalanchesFrozen" then
      throwError "Unavailable draft imported: {m}"
  let pure := #[`propext, `Classical.choice, `Quot.sound]
  let registered := #[`FiniteAvalanches.External.square_lattice_wired_ust_weak_limit,
    `FiniteAvalanches.External.square_lattice_wired_ust_one_tree_one_end]
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      count := count + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless pure.contains ax ||
            (name == `FixedCutCertificate11.actualUST_fixed_cut_certificates && registered.contains ax) do
          throwError "Unregistered/non-deterministic {ax} in {name}"
      logInfo m!"FIXED_CUT11_TYPE {name}: {ci.type}"
      logInfo m!"FIXED_CUT11_CLOSURE {name}: {axs.toList}"
  logInfo m!"FIXED_CUT11_COUNT {count}"
