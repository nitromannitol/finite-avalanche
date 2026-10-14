import FiniteAvalanches.Trees.Lattice.FixedCutCertificate
import FiniteAvalanches.Trees.Lattice.WiredCutComponents

/-! Incoming cd552a5, main.tex 177: the infinite one-ended-tree incident pattern.
All original lattice vertices and every present or absent incident coordinate remain.
No probability law or convergence estimate is used. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Trees.Lattice.CurrentInfinitePastPattern
open LatticeProb SimpleGraph FiniteAvalanches.Wilson.Lattice TreeMeasurability11
open scoped Classical
noncomputable section

/-- The actual four-neighbor coordinate family means one endpoint in F. -/
theorem mem_incident_coordinates_iff (F : Finset (Site 2)) (f : LatticeEdge) :
    f ∈ incidentCoordinates F ↔ ∃ u ∈ F, ∃ v : Site 2, f.val = s(u, v) := by
  constructor
  · intro hf
    obtain ⟨u, hu, hf⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨v, _hv, he⟩ := Finset.mem_image.mp hf
    exact ⟨u, hu, v.val, (congrArg Subtype.val he).symm⟩
  · rintro ⟨u, hu, v, he⟩
    have ha : (lattice 2).Adj u v := by
      change s(u, v) ∈ (lattice 2).edgeSet
      exact he ▸ f.property
    have hf : f = ⟨s(u, v), ha⟩ := Subtype.ext he
    rw [hf]
    exact mem_incidentCoordinates hu ha

/-- Either orientation of an original unordered coordinate has the same incidence. -/
theorem incident_coordinates_iff_endpoint (F : Finset (Site 2)) (f : LatticeEdge)
    (u v : Site 2) (he : f.val = s(u, v)) :
    f ∈ incidentCoordinates F ↔ u ∈ F ∨ v ∈ F := by
  rw [mem_incident_coordinates_iff]
  constructor
  · rintro ⟨a, ha, b, hab⟩
    rcases Sym2.eq_iff.mp (hab.symm.trans he) with h | h
    · exact Or.inl (h.1 ▸ ha)
    · exact Or.inr (h.1 ▸ ha)
  · rintro (hu | hv)
    · exact ⟨u, hu, v, he⟩
    · exact ⟨v, hv, u, he.trans (Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩))⟩

/-- Literal support of raw H fixes both endpoints, in either orientation. -/
theorem endpoints_mem_of_raw_support (F : Finset (Site 2)) (H : Finset LatticeEdge)
    (hs : ∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v))
    (f : LatticeEdge) (hf : f ∈ H) (u v : Site 2) (he : f.val = s(u, v)) :
    u ∈ F ∧ v ∈ F := by
  obtain ⟨a, ha, b, hb, hab⟩ := hs f hf
  rcases Sym2.eq_iff.mp (hab.symm.trans he) with h | h
  · exact ⟨h.1 ▸ ha, h.2 ▸ hb⟩
  · exact ⟨h.2 ▸ hb, h.1 ▸ ha⟩

                                                                                     
theorem exit_edge_ne_internal (F : Finset (Site 2)) (e : LatticeEdge)
    (x y : Site 2) (he : e.val = s(x, y)) (hy : y ∉ F)
    (u v : Site 2) (hu : u ∈ F) (hv : v ∈ F) : s(u, v) ≠ e.val := by
  intro h
  rw [he] at h
  rcases Sym2.eq_iff.mp h with h | h
  · exact hy (h.2 ▸ hv)
  · exact hy (h.1 ▸ hu)

/-- A selected edge that crosses the proposed finite tree is exactly the listed exit.
This is an actual adjacency statement, derived from present AND absent coordinates. -/
theorem selected_boundary_eq_exit (ω : EdgeField) (F : Finset (Site 2))
    (H : Finset LatticeEdge) (e : LatticeEdge)
    (hs : ∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v))
    (hp : ∀ f ∈ incidentCoordinates F, ω f = decide (f ∈ insert e H))
    (u v : Site 2) (hu : u ∈ F) (hv : v ∉ F) (ha : (toGraph ω).Adj u v) :
    s(u, v) = e.val := by
  let f : LatticeEdge := ⟨s(u, v), toGraph_le_lattice ω ha⟩
  have hi : f ∈ incidentCoordinates F := mem_incidentCoordinates hu f.property
  have hf : f ∈ insert e H := by
    have htrue : ω f = true := (toGraph_adj_iff ω f.property).mp ha
    rw [hp f hi] at htrue
    exact of_decide_eq_true htrue
  rcases Finset.mem_insert.mp hf with hf | hf
  · exact congrArg Subtype.val hf
  · exact (hv (endpoints_mem_of_raw_support F H hs f hf u v rfl).2).elim

/-- The exact one-exit raw pattern forces the actual cut component to be F.
Connectivity is supplied only by the literal inside-tree clause. -/
theorem cut_component_eq_of_raw_pattern (ω : EdgeField) (F : Finset (Site 2))
    (H : Finset LatticeEdge)
    (hH : ((toGraph (fun f : LatticeEdge => decide (f ∈ H))).induce
      (F : Set (Site 2))).IsTree)
    (hs : ∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v))
    (x : Site 2) (hx : x ∈ F) (e : LatticeEdge) (y : Site 2)
    (he : e.val = s(x, y)) (hy : y ∉ F)
    (hp : ∀ f ∈ incidentCoordinates F, ω f = decide (f ∈ insert e H)) :
    cutComponent ω e x = (F : Set (Site 2)) := by
  let D := cutGraph ω e
  have closed {u v : Site 2} (hu : u ∈ F) (ha : D.Adj u v) : v ∈ F := by
    by_contra hv
    have ha' := SimpleGraph.deleteEdges_adj.mp ha
    have heq := selected_boundary_eq_exit ω F H e hs hp u v hu hv ha'.1
    exact ha'.2 (Set.mem_singleton_iff.mpr heq)
  have stays {u v : Site 2} (p : D.Walk u v) : u ∈ F → v ∈ F := by
    induction p with
    | nil => exact id
    | @cons u v w huv p ih =>
      intro hu
      exact ih (closed hu huv)
  let φ : (toGraph (fun f : LatticeEdge => decide (f ∈ H))).induce
      (F : Set (Site 2)) →g D :=
    { toFun := Subtype.val
      map_rel' := by
        intro u v ha
        change (toGraph (fun f : LatticeEdge => decide (f ∈ H))).Adj u.val v.val at ha
        let f : LatticeEdge := ⟨s(u.val, v.val), ha.1⟩
        have hf : f ∈ H := of_decide_eq_true ha.2
        have hi : f ∈ incidentCoordinates F := mem_incidentCoordinates u.property f.property
        have ht : ω f = true := by
          rw [hp f hi]
          exact decide_eq_true (Finset.mem_insert_of_mem hf)
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨⟨ha.1, ht⟩, ?_⟩
        simpa only [Set.mem_singleton_iff] using
          exit_edge_ne_internal F e x y he hy u.val v.val u.property v.property }
  ext z
  constructor
  · intro hz
    have hr := (mem_cutComponent_iff ω e x z).mp hz
    exact stays hr.symm.some hx
  · intro hz
    have hr := hH.connected.preconnected
      (⟨z, hz⟩ : (F : Set (Site 2))) (⟨x, hx⟩ : (F : Set (Site 2)))
    exact (mem_cutComponent_iff ω e x z).mpr (hr.map φ)

/-- An incident edge at the start of the actual ray must be its first edge.
The reversed Sym2 orientation would force n+1=0 by ray injectivity. -/
theorem incident_finite_cut_eq_outgoing (T : EndedTree) (x : Site 2)
    (e : LatticeEdge) (y : Site 2) (he : e.val = s(x, y))
    (hfin : (cutComponent T.val e x).Finite) :
    e = outgoingEdge T.val T.property.1 T.property.2 x := by
  obtain ⟨n, hn⟩ := (FixedCutCertificate11.ray_edge_iff_cutComponent_finite T x e).mpr hfin
  let r := orientedRay T.val T.property.1 T.property.2 x
  have h0 : r.vertex 0 = x :=
    ((orientedRay_characterization T.val T.property.1 T.property.2 x r).mp rfl).1
  have heq : s(r.vertex n, r.vertex (n + 1)) = s(x, y) := hn.symm.trans he
  have hn0 : n = 0 := by
    rcases Sym2.eq_iff.mp heq with h | h
    · exact r.injective (h.1.trans h0.symm)
    · have hn' := r.injective (h.2.trans h0.symm)
      omega
  subst n
  apply Subtype.ext
  change e.val = s(x, towardEnd T.val T.property.1 T.property.2 x)
  calc
    e.val = s(r.vertex 0, r.vertex 1) := hn
    _ = s(x, towardEnd T.val T.property.1 T.property.2 x) := by rw [h0]; rfl

/-- Reverse source inference: the literal finite inside-tree and full incident
pattern determine the actual infinite-tree past, with no component premise. -/
theorem vertex_past_eq_of_raw_pattern (T : EndedTree) (F : Finset (Site 2))
    (H : Finset LatticeEdge)
    (hH : ((toGraph (fun f : LatticeEdge => decide (f ∈ H))).induce
      (F : Set (Site 2))).IsTree)
    (hs : ∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v))
    (x : Site 2) (hx : x ∈ F) (e : LatticeEdge) (y : Site 2)
    (he : e.val = s(x, y)) (hy : y ∉ F)
    (hp : ∀ f ∈ incidentCoordinates F, T.val f = decide (f ∈ insert e H)) :
    vertexPast T.val T.property.1 T.property.2 x = (F : Set (Site 2)) := by
  have hc := cut_component_eq_of_raw_pattern T.val F H hH hs x hx e y he hy hp
  have hfin : (cutComponent T.val e x).Finite := hc ▸ F.finite_toSet
  have heout := incident_finite_cut_eq_outgoing T x e y he hfin
  rw [vertexPast_eq_cutComponent, ← heout]
  exact hc

/-- All selected original edges with BOTH endpoints in F, including empty H. -/
def insideSelectedEdges (ω : EdgeField) (F : Finset (Site 2)) : Finset LatticeEdge :=
  (incidentCoordinates F).filter fun f => ω f = true ∧
    ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v)

/-- Transparent raw-edge selection: incidence follows from the first endpoint. -/
theorem mem_inside_selected_edges_iff (ω : EdgeField) (F : Finset (Site 2))
    (f : LatticeEdge) : f ∈ insideSelectedEdges ω F ↔
      ω f = true ∧ ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v) := by
  constructor
  · intro hf
    exact (Finset.mem_filter.mp hf).2
  · rintro ⟨ht, u, hu, v, hv, he⟩
    exact Finset.mem_filter.mpr
      ⟨(mem_incident_coordinates_iff F f).mpr ⟨u, hu, v, he⟩, ht, u, hu, v, hv, he⟩

/-- The actual raw inside edges have exactly the original induced graph on F. -/
theorem inside_selected_induce_eq (ω : EdgeField) (F : Finset (Site 2)) :
    (toGraph (fun f : LatticeEdge => decide (f ∈ insideSelectedEdges ω F))).induce
      (F : Set (Site 2)) = (toGraph ω).induce (F : Set (Site 2)) := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  change (toGraph (fun f : LatticeEdge => decide (f ∈ insideSelectedEdges ω F))).Adj
    u.val v.val ↔ (toGraph ω).Adj u.val v.val
  constructor
  · intro ha
    let f : LatticeEdge := ⟨s(u.val, v.val), ha.1⟩
    have hf : f ∈ insideSelectedEdges ω F := of_decide_eq_true ha.2
    exact ⟨ha.1, ((mem_inside_selected_edges_iff ω F f).mp hf).1⟩
  · intro ha
    let f : LatticeEdge := ⟨s(u.val, v.val), ha.1⟩
    have hf : f ∈ insideSelectedEdges ω F :=
      (mem_inside_selected_edges_iff ω F f).mpr ⟨ha.2, u.val, u.property,
        v.val, v.property, rfl⟩
    exact ⟨ha.1, decide_eq_true hf⟩

/-- Deleting a boundary exit leaves the full inside induced graph unchanged. -/
theorem cut_induce_eq_of_exit (ω : EdgeField) (F : Finset (Site 2))
    (e : LatticeEdge) (x y : Site 2) (he : e.val = s(x, y)) (hy : y ∉ F) :
    (cutGraph ω e).induce (F : Set (Site 2)) = (toGraph ω).induce (F : Set (Site 2)) := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  change ((toGraph ω).deleteEdges {e.val}).Adj u.val v.val ↔ (toGraph ω).Adj u.val v.val
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · exact And.left
  · intro ha
    refine ⟨ha, ?_⟩
    simpa only [Set.mem_singleton_iff] using
      exit_edge_ne_internal F e x y he hy u.val v.val u.property v.property

/-- Every actual cut component induces a tree by original acyclicity and component connectivity. -/
theorem cut_component_induced_tree (ω : EdgeField) (hT : IsTree ω)
    (e : LatticeEdge) (x : Site 2) :
    ((cutGraph ω e).induce (cutComponent ω e x)).IsTree := by
  have ha : (cutGraph ω e).IsAcyclic :=
    hT.isAcyclic.anti ((toGraph ω).deleteEdges_le {e.val})
  exact ha.isTree_connectedComponent ((cutGraph ω e).connectedComponentMk x)

/-- The selected inside tree of a singleton has no original loop coordinate. -/
theorem inside_selected_singleton_eq_empty (ω : EdgeField) (x : Site 2) :
    insideSelectedEdges ω {x} = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨_ht, u, hu, v, hv, he⟩ := (mem_inside_selected_edges_iff ω {x} f).mp hf
  have hu' : u = x := Finset.mem_singleton.mp hu
  have hv' : v = x := Finset.mem_singleton.mp hv
  subst u; subst v
  have ha : (lattice 2).Adj x x := by
    change s(x, x) ∈ (lattice 2).edgeSet
    exact he ▸ f.property
  exact ha.ne rfl

/-- The actual finite past supplies one shared F, raw inside H and outgoing e.
No cut equality, finite-past certificate or selected ray is a caller hypothesis. -/
theorem exists_actual_past_raw_pattern (T : EndedTree) (x : Site 2) :
    ∃ F : Finset (Site 2), (F : Set (Site 2)) = vertexPast T.val T.property.1 T.property.2 x ∧
      x ∈ F ∧ ∃ H : Finset LatticeEdge,
        ((toGraph (fun f : LatticeEdge => decide (f ∈ H))).induce
          (F : Set (Site 2))).IsTree ∧
        (∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v)) ∧
        ∃ e : LatticeEdge, ∃ y : Site 2, e.val = s(x, y) ∧ y ∉ F ∧
          ∀ f ∈ incidentCoordinates F, T.val f = decide (f ∈ insert e H) := by
  let F := (vertexPast_finite T.val T.property.1 T.property.2 x).toFinset
  let e := outgoingEdge T.val T.property.1 T.property.2 x
  let y := towardEnd T.val T.property.1 T.property.2 x
  let H := insideSelectedEdges T.val F
  have hF : (F : Set (Site 2)) = vertexPast T.val T.property.1 T.property.2 x :=
    Set.Finite.coe_toFinset _
  have hFC : (F : Set (Site 2)) = cutComponent T.val e x :=
    hF.trans (vertexPast_eq_cutComponent T.val T.property.1 T.property.2 x)
  have hx : x ∈ F := by
    change x ∈ (F : Set (Site 2))
    rw [hFC]
    exact (mem_cutComponent_iff T.val e x x).mpr (SimpleGraph.Reachable.refl x)
  have he : e.val = s(x, y) := rfl
  have hy : y ∉ F := by
    intro hyF
    have hyC : y ∈ cutComponent T.val e x := hFC ▸ hyF
    have hceq : (cutGraph T.val e).connectedComponentMk y =
        (cutGraph T.val e).connectedComponentMk x := hyC
    have hsame : cutComponent T.val e y = cutComponent T.val e x :=
      congrArg ConnectedComponent.supp hceq
    have hdir := (towardEnd_characterization T.val T.property.1 T.property.2 x y).mp rfl
    have hinf : (cutComponent T.val e y).Infinite := by
      change (((toGraph T.val).deleteEdges {e.val}).connectedComponentMk y).supp.Infinite
      rw [he]
      exact hdir.2
    rw [hsame, ← hFC] at hinf
    exact hinf F.finite_toSet
  have htree : ((toGraph (fun f : LatticeEdge => decide (f ∈ H))).induce
      (F : Set (Site 2))).IsTree := by
    change ((toGraph (fun f : LatticeEdge => decide (f ∈ insideSelectedEdges T.val F))).induce
      (F : Set (Site 2))).IsTree
    rw [inside_selected_induce_eq, ← cut_induce_eq_of_exit T.val F e x y he hy, hFC]
    exact cut_component_induced_tree T.val T.property.1 e x
  have hs : ∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v) :=
    fun f hf => ((mem_inside_selected_edges_iff T.val F f).mp hf).2
  refine ⟨F, hF, hx, H, htree, hs, e, y, he, hy, ?_⟩
  intro f hi
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · intro ht
    by_cases hfe : f = e
    · exact Finset.mem_insert.mpr (Or.inl hfe)
    · obtain ⟨u, hu, v, hfuv⟩ := (mem_incident_coordinates_iff F f).mp hi
      have haL : (lattice 2).Adj u v := by
        change s(u, v) ∈ (lattice 2).edgeSet
        exact hfuv ▸ f.property
      have hfu : f = ⟨s(u, v), haL⟩ := Subtype.ext hfuv
      have ha : (cutGraph T.val e).Adj u v := by
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨⟨haL, by rw [← hfu]; exact ht⟩, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro hne
        exact hfe (Subtype.ext (hfuv.trans hne))
      have huC : u ∈ ((cutGraph T.val e).connectedComponentMk x).supp := by
        change u ∈ cutComponent T.val e x
        rw [← hFC]
        exact hu
      have hvC := ((cutGraph T.val e).connectedComponentMk x).mem_supp_of_adj_mem_supp huC ha
      have hv : v ∈ F := by
        change v ∈ (F : Set (Site 2))
        rw [hFC]
        exact hvC
      exact Finset.mem_insert_of_mem
        ((mem_inside_selected_edges_iff T.val F f).mpr ⟨ht, u, hu, v, hv, hfuv⟩)
  · intro hf
    rcases Finset.mem_insert.mp hf with hf | hf
    · rw [hf]
      exact outgoingEdge_selected T.val T.property.1 T.property.2 x
    · exact ((mem_inside_selected_edges_iff T.val F f).mp hf).1

/-- Incoming source 177: finite inside tree plus its unique listed boundary exit,
checking every present AND absent original coordinate touching F. -/
theorem past_subset_iff_exists_raw_tree (T : EndedTree) (x : Site 2)
    (W : Finset (Site 2)) :
    vertexPast T.val T.property.1 T.property.2 x ⊆ (W : Set (Site 2)) ↔
      ∃ F : Finset (Site 2), F ⊆ W ∧ x ∈ F ∧ ∃ H : Finset LatticeEdge,
        ((toGraph (fun f : LatticeEdge => decide (f ∈ H))).induce
          (F : Set (Site 2))).IsTree ∧
        (∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v)) ∧
        ∃ e : LatticeEdge, ∃ y : Site 2, e.val = s(x, y) ∧ y ∉ F ∧
          ∀ f ∈ incidentCoordinates F, T.val f = decide (f ∈ insert e H) := by
  constructor
  · intro hW
    obtain ⟨F, hF, hx, H, hH, hs, e, y, he, hy, hp⟩ := exists_actual_past_raw_pattern T x
    refine ⟨F, ?_, hx, H, hH, hs, e, y, he, hy, hp⟩
    intro z hz
    exact hW (hF ▸ hz)
  · rintro ⟨F, hFW, hx, H, hH, hs, e, y, he, hy, hp⟩
    rw [vertex_past_eq_of_raw_pattern T F H hH hs x hx e y he hy hp]
    exact hFW

/-- Every vertex is in its actual outgoing-edge past, even outside a proposed window. -/
theorem self_mem_vertex_past (T : EndedTree) (x : Site 2) :
    x ∈ vertexPast T.val T.property.1 T.property.2 x := by
  rw [vertexPast_eq_cutComponent]
  exact (mem_cutComponent_iff T.val _ x x).mpr (SimpleGraph.Reachable.refl x)

/-- An outside-window origin gives an impossible past containment, not a default past. -/
theorem not_past_subset_of_not_mem (T : EndedTree) (x : Site 2) (W : Finset (Site 2))
    (hx : x ∉ W) : ¬vertexPast T.val T.property.1 T.property.2 x ⊆ (W : Set (Site 2)) :=
  fun h => hx (h (self_mem_vertex_past T x))

end
end FiniteAvalanches.Trees.Lattice.CurrentInfinitePastPattern
