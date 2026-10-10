import FiniteAvalanches.Trees.Lattice.WiredCutComponents
import FiniteAvalanches.Trees.Lattice.TreeContinuityMeasurability
import FiniteAvalanches.Trees.Past
import FiniteAvalanches.Sandpile.Components.Directions

set_option autoImplicit false
open scoped Classical
noncomputable section
namespace ReciprocalCertificate14
open LatticeProb SimpleGraph FiniteAvalanches FiniteAvalanches.Trees
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice TreeMeasurability11

private theorem selected_internal_adj {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (x y : FiniteWired.Active N) (hxy : (toGraph (wiredField t)).Adj
      (FiniteWired.site x) (FiniteWired.site y)) :
    ((WiredTrees.graph N).toSimple t.val).Adj (some x) (some y) := by
  obtain ⟨j, hj, he⟩ := (wiredField_eq_true t
    ⟨s(FiniteWired.site x, FiniteWired.site y), hxy.1⟩).mp hxy.2
  rcases Sym2.eq_iff.mp (congrArg Subtype.val he) with h | h
  · exact ⟨.inl j, hj, Or.inl ⟨congrArg some (FiniteWired.site_injective N h.1),
      congrArg some (FiniteWired.site_injective N h.2)⟩⟩
  · exact ⟨.inl j, hj, Or.inr ⟨congrArg some (FiniteWired.site_injective N h.2),
      congrArg some (FiniteWired.site_injective N h.1)⟩⟩

/-- Actual unique finite paths are the active lifts of the actual selected infinite
paths. The only agreement required is on the finite true minimal span. -/
theorem path_support_transport (T : EndedTree) (S : Finset (Site 2)) (hS : S.Nonempty)
    {N : ℕ} (hbox : ∀ z ∈ connectingSites T.val T.property.1 T.property.2 S hS,
      FiniteWired.inBox N z) (t : (WiredTrees.graph N).SpanningTree)
    (hagree : ∀ z ∈ connectingSites T.val T.property.1 T.property.2 S hS,
      ∀ y, ∀ hzy : (lattice 2).Adj z y,
      wiredField t ⟨s(z,y), hzy⟩ = T.val ⟨s(z,y), hzy⟩)
    (x y : FiniteWired.Active N) (hx : FiniteWired.site x ∈ S)
    (hy : FiniteWired.site y ∈ S) :
    {v | v ∈ (RootedPaths.path ((WiredTrees.graph N).toSimple_isTree t.property)
      (some x) (some y)).support} =
      activeLift N {z | z ∈ (RootedPaths.path T.property.1
        (FiniteWired.site x) (FiniteWired.site y)).support} := by
  let K : Set (Site 2) := connectingSites T.val T.property.1 T.property.2 S hS
  have hpK : ∀ z ∈ (RootedPaths.path T.property.1
      (FiniteWired.site x) (FiniteWired.site y)).support, z ∈ K := by
    intro z hz
    change z ∈ (connectingSites T.val T.property.1 T.property.2 S hS : Set (Site 2))
    rw [connectingSites_eq_span]
    exact ⟨FiniteWired.site x, hx, FiniteWired.site y, hy, hz⟩
  let φ : (toGraph T.val).induce K →g (WiredTrees.graph N).toSimple t.val := {
    toFun := fun z => some (FiniteWired.activeOfSite N z.val (hbox _ z.property))
    map_rel' := by
      intro z w hzw
      apply selected_internal_adj t _ _
      exact ⟨hzw.1, (hagree _ z.property _ hzw.1).symm ▸ hzw.2⟩ }
  have hφ : Function.Injective φ := by
    intro z w h
    apply Subtype.ext
    exact congrArg FiniteWired.site (Option.some.inj h)
  let p := (RootedPaths.path T.property.1 (FiniteWired.site x) (FiniteWired.site y)).induce K hpK
  let q : ((WiredTrees.graph N).toSimple t.val).Walk (some x) (some y) :=
    (p.map φ).copy (by exact congrArg some (FiniteWired.site_injective N rfl))
      (by exact congrArg some (FiniteWired.site_injective N rfl))
  have hp : p.IsPath := by
    apply Walk.IsPath.mk'
    apply List.Nodup.of_map Subtype.val
    have he := congrArg Walk.support (Walk.map_induce
      (RootedPaths.path T.property.1 (FiniteWired.site x) (FiniteWired.site y)) hpK)
    rw [Walk.support_map] at he
    exact he.symm ▸ (RootedPaths.path_isPath T.property.1
      (FiniteWired.site x) (FiniteWired.site y)).support_nodup
  have hq : q.IsPath := by
    simpa only [q, Walk.isPath_copy] using (Walk.isPath_map_iff_of_injective hφ).mpr hp
  rw [RootedPaths.path_eq _ q hq]
  ext v
  simp only [q, Walk.support_copy, Walk.support_map, List.mem_map, activeLift, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨FiniteWired.activeOfSite N z.val (hbox _ z.property), rfl, ?_⟩
    simpa only [p, Walk.support_induce, List.mem_attachWith, FiniteWired.site_activeOfSite] using hz
  · rintro ⟨a, rfl, ha⟩
    refine ⟨⟨FiniteWired.site a, hpK _ ha⟩, ?_, ?_⟩
    · simpa only [p, Walk.support_induce, List.mem_attachWith] using ha
    · exact congrArg some (FiniteWired.site_injective N rfl)

/-- Agreement on the true span preserves that whole minimal span, for arbitrary
finite source sets, without replacing it by the ancestor past. -/
theorem span_transport (T : EndedTree) (S : Finset (Site 2)) (hS : S.Nonempty)
    {N : ℕ} (hbox : ∀ z ∈ connectingSites T.val T.property.1 T.property.2 S hS,
      FiniteWired.inBox N z) (t : (WiredTrees.graph N).SpanningTree)
    (hagree : ∀ z ∈ connectingSites T.val T.property.1 T.property.2 S hS,
      ∀ y, ∀ hzy : (lattice 2).Adj z y,
      wiredField t ⟨s(z,y), hzy⟩ = T.val ⟨s(z,y), hzy⟩) :
    (WiredTrees.graph N).span t (finiteMarks N S) =
      activeLift N (connectingSites T.val T.property.1 T.property.2 S hS) := by
  have hsub := ((connectingSites_characterization T.val T.property.1 T.property.2 S hS _).mp rfl).1
  ext v
  change (∃ x ∈ finiteMarks N S, ∃ y ∈ finiteMarks N S,
    v ∈ (RootedPaths.path ((WiredTrees.graph N).toSimple_isTree t.property) x y).support) ↔ _
  constructor
  · rintro ⟨_, ⟨x,hx,rfl⟩, _, ⟨y,hy,rfl⟩, hv⟩
    have he := path_support_transport T S hS hbox t hagree
      x y hx hy
    have he' : {v | v ∈ (RootedPaths.path ((WiredTrees.graph N).toSimple_isTree t.property)
        (some x) (some y)).support} = activeLift N
      {z | z ∈ (RootedPaths.path T.property.1 (FiniteWired.site x) (FiniteWired.site y)).support} := he
    have hv' : v ∈ activeLift N {z | z ∈ (RootedPaths.path T.property.1
        (FiniteWired.site x) (FiniteWired.site y)).support} := (Set.ext_iff.mp he' v).mp hv
    obtain ⟨a, rfl, ha⟩ := hv'
    apply (some_mem_activeLift N _ a).mpr
    rw [connectingSites_eq_span]
    exact ⟨FiniteWired.site x, hx, FiniteWired.site y, hy, ha⟩
  · rintro ⟨a, rfl, ha⟩
    rw [connectingSites_eq_span] at ha
    obtain ⟨x,hx,y,hy,ha⟩ := ha
    let ax := FiniteWired.activeOfSite N x (hbox _ (hsub hx))
    let ay := FiniteWired.activeOfSite N y (hbox _ (hsub hy))
    refine ⟨some ax, ⟨ax,hx,rfl⟩, some ay, ⟨ay,hy,rfl⟩, ?_⟩
    have he := path_support_transport T S hS hbox t hagree ax ay hx hy
    exact (Set.ext_iff.mp he (some a)).mpr (⟨a, rfl, ha⟩ : some a ∈ activeLift N
      {z | z ∈ (RootedPaths.path T.property.1 x y).support})

/-- A finite original-edge certificate forces the true minimal span, earliest
common ancestor and its whole actual finite past in every larger wired volume. -/
theorem ancestor_past_span_certificate (T : EndedTree) (S : Finset (Site 2))
    (hS : S.Nonempty) :
    ∃ (F : Finset LatticeEdge) (R : ℕ), ∀ N ≥ R,
      ∀ t : (WiredTrees.graph N).SpanningTree,
      (∀ f ∈ F, wiredField t f = T.val f) →
      ∃ (hN : ∀ x ∈ S, FiniteWired.inBox N x)
        (hcN : FiniteWired.inBox N (earliestCommonAncestor T.val T.property.1 T.property.2 S hS)),
        (∀ z ∈ vertexPast T.val T.property.1 T.property.2
          (earliestCommonAncestor T.val T.property.1 T.property.2 S hS), FiniteWired.inBox N z) ∧
        (WiredTrees.graph N).span t (finiteMarks N S) =
          activeLift N (connectingSites T.val T.property.1 T.property.2 S hS) ∧
        (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
          (finiteMarks_nonempty N S hS hN) =
          some (FiniteWired.activeOfSite N
            (earliestCommonAncestor T.val T.property.1 T.property.2 S hS) hcN) ∧
        (WiredTrees.graph N).descendants t none
          ((WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
            (finiteMarks_nonempty N S hS hN)) =
          activeLift N (vertexPast T.val T.property.1 T.property.2
            (earliestCommonAncestor T.val T.property.1 T.property.2 S hS)) := by
  let c := earliestCommonAncestor T.val T.property.1 T.property.2 S hS
  let e := outgoingEdge T.val T.property.1 T.property.2 c
  let C := (cutGraph T.val e).connectedComponentMk c
  have hCP : C.supp = vertexPast T.val T.property.1 T.property.2 c := rfl
  have hC : C.supp.Finite := vertexPast_finite T.val T.property.1 T.property.2 c
  have hc : c ∈ C.supp := rfl
  have hKC : (connectingSites T.val T.property.1 T.property.2 S hS : Set (Site 2)) ⊆ C.supp :=
    connectingSites_subset_past T.val T.property.1 T.property.2 S hS
  have hSC : (S : Set (Site 2)) ⊆ C.supp := sources_mem_earliestCommonAncestor_past T.val T.property.1 T.property.2 S hS
  let H := hC.toFinset.biUnion fun x => insert x (nbrFinset x)
  let F := insert e (incidentCoordinates hC.toFinset)
  refine ⟨F, H.sup (siteRadius 0), ?_⟩
  intro N hRN t hmatch
  have hH : ∀ x ∈ H, FiniteWired.inBox N x := by
    intro x hx
    exact (mem_box_sites N x).mp
      ((site_radius_zero_le_iff x N).mp
        ((Finset.le_sup (f := siteRadius 0) hx).trans hRN))
  have hbox : ∀ x ∈ C.supp, FiniteWired.inBox N x := by
    intro x hx
    exact hH x (Finset.mem_biUnion.mpr ⟨x, hC.mem_toFinset.mpr hx, Finset.mem_insert_self _ _⟩)
  have hbuffer : ∀ x ∈ C.supp, ∀ y, (lattice 2).Adj x y → FiniteWired.inBox N y := by
    intro x hx y hxy
    exact hH y (Finset.mem_biUnion.mpr ⟨x, hC.mem_toFinset.mpr hx,
      Finset.mem_insert_of_mem ((FiniteWired.mem_neighbors_iff x y).mpr hxy)⟩)
  have hagree : ∀ x ∈ C.supp, ∀ y, ∀ hxy : (lattice 2).Adj x y,
      wiredField t ⟨s(x,y),hxy⟩ = T.val ⟨s(x,y),hxy⟩ := by
    intro x hx y hxy
    exact hmatch _ (Finset.mem_insert_of_mem (mem_incidentCoordinates (hC.mem_toFinset.mpr hx) hxy))
  have he : T.val e = true := outgoingEdge_selected T.val T.property.1 T.property.2 c
  have het : wiredField t e = true := (hmatch e (Finset.mem_insert_self _ _)).trans he
  obtain ⟨i, hi, hei⟩ := (wiredField_eq_true t e).mp het
  have hcomp := componentAfter_of_incident_agreement T.val e C c hc hbox hbuffer t i hei he
    ⟨hmatch e (Finset.mem_insert_self _ _), hagree⟩
  let G := WiredTrees.graph N
  let a := FiniteWired.activeOfSite N c (hbox c hc)
  have hcut : G.cut_components (activeLift N C.supp) t.val (.inl i) := by
    have h := G.cut_components_at_source t (.inl i) hi (some a)
    rwa [hcomp] at h
  let p : G.CutTree (activeLift N C.supp) := ⟨(t.val, .inl i), t.property, hcut⟩
  have hve : G.left (.inl i) = some a ∨ G.right (.inl i) = some a := by
    have heq := congrArg Subtype.val hei
    change s(FiniteWired.site i.val.1, FiniteWired.site i.val.2) =
      s(c, infiniteDirection T.val T.property.1
        (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2) c) at heq
    rcases Sym2.eq_iff.mp heq with h | h
    · exact Or.inl (congrArg some (FiniteWired.site_injective N h.1))
    · exact Or.inr (congrArg some (FiniteWired.site_injective N h.2))
  have haC : some a ∈ activeLift N C.supp := (some_mem_activeLift _ _ _).mpr hc
  have hd : G.descendants t none (some a) = activeLift N C.supp :=
    G.descendants_eq_cut p none (some a) (sink_not_mem_activeLift _ _) haC hve
  have hN : ∀ x ∈ S, FiniteWired.inBox N x := fun x hx => hbox x (hSC hx)
  have hspan : G.span t (finiteMarks N S) =
      activeLift N (connectingSites T.val T.property.1 T.property.2 S hS) :=
    span_transport T S hS (fun z hz => hbox z (hKC hz)) t
      (fun z hz => hagree z (hKC hz))
  have hac : ∀ x ∈ finiteMarks N S,
      RootedPaths.ancestor (G.toSimple_isTree t.property) none (some a) x := by
    rintro _ ⟨x,hx,rfl⟩
    change some x ∈ G.descendants t none (some a)
    rw [hd, some_mem_activeLift]
    exact hSC hx
  have haK : some a ∈ G.span t (finiteMarks N S) := by
    rw [hspan, some_mem_activeLift]
    exact ancestor_mem_connectingSites T.val T.property.1 T.property.2 S hS
  have hanc : G.ancestorOf t none (finiteMarks N S) (finiteMarks_nonempty N S hS hN) = some a :=
    (RootedPaths.commonAncestor_eq_iff_mem_connectingSubtree
      (G.toSimple_isTree t.property) none (finiteMarks N S)
        (finiteMarks_nonempty N S hS hN) hac).mpr haK
  refine ⟨hN, hbox c hc, hbox, hspan, hanc, ?_⟩
  rw [hanc]
  exact hd

#print axioms ancestor_past_span_certificate
#print axioms path_support_transport
#print axioms span_transport
end ReciprocalCertificate14
