import FiniteAvalanches.Trees.Lattice.WiredCutComponents
import FiniteAvalanches.Trees.Lattice.TreeContinuityMeasurability
import FiniteAvalanches.Trees.CutComponents
import FiniteAvalanches.Trees.Lattice.FixedCutCertificate

set_option autoImplicit false
open LatticeProb SimpleGraph Filter
open scoped Classical

namespace FixedCutLimit12
open FiniteAvalanches FiniteAvalanches.Trees.Lattice FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Components TreeMeasurability11
noncomputable section

private theorem eventually_internal_representative (f : LatticeEdge) :
    ∀ᶠ N : ℕ in atTop, ∃ i : FiniteWired.InteriorEdge N, interiorEdge i = f := by
  rcases f with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | hf u v =>
    filter_upwards [eventually_ge_atTop (max (siteRadius 0 u) (siteRadius 0 v))] with N hN
    have hu : FiniteWired.inBox N u := (mem_box_sites N u).mp
      ((site_radius_zero_le_iff u N).mp ((le_max_left _ _).trans hN))
    have hv : FiniteWired.inBox N v := (mem_box_sites N v).mp
      ((site_radius_zero_le_iff v N).mp ((le_max_right _ _).trans hN))
    obtain ⟨k, h | h⟩ := he
    · exact ⟨⟨(FiniteWired.activeOfSite N u hu, FiniteWired.activeOfSite N v hv), k, h⟩,
        Subtype.ext rfl⟩
    · exact ⟨⟨(FiniteWired.activeOfSite N v hv, FiniteWired.activeOfSite N u hu), k, h⟩,
        Subtype.ext Sym2.eq_swap⟩

                                                                            
                                                                               
theorem originalCopyEdge_eq_internal {N : ℕ} (i : FiniteWired.InteriorEdge N)
    (e : FiniteWired.Edge N) (he : originalCopyEdge e = interiorEdge i) : e = .inl i := by
  cases e with
  | inl j => exact congrArg Sum.inl (interiorEdge_injective N he)
  | inr j =>
    have hs := congrArg Subtype.val he
    rcases Sym2.eq_iff.mp hs with h | h
    · exact False.elim (j.property (h.2 ▸ fun k => (i.val.2 k).property))
    · exact False.elim (j.property (h.2 ▸ fun k => (i.val.1 k).property))

private theorem finiteCutEscape_internal_iff {N : ℕ}
    (t : (WiredTrees.graph N).SpanningTree) (o : Site 2) (ho : FiniteWired.inBox N o)
    (i : FiniteWired.InteriorEdge N) (M : ℕ) :
    t ∈ finiteCutEscape o (interiorEdge i) M N ↔
      .inl i ∈ (WiredTrees.graph N).rootPathCopies t
        (some (FiniteWired.activeOfSite N o ho)) none ∧
      ¬cutSites (FiniteWired.activeOfSite N o ho) t (.inl i) ⊆ boxSites M := by
  constructor
  · rintro ⟨a, ha, e, he, hp, hc⟩
    have hae : a = FiniteWired.activeOfSite N o ho := FiniteWired.site_injective N ha
    have hee := originalCopyEdge_eq_internal i e he
    subst a; subst e
    exact ⟨hp, hc⟩
  · rintro ⟨hp, hc⟩
    exact ⟨FiniteWired.activeOfSite N o ho, rfl, .inl i, rfl, hp, hc⟩

private theorem cutSites_eq_of_componentAfter {N : ℕ}
    (t : (WiredTrees.graph N).SpanningTree) (a : FiniteWired.Active N)
    (i : FiniteWired.InteriorEdge N) (A : Set (Site 2))
    (hbox : ∀ y ∈ A, FiniteWired.inBox N y)
    (hcomp : (WiredTrees.graph N).componentAfter t.val (.inl i) (some a) = activeLift N A) :
    (cutSites a t (.inl i) : Set (Site 2)) = A := by
  ext y
  constructor
  · intro hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hr := (Finset.mem_filter.mp hb).2
    exact (some_mem_activeLift N A b).mp (hcomp ▸ hr)
  · intro hy
    let b := FiniteWired.activeOfSite N y (hbox y hy)
    have hr : (WiredTrees.graph N).reaches (t.val.erase (.inl i)) (some a) (some b) := by
      change some b ∈ (WiredTrees.graph N).componentAfter t.val (.inl i) (some a)
      rw [hcomp]
      exact (some_mem_activeLift N A b).mpr hy
    exact (mem_cutSites a t (.inl i) b).mpr hr

private theorem path_iff_finite_side {N : ℕ}
    (t : (WiredTrees.graph N).SpanningTree) (i : FiniteWired.InteriorEdge N)
    (A : Set (FiniteWired.Vertex N)) (hcut : (WiredTrees.graph N).cut_components A t.val (.inl i))
    (hsink : none ∉ A) (a : FiniteWired.Active N) :
    .inl i ∈ (WiredTrees.graph N).rootPathCopies t (some a) none ↔ some a ∈ A := by
  rw [(WiredTrees.graph N).mem_rootPathCopies]
  constructor
  · intro hp
    by_contra ha
    exact hp.2 (hcut.2.2.2.2 _ ha _ hsink)
  · intro ha
    exact ⟨hcut.1, fun hr => hsink (((WiredTrees.graph N).reaches_mem_iff hcut.2.2.1 hr).mp ha)⟩

private theorem infinite_event_iff_side (T : EndedTree) (o : Site 2) (f : LatticeEdge)
    (M : ℕ) (hf : T.val f = true) (c : Site 2)
    (hfin : (cutComponent T.val f c).Finite) :
    T ∈ infiniteCutEscape o f M ↔
      o ∈ cutComponent T.val f c ∧
        ¬cutComponent T.val f c ⊆ (boxSites M : Set (Site 2)) := by
  obtain ⟨hUnique, _⟩ := cutGraph_existsUnique_finite_and_infinite T.val T.property.1
    (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2) f hf
  have hcomp : (cutComponent T.val f o).Finite ↔ o ∈ cutComponent T.val f c := by
    constructor
    · intro ho; exact hUnique.unique ho hfin
    · intro ho
      change (cutGraph T.val f).connectedComponentMk o =
        (cutGraph T.val f).connectedComponentMk c at ho
      change ((cutGraph T.val f).connectedComponentMk o).supp.Finite
      rw [ho]; exact hfin
  have heq (ho : o ∈ cutComponent T.val f c) :
      cutComponent T.val f o = cutComponent T.val f c := congrArg ConnectedComponent.supp ho
  change (_ ∧ _) ↔ _
  rw [FixedCutCertificate11.ray_edge_iff_cutComponent_finite, hcomp]
  exact and_congr_right fun ho => by rw [heq ho]

private theorem infinite_event_selected (T : EndedTree) (o : Site 2) (f : LatticeEdge)
    (M : ℕ) (h : T ∈ infiniteCutEscape o f M) : T.val f = true := by
  obtain ⟨n, hn⟩ := h.1
  let r := orientedRay T.val T.property.1 T.property.2 o
  have he : f = ⟨s(r.vertex n, r.vertex (n+1)), r.adjacent n⟩ := Subtype.ext hn
  rw [he]
  exact ((orientedRay_characterization T.val T.property.1 T.property.2 o r).mp rfl).2 n

/-- Actual original-coordinate agreement fixes the copied source-to-sink cut event
in every sufficiently large genuine finite wired tree. The certificate and volume
threshold are constructed, and no infinite-tree property is assigned to wiredField. -/
theorem exists_finite_wired_fixed_cut_certificate (T : EndedTree) (o : Site 2)
    (f : LatticeEdge) (M : ℕ) :
    ∃ F : Finset LatticeEdge, ∃ R : ℕ,
      ∀ N ≥ R, ∀ t : (WiredTrees.graph N).SpanningTree,
        (∀ e ∈ F, wiredField t e = T.val e) →
          (t ∈ finiteCutEscape o f M N ↔ T ∈ infiniteCutEscape o f M) := by
  have hrep := eventually_internal_representative f
  have ho : ∀ᶠ N : ℕ in atTop, FiniteWired.inBox N o := by
    filter_upwards [eventually_ge_atTop (siteRadius 0 o)] with N hN
    exact (mem_box_sites N o).mp ((site_radius_zero_le_iff o N).mp hN)
  by_cases hf : T.val f = true
  · obtain ⟨⟨C, hCfin, _⟩, _⟩ := cutGraph_existsUnique_finite_and_infinite T.val T.property.1
      (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2) f hf
    obtain ⟨c, hc⟩ := C.nonempty_supp
    let A := C.supp
    let B := hCfin.toFinset
    let H := B.biUnion fun x => insert x (nbrFinset x)
    let R₀ := H.sup (siteRadius 0)
    have hgood : ∀ᶠ N : ℕ in atTop,
        (∃ i : FiniteWired.InteriorEdge N, interiorEdge i = f) ∧
        FiniteWired.inBox N o ∧ R₀ ≤ N := hrep.and (ho.and (eventually_ge_atTop R₀))
    obtain ⟨R, hR⟩ := eventually_atTop.mp hgood
    refine ⟨insert f (incidentCoordinates B), R, ?_⟩
    intro N hN t hagree
    obtain ⟨⟨i, hei⟩, hoN, hR₀⟩ := hR N hN
    have hH : ∀ x ∈ H, FiniteWired.inBox N x := by
      intro x hx
      exact (mem_box_sites N x).mp ((site_radius_zero_le_iff x N).mp
        ((Finset.le_sup (f := siteRadius 0) hx).trans hR₀))
    have hbox : ∀ x ∈ C.supp, FiniteWired.inBox N x := by
      intro x hx
      exact hH x (Finset.mem_biUnion.mpr ⟨x, hCfin.mem_toFinset.mpr hx, Finset.mem_insert_self _ _⟩)
    have hbuffer : ∀ x ∈ C.supp, ∀ y, (lattice 2).Adj x y → FiniteWired.inBox N y := by
      intro x hx y hxy
      exact hH y (Finset.mem_biUnion.mpr ⟨x, hCfin.mem_toFinset.mpr hx,
        Finset.mem_insert_of_mem ((FiniteWired.mem_neighbors_iff x y).mpr hxy)⟩)
    have hcfin : (cutComponent T.val f c).Finite := by
      change ((cutGraph T.val f).connectedComponentMk c).supp.Finite
      rw [hc]; exact hCfin
    have hCe : cutComponent T.val f c = A := congrArg ConnectedComponent.supp hc
    have hi : Sum.inl i ∈ t.val := by
      apply (wiredField_internal_iff t i).mp
      rw [hei, hagree f (Finset.mem_insert_self _ _), hf]
    have hcomp := componentAfter_of_incident_agreement T.val f C c hc hbox hbuffer
      t i hei hf ⟨hagree f (Finset.mem_insert_self _ _), fun x hx y hxy =>
        hagree _ (Finset.mem_insert_of_mem (mem_incidentCoordinates (hCfin.mem_toFinset.mpr hx) hxy))⟩
    have hcut := (WiredTrees.graph N).cut_components_at_source t (.inl i) hi
      (some (FiniteWired.activeOfSite N c (hbox c hc)))
    rw [hcomp] at hcut
    let a := FiniteWired.activeOfSite N o hoN
    have hp : Sum.inl i ∈ (WiredTrees.graph N).rootPathCopies t (some a) none ↔ o ∈ A :=
      (path_iff_finite_side t i (activeLift N A) hcut (sink_not_mem_activeLift N A) a).trans
        (some_mem_activeLift N A a)
    have hsites (ha : o ∈ A) : (cutSites a t (.inl i) : Set (Site 2)) = A :=
      cutSites_eq_of_componentAfter t a i A hbox
        ((WiredTrees.graph N).componentAfter_eq_of_cut hcut ((some_mem_activeLift N A a).mpr ha))
    rw [infinite_event_iff_side T o f M hf c hcfin, hCe]
    rw [← hei, finiteCutEscape_internal_iff t o hoN i M]
    rw [show (Sum.inl i ∈ (WiredTrees.graph N).rootPathCopies t (some a) none) ↔ o ∈ A from hp]
    apply and_congr_right
    intro ha
    have hsubset : cutSites a t (.inl i) ⊆ boxSites M ↔ A ⊆ (boxSites M : Set (Site 2)) := by
      rw [← hsites ha]
      exact Finset.coe_subset
    exact not_congr hsubset
  · have hgood := hrep.and ho
    obtain ⟨R, hR⟩ := eventually_atTop.mp hgood
    refine ⟨{f}, R, ?_⟩
    intro N hN t hagree
    obtain ⟨⟨i, hei⟩, hoN⟩ := hR N hN
    have hneg : t ∉ finiteCutEscape o f M N := by
      rw [← hei, finiteCutEscape_internal_iff t o hoN i M]
      intro h
      have hi := ((WiredTrees.graph N).mem_rootPathCopies t _ _ _).mp h.1 |>.1
      have ht := (wiredField_internal_iff t i).mpr hi
      rw [hei, hagree f (Finset.mem_singleton_self _)] at ht
      exact hf ht
    have hneg' : T ∉ infiniteCutEscape o f M := fun h => hf (infinite_event_selected T o f M h)
    exact iff_of_false hneg hneg'

end
end FixedCutLimit12
