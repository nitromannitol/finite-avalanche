import FiniteAvalanches.Trees.Lattice.WiredOutgoingRaw
import FiniteAvalanches.Trees.Lattice.WiredInsideRawTree

/-! Incoming cd552a5, main.tex177: the finite past uses the same original
F/H/e candidate as the one-ended infinite tree. No neighbor buffer is needed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Trees.Lattice.CurrentCommonRawPast
open LatticeProb FiniteAvalanches.Sandpile TreeMeasurability11 CurrentOriginalField
open scoped Classical
noncomputable section

/-- All genuine copies of the specified raw inside edges. -/
def copiesOfRaw (N : ℕ) (H : Finset LatticeEdge) : Finset (FiniteWired.Edge N) :=
  Finset.univ.filter fun c => originalCopyEdge c ∈ H

/-- Membership retains the individual original copied edge. -/
theorem mem_copiesOfRaw (N : ℕ) (H : Finset LatticeEdge) (c : FiniteWired.Edge N) :
    c ∈ copiesOfRaw N H ↔ originalCopyEdge c ∈ H := by
  simp only [copiesOfRaw, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A raw coordinate with an endpoint in F belongs to its full incident family. -/
theorem raw_edge_incident (F : Finset (Site 2)) (f : LatticeEdge)
    (u v : Site 2) (hu : u ∈ F) (hpair : f.val = s(u, v)) :
    f ∈ incidentCoordinates F := by
  have ha : (lattice 2).Adj u v := by
    change s(u, v) ∈ (lattice 2).edgeSet
    exact hpair ▸ f.property
  have hf : f = ⟨s(u, v), ha⟩ := Subtype.ext hpair
  rw [hf]
  exact mem_incidentCoordinates hu ha

/-- Support supplies all actual representatives and the image is exactly H.
Both endpoints stay in F; no exit edge is introduced into the inside tree. -/
theorem image_copiesOfRaw (N : ℕ) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) (H : Finset LatticeEdge)
    (hs : ∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v)) :
    (copiesOfRaw N H).image originalCopyEdge = H := by
  ext f
  constructor
  · intro hf
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hf
    exact (mem_copiesOfRaw N H c).mp hc
  · intro hf
    obtain ⟨u, hu, v, _hv, hpair⟩ := hs f hf
    have hinc := raw_edge_incident F f u v hu hpair
    obtain ⟨c, _hc, hcf⟩ :=
      CurrentIncidentPattern.exists_incident_copy_of_coordinate N F hbox f hinc
    apply Finset.mem_image.mpr
    refine ⟨c, (mem_copiesOfRaw N H c).mpr ?_, hcf⟩
    rw [hcf]
    exact hf

/-- The literal raw inside-tree clauses produce an actual copied inside tree. -/
theorem copiesOfRaw_is_tree (N : ℕ) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) (H : Finset LatticeEdge)
    (ht : ((toGraph (fun f : LatticeEdge => decide (f ∈ H))).induce
      (F : Set (Site 2))).IsTree)
    (hs : ∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v)) :
    (WiredTrees.graph N).is_tree (activeLift N (F : Set (Site 2))) (copiesOfRaw N H) := by
  apply (CurrentInsideRawTree.copied_tree_iff_raw_tree N F hbox (copiesOfRaw N H)).mpr
  rw [image_copiesOfRaw N F hbox H hs]
  exact ⟨ht, hs⟩

/-- The author's finite incident-pattern union with common original raw candidates.
All present and absent coordinates touching the SAME F are tested. -/
theorem past_subset_iff_exists_common_raw_tree (N : ℕ)
    (t : (WiredTrees.graph N).SpanningTree) (x : Site 2)
    (hxbox : FiniteWired.inBox N x) (W : Finset (Site 2))
    (hWbox : ∀ y ∈ W, FiniteWired.inBox N y) :
    (WiredTrees.graph N).past t none
        (some (FiniteWired.activeOfSite N x hxbox)) (by simp) ⊆
      activeLift N (W : Set (Site 2)) ↔
    ∃ F : Finset (Site 2), F ⊆ W ∧ x ∈ F ∧ ∃ H : Finset LatticeEdge,
      ((toGraph (fun f : LatticeEdge => decide (f ∈ H))).induce
        (F : Set (Site 2))).IsTree ∧
      (∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v)) ∧
      ∃ e : LatticeEdge, ∃ y : Site 2, e.val = s(x, y) ∧ y ∉ F ∧
        ∀ f ∈ incidentCoordinates F, originalWiredField t f = decide (f ∈ insert e H) := by
  have hp := CurrentWiredOutgoingRaw.past_subset_iff_exists_raw_outgoing_pattern
    N t x hxbox W hWbox
  constructor
  · intro h
    obtain ⟨F, hFW, hxF, H, hH, e, ⟨y, hy, he⟩, hpattern⟩ := hp.mp h
    have hbox : ∀ z ∈ F, FiniteWired.inBox N z := fun z hz => hWbox z (hFW hz)
    obtain ⟨ht, hs⟩ := (CurrentInsideRawTree.copied_tree_iff_raw_tree N F hbox H).mp hH
    refine ⟨F, hFW, hxF, H.image originalCopyEdge, ht, hs,
      originalCopyEdge e, y, he, hy, ?_⟩
    intro f hf
    simpa only [Finset.image_insert] using hpattern f hf
  · rintro ⟨F, hFW, hxF, H, ht, hs, e, y, he, hy, hpattern⟩
    have hbox : ∀ z ∈ F, FiniteWired.inBox N z := fun z hz => hWbox z (hFW hz)
    have himage := image_copiesOfRaw N F hbox H hs
    have htree := copiesOfRaw_is_tree N F hbox H ht hs
    obtain ⟨c, _hc, hce⟩ := CurrentIncidentPattern.exists_incident_copy_of_coordinate
      N F hbox e (raw_edge_incident F e x y hxF he)
    apply hp.mpr
    refine ⟨F, hFW, hxF, copiesOfRaw N H, htree, c, ⟨y, hy, ?_⟩, ?_⟩
    · exact (congrArg Subtype.val hce).trans he
    · intro f hf
      rw [Finset.image_insert, hce, himage]
      exact hpattern f hf

end
end FiniteAvalanches.Trees.Lattice.CurrentCommonRawPast

set_option pp.fullNames true
#print FiniteAvalanches.Trees.Lattice.CurrentCommonRawPast.copiesOfRaw
#print FiniteAvalanches.Trees.Lattice.CurrentCommonRawPast.past_subset_iff_exists_common_raw_tree
#print axioms FiniteAvalanches.Trees.Lattice.CurrentCommonRawPast.copiesOfRaw
#print axioms FiniteAvalanches.Trees.Lattice.CurrentCommonRawPast.mem_copiesOfRaw
#print axioms FiniteAvalanches.Trees.Lattice.CurrentCommonRawPast.raw_edge_incident
#print axioms FiniteAvalanches.Trees.Lattice.CurrentCommonRawPast.image_copiesOfRaw
#print axioms FiniteAvalanches.Trees.Lattice.CurrentCommonRawPast.copiesOfRaw_is_tree
#print axioms FiniteAvalanches.Trees.Lattice.CurrentCommonRawPast.past_subset_iff_exists_common_raw_tree
