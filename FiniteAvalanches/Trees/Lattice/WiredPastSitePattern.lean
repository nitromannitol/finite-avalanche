import FiniteAvalanches.Trees.Lattice.WiredIncidentPattern

/-! Original-site finite past witnesses for the incident-pattern union in
incoming main.tex177. The copied inside tree remains explicit, and every raw
coordinate, including wired exits, is tested against the same candidate. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Trees.Lattice.CurrentWiredPastSitePattern

open LatticeProb FiniteAvalanches.Sandpile TreeMeasurability11 CurrentOriginalField
open FiniteAvalanches.Trees.Multigraph
open scoped Classical
noncomputable section

/-- All genuine finite vertices lifting a given original finite support. -/
def liftedSites (N : ℕ) (F : Finset (Site 2)) : Finset (FiniteWired.Vertex N) :=
  Finset.univ.filter fun v => v ∈ activeLift N (F : Set (Site 2))

theorem coe_liftedSites (N : ℕ) (F : Finset (Site 2)) :
    (liftedSites N F : Set (FiniteWired.Vertex N)) = activeLift N (F : Set (Site 2)) := by
  ext v
  simp only [liftedSites, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Original sites of the active members of a finite vertex support. -/
def originalSites {N : ℕ} (F : Finset (FiniteWired.Vertex N)) : Finset (Site 2) :=
  (Finset.univ.filter fun a : FiniteWired.Active N => some a ∈ F).image FiniteWired.site

theorem mem_originalSites {N : ℕ} (F : Finset (FiniteWired.Vertex N)) (a : FiniteWired.Active N) :
    FiniteWired.site a ∈ originalSites F ↔ some a ∈ F := by
  constructor
  · intro h
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp h
    have hba := FiniteWired.site_injective N he
    subst b
    exact (Finset.mem_filter.mp hb).2
  · intro h
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

theorem activeLift_originalSites {N : ℕ} (F : Finset (FiniteWired.Vertex N))
    (hsink : none ∉ F) :
    activeLift N (originalSites F : Set (Site 2)) = (F : Set (FiniteWired.Vertex N)) := by
  ext v
  cases v with
  | none =>
    exact iff_of_false (sink_not_mem_activeLift N _) hsink
  | some a =>
    exact (some_mem_activeLift N _ a).trans (mem_originalSites F a)

theorem originalSites_subset {N : ℕ} (F : Finset (FiniteWired.Vertex N))
    (W : Finset (Site 2)) (hFW : F ⊆ liftedSites N W) : originalSites F ⊆ W := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hsome := hFW (Finset.mem_filter.mp ha).2
  rw [← Finset.mem_coe, coe_liftedSites, some_mem_activeLift] at hsome
  exact hsome

/-- No original witness site acquires a fictitious finite vertex. -/
theorem originalSites_inBox {N : ℕ} (F : Finset (FiniteWired.Vertex N)) :
    ∀ x ∈ originalSites F, FiniteWired.inBox N x := by
  intro x hx
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
  exact fun i => (a i).property

/-- The exact finite past-event union with original-site witnesses. The inside tree
and the outgoing edge are individual copied edges; their complete incident pattern
is tested in original coordinates. No past or component equality is a premise. -/
theorem past_subset_iff_exists_original_site_pattern (N : ℕ)
    (t : (WiredTrees.graph N).SpanningTree) (x : Site 2)
    (hxbox : FiniteWired.inBox N x) (W : Finset (Site 2))
    (hWbox : ∀ y ∈ W, FiniteWired.inBox N y) :
    (WiredTrees.graph N).past t none
        (some (FiniteWired.activeOfSite N x hxbox)) (by simp) ⊆
      activeLift N (W : Set (Site 2)) ↔
    ∃ F : Finset (Site 2), F ⊆ W ∧ x ∈ F ∧ ∃ H : Finset (FiniteWired.Edge N),
      (WiredTrees.graph N).is_tree (activeLift N (F : Set (Site 2))) H ∧
      ∃ e : FiniteWired.Edge N,
        (((WiredTrees.graph N).left e = some (FiniteWired.activeOfSite N x hxbox) ∧
            (WiredTrees.graph N).right e ∉ activeLift N (F : Set (Site 2))) ∨
          ((WiredTrees.graph N).right e = some (FiniteWired.activeOfSite N x hxbox) ∧
            (WiredTrees.graph N).left e ∉ activeLift N (F : Set (Site 2)))) ∧
        ∀ f ∈ incidentCoordinates F,
          originalWiredField t f = decide (f ∈ (insert e H).image originalCopyEdge) := by
  let G := WiredTrees.graph N
  let a := FiniteWired.activeOfSite N x hxbox
  have hsink : (none : FiniteWired.Vertex N) ∉ liftedSites N W := by
    rw [← Finset.mem_coe, coe_liftedSites]
    exact sink_not_mem_activeLift N _
  have hp := CurrentPastPattern.past_subset_iff_exists_incident_tree G t none (some a)
    (by simp) (liftedSites N W) hsink
  rw [coe_liftedSites] at hp
  constructor
  · intro h
    obtain ⟨V, hVW, haV, H, hH, e, he, hpattern⟩ := hp.mp h
    have hnoneV : (none : FiniteWired.Vertex N) ∉ V := fun hn => hsink (hVW hn)
    let F := originalSites V
    have hFV : activeLift N (F : Set (Site 2)) = (V : Set (FiniteWired.Vertex N)) :=
      activeLift_originalSites V hnoneV
    have hxF : x ∈ F := by
      have haF := (mem_originalSites V a).mpr haV
      exact haF
    have hHF : G.is_tree (activeLift N (F : Set (Site 2))) H := by
      rw [hFV]
      exact hH
    have heF : (G.left e = some a ∧ G.right e ∉ activeLift N (F : Set (Site 2))) ∨
        (G.right e = some a ∧ G.left e ∉ activeLift N (F : Set (Site 2))) := by
      rw [hFV]
      exact he
    have hac : some a ∈ activeLift N (F : Set (Site 2)) := hFV.symm ▸ haV
    have hcross : (G.left e ∈ activeLift N (F : Set (Site 2)) ∧
        G.right e ∉ activeLift N (F : Set (Site 2))) ∨
        (G.right e ∈ activeLift N (F : Set (Site 2)) ∧
        G.left e ∉ activeLift N (F : Set (Site 2))) := by
      rcases heF with he | he
      · exact Or.inl ⟨he.1.symm ▸ hac, he.2⟩
      · exact Or.inr ⟨he.1.symm ▸ hac, he.2⟩
    refine ⟨F, originalSites_subset V W hVW, hxF, H, hHF, e, heF, ?_⟩
    apply (CurrentIncidentPattern.incident_pattern_iff_raw_coordinates N t F
      (originalSites_inBox V) H hHF e hcross).mp
    rw [hFV]
    exact hpattern
  · rintro ⟨F, hFW, hxF, H, hH, e, he, hraw⟩
    have hbox : ∀ y ∈ F, FiniteWired.inBox N y := fun y hy => hWbox y (hFW hy)
    have haF : some a ∈ activeLift N (F : Set (Site 2)) :=
      (some_mem_activeLift N _ a).mpr hxF
    have hcross : (G.left e ∈ activeLift N (F : Set (Site 2)) ∧
        G.right e ∉ activeLift N (F : Set (Site 2))) ∨
        (G.right e ∈ activeLift N (F : Set (Site 2)) ∧
        G.left e ∉ activeLift N (F : Set (Site 2))) := by
      rcases he with he | he
      · exact Or.inl ⟨he.1.symm ▸ haF, he.2⟩
      · exact Or.inr ⟨he.1.symm ▸ haF, he.2⟩
    apply hp.mpr
    refine ⟨liftedSites N F, ?_, ?_, H, ?_, e, ?_, ?_⟩
    · intro v hv
      rw [← Finset.mem_coe, coe_liftedSites] at hv ⊢
      obtain ⟨v, hvo, hvF⟩ := hv
      exact ⟨v, hvo, hFW hvF⟩
    · rw [← Finset.mem_coe, coe_liftedSites]
      exact haF
    · rw [coe_liftedSites]
      exact hH
    · change (G.left e = some a ∧ G.right e ∉ (liftedSites N F : Set _)) ∨
        (G.right e = some a ∧ G.left e ∉ (liftedSites N F : Set _))
      rw [coe_liftedSites]
      exact he
    · rw [coe_liftedSites]
      exact (CurrentIncidentPattern.incident_pattern_iff_raw_coordinates N t F
        hbox H hH e hcross).mpr hraw

end
end FiniteAvalanches.Trees.Lattice.CurrentWiredPastSitePattern
