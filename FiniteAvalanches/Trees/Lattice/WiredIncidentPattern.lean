import FiniteAvalanches.Trees.FinitePastPattern
import FiniteAvalanches.Trees.Lattice.WiredOriginalFieldV1
import FiniteAvalanches.Sandpile.Components.Incident

/-! Original-coordinate transport of the finite incident-copy pattern in main.tex177.
No buffer is imposed: directions leaving the wired box retain their original exit copy. -/

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice.CurrentIncidentPattern

open LatticeProb FiniteAvalanches.Sandpile
open TreeMeasurability11 CurrentOriginalField
open FiniteAvalanches.Trees.Multigraph
open scoped Classical
noncomputable section

/-- The directional copy retains the original unordered lattice edge in either orientation. -/
theorem originalCopyEdge_directionEdge_val {N : ℕ} (x : FiniteWired.Active N)
    (d : FiniteWired.Direction) :
    (originalCopyEdge (FiniteWired.directionEdge x d)).val =
      s(FiniteWired.site x, FiniteWired.site x + FiniteWired.step d) := by
  rcases d with ⟨i, b⟩
  cases b
  · simp only [FiniteWired.directionEdge]
    split_ifs
    · simpa only [originalCopyEdge, interiorEdge, FiniteWired.site_activeOfSite,
        FiniteWired.step, Bool.false_eq_true, if_false, ← sub_eq_add_neg] using
        (Sym2.eq_swap : s(FiniteWired.site x - unit i, FiniteWired.site x) =
          s(FiniteWired.site x, FiniteWired.site x - unit i))
    · rfl
  · simp only [FiniteWired.directionEdge]
    split_ifs <;> rfl

/-- The actual nearest-neighbor coordinate of a direction. -/
theorem lattice_adj_step (x : Site 2) (d : FiniteWired.Direction) :
    (lattice 2).Adj x (x + FiniteWired.step d) := by
  rcases d with ⟨i, b⟩
  cases b
  · refine ⟨i, Or.inr ?_⟩
    simp only [FiniteWired.step, Bool.false_eq_true, if_false]
    abel
  · exact ⟨i, Or.inl (by simp only [FiniteWired.step, if_true])⟩

/-- All raw incident coordinates have genuine wired representatives, including exits. -/
theorem exists_incident_copy_of_coordinate (N : ℕ) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) (f : LatticeEdge)
    (hf : f ∈ incidentCoordinates F) :
    ∃ e : FiniteWired.Edge N,
      ((WiredTrees.graph N).left e ∈ activeLift N (F : Set (Site 2)) ∨
       (WiredTrees.graph N).right e ∈ activeLift N (F : Set (Site 2))) ∧
      originalCopyEdge e = f := by
  obtain ⟨x, hx, hf⟩ := Finset.mem_biUnion.mp hf
  obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hf
  have hxy := (FiniteWired.mem_neighbors_iff x y.val).mp y.property
  obtain ⟨i, hxy | hxy⟩ := hxy
  · let a := FiniteWired.activeOfSite N x (hbox x hx)
    refine ⟨FiniteWired.directionEdge a (i, true), ?_, ?_⟩
    · have hinc := Components.direction_edge_incident a (i, true)
      have ha : some a ∈ activeLift N (F : Set (Site 2)) :=
        (some_mem_activeLift N _ a).mpr hx
      rcases hinc with hl | hr
      · apply Or.inl
        change (FiniteWired.endpoints _).1 ∈ activeLift N (F : Set (Site 2))
        rw [hl]
        exact ha
      · apply Or.inr
        change (FiniteWired.endpoints _).2 ∈ activeLift N (F : Set (Site 2))
        rw [hr]
        exact ha
    · apply Subtype.ext
      rw [originalCopyEdge_directionEdge_val]
      change s(x, x + FiniteWired.step (i, true)) = s(x, y.val)
      simpa only [FiniteWired.step, if_true] using congrArg (fun z => s(x, z)) hxy.symm
  · let a := FiniteWired.activeOfSite N x (hbox x hx)
    refine ⟨FiniteWired.directionEdge a (i, false), ?_, ?_⟩
    · have hinc := Components.direction_edge_incident a (i, false)
      have ha : some a ∈ activeLift N (F : Set (Site 2)) :=
        (some_mem_activeLift N _ a).mpr hx
      rcases hinc with hl | hr
      · apply Or.inl
        change (FiniteWired.endpoints _).1 ∈ activeLift N (F : Set (Site 2))
        rw [hl]
        exact ha
      · apply Or.inr
        change (FiniteWired.endpoints _).2 ∈ activeLift N (F : Set (Site 2))
        rw [hr]
        exact ha
    · apply Subtype.ext
      rw [originalCopyEdge_directionEdge_val]
      change s(x, x + FiniteWired.step (i, false)) = s(x, y.val)
      have hy : x - unit i = y.val := by
        calc
          x - unit i = (y.val + unit i) - unit i :=
            congrArg (fun z : Site 2 => z - unit i) hxy
          _ = y.val := by abel
      simpa only [FiniteWired.step, Bool.false_eq_true, if_false, ← sub_eq_add_neg] using
        congrArg (fun z => s(x, z)) hy

/-- Conversely, every incident copied edge is an incident original coordinate. -/
theorem coordinate_mem_of_incident_copy {N : ℕ} (F : Finset (Site 2))
    (e : FiniteWired.Edge N)
    (he : (WiredTrees.graph N).left e ∈ activeLift N (F : Set (Site 2)) ∨
      (WiredTrees.graph N).right e ∈ activeLift N (F : Set (Site 2))) :
    originalCopyEdge e ∈ incidentCoordinates F := by
  have ha : ∃ a : FiniteWired.Active N,
      FiniteWired.site a ∈ F ∧ Components.incident a e := by
    rcases he with hl | hr
    · obtain ⟨a, hl, ha⟩ := hl
      exact ⟨a, ha, Or.inl hl⟩
    · obtain ⟨a, hr, ha⟩ := hr
      exact ⟨a, ha, Or.inr hr⟩
  obtain ⟨a, ha, he⟩ := ha
  obtain ⟨d, rfl⟩ := Components.exists_direction_of_incident a e he
  have hraw : originalCopyEdge (FiniteWired.directionEdge a d) =
      (⟨s(FiniteWired.site a, FiniteWired.site a + FiniteWired.step d),
        lattice_adj_step (FiniteWired.site a) d⟩ : LatticeEdge) :=
    Subtype.ext (originalCopyEdge_directionEdge_val a d)
  rw [hraw]
  exact mem_incidentCoordinates ha (lattice_adj_step (FiniteWired.site a) d)


/-- Injectivity keeps presence in an image equivalent to presence of the same copy. -/
theorem copy_mem_image_iff {N : ℕ} (S : Finset (FiniteWired.Edge N))
    (e : FiniteWired.Edge N) :
    originalCopyEdge e ∈ S.image originalCopyEdge ↔ e ∈ S := by
  constructor
  · rintro he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    exact (originalCopyEdge_injective N hfe) ▸ hf
  · exact Finset.mem_image_of_mem originalCopyEdge

/-- Candidate inside-tree copies and the outgoing copy are all genuinely incident. -/
theorem candidate_copy_incident {N : ℕ} (F : Finset (Site 2))
    (H : Finset (FiniteWired.Edge N))
    (hH : (WiredTrees.graph N).is_tree (activeLift N (F : Set (Site 2))) H)
    (e : FiniteWired.Edge N)
    (he : ((WiredTrees.graph N).left e ∈ activeLift N (F : Set (Site 2)) ∧
        (WiredTrees.graph N).right e ∉ activeLift N (F : Set (Site 2))) ∨
      ((WiredTrees.graph N).right e ∈ activeLift N (F : Set (Site 2)) ∧
        (WiredTrees.graph N).left e ∉ activeLift N (F : Set (Site 2))))
    (f : FiniteWired.Edge N) (hf : f ∈ insert e H) :
    (WiredTrees.graph N).left f ∈ activeLift N (F : Set (Site 2)) ∨
      (WiredTrees.graph N).right f ∈ activeLift N (F : Set (Site 2)) := by
  rcases Finset.mem_insert.mp hf with rfl | hf
  · rcases he with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  · exact Or.inl (hH.2.1 f hf).1

/-- The literal finite incident-copy pattern is exactly its full raw-coordinate cylinder.
Both selected and absent coordinates are tested, including every original exit copy. -/
theorem incident_pattern_iff_raw_coordinates (N : ℕ)
    (t : (WiredTrees.graph N).SpanningTree) (F : Finset (Site 2))
    (hbox : ∀ x ∈ F, FiniteWired.inBox N x) (H : Finset (FiniteWired.Edge N))
    (hH : (WiredTrees.graph N).is_tree (activeLift N (F : Set (Site 2))) H)
    (e : FiniteWired.Edge N)
    (he : ((WiredTrees.graph N).left e ∈ activeLift N (F : Set (Site 2)) ∧
        (WiredTrees.graph N).right e ∉ activeLift N (F : Set (Site 2))) ∨
      ((WiredTrees.graph N).right e ∈ activeLift N (F : Set (Site 2)) ∧
        (WiredTrees.graph N).left e ∉ activeLift N (F : Set (Site 2)))) :
    CurrentPastPattern.incidentEdges (WiredTrees.graph N)
        (activeLift N (F : Set (Site 2))) t.val = insert e H ↔
      ∀ f ∈ incidentCoordinates F, originalWiredField t f =
        decide (f ∈ (insert e H).image originalCopyEdge) := by
  constructor
  · intro hpattern f hf
    obtain ⟨c, hc, rfl⟩ := exists_incident_copy_of_coordinate N F hbox f hf
    apply Bool.eq_iff_iff.mpr
    rw [originalWiredField_copy_iff, decide_eq_true_eq, copy_mem_image_iff]
    constructor
    · intro hct
      have hci := (CurrentPastPattern.mem_incidentEdges _ _ _ c).mpr ⟨hct, hc⟩
      rw [hpattern] at hci
      exact hci
    · intro hcc
      rw [← hpattern] at hcc
      exact ((CurrentPastPattern.mem_incidentEdges _ _ _ c).mp hcc).1
  · intro hraw
    ext c
    constructor
    · intro hc
      obtain ⟨hct, hinc⟩ := (CurrentPastPattern.mem_incidentEdges _ _ _ c).mp hc
      have hcoord := coordinate_mem_of_incident_copy F c hinc
      have hfield := (originalWiredField_copy_iff t c).mpr hct
      rw [hraw (originalCopyEdge c) hcoord, decide_eq_true_eq] at hfield
      exact (copy_mem_image_iff (insert e H) c).mp hfield
    · intro hc
      have hinc := candidate_copy_incident F H hH e he c hc
      have hcoord := coordinate_mem_of_incident_copy F c hinc
      have hfield : originalWiredField t (originalCopyEdge c) = true := by
        rw [hraw (originalCopyEdge c) hcoord, decide_eq_true_eq]
        exact (copy_mem_image_iff (insert e H) c).mpr hc
      exact (CurrentPastPattern.mem_incidentEdges _ _ _ c).mpr
        ⟨(originalWiredField_copy_iff t c).mp hfield, hinc⟩

end
end FiniteAvalanches.Trees.Lattice.CurrentIncidentPattern
