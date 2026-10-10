import FiniteAvalanches.Sandpile.Components.Fields
import FiniteAvalanches.Model.WiredLaplacian

/-! Induced complementary degrees retain individual wired direction copies.
Each outside direction is retained, including every distinct sink exit. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

def innerDirections (C : Finset Site2) (x : Site2) : Finset FiniteWired.Direction :=
  Finset.univ.filter (fun d => x + FiniteWired.step d ∈ C)
def outerDirections (C : Finset Site2) (x : Site2) : Finset FiniteWired.Direction :=
  Finset.univ.filter (fun d => x + FiniteWired.step d ∉ C)

theorem degree_eq_card_inner_directions (C : Finset Site2) (x : Site2) :
    degree C x = (innerDirections C x).card := by
  have hi : Function.Injective (fun d : FiniteWired.Direction => x + FiniteWired.step d) := by
    intro d e h
    exact FiniteWired.step_injective (add_left_cancel h)
  have he : (innerDirections C x).image (fun d => x + FiniteWired.step d) = nbrFinset x ∩ C := by
    ext y
    simp only [innerDirections, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_inter, nbrFinset, Finset.mem_biUnion, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨i, b⟩, hC, rfl⟩
      refine ⟨?_, hC⟩
      cases b
      · exact ⟨i, Or.inr (by simp [FiniteWired.step, sub_eq_add_neg])⟩
      · exact ⟨i, Or.inl (by simp [FiniteWired.step])⟩
    · rintro ⟨⟨i, h | h⟩, hC⟩
      · refine ⟨(i, true), ?_, ?_⟩
        · simpa [FiniteWired.step, ← h] using hC
        · simpa [FiniteWired.step] using h.symm
      · refine ⟨(i, false), ?_, ?_⟩
        · simpa [FiniteWired.step, ← sub_eq_add_neg, ← h] using hC
        · simpa [FiniteWired.step, ← sub_eq_add_neg] using h.symm
  rw [degree, ← he, Finset.card_image_of_injective _ hi]

theorem card_outer_directions (C : Finset Site2) (x : Site2) :
    (outerDirections C x).card = 4 - degree C x := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset FiniteWired.Direction)) (p := fun d => x + FiniteWired.step d ∈ C)
  change (innerDirections C x).card + (outerDirections C x).card = _ at h
  rw [← degree_eq_card_inner_directions C x] at h
  have hc : (Finset.univ : Finset FiniteWired.Direction).card = 4 := by decide
  change degree C x + (outerDirections C x).card = _ at h
  omega

/-- Distinct directions give distinct original incident edge copies. -/
theorem direction_edge_injective {N : ℕ} (x : FiniteWired.Active N) :
    Function.Injective (FiniteAvalanches.Sandpile.FiniteWired.directionEdge x) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  fin_cases i <;> fin_cases j <;> cases b <;> cases c
  all_goals first | rfl | skip
  all_goals simp only [FiniteAvalanches.Sandpile.FiniteWired.directionEdge] at h
  all_goals split_ifs at h
  all_goals first
    | exact Sum.noConfusion h
    | exact congrArg (fun e : FiniteAvalanches.Sandpile.FiniteWired.ExitEdge N => e.val.2)
        (Sum.inr.inj h)
    | have hp := congrArg Subtype.val (Sum.inl.inj h)
      have ha0 := congrArg (fun p : FiniteWired.Active N × FiniteWired.Active N =>
        FiniteWired.site p.1 0) hp
      have ha1 := congrArg (fun p : FiniteWired.Active N × FiniteWired.Active N =>
        FiniteWired.site p.1 1) hp
      have hb0 := congrArg (fun p : FiniteWired.Active N × FiniteWired.Active N =>
        FiniteWired.site p.2 0) hp
      have hb1 := congrArg (fun p : FiniteWired.Active N × FiniteWired.Active N =>
        FiniteWired.site p.2 1) hp
      simp [FiniteWired.site,
        FiniteAvalanches.Sandpile.FiniteWired.activeOfSite, unit] at ha0 ha1 hb0 hb1

/-- Original edge copies incident to an outer active vertex and retained in D.
The set carrier restricts C to the original wired volume. -/
def outerIncidentCopies {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (x : {x : FiniteWired.Active N // FiniteWired.site x ∉ C.val}) : Finset (FiniteWired.Edge N) :=
  (outerDirections C.val (FiniteWired.site x.val)).image
    (FiniteWired.directionEdge x.val)

theorem card_outer_incident_copies {N : ℕ}
    {o : FiniteWired.Active N} (C : ComponentShape o)
    (x : {x : FiniteWired.Active N // FiniteWired.site x ∉ C.val}) :
    (outerIncidentCopies C x).card = 4 - degree C.val (FiniteWired.site x.val) := by
  rw [outerIncidentCopies, Finset.card_image_of_injective _ (direction_edge_injective x.val)]
  exact card_outer_directions C.val (FiniteWired.site x.val)

/-- Internal original copies incident to a C-vertex; source edges remain present. -/
def innerIncidentCopies {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (x : {x : FiniteWired.Active N // FiniteWired.site x ∈ C.val}) : Finset (FiniteWired.Edge N) :=
  (innerDirections C.val (FiniteWired.site x.val)).image
    (FiniteWired.directionEdge x.val)

theorem card_inner_incident_copies {N : ℕ}
    {o : FiniteWired.Active N} (C : ComponentShape o)
    (x : {x : FiniteWired.Active N // FiniteWired.site x ∈ C.val}) :
    (innerIncidentCopies C x).card = degree C.val (FiniteWired.site x.val) := by
  rw [innerIncidentCopies, Finset.card_image_of_injective _ (direction_edge_injective x.val)]
  exact (degree_eq_card_inner_directions C.val (FiniteWired.site x.val)).symm

def outsideVertex {N : ℕ} (C : Finset Site2) : FiniteWired.Vertex N → Prop
  | none => True
  | some x => FiniteWired.site x ∉ C

def insideVertex {N : ℕ} (C : Finset Site2) : FiniteWired.Vertex N → Prop
  | none => False
  | some x => FiniteWired.site x ∈ C

theorem outer_direction_edge_endpoints {N : ℕ} {o : FiniteWired.Active N}
    {C : ComponentShape o} {x : FiniteWired.Active N}
    (hx : FiniteWired.site x ∉ C.val) (d : FiniteWired.Direction)
    (hd : FiniteWired.site x + FiniteWired.step d ∉ C.val) :
    outsideVertex C.val (FiniteWired.endpoints (FiniteWired.directionEdge x d)).1 ∧
      outsideVertex C.val (FiniteWired.endpoints (FiniteWired.directionEdge x d)).2 := by
  rcases d with ⟨i, b⟩
  cases b
  all_goals simp only [FiniteWired.step, Bool.false_eq_true, if_false, if_true,
    ← sub_eq_add_neg] at hd
  all_goals simp only [FiniteWired.directionEdge]
  all_goals split_ifs
  all_goals simp only [FiniteWired.endpoints, outsideVertex]
  all_goals first | exact ⟨hd, hx⟩ | exact ⟨hx, hd⟩ | exact ⟨hx, True.intro⟩

theorem inner_direction_edge_endpoints {N : ℕ} {C : Finset Site2}
    (hC : C ⊆ boxSites N) {x : FiniteWired.Active N}
    (hx : FiniteWired.site x ∈ C) (d : FiniteWired.Direction)
    (hd : FiniteWired.site x + FiniteWired.step d ∈ C) :
    insideVertex C (FiniteWired.endpoints (FiniteWired.directionEdge x d)).1 ∧
      insideVertex C (FiniteWired.endpoints (FiniteWired.directionEdge x d)).2 := by
  have hb : FiniteWired.inBox N
      (FiniteWired.site x + FiniteWired.step d) := (mem_box_sites N _).mp (hC hd)
  rcases d with ⟨i, b⟩
  cases b
  all_goals simp only [FiniteWired.step, Bool.false_eq_true, if_false, if_true,
    ← sub_eq_add_neg] at hd hb
  all_goals simp only [FiniteWired.directionEdge, dif_pos hb, FiniteWired.endpoints, insideVertex]
  all_goals first | exact ⟨hd, hx⟩ | exact ⟨hx, hd⟩

end
end FiniteAvalanches.Sandpile.Components
