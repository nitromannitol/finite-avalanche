import FiniteAvalanches.Wilson.Lattice.LocalComparison.BoxVertices

set_option autoImplicit false
namespace LocalBoxContraction
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical
noncomputable section

/-- The original unoriented physical edge represented by a positive-coordinate ID. -/
def idEdge (e : OriginalCopy) : Sym2 (Site 2) := s(originalA e, originalB e)

theorem idEdge_injective : Function.Injective idEdge := by
  intro e f h
  rcases Sym2.eq_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · change e.1 = f.1 at ha
    change e.1 + unit e.2 = f.1 + unit f.2 at hb
    rw [ha] at hb
    have hu : unit e.2 = unit f.2 := add_left_cancel hb
    have hi : e.2 = f.2 := congrArg Prod.fst
      (FiniteWired.step_injective (a₁ := (e.2,true)) (a₂ := (f.2,true)) hu)
    exact Prod.ext ha hi
  · have ha' := congrFun ha e.2
    have hb' := congrFun hb e.2
    rcases e with ⟨x,i⟩
    rcases f with ⟨y,j⟩
    fin_cases i <;> fin_cases j <;> simp [originalA,originalB,unit] at ha' hb' <;> omega

theorem interior_axis_existsUnique {N : ℕ} (e : FiniteWired.InteriorEdge N) :
    ∃! i : Fin 2, FiniteWired.site e.val.2 = FiniteWired.site e.val.1 + unit i := by
  obtain ⟨i,hi⟩ := e.property
  refine ⟨i,hi,?_⟩
  intro j hj
  have hs : FiniteWired.step (j,true) = FiniteWired.step (i,true) :=
    add_left_cancel (hj.symm.trans hi)
  exact congrArg Prod.fst (FiniteWired.step_injective hs)

def boxID {N : ℕ} : FiniteWired.Edge N → OriginalCopy
  | .inl e => (FiniteWired.site e.val.1, Classical.choose (interior_axis_existsUnique e))
  | .inr e => incidentID (FiniteWired.site e.val.1) e.val.2

theorem boxID_physical {N : ℕ} (e : FiniteWired.Edge N) :
    idEdge (boxID e) = (TreeMeasurability11.originalCopyEdge e).val := by
  cases e with
  | inl e =>
    change s(FiniteWired.site e.val.1,
      FiniteWired.site e.val.1 + unit (Classical.choose (interior_axis_existsUnique e))) =
      s(FiniteWired.site e.val.1, FiniteWired.site e.val.2)
    rw [← (Classical.choose_spec (interior_axis_existsUnique e)).1]
  | inr e =>
    rcases e with ⟨⟨x,⟨i,b⟩⟩,he⟩
    cases b
    · change s(FiniteWired.site x - unit i, FiniteWired.site x - unit i + unit i) =
        s(FiniteWired.site x, FiniteWired.site x + -unit i)
      rw [sub_add_cancel, ← sub_eq_add_neg]
      exact Sym2.eq_swap
    · rfl

/-- The original physical edge characterizes the positive ID uniquely. -/
theorem boxID_unique {N : ℕ} (e : FiniteWired.Edge N) :
    ∃! r : OriginalCopy, idEdge r = (TreeMeasurability11.originalCopyEdge e).val :=
  ⟨boxID e, boxID_physical e, fun _ hr => idEdge_injective (hr.trans (boxID_physical e).symm)⟩

theorem boxID_injective (N : ℕ) : Function.Injective (@boxID N) := by
  intro e f h
  apply WiredBoxCopies.originalCopyEdge_injective N
  apply Subtype.ext
  rw [← boxID_physical e, ← boxID_physical f, h]

theorem boxID_direction {N : ℕ} (x : FiniteWired.Active N) (d : FiniteWired.Direction) :
    boxID (FiniteWired.directionEdge x d) = incidentID (FiniteWired.site x) d := by
  apply idEdge_injective
  rw [boxID_physical, WiredBoxCopies.originalCopyEdge_direction]
  rcases d with ⟨i,b⟩
  cases b
  · change s(FiniteWired.site x, FiniteWired.site x + -unit i) =
      s(FiniteWired.site x - unit i, FiniteWired.site x - unit i + unit i)
    rw [sub_add_cancel, ← sub_eq_add_neg]
    exact Sym2.eq_swap
  · rfl

/-- Endpoint accounting includes the physical endpoint hidden by every wired sink copy. -/
theorem boxID_endpoints (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (e : FiniteWired.Edge N) :
    (vertexMap D P N ((WiredTrees.graph N).left e) = project D P (originalA (boxID e)) ∧
      vertexMap D P N ((WiredTrees.graph N).right e) = project D P (originalB (boxID e))) ∨
    (vertexMap D P N ((WiredTrees.graph N).left e) = project D P (originalB (boxID e)) ∧
      vertexMap D P N ((WiredTrees.graph N).right e) = project D P (originalA (boxID e))) := by
  cases e with
  | inl e =>
    refine Or.inl ⟨rfl, ?_⟩
    exact congrArg (project D P) ((Classical.choose_spec (interior_axis_existsUnique e)).1)
  | inr e =>
    have hout : FiniteWired.site e.val.1 + FiniteWired.step e.val.2 ∉ D :=
      fun hd => e.property (hDbox _ hd)
    have hp := (project_eq_alpha_iff D P _).mpr hout
    rcases e with ⟨⟨x,⟨i,b⟩⟩,he⟩
    cases b
    · refine Or.inr ⟨?_, ?_⟩
      · change project D P (FiniteWired.site x) =
          project D P (FiniteWired.site x - unit i + unit i)
        rw [sub_add_cancel]
      · exact hp.symm
    · exact Or.inl ⟨rfl, hp.symm⟩

/-- Every original copy incident to D has a unique wired representative, even at the box boundary. -/
theorem boxID_covers_domain (D : Finset (Site 2)) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (e : OriginalCopy)
    (he : e ∈ domainCopies D) : ∃ f : FiniteWired.Edge N, boxID f = e := by
  rcases (mem_domainCopies D e).mp he with ha | hb
  · refine ⟨FiniteWired.directionEdge (FiniteWired.activeOfSite N (originalA e) (hDbox _ ha))
      (e.2,true), ?_⟩
    rw [boxID_direction]
    rfl
  · refine ⟨FiniteWired.directionEdge (FiniteWired.activeOfSite N (originalB e) (hDbox _ hb))
      (e.2,false), ?_⟩
    rw [boxID_direction]
    rcases e with ⟨x,i⟩
    simp [incidentID, originalB, FiniteWired.site_activeOfSite]

end
end LocalBoxContraction
