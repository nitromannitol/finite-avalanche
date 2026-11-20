import FiniteAvalanches.Wilson.Lattice.WiredDualFaceWordCoupling

/-! Face-square incident and direction explorations stopped at the inner boundary. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- An interior face label is also a vertex of the centered box. -/
def wiredDualFaceInteriorVertex (B : ℕ) (v : WiredDualFace (B + 1))
    (hv : FiniteWired.inBox B (wiredDualFaceSite v)) : FiniteWired.Active (B + 1) :=
  FiniteWired.activeOfSite (B + 1) (wiredDualFaceSite v) (by
    intro i
    have hi := hv i
    constructor <;> omega)

/-- The centered-box vertex constructed from an interior face has the same label. -/
theorem site_wiredDualFaceInteriorVertex (B : ℕ) (v : WiredDualFace (B + 1))
    (hv : FiniteWired.inBox B (wiredDualFaceSite v)) :
    FiniteWired.site (wiredDualFaceInteriorVertex B v hv) = wiredDualFaceSite v := rfl

/-- The interior face is recovered by including its centered-box vertex. -/
theorem wiredDualFaceInnerVertex_interiorVertex (B : ℕ) (v : WiredDualFace (B + 1))
    (hv : FiniteWired.inBox B (wiredDualFaceSite v)) :
    wiredDualFaceInnerVertex (B + 1) (wiredDualFaceInteriorVertex B v hv) = v := by
  apply wiredDualFaceSite_injective (B + 1)
  rfl

/-- Restrict face direction stacks to centered interior vertices. -/
def wiredDualFaceInteriorProjection (B : ℕ)
    (σ : WiredDualFace (B + 1) × ℕ → FiniteWired.Direction) :
    FreeInterior B × ℕ → FiniteWired.Direction :=
  fun p => σ (wiredDualFaceInnerVertex (B + 1) p.1.val, p.2)

/-- Extend centered interior direction stacks by a fixed boundary direction. -/
def padWiredDualFaceInteriorStacks (B : ℕ)
    (σ : FreeInterior B × ℕ → FiniteWired.Direction) :
    WiredDualFace (B + 1) × ℕ → FiniteWired.Direction :=
  fun p => if h : FiniteWired.inBox B (wiredDualFaceSite p.1) then
    σ (⟨wiredDualFaceInteriorVertex B p.1 h, by
      rw [site_wiredDualFaceInteriorVertex]
      exact h⟩, p.2)
  else (0, false)

/-- Restriction of face direction stacks preserves their independent law. -/
theorem directionStackLaw_map_wiredDualFaceInteriorProjection (B : ℕ) :
    (directionStackLaw (WiredDualFace (B + 1))).map (wiredDualFaceInteriorProjection B) =
      directionStackLaw (FreeInterior B) := by
  let f : FreeInterior B × ℕ → WiredDualFace (B + 1) × ℕ :=
    fun p => (wiredDualFaceInnerVertex (B + 1) p.1.val, p.2)
  have hf : Function.Injective f := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    have he : (wiredDualFaceInnerVertex (B + 1) x.val, i) =
        (wiredDualFaceInnerVertex (B + 1) y.val, j) := h
    cases Prod.mk.inj he with
    | intro hxy hij =>
      exact Prod.ext (Subtype.ext (wiredDualFaceInnerVertex_injective (B + 1) hxy)) hij
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ => directionLaw) hf

/-- Padding interior face stacks is measurable. -/
theorem measurable_padWiredDualFaceInteriorStacks (B : ℕ) :
    Measurable (padWiredDualFaceInteriorStacks B) := by
  apply measurable_pi_iff.mpr
  rintro ⟨v, i⟩
  by_cases hv : FiniteWired.inBox B (wiredDualFaceSite v)
  · simp only [padWiredDualFaceInteriorStacks, dif_pos hv]
    exact measurable_pi_apply _
  · simp only [padWiredDualFaceInteriorStacks, dif_neg hv]
    exact measurable_const

/-- Incident-copy and padded-direction explorations agree when all outer
face-square vertices are roots. -/
theorem wiredDualFaceIncidentStackExplore_eq_paddedDirections (B : ℕ)
    (σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1)
    (R : Set (WiredDualFace (B + 1)))
    (hR : ∀ v, ¬FiniteWired.inBox B (wiredDualFaceSite v) → v ∈ R)
    (k : Cursor (WiredDualFace (B + 1))) (L : List (WiredDualFace (B + 1))) :
    stackExplore (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i)) R k L =
      stackExplore (wiredDualFaceDirectionHead (B + 1))
        (fun v i => padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) (v, i)) R k L := by
  apply stackExplore_eq_of_matching_successors
  intro v hv i
  have hin : FiniteWired.inBox B (wiredDualFaceSite v) := by
    by_contra hn
    exact hv (hR v hn)
  let x := wiredDualFaceInteriorVertex B v hin
  have hx : FiniteWired.inBox B (FiniteWired.site x) := by
    rw [site_wiredDualFaceInteriorVertex]
    exact hin
  have he : wiredDualFaceInnerVertex (B + 1) x = v :=
    wiredDualFaceInnerVertex_interiorVertex B v hin
  simp only [padWiredDualFaceInteriorStacks, dif_pos hin, wiredDualFaceInteriorDirectionStacks]
  change incidentCopyHead (wiredDualFaceGraph (B + 1)) v (σ (v, i)) =
    wiredDualFaceDirectionHead (B + 1) v
      ((wiredDualFaceInteriorDirectionEquiv B x hx).symm
        (σ (wiredDualFaceInnerVertex (B + 1) x, i)))
  have h := wiredDualFaceDirectionHead_eq_incident B x hx
    ((wiredDualFaceInteriorDirectionEquiv B x hx).symm
      (σ (wiredDualFaceInnerVertex (B + 1) x, i)))
  have hm := congrArg (fun z => incidentCopyHead (wiredDualFaceGraph (B + 1)) z (σ (z, i))) he.symm
  calc
    incidentCopyHead (wiredDualFaceGraph (B + 1)) v (σ (v, i)) = _ := hm
    _ = wiredDualFaceDirectionHead (B + 1) (wiredDualFaceInnerVertex (B + 1) x)
        ((wiredDualFaceInteriorDirectionEquiv B x hx).symm
          (σ (wiredDualFaceInnerVertex (B + 1) x, i))) := by
      simpa only [Equiv.apply_symm_apply] using h
    _ = _ := congrArg (fun z => wiredDualFaceDirectionHead (B + 1) z
      ((wiredDualFaceInteriorDirectionEquiv B x hx).symm
        (σ (wiredDualFaceInnerVertex (B + 1) x, i)))) he

/-- A direction exploration stopped at the inner boundary ignores boundary instructions. -/
theorem wiredDualFaceDirectionStackExplore_eq_pad (B : ℕ)
    (σ : WiredDualFace (B + 1) × ℕ → FiniteWired.Direction)
    (R : Set (WiredDualFace (B + 1)))
    (hR : ∀ v, ¬FiniteWired.inBox B (wiredDualFaceSite v) → v ∈ R)
    (k : Cursor (WiredDualFace (B + 1))) (L : List (WiredDualFace (B + 1))) :
    stackExplore (wiredDualFaceDirectionHead (B + 1)) (fun v i => σ (v, i)) R k L =
      stackExplore (wiredDualFaceDirectionHead (B + 1))
        (fun v i => padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorProjection B σ) (v, i)) R k L := by
  apply stackExplore_eq_of_matching_successors
  intro v hv i
  have hin : FiniteWired.inBox B (wiredDualFaceSite v) := by
    by_contra hn
    exact hv (hR v hn)
  simp only [padWiredDualFaceInteriorStacks, dif_pos hin, wiredDualFaceInteriorProjection,
    wiredDualFaceInnerVertex_interiorVertex]

/-- Measurable events of stopped face explorations have the direction-stack law. -/
theorem variableStackLaw_wiredDualFaceStoppedExplore_event_eq (B : ℕ)
    (R : Set (WiredDualFace (B + 1)))
    (hR : ∀ v, ¬FiniteWired.inBox B (wiredDualFaceSite v) → v ∈ R)
    (k : Cursor (WiredDualFace (B + 1))) (L : List (WiredDualFace (B + 1)))
    (P : Option (Set (WiredDualFace (B + 1)) × Cursor (WiredDualFace (B + 1))) → Prop)
    (hP : MeasurableSet {σ : WiredDualFace (B + 1) × ℕ → FiniteWired.Direction |
      P (stackExplore (wiredDualFaceDirectionHead (B + 1)) (fun v i => σ (v, i)) R k L)}) :
    variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
      {σ | P (stackExplore (incidentCopyHead (wiredDualFaceGraph (B + 1)))
        (fun v i => σ (v, i)) R k L)} =
    directionStackLaw (WiredDualFace (B + 1))
      {σ | P (stackExplore (wiredDualFaceDirectionHead (B + 1)) (fun v i => σ (v, i)) R k L)} := by
  let E : Set (WiredDualFace (B + 1) × ℕ → FiniteWired.Direction) :=
    {σ | P (stackExplore (wiredDualFaceDirectionHead (B + 1)) (fun v i => σ (v, i)) R k L)}
  let A := (padWiredDualFaceInteriorStacks B) ⁻¹' E
  have hA : MeasurableSet A := hP.preimage (measurable_padWiredDualFaceInteriorStacks B)
  have he := congrArg (fun μ : Measure (FreeInterior B × ℕ → FiniteWired.Direction) => μ A)
    (variableStackLaw_map_wiredDualFaceInteriorDirections B)
  rw [Measure.map_apply (by
      apply measurable_pi_iff.mpr
      intro p
      exact (measurable_of_finite (wiredDualFaceInteriorDirectionEquiv B p.1.val p.1.property).symm).comp
        (measurable_pi_apply (wiredDualFaceInnerVertex (B + 1) p.1.val, p.2))) hA] at he
  have hd := congrArg (fun μ : Measure (FreeInterior B × ℕ → FiniteWired.Direction) => μ A)
    (directionStackLaw_map_wiredDualFaceInteriorProjection B)
  rw [Measure.map_apply (by
      apply measurable_pi_iff.mpr
      intro p
      exact measurable_pi_apply (wiredDualFaceInnerVertex (B + 1) p.1.val, p.2)) hA] at hd
  have hset : (wiredDualFaceInteriorProjection B) ⁻¹' A = E := by
    ext σ
    change P (stackExplore (wiredDualFaceDirectionHead (B + 1))
      (fun v i => padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorProjection B σ) (v, i)) R k L) ↔
      P (stackExplore (wiredDualFaceDirectionHead (B + 1)) (fun v i => σ (v, i)) R k L)
    rw [← wiredDualFaceDirectionStackExplore_eq_pad B σ R hR k L]
  rw [hset] at hd
  have hset' : {σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1 |
      P (stackExplore (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i)) R k L)} =
      {σ | padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) ∈ E} := by
    ext σ
    change P (stackExplore (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i)) R k L) ↔
      P (stackExplore (wiredDualFaceDirectionHead (B + 1))
        (fun v i => padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) (v, i)) R k L)
    rw [wiredDualFaceIncidentStackExplore_eq_paddedDirections B σ R hR k L]
  rw [hset']
  exact he.trans hd.symm

end
end FiniteAvalanches.Wilson.Lattice
