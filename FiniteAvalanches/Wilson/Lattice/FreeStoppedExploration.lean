import FiniteAvalanches.Wilson.Lattice.FreeInteriorCopies
import FiniteAvalanches.Wilson.CyclePopping.StackAlphabetCoupling

/-! Free-box explorations stopped on the boundary use ordinary direction stacks. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqInteriorEdgeFreeStoppedExploration (N : ℕ) : DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- A lattice direction followed inside a box, with a fixed value at a would-be exit. -/
def freeDirectionHead (B : ℕ) (x : FiniteWired.Active B) (d : FiniteWired.Direction) :
    FiniteWired.Active B :=
  if h : FiniteWired.inBox B (FiniteWired.site x + FiniteWired.step d) then
    FiniteWired.activeOfSite B (FiniteWired.site x + FiniteWired.step d) h else x

/-- At inner vertices, the free direction successor is the incident-copy successor. -/
theorem freeInteriorDirection_head_eq (N : ℕ) (x : FiniteWired.Active (N + 1))
    (hx : FiniteWired.inBox N (FiniteWired.site x)) (d : FiniteWired.Direction) :
    incidentCopyHead (freeBoxGraph (N + 1)) x (freeInteriorDirectionEquiv N x hx d) =
      freeDirectionHead (N + 1) x d := by
  have hbox := inBox_succ_of_step N (FiniteWired.site x) hx d
  have h := freeInteriorDirection_head N x hx d
  simp only [wiredHead, wiredSite, dif_pos hbox] at h
  simp only [freeDirectionHead, dif_pos hbox]
  exact Option.some.inj h

/-- Restrict full direction stacks to the inner vertices. -/
def freeInteriorProjection (N : ℕ)
    (σ : FiniteWired.Active (N + 1) × ℕ → FiniteWired.Direction) :
    FreeInterior N × ℕ → FiniteWired.Direction := fun p => σ (p.1.val, p.2)

/-- Extend inner stacks by a fixed direction on the outer boundary. -/
def padFreeInteriorStacks (N : ℕ) (σ : FreeInterior N × ℕ → FiniteWired.Direction) :
    FiniteWired.Active (N + 1) × ℕ → FiniteWired.Direction :=
  fun p => if h : FiniteWired.inBox N (FiniteWired.site p.1) then σ (⟨p.1, h⟩, p.2)
    else (0, false)

/-- The restriction of iid direction stacks to inner vertices remains iid. -/
theorem directionStackLaw_map_freeInteriorProjection (N : ℕ) :
    (directionStackLaw (FiniteWired.Active (N + 1))).map (freeInteriorProjection N) =
      directionStackLaw (FreeInterior N) := by
  let f : FreeInterior N × ℕ → FiniteWired.Active (N + 1) × ℕ := fun p => (p.1.val, p.2)
  have hf : Function.Injective f := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    have he : (x.val, i) = (y.val, j) := h
    cases Prod.mk.inj he with
    | intro hxy hij => exact Prod.ext (Subtype.ext hxy) hij
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ => directionLaw) hf

/-- Padding an inner direction stack is measurable. -/
theorem measurable_padFreeInteriorStacks (N : ℕ) : Measurable (padFreeInteriorStacks N) := by
  apply measurable_pi_iff.mpr
  rintro ⟨x, i⟩
  by_cases hx : FiniteWired.inBox N (FiniteWired.site x)
  · simp only [padFreeInteriorStacks, dif_pos hx]
    exact measurable_pi_apply ((⟨x, hx⟩ : FreeInterior N), i)
  · simp only [padFreeInteriorStacks, dif_neg hx]
    exact measurable_const

/-- Free incident and direction explorations agree until the outer boundary. -/
theorem freeIncidentStackExplore_eq_paddedDirections (N : ℕ)
    (σ : (p : FiniteWired.Active (N + 1) × ℕ) → IncidentCopy (freeBoxGraph (N + 1)) p.1)
    (R : Set (FiniteWired.Active (N + 1)))
    (hR : ∀ x, ¬FiniteWired.inBox N (FiniteWired.site x) → x ∈ R)
    (k : Cursor (FiniteWired.Active (N + 1))) (L : List (FiniteWired.Active (N + 1))) :
    stackExplore (incidentCopyHead (freeBoxGraph (N + 1))) (fun v i => σ (v, i)) R k L =
      stackExplore (freeDirectionHead (N + 1))
        (fun v i => padFreeInteriorStacks N (freeInteriorDirectionStacks N σ) (v, i)) R k L := by
  apply stackExplore_eq_of_matching_successors
  intro v hv i
  have hin : FiniteWired.inBox N (FiniteWired.site v) := by
    by_contra hn
    exact hv (hR v hn)
  simp only [padFreeInteriorStacks, dif_pos hin, freeInteriorDirectionStacks]
  have h := freeInteriorDirection_head_eq N v hin
    ((freeInteriorDirectionEquiv N v hin).symm (σ (v, i)))
  simpa only [Equiv.apply_symm_apply] using h

/-- Direction explorations stopped on the outer boundary ignore boundary stacks. -/
theorem freeDirectionStackExplore_eq_pad (N : ℕ)
    (σ : FiniteWired.Active (N + 1) × ℕ → FiniteWired.Direction)
    (R : Set (FiniteWired.Active (N + 1)))
    (hR : ∀ x, ¬FiniteWired.inBox N (FiniteWired.site x) → x ∈ R)
    (k : Cursor (FiniteWired.Active (N + 1))) (L : List (FiniteWired.Active (N + 1))) :
    stackExplore (freeDirectionHead (N + 1)) (fun v i => σ (v, i)) R k L =
      stackExplore (freeDirectionHead (N + 1))
        (fun v i => padFreeInteriorStacks N (freeInteriorProjection N σ) (v, i)) R k L := by
  apply stackExplore_eq_of_matching_successors
  intro v hv i
  have hin : FiniteWired.inBox N (FiniteWired.site v) := by
    by_contra hn
    exact hv (hR v hn)
  simp only [padFreeInteriorStacks, dif_pos hin, freeInteriorProjection]

/-- Measurable events of stopped free-box explorations have the direction-stack law. -/
theorem variableStackLaw_freeStoppedExplore_event_eq (N : ℕ)
    (R : Set (FiniteWired.Active (N + 1)))
    (hR : ∀ x, ¬FiniteWired.inBox N (FiniteWired.site x) → x ∈ R)
    (k : Cursor (FiniteWired.Active (N + 1))) (L : List (FiniteWired.Active (N + 1)))
    (P : Option (Set (FiniteWired.Active (N + 1)) × Cursor (FiniteWired.Active (N + 1))) → Prop)
    (hP : MeasurableSet {σ : FiniteWired.Active (N + 1) × ℕ → FiniteWired.Direction |
      P (stackExplore (freeDirectionHead (N + 1)) (fun v i => σ (v, i)) R k L)}) :
    variableStackLaw (IncidentCopy (freeBoxGraph (N + 1)))
      {σ | P (stackExplore (incidentCopyHead (freeBoxGraph (N + 1)))
        (fun v i => σ (v, i)) R k L)} =
    directionStackLaw (FiniteWired.Active (N + 1))
      {σ | P (stackExplore (freeDirectionHead (N + 1)) (fun v i => σ (v, i)) R k L)} := by
  let E : Set (FiniteWired.Active (N + 1) × ℕ → FiniteWired.Direction) :=
    {σ | P (stackExplore (freeDirectionHead (N + 1)) (fun v i => σ (v, i)) R k L)}
  let A := (padFreeInteriorStacks N) ⁻¹' E
  have hA : MeasurableSet A := hP.preimage (measurable_padFreeInteriorStacks N)
  have he := congrArg (fun μ : Measure (FreeInterior N × ℕ → FiniteWired.Direction) => μ A)
    (variableStackLaw_map_freeInteriorDirections N)
  rw [Measure.map_apply (by
      apply measurable_pi_iff.mpr
      intro p
      exact (measurable_of_finite (freeInteriorDirectionEquiv N p.1.val p.1.property).symm).comp
        (measurable_pi_apply (p.1.val, p.2))) hA] at he
  have hd := congrArg (fun μ : Measure (FreeInterior N × ℕ → FiniteWired.Direction) => μ A)
    (directionStackLaw_map_freeInteriorProjection N)
  rw [Measure.map_apply (by
      apply measurable_pi_iff.mpr
      intro p
      exact measurable_pi_apply (p.1.val, p.2)) hA] at hd
  have hset : (freeInteriorProjection N) ⁻¹' A = E := by
    ext σ
    change P (stackExplore (freeDirectionHead (N + 1))
      (fun v i => padFreeInteriorStacks N (freeInteriorProjection N σ) (v, i)) R k L) ↔
      P (stackExplore (freeDirectionHead (N + 1)) (fun v i => σ (v, i)) R k L)
    rw [← freeDirectionStackExplore_eq_pad N σ R hR k L]
  rw [hset] at hd
  have hset' : {σ : (p : FiniteWired.Active (N + 1) × ℕ) → IncidentCopy (freeBoxGraph (N + 1)) p.1 |
      P (stackExplore (incidentCopyHead (freeBoxGraph (N + 1))) (fun v i => σ (v, i)) R k L)} =
      {σ | padFreeInteriorStacks N (freeInteriorDirectionStacks N σ) ∈ E} := by
    ext σ
    change P (stackExplore (incidentCopyHead (freeBoxGraph (N + 1)))
      (fun v i => σ (v, i)) R k L) ↔
      P (stackExplore (freeDirectionHead (N + 1))
        (fun v i => padFreeInteriorStacks N (freeInteriorDirectionStacks N σ) (v, i)) R k L)
    rw [freeIncidentStackExplore_eq_paddedDirections N σ R hR k L]
  rw [hset']
  exact he.trans hd.symm

end
end FiniteAvalanches.Wilson.Lattice
