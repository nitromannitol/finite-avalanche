import FiniteAvalanches.Wilson.Lattice.WiredDualFaceSafeIncident

/-! Completed face-square branch histories have the independent-row law. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqWiredEdgeDualFaceCompletedHistoryLaw (N : ℕ) :
    DecidableEq (FiniteWired.Edge N) := Classical.decEq _

/-- A completed face-square direction history satisfying a predicate. -/
def wiredDualFaceCompletedStackHistoryEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ) (P : BranchHistory n → Prop) :
    Set (WiredDualFace (B + 1) × ℕ → FiniteWired.Direction) :=
  {σ | ∃ N, BranchHistory.HitsBefore N n
      (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
        (wiredDualFaceOriginAndBoundary B) k N σ n) ∧
    P (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
      (wiredDualFaceOriginAndBoundary B) k N σ n)}

/-- Completed face-square stack-history events are measurable. -/
theorem measurableSet_wiredDualFaceCompletedStackHistoryEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ) (P : BranchHistory n → Prop) :
    MeasurableSet (wiredDualFaceCompletedStackHistoryEvent B x k n P) := by
  have he : wiredDualFaceCompletedStackHistoryEvent B x k n P = ⋃ N : ℕ,
      {σ | BranchHistory.HitsBefore N n
          (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
            (wiredDualFaceOriginAndBoundary B) k N σ n) ∧
        P (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
          (wiredDualFaceOriginAndBoundary B) k N σ n)} := by
    ext σ
    simp only [wiredDualFaceCompletedStackHistoryEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  apply measurableSet_of_countable_fibers
    (fun σ => boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
      (wiredDualFaceOriginAndBoundary B) k N σ n)
    (measurableSet_boundedBranchHistory_eq (wiredDualFaceDirectionHead (B + 1))
      (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) (wiredDualFaceOriginAndBoundary B) k N n)
    (fun a => BranchHistory.HitsBefore N n a ∧ P a)

/-- A completed history is unchanged if only boundary-root stacks are modified. -/
theorem wiredDualFaceCompletedStackHistoryEvent_of_agree_interior (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1)))
    (hk : ∀ v ∈ wiredDualFaceOuterBoundary B, k v = 0) (n : ℕ) (P : BranchHistory n → Prop)
    (σ τ : WiredDualFace (B + 1) × ℕ → FiniteWired.Direction)
    (hactive : ∀ v, FiniteWired.inBox B (wiredDualFaceSite v) → ∀ i, τ (v, i) = σ (v, i))
    (hσ : σ ∈ wiredDualFaceCompletedStackHistoryEvent B x k n P) :
    τ ∈ wiredDualFaceCompletedStackHistoryEvent B x k n P := by
  obtain ⟨N, hhit, hP⟩ := hσ
  let h := boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
    (wiredDualFaceOriginAndBoundary B) k N σ n
  have hh := (boundedBranchHistory_hitsBefore_iff (wiredDualFaceDirectionHead (B + 1))
    (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) (wiredDualFaceOriginAndBoundary B) k N n σ).mp hhit
  have hboundary (v : WiredDualFace (B + 1)) (hv : v ∈ wiredDualFaceOuterBoundary B) :
      branchHistoryCursor (wiredDualFaceDirectionHead (B + 1)) (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) k n h v = 0 := by
    rw [branchHistoryCursor_eq_at_initial_root (wiredDualFaceDirectionHead (B + 1))
      (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) (wiredDualFaceOriginAndBoundary B) k N n σ hh v
      (Set.mem_union_right _ hv), hk v hv]
  have hagree : ∀ v i, i < branchHistoryCursor (wiredDualFaceDirectionHead (B + 1))
      (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) k n h v → τ (v, i) = σ (v, i) := by
    intro v i hi
    by_cases hv : FiniteWired.inBox B (wiredDualFaceSite v)
    · exact hactive v hv i
    · have hv' : v ∈ wiredDualFaceOuterBoundary B := hv
      rw [hboundary v hv'] at hi
      omega
  have he := boundedBranchHistory_stable (wiredDualFaceDirectionHead (B + 1))
    (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) (wiredDualFaceOriginAndBoundary B) k N n σ τ hagree
  refine ⟨N, ?_, ?_⟩ <;> rw [he]
  · exact hhit
  · exact hP

/-- Padding boundary stacks does not change a completed-history event. -/
theorem wiredDualFaceCompletedStackHistoryEvent_pad_iff (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1)))
    (hk : ∀ v ∈ wiredDualFaceOuterBoundary B, k v = 0) (n : ℕ) (P : BranchHistory n → Prop)
    (σ : WiredDualFace (B + 1) × ℕ → FiniteWired.Direction) :
    padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorProjection B σ) ∈ wiredDualFaceCompletedStackHistoryEvent B x k n P ↔
      σ ∈ wiredDualFaceCompletedStackHistoryEvent B x k n P := by
  constructor
  · intro h
    apply wiredDualFaceCompletedStackHistoryEvent_of_agree_interior B x k hk n P
      (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorProjection B σ)) σ ?_ h
    intro v hv i
    simp only [padWiredDualFaceInteriorStacks, dif_pos hv, wiredDualFaceInteriorProjection,
      wiredDualFaceInnerVertex_interiorVertex]
  · intro h
    apply wiredDualFaceCompletedStackHistoryEvent_of_agree_interior B x k hk n P σ
      (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorProjection B σ)) ?_ h
    intro v hv i
    simp only [padWiredDualFaceInteriorStacks, dif_pos hv, wiredDualFaceInteriorProjection,
      wiredDualFaceInnerVertex_interiorVertex]

/-- Face incident stacks and independent rows give the same completed-history law. -/
theorem variableStackLaw_wiredDualFaceCompletedHistory_eq_wilsonRows (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1)))
    (hk : ∀ v ∈ wiredDualFaceOuterBoundary B, k v = 0) (n : ℕ) (P : BranchHistory n → Prop) :
    variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
      {σ | padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) ∈
        wiredDualFaceCompletedStackHistoryEvent B x k n P} =
      wilsonRows {rows | ∃ N, BranchHistory.HitsBefore N n
          (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
            (wiredDualFaceOriginAndBoundary B) k N rows n) ∧
        P (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
          (wiredDualFaceOriginAndBoundary B) k N rows n)} := by
  rw [variableStackLaw_wiredDualFaceInterior_event_eq B (wiredDualFaceCompletedStackHistoryEvent B x k n P)
    (measurableSet_wiredDualFaceCompletedStackHistoryEvent B x k n P)
    (wiredDualFaceCompletedStackHistoryEvent_pad_iff B x k hk n P)]
  exact directionStackLaw_completedBranchHistory_eq_wilsonRows (wiredDualFaceDirectionHead (B + 1))
    (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) (wiredDualFaceOriginAndBoundary B) k n P

end
end FiniteAvalanches.Wilson.Lattice
