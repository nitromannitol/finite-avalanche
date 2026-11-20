import FiniteAvalanches.Wilson.Lattice.FreeSafeIncidentLaw

/-! Completed free-box branch histories have the independent-row law. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqInteriorEdgeFreeCompletedHistoryLaw (N : ℕ) :
    DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- A completed free-box direction history satisfying a predicate. -/
def freeCompletedStackHistoryEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) (P : BranchHistory n → Prop) :
    Set (FiniteWired.Active (B + 1) × ℕ → FiniteWired.Direction) :=
  {σ | ∃ N, BranchHistory.HitsBefore N n
      (boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
        (freeOriginAndBoundary B) k N σ n) ∧
    P (boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
      (freeOriginAndBoundary B) k N σ n)}

/-- Completed free-box stack-history events are measurable. -/
theorem measurableSet_freeCompletedStackHistoryEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) (P : BranchHistory n → Prop) :
    MeasurableSet (freeCompletedStackHistoryEvent B x k n P) := by
  have he : freeCompletedStackHistoryEvent B x k n P = ⋃ N : ℕ,
      {σ | BranchHistory.HitsBefore N n
          (boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
            (freeOriginAndBoundary B) k N σ n) ∧
        P (boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
          (freeOriginAndBoundary B) k N σ n)} := by
    ext σ
    simp only [freeCompletedStackHistoryEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  apply measurableSet_of_countable_fibers
    (fun σ => boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
      (freeOriginAndBoundary B) k N σ n)
    (measurableSet_boundedBranchHistory_eq (freeDirectionHead (B + 1))
      (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k N n)
    (fun a => BranchHistory.HitsBefore N n a ∧ P a)

/-- A completed history is unchanged if only boundary-root stacks are modified. -/
theorem freeCompletedStackHistoryEvent_of_agree_interior (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1)))
    (hk : ∀ v ∈ freeOuterBoundary B, k v = 0) (n : ℕ) (P : BranchHistory n → Prop)
    (σ τ : FiniteWired.Active (B + 1) × ℕ → FiniteWired.Direction)
    (hactive : ∀ v, FiniteWired.inBox B (FiniteWired.site v) → ∀ i, τ (v, i) = σ (v, i))
    (hσ : σ ∈ freeCompletedStackHistoryEvent B x k n P) :
    τ ∈ freeCompletedStackHistoryEvent B x k n P := by
  obtain ⟨N, hhit, hP⟩ := hσ
  let h := boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
    (freeOriginAndBoundary B) k N σ n
  have hh := (boundedBranchHistory_hitsBefore_iff (freeDirectionHead (B + 1))
    (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k N n σ).mp hhit
  have hboundary (v : FiniteWired.Active (B + 1)) (hv : v ∈ freeOuterBoundary B) :
      branchHistoryCursor (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i)) k n h v = 0 := by
    rw [branchHistoryCursor_eq_at_initial_root (freeDirectionHead (B + 1))
      (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k N n σ hh v
      (Set.mem_union_right _ hv), hk v hv]
  have hagree : ∀ v i, i < branchHistoryCursor (freeDirectionHead (B + 1))
      (fun i => freeSite (B + 1) (x i)) k n h v → τ (v, i) = σ (v, i) := by
    intro v i hi
    by_cases hv : FiniteWired.inBox B (FiniteWired.site v)
    · exact hactive v hv i
    · have hv' : v ∈ freeOuterBoundary B := hv
      rw [hboundary v hv'] at hi
      omega
  have he := boundedBranchHistory_stable (freeDirectionHead (B + 1))
    (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k N n σ τ hagree
  refine ⟨N, ?_, ?_⟩ <;> rw [he]
  · exact hhit
  · exact hP

/-- Padding boundary stacks does not change a completed-history event. -/
theorem freeCompletedStackHistoryEvent_pad_iff (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1)))
    (hk : ∀ v ∈ freeOuterBoundary B, k v = 0) (n : ℕ) (P : BranchHistory n → Prop)
    (σ : FiniteWired.Active (B + 1) × ℕ → FiniteWired.Direction) :
    padFreeInteriorStacks B (freeInteriorProjection B σ) ∈ freeCompletedStackHistoryEvent B x k n P ↔
      σ ∈ freeCompletedStackHistoryEvent B x k n P := by
  constructor
  · intro h
    apply freeCompletedStackHistoryEvent_of_agree_interior B x k hk n P
      (padFreeInteriorStacks B (freeInteriorProjection B σ)) σ ?_ h
    intro v hv i
    simp only [padFreeInteriorStacks, dif_pos hv, freeInteriorProjection]
  · intro h
    apply freeCompletedStackHistoryEvent_of_agree_interior B x k hk n P σ
      (padFreeInteriorStacks B (freeInteriorProjection B σ)) ?_ h
    intro v hv i
    simp only [padFreeInteriorStacks, dif_pos hv, freeInteriorProjection]

/-- Free incident stacks and independent rows give the same completed-history law. -/
theorem variableStackLaw_freeCompletedHistory_eq_wilsonRows (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1)))
    (hk : ∀ v ∈ freeOuterBoundary B, k v = 0) (n : ℕ) (P : BranchHistory n → Prop) :
    variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
      {σ | padFreeInteriorStacks B (freeInteriorDirectionStacks B σ) ∈
        freeCompletedStackHistoryEvent B x k n P} =
      wilsonRows {rows | ∃ N, BranchHistory.HitsBefore N n
          (rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
            (freeOriginAndBoundary B) k N rows n) ∧
        P (rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
          (freeOriginAndBoundary B) k N rows n)} := by
  rw [variableStackLaw_freeInterior_event_eq B (freeCompletedStackHistoryEvent B x k n P)
    (measurableSet_freeCompletedStackHistoryEvent B x k n P)
    (freeCompletedStackHistoryEvent_pad_iff B x k hk n P)]
  exact directionStackLaw_completedBranchHistory_eq_wilsonRows (freeDirectionHead (B + 1))
    (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k n P

end
end FiniteAvalanches.Wilson.Lattice
