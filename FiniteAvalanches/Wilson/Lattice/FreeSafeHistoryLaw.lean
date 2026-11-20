import FiniteAvalanches.Wilson.Lattice.FreeOriginAvoidBoundary
import FiniteAvalanches.Wilson.Lattice.OriginSafeHistoryLaw

/-! Free-box safe Wilson histories have probabilities tending to one. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Finite row histories that terminate and avoid the outer free-box boundary. -/
def freeSafeRowEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) : Set (ℕ → WalkDriver) :=
  {rows | ∃ N, BranchHistory.HitsBefore N n
      (rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
        (freeOriginAndBoundary B) k N rows n) ∧
    BranchHistory.EndsAvoid (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
      (freeOuterBoundary B) n
      (rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
        (freeOriginAndBoundary B) k N rows n)}

/-- The free-box safe row event is measurable. -/
theorem measurableSet_freeSafeRowEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) :
    MeasurableSet (freeSafeRowEvent B x k n) := by
  have he : freeSafeRowEvent B x k n = ⋃ N : ℕ,
      {rows | BranchHistory.HitsBefore N n
          (rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
            (freeOriginAndBoundary B) k N rows n) ∧
        BranchHistory.EndsAvoid (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
          (freeOuterBoundary B) n
          (rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
            (freeOriginAndBoundary B) k N rows n)} := by
    ext rows
    simp only [freeSafeRowEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  apply measurableSet_of_countable_fibers
    (fun rows => rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
      (freeOriginAndBoundary B) k N rows n)
    (fun a => measurableSet_rowBranchHistory_eq (freeDirectionHead (B + 1))
      (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k N n
      (fun i (rows : ℕ → WalkDriver) => rows i) (fun i => measurable_pi_apply i) a)
    (fun a => BranchHistory.HitsBefore N n a ∧ BranchHistory.EndsAvoid (freeDirectionHead (B + 1))
      (fun i => freeSite (B + 1) (x i)) (freeOuterBoundary B) n a)

/-- Safe finite free-box row histories occur eventually almost surely. -/
theorem wilsonRows_ae_eventually_freeSafeRowEvent (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1))) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∀ᶠ B : ℕ in atTop, rows ∈ freeSafeRowEvent B x (kb B) n := by
  filter_upwards [wilsonRows_ae_eventually_freeOrigin_history_eq x ka kb n] with rows hrows
  obtain ⟨T, hT, heq⟩ := hrows
  filter_upwards [heq, eventually_walkSegments_inBox x rows n T] with B hEq hbox
  have hconf : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x {0} ka T rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j) := by
    intro i hi j hj
    exact hbox i hi j (lt_of_le_of_lt hj (hT i hi))
  have hh := (rowBranchHistory_hitsBefore_iff latticeDirectionHead x {0} ka T n rows).mpr hT
  refine ⟨T, ?_, freeOrigin_history_endsAvoid_of_confined B T x ka (kb B) rows n hEq hT hconf⟩
  rw [hEq]
  exact hh

/-- The probabilities of safe free-box row histories tend to one. -/
theorem freeSafeRowEvent_tendsto_one (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1))) (n : ℕ) :
    Tendsto (fun B => wilsonRows (freeSafeRowEvent B x (kb B) n)) atTop (nhds 1) := by
  have hpoint : ∀ᵐ rows ∂wilsonRows, ∀ᶠ B : ℕ in atTop,
      rows ∈ freeSafeRowEvent B x (kb B) n ↔ rows ∈ (Set.univ : Set (ℕ → WalkDriver)) := by
    filter_upwards [wilsonRows_ae_eventually_freeSafeRowEvent x ka kb n] with rows hrows
    filter_upwards [hrows] with B hB
    simp only [Set.mem_univ, iff_true]
    exact hB
  have ht := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (μ := wilsonRows) (A := Set.univ) (As := fun B => freeSafeRowEvent B x (kb B) n)
    MeasurableSet.univ (fun B => measurableSet_freeSafeRowEvent B x (kb B) n) hpoint
  simpa only [measure_univ] using ht

/-- The corresponding safe event for chronological direction stacks. -/
def freeSafeStackHistoryEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) :
    Set (FiniteWired.Active (B + 1) × ℕ → FiniteWired.Direction) :=
  {σ | ∃ N, BranchHistory.HitsBefore N n
      (boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
        (freeOriginAndBoundary B) k N σ n) ∧
    BranchHistory.EndsAvoid (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
      (freeOuterBoundary B) n
      (boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
        (freeOriginAndBoundary B) k N σ n)}

/-- Direction stacks and independent rows give equal safe-history probabilities. -/
theorem freeSafeStackHistoryEvent_measure (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) :
    directionStackLaw (FiniteWired.Active (B + 1)) (freeSafeStackHistoryEvent B x k n) =
      wilsonRows (freeSafeRowEvent B x k n) :=
  directionStackLaw_completedBranchHistory_eq_wilsonRows (freeDirectionHead (B + 1))
    (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k n
    (BranchHistory.EndsAvoid (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
      (freeOuterBoundary B) n)

end
end FiniteAvalanches.Wilson.Lattice
