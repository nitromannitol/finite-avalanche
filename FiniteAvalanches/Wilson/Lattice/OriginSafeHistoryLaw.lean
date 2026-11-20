import FiniteAvalanches.Wilson.Lattice.OriginBranchAvoidsSink

/-! Origin-rooted finite histories avoid the sink with probability tending to one. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- A finite wired row history terminates and all its branch endpoints avoid
the sink. -/
def originSafeRowEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) : Set (ℕ → WalkDriver) :=
  {rows | ∃ N, BranchHistory.HitsBefore N n
      (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
        k N rows n) ∧
    BranchHistory.EndsAvoid (wiredHead B) (fun i => wiredSite B (x i)) {none} n
      (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
        k N rows n)}

/-- Safe finite row histories form a measurable event. -/
theorem measurableSet_originSafeRowEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) : MeasurableSet (originSafeRowEvent B x k n) := by
  have he : originSafeRowEvent B x k n = ⋃ N : ℕ,
      {rows | BranchHistory.HitsBefore N n
          (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
            k N rows n) ∧
        BranchHistory.EndsAvoid (wiredHead B) (fun i => wiredSite B (x i)) {none} n
          (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
            k N rows n)} := by
    ext rows
    simp only [originSafeRowEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  apply measurableSet_of_countable_fibers
    (fun rows => rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i))
      (wiredOriginAndSink B) k N rows n)
    (fun a => measurableSet_rowBranchHistory_eq (wiredHead B) (fun i => wiredSite B (x i))
      (wiredOriginAndSink B) k N n (fun i (rows : ℕ → WalkDriver) => rows i)
      (fun i => measurable_pi_apply i) a)
    (fun a => BranchHistory.HitsBefore N n a ∧
      BranchHistory.EndsAvoid (wiredHead B) (fun i => wiredSite B (x i)) {none} n a)

/-- Safe finite row histories occur eventually almost surely as the wired box grows. -/
theorem wilsonRows_ae_eventually_originSafeRowEvent (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∀ᶠ B : ℕ in atTop, rows ∈ originSafeRowEvent B x (kb B) n := by
  filter_upwards [wilsonRows_origin_ae_finite_branch_horizon x ka n] with rows hrows
  obtain ⟨N, hN⟩ := hrows
  filter_upwards [eventually_walkSegments_inBox x rows n N] with B hbox
  have hconf : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x {0} ka N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j) := by
    intro i hi j hj
    exact hbox i hi j (lt_of_le_of_lt hj (hN i hi))
  have he := (rowBranchHistory_wired_eq_of_confined B N x (wiredOriginAndSink B) {0}
    (kb B) ka rows n (wiredOriginAndSink_wiredSite_iff B) hN hconf).1
  have hh := (rowBranchHistory_hitsBefore_iff latticeDirectionHead x {0} ka N n rows).mpr hN
  refine ⟨N, ?_, rowBranchHistory_wired_endsAvoid_sink_of_confined B N x ka (kb B) rows n hN hconf⟩
  rw [he]
  exact hh

/-- The probability of a finite row exploration avoiding the wired sink tends to one. -/
theorem originSafeRowEvent_tendsto_one (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    Tendsto (fun B => wilsonRows (originSafeRowEvent B x (kb B) n)) atTop (nhds 1) := by
  have hpoint : ∀ᵐ rows ∂wilsonRows, ∀ᶠ B : ℕ in atTop,
      rows ∈ originSafeRowEvent B x (kb B) n ↔ rows ∈ (Set.univ : Set (ℕ → WalkDriver)) := by
    filter_upwards [wilsonRows_ae_eventually_originSafeRowEvent x ka kb n] with rows hrows
    filter_upwards [hrows] with B hB
    simp only [Set.mem_univ, iff_true]
    exact hB
  have ht := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (μ := wilsonRows) (A := Set.univ) (As := fun B => originSafeRowEvent B x (kb B) n)
    MeasurableSet.univ (fun B => measurableSet_originSafeRowEvent B x (kb B) n) hpoint
  simpa only [measure_univ] using ht

/-- The corresponding event for chronological stack-driven branch histories. -/
def originSafeStackHistoryEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    Set (FiniteWired.Vertex B × ℕ → FiniteWired.Direction) :=
  {σ | ∃ N, BranchHistory.HitsBefore N n
      (boundedBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
        k N σ n) ∧
    BranchHistory.EndsAvoid (wiredHead B) (fun i => wiredSite B (x i)) {none} n
      (boundedBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
        k N σ n)}

/-- The stack and independent-row safe-history probabilities agree. -/
theorem originSafeStackHistoryEvent_measure (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    directionStackLaw (FiniteWired.Vertex B) (originSafeStackHistoryEvent B x k n) =
      wilsonRows (originSafeRowEvent B x k n) :=
  directionStackLaw_completedBranchHistory_eq_wilsonRows (wiredHead B)
    (fun i => wiredSite B (x i)) (wiredOriginAndSink B) k n
    (BranchHistory.EndsAvoid (wiredHead B) (fun i => wiredSite B (x i)) {none} n)

end
end FiniteAvalanches.Wilson.Lattice
