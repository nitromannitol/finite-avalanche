import FiniteAvalanches.Wilson.Lattice.FreeOriginHistory
import FiniteAvalanches.Wilson.Lattice.OriginBranchAvoidsSink

/-! Confined origin-rooted branches avoid the free box boundary. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- If the free and lattice histories agree and the lattice branches stay in
the inner box, each free branch ends away from the outer boundary. -/
theorem freeOrigin_history_endsAvoid_of_confined (N T : ℕ) (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : Cursor (FiniteWired.Active (N + 1)))
    (rows : ℕ → WalkDriver) (n : ℕ)
    (heq : rowBranchHistory (freeDirectionHead (N + 1)) (fun i => freeSite (N + 1) (x i))
      (freeOriginAndBoundary N) kb T rows n = rowBranchHistory latticeDirectionHead x {0} ka T rows n)
    (hhit : ∀ i < n, (rowBranchHistory latticeDirectionHead x {0} ka T rows (i + 1)).2.1 < T)
    (hbox : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x {0} ka T rows (i + 1)).2.1,
      FiniteWired.inBox N (position (x i) (rows i) j)) :
    BranchHistory.EndsAvoid (freeDirectionHead (N + 1)) (fun i => freeSite (N + 1) (x i))
      (freeOuterBoundary N) n
      (rowBranchHistory (freeDirectionHead (N + 1)) (fun i => freeSite (N + 1) (x i))
        (freeOriginAndBoundary N) kb T rows n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have heprev := congrArg (fun h : BranchHistory (n + 1) => h.1) heq
    have hpast : ∀ i < n,
        (rowBranchHistory latticeDirectionHead x {0} ka T rows (i + 1)).2.1 < T :=
      fun i hi => hhit i (Nat.lt_succ_of_lt hi)
    have hboxpast : ∀ i < n, ∀ j ≤
        (rowBranchHistory latticeDirectionHead x {0} ka T rows (i + 1)).2.1,
        FiniteWired.inBox N (position (x i) (rows i) j) :=
      fun i hi => hbox i (Nat.lt_succ_of_lt hi)
    refine ⟨ih heprev hpast hboxpast, ?_⟩
    have ht := congrArg (fun h : BranchHistory (n + 1) => h.2.1) heq
    let t := (rowBranchHistory latticeDirectionHead x {0} ka T rows (n + 1)).2.1
    let c := branchHistoryCursor (freeDirectionHead (N + 1))
      (fun i => freeSite (N + 1) (x i)) kb n
      (rowBranchHistory (freeDirectionHead (N + 1)) (fun i => freeSite (N + 1) (x i))
        (freeOriginAndBoundary N) kb T rows n)
    have htime : boundedWordHit (freeDirectionHead (N + 1))
        (branchHistoryRoots (freeDirectionHead (N + 1)) (fun i => freeSite (N + 1) (x i))
          (freeOriginAndBoundary N) n
          (rowBranchHistory (freeDirectionHead (N + 1)) (fun i => freeSite (N + 1) (x i))
            (freeOriginAndBoundary N) kb T rows n)) (freeSite (N + 1) (x n)) c T (rows n) = t := ht
    change (historyTrace (freeDirectionHead (N + 1)) (freeSite (N + 1) (x n))
      (stoppedDirectionHistory (boundedWordHit (freeDirectionHead (N + 1))
        (branchHistoryRoots (freeDirectionHead (N + 1)) (fun i => freeSite (N + 1) (x i))
          (freeOriginAndBoundary N) n
          (rowBranchHistory (freeDirectionHead (N + 1)) (fun i => freeSite (N + 1) (x i))
            (freeOriginAndBoundary N) kb T rows n)) (freeSite (N + 1) (x n)) c T) (rows n))).1 ∉
      freeOuterBoundary N
    simp only [stoppedDirectionHistory]
    rw [htime]
    change (historyTrace (freeDirectionHead (N + 1)) (freeSite (N + 1) (x n))
      (stoppedDirectionHistory (fun _ => t) (rows n))).1 ∉ freeOuterBoundary N
    rw [historyTrace_stopped_fst (freeDirectionHead (N + 1)) (freeSite (N + 1) (x n)) (rows n) c t]
    have hconf : ∀ j ≤ t, FiniteWired.inBox N (position (x n) (rows n) j) :=
      hbox n (Nat.lt_succ_self n)
    have hconf' : ∀ j ≤ t, FiniteWired.inBox (N + 1) (position (x n) (rows n) j) := by
      intro j hj k
      have hk := hconf j hj k
      constructor <;> omega
    rw [freeWordState_eq_of_confined (N + 1) (x n) (rows n) c t hconf' t le_rfl]
    change ¬¬FiniteWired.inBox N (FiniteWired.site (freeSite (N + 1) (position (x n) (rows n) t)))
    rw [site_freeSite_of_inBox _ _ (hconf' t le_rfl)]
    exact not_not.mpr (hconf t le_rfl)

/-- Almost surely, all branches in a fixed finite exploration avoid the free
outer boundary in every sufficiently large box. -/
theorem wilsonRows_ae_eventually_freeOrigin_avoid_boundary (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (N : ℕ) → Cursor (FiniteWired.Active (N + 1))) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∃ T,
      (∀ i < n, (rowBranchHistory latticeDirectionHead x {0} ka T rows (i + 1)).2.1 < T) ∧
      ∀ᶠ N : ℕ in atTop,
        BranchHistory.EndsAvoid (freeDirectionHead (N + 1)) (fun i => freeSite (N + 1) (x i))
          (freeOuterBoundary N) n
          (rowBranchHistory (freeDirectionHead (N + 1)) (fun i => freeSite (N + 1) (x i))
            (freeOriginAndBoundary N) (kb N) T rows n) := by
  filter_upwards [wilsonRows_ae_eventually_freeOrigin_history_eq x ka kb n] with rows hrows
  obtain ⟨T, hT, heq⟩ := hrows
  refine ⟨T, hT, ?_⟩
  filter_upwards [heq, eventually_walkSegments_inBox x rows n T] with N heq' hbox
  apply freeOrigin_history_endsAvoid_of_confined N T x ka (kb N) rows n heq' hT
  intro i hi j hj
  exact hbox i hi j (lt_of_le_of_lt hj (hT i hi))

end
end FiniteAvalanches.Wilson.Lattice
