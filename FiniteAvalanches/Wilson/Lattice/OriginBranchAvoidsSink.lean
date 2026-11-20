import FiniteAvalanches.Wilson.Lattice.OriginRootCoupling

/-! Confined origin-rooted Wilson branches avoid the wired sink. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver MeasureTheory Filter FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Every branch in a finite recorded history ends outside a designated set. -/
def BranchHistory.EndsAvoid (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (D : Set V) : (n : ℕ) → BranchHistory n → Prop
  | 0, _ => True
  | n + 1, h =>
    BranchHistory.EndsAvoid head x D n h.1 ∧ (historyTrace head (x n) h.2).1 ∉ D

/-- A stopped direction history ends at the actual word-driven position. -/
theorem historyTrace_stopped_fst (head : V → FiniteWired.Direction → V)
    (x : V) (w : WalkDriver) (k : Cursor V) (t : ℕ) :
    (historyTrace head x (stoppedDirectionHistory (fun _ => t) w)).1 =
      (wordState head x k w t).1 := by
  let p := stoppedDirectionHistory (fun _ => t) w
  have hp : ∀ i < t, p.extend i = w i := by
    intro i hi
    simp only [p, stoppedDirectionHistory, DirectionHistory.extend, dif_pos hi]
  have he := wordTrace_eq_of_prefix head x w p.extend t hp
  change (wordTrace head x p.extend t).1 = (wordState head x k w t).1
  rw [he, wordTrace_fst_eq_wordState head x k w]

/-- A confined wired row history has no branch ending at the sink. -/
theorem rowBranchHistory_wired_endsAvoid_sink_of_confined
    (B N : ℕ) (x : ℕ → Site 2) (ka : Cursor (Site 2))
    (kb : Cursor (FiniteWired.Vertex B)) (rows : ℕ → WalkDriver) (n : ℕ)
    (hhit : ∀ i < n, (rowBranchHistory latticeDirectionHead x {0} ka N rows (i + 1)).2.1 < N)
    (hbox : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x {0} ka N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j)) :
    BranchHistory.EndsAvoid (wiredHead B) (fun i => wiredSite B (x i)) {none} n
      (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
        kb N rows n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hpast : ∀ i < n,
        (rowBranchHistory latticeDirectionHead x {0} ka N rows (i + 1)).2.1 < N :=
      fun i hi => hhit i (Nat.lt_succ_of_lt hi)
    have hboxpast : ∀ i < n, ∀ j ≤
        (rowBranchHistory latticeDirectionHead x {0} ka N rows (i + 1)).2.1,
        FiniteWired.inBox B (position (x i) (rows i) j) :=
      fun i hi => hbox i (Nat.lt_succ_of_lt hi)
    refine ⟨ih hpast hboxpast, ?_⟩
    have he := (rowBranchHistory_wired_eq_of_confined B N x (wiredOriginAndSink B) {0}
      kb ka rows (n + 1) (wiredOriginAndSink_wiredSite_iff B) hhit hbox).1
    have ht := congrArg (fun h : BranchHistory (n + 1) => h.2.1) he
    let t := (rowBranchHistory latticeDirectionHead x {0} ka N rows (n + 1)).2.1
    let c := branchHistoryCursor (wiredHead B) (fun i => wiredSite B (x i)) kb n
      (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
        kb N rows n)
    have htime : boundedWordHit (wiredHead B)
        (branchHistoryRoots (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B) n
          (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
            kb N rows n)) (wiredSite B (x n)) c N (rows n) = t := ht
    change (historyTrace (wiredHead B) (wiredSite B (x n))
      (stoppedDirectionHistory (boundedWordHit (wiredHead B)
        (branchHistoryRoots (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B) n
          (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
            kb N rows n)) (wiredSite B (x n)) c N) (rows n))).1 ∉ ({none} : Set _) 
    simp only [stoppedDirectionHistory]
    rw [htime]
    change (historyTrace (wiredHead B) (wiredSite B (x n))
      (stoppedDirectionHistory (fun _ => t) (rows n))).1 ∉ ({none} : Set _)
    rw [historyTrace_stopped_fst (wiredHead B) (wiredSite B (x n)) (rows n) c t]
    have hconf : ∀ j ≤ t, FiniteWired.inBox B (position (x n) (rows n) j) :=
      hbox n (Nat.lt_succ_self n)
    rw [wiredWordState_eq_of_confined B (x n) (rows n) c t hconf t le_rfl]
    have hnot : wiredSite B (position (x n) (rows n) t) ≠ none := by
      simp [wiredSite, hconf t le_rfl]
    simpa only [Set.mem_singleton_iff] using hnot

/-- Almost surely, every branch of a fixed finite origin-rooted exploration
ends away from the sink in all sufficiently large wired boxes. -/
theorem wilsonRows_ae_eventually_originBranches_avoid_sink
    (x : ℕ → Site 2) (ka : Cursor (Site 2))
    (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∃ N,
      (∀ i < n, (rowBranchHistory latticeDirectionHead x {0} ka N rows (i + 1)).2.1 < N) ∧
      ∀ᶠ B : ℕ in atTop,
        BranchHistory.EndsAvoid (wiredHead B) (fun i => wiredSite B (x i)) {none} n
          (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
            (kb B) N rows n) := by
  filter_upwards [wilsonRows_origin_ae_finite_branch_horizon x ka n] with rows hrows
  obtain ⟨N, hN⟩ := hrows
  refine ⟨N, hN, ?_⟩
  filter_upwards [eventually_walkSegments_inBox x rows n N] with B hbox
  apply rowBranchHistory_wired_endsAvoid_sink_of_confined B N x ka (kb B) rows n hN
  intro i hi j hj
  exact hbox i hi j (lt_of_le_of_lt hj (hN i hi))

end
end FiniteAvalanches.Wilson.Lattice
