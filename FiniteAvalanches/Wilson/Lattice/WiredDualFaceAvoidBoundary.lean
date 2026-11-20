import FiniteAvalanches.Wilson.Lattice.WiredDualFaceHistoryLimit
import FiniteAvalanches.Wilson.Lattice.OriginBranchAvoidsSink

/-! Confined face-square Wilson branches avoid the added boundary roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The vertices outside the centered inner square. -/
def wiredDualFaceOuterBoundary (B : ℕ) : Set (WiredDualFace (B + 1)) :=
  {v | ¬FiniteWired.inBox B (wiredDualFaceSite v)}

/-- Equal confined histories have no face branch ending at the outer boundary. -/
theorem rowBranchHistory_wiredDualFace_endsAvoid_of_confined (B N : ℕ)
    (x : ℕ → FiniteWired.Active (B + 1))
    (S : Set (FiniteWired.Active (B + 1))) (R : Set (WiredDualFace (B + 1)))
    (k : Cursor (FiniteWired.Active (B + 1))) (l : Cursor (WiredDualFace (B + 1)))
    (rows : ℕ → WalkDriver) (n : ℕ)
    (heq : rowBranchHistory (wiredDualFaceDirectionHead (B + 1))
        (fun i => wiredDualFaceInnerVertex (B + 1) (x i)) R l N rows n =
      rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows n)
    (hconf : ∀ i < n, ∀ j ≤
      (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows (i + 1)).2.1,
      FiniteWired.inBox B (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (x i)
        (branchHistoryCursor (freeDirectionHead (B + 1)) x k i
          (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows i)) (rows i) j).1)) :
    BranchHistory.EndsAvoid (wiredDualFaceDirectionHead (B + 1))
      (fun i => wiredDualFaceInnerVertex (B + 1) (x i)) (wiredDualFaceOuterBoundary B) n
      (rowBranchHistory (wiredDualFaceDirectionHead (B + 1))
        (fun i => wiredDualFaceInnerVertex (B + 1) (x i)) R l N rows n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hp : rowBranchHistory (wiredDualFaceDirectionHead (B + 1))
        (fun i => wiredDualFaceInnerVertex (B + 1) (x i)) R l N rows n =
      rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows n := congrArg Prod.fst heq
    have hc : ∀ i < n, ∀ j ≤
        (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows (i + 1)).2.1,
        FiniteWired.inBox B (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (x i)
          (branchHistoryCursor (freeDirectionHead (B + 1)) x k i
            (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows i)) (rows i) j).1) :=
      fun i hi => hconf i (Nat.lt_succ_of_lt hi)
    refine ⟨ih hp hc, ?_⟩
    have ht := congrArg (fun h : BranchHistory (n + 1) => h.2.1) heq
    let t := (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows (n + 1)).2.1
    let cf := branchHistoryCursor (freeDirectionHead (B + 1)) x k n
      (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows n)
    let y := fun i => wiredDualFaceInnerVertex (B + 1) (x i)
    let cd := branchHistoryCursor (wiredDualFaceDirectionHead (B + 1)) y l n
      (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y R l N rows n)
    have htime : boundedWordHit (wiredDualFaceDirectionHead (B + 1))
        (branchHistoryRoots (wiredDualFaceDirectionHead (B + 1)) y R n
          (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y R l N rows n))
        (y n) cd N (rows n) = t := ht
    change (historyTrace (wiredDualFaceDirectionHead (B + 1)) (y n)
      (stoppedDirectionHistory (boundedWordHit (wiredDualFaceDirectionHead (B + 1))
        (branchHistoryRoots (wiredDualFaceDirectionHead (B + 1)) y R n
          (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y R l N rows n))
        (y n) cd N) (rows n))).1 ∉ wiredDualFaceOuterBoundary B
    simp only [stoppedDirectionHistory]
    rw [htime]
    change (historyTrace (wiredDualFaceDirectionHead (B + 1)) (y n)
      (stoppedDirectionHistory (fun _ => t) (rows n))).1 ∉ wiredDualFaceOuterBoundary B
    rw [historyTrace_stopped_fst (wiredDualFaceDirectionHead (B + 1)) (y n) (rows n) cd t]
    have hcf : ∀ j ≤ t, FiniteWired.inBox B
        (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (x n) cf (rows n) j).1) :=
      hconf n (Nat.lt_succ_self n)
    have hmap := wiredDualFace_wordState_of_confined B (x n) cf cd (rows n) t
      (fun j hj => hcf j (Nat.le_of_lt hj)) t le_rfl
    rw [← hmap]
    change ¬¬FiniteWired.inBox B (wiredDualFaceSite (wiredDualFaceInnerVertex (B + 1)
      (wordState (freeDirectionHead (B + 1)) (x n) cf (rows n) t).1))
    rw [wiredDualFaceSite_innerVertex]
    exact not_not.mpr (hcf t le_rfl)

/-- Every branch of a fixed finite face-square exploration almost surely ends
away from the outer boundary in all sufficiently large squares. -/
theorem wilsonRows_ae_eventually_wiredDualFace_avoid_boundary (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1)))
    (kc : (B : ℕ) → Cursor (WiredDualFace (B + 1))) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∃ T,
      (∀ i < n, (rowBranchHistory latticeDirectionHead x {0} ka T rows (i + 1)).2.1 < T) ∧
      ∀ᶠ B : ℕ in atTop,
        BranchHistory.EndsAvoid (wiredDualFaceDirectionHead (B + 1))
          (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
          (wiredDualFaceOuterBoundary B) n
          (rowBranchHistory (wiredDualFaceDirectionHead (B + 1))
            (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
            (wiredDualFaceOriginAndBoundary B) (kc B) T rows n) := by
  filter_upwards [wilsonRows_ae_eventually_freeOrigin_history_eq x ka kb n] with rows hrows
  obtain ⟨T, hT, heq⟩ := hrows
  refine ⟨T, hT, ?_⟩
  filter_upwards [heq, eventually_walkSegments_inBox x rows n T] with B heq' hbox
  let xf := fun i => freeSite (B + 1) (x i)
  let S := freeOriginAndBoundary B
  have hprefix : ∀ m ≤ n, rowBranchHistory (freeDirectionHead (B + 1)) xf S (kb B) T rows m =
      rowBranchHistory latticeDirectionHead x {0} ka T rows m :=
    rowBranchHistory_prefix_eq _ _ _ _ _ _ _ _ _ _ _ heq'
  have hfhit : ∀ i < n,
      (rowBranchHistory (freeDirectionHead (B + 1)) xf S (kb B) T rows (i + 1)).2.1 < T := by
    intro i hi
    rw [hprefix (i + 1) (by omega)]
    exact hT i hi
  have hfconf : ∀ i < n, ∀ j ≤
      (rowBranchHistory (freeDirectionHead (B + 1)) xf S (kb B) T rows (i + 1)).2.1,
      FiniteWired.inBox B (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (xf i)
        (branchHistoryCursor (freeDirectionHead (B + 1)) xf (kb B) i
          (rowBranchHistory (freeDirectionHead (B + 1)) xf S (kb B) T rows i)) (rows i) j).1) := by
    intro i hi j hj
    have hjT : j < T := lt_of_le_of_lt hj (hfhit i hi)
    have hbox' : ∀ s ≤ j, FiniteWired.inBox (B + 1) (position (x i) (rows i) s) := by
      intro s hs d
      have hh := hbox i hi s (lt_of_le_of_lt hs hjT) d
      constructor <;> omega
    rw [freeWordState_eq_of_confined (B + 1) (x i) (rows i) _ j hbox' j le_rfl,
      site_freeSite_of_inBox _ _ (hbox' j le_rfl)]
    exact hbox i hi j hjT
  have hface := rowBranchHistory_wiredDualFace_eq_of_confined B T xf S
    (wiredDualFaceOriginAndBoundary B) (kb B) (kc B) rows n
    (wiredDualFaceOriginAndBoundary_inner_iff B) hfhit
    (fun i hi j hj => hfconf i hi j (Nat.le_of_lt hj))
  exact rowBranchHistory_wiredDualFace_endsAvoid_of_confined B T xf S
    (wiredDualFaceOriginAndBoundary B) (kb B) (kc B) rows n hface.1 hfconf

end
end FiniteAvalanches.Wilson.Lattice
