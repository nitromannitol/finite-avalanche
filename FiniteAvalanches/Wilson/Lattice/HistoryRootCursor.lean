import FiniteAvalanches.Wilson.Lattice.HistoryAvoidsRoots

/-! Initial roots are never consumed by successful Wilson branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- A word-driven cursor stays fixed at any vertex never visited as a departure. -/
theorem wordState_cursor_eq_of_avoids (head : V → FiniteWired.Direction → V)
    (x v : V) (k : Cursor V) (w : WalkDriver) (n : ℕ)
    (h : ∀ i < n, (wordState head x k w i).1 ≠ v) :
    (wordState head x k w n).2 v = k v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpast := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hv := h n (Nat.lt_succ_self n)
    change pop (wordState head x k w n).2 {(wordState head x k w n).1} v = k v
    rw [pop_apply_of_not_mem _ _ (by simpa only [Finset.mem_singleton] using hv.symm)]
    exact hpast

/-- A successful bounded history never advances the initial cursor at an
initially attached root. -/
theorem branchHistoryCursor_eq_at_initial_root
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (k : Cursor V) (N n : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (hhit : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N)
    (r : V) (hr : r ∈ R) :
    branchHistoryCursor head x k n (boundedBranchHistory head x R k N σ n) r = k r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpast : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N :=
      fun i hi => hhit i (Nat.lt_succ_of_lt hi)
    let a := boundedBranchHistory head x R k N σ n
    let S := branchHistoryRoots head x R n a
    let c := branchHistoryCursor head x k n a
    let w := readingLetter head (x n) c σ
    let t := boundedWordHit head S (x n) c N w
    have hrS : r ∈ S := branchHistoryRoots_initial_subset head x R n a hr
    have hav : ∀ i < t, (wordState head (x n) c w i).1 ≠ r := by
      intro i hi he
      have hn := boundedWordHit_avoids head S (x n) c N w i hi
      exact hn (he.symm ▸ hrS)
    have he := wordState_cursor_eq_of_avoids head (x n) r c w t hav
    have hread := (instructionTrace_eq_readingState head (x n) c σ t).2.symm.trans
      ((instructionTrace_eq_read_driver head (x n) c σ t).2)
    change historyCursor head (x n) c
      (stoppedDirectionHistory (boundedWordHit head S (x n) c N) w) r = k r
    rw [historyCursor_stoppedDirectionHistory, hread]
    exact he.trans (ih hpast)

end
end FiniteAvalanches.Wilson.Lattice
