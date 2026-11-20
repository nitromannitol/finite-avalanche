import FiniteAvalanches.Wilson.Lattice.HistoryFirstHit
import FiniteAvalanches.Wilson.Lattice.FiniteBranchHistories

/-! Successful bounded stack histories satisfy the first-hit conditions. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Each successful bounded stack branch first meets the previously attached roots. -/
theorem boundedBranchHistory_firstHits_of_hits (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (N n : ℕ) (σ : V × ℕ → FiniteWired.Direction)
    (h : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N) :
    BranchHistory.FirstHits head x R n (boundedBranchHistory head x R k N σ n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hpast : ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    let a := boundedBranchHistory head x R k N σ n
    let S := branchHistoryRoots head x R n a
    let c := branchHistoryCursor head x k n a
    let w := readingLetter head (x n) c σ
    let t := boundedWordHit head S (x n) c N w
    have ht : t < N := h n (Nat.lt_succ_self n)
    have hlast := historyTrace_firstHit_of_boundedHit head S (x n) c N w ht
    change BranchHistory.FirstHits head x R n a ∧ _
    exact ⟨ih hpast, hlast⟩

end
end FiniteAvalanches.Wilson.Lattice
