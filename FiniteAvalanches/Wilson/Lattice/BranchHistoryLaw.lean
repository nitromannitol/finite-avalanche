import FiniteAvalanches.Wilson.Lattice.FiniteBranchHistories
import FiniteAvalanches.Wilson.Lattice.StoppedHistoryEvents

/-! Transition probabilities for finite Wilson branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The probability of extending an exact finite branch history factors into
its previous probability and the ordinary walk's stopped-history probability. -/
theorem directionStackLaw_boundedBranchHistory_succ (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (N n : ℕ)
    (a : BranchHistory n) (p : DirectionHistory) :
    directionStackLaw V {σ | boundedBranchHistory head x R k N σ (n + 1) = (a, p)} =
      directionStackLaw V {σ | boundedBranchHistory head x R k N σ n = a} *
        walkLaw {w | stoppedDirectionHistory
          (boundedWordHit head (branchHistoryRoots head x R n a) (x n)
            (branchHistoryCursor head x k n a) N) w = p} := by
  let t := boundedWordHit head (branchHistoryRoots head x R n a) (x n)
    (branchHistoryCursor head x k n a) N
  let A : Set WalkDriver := {w | stoppedDirectionHistory t w = p}
  have hA : MeasurableSet A :=
    measurableSet_stoppedDirectionHistory_eq t
      (boundedWordHit_stable head (branchHistoryRoots head x R n a) (x n)
        (branchHistoryCursor head x k n a) N) p
  have h := directionStackLaw_boundedBranchHistory_indep head x R k N n
    (fun _ => x n) (fun b => b = a) A hA
  have he : {σ : V × ℕ → FiniteWired.Direction |
      boundedBranchHistory head x R k N σ (n + 1) = (a, p)} =
      {σ | boundedBranchHistory head x R k N σ n = a ∧
        readingLetter head (x n)
          (branchHistoryCursor head x k n (boundedBranchHistory head x R k N σ n)) σ ∈ A} := by
    ext σ
    change ((boundedBranchHistory head x R k N σ n,
        stoppedDirectionHistory (boundedWordHit head
          (branchHistoryRoots head x R n (boundedBranchHistory head x R k N σ n)) (x n)
          (branchHistoryCursor head x k n (boundedBranchHistory head x R k N σ n)) N)
          (readingLetter head (x n)
            (branchHistoryCursor head x k n (boundedBranchHistory head x R k N σ n)) σ)) :
        BranchHistory n × DirectionHistory) = (a, p) ↔
      boundedBranchHistory head x R k N σ n = a ∧
        readingLetter head (x n)
          (branchHistoryCursor head x k n (boundedBranchHistory head x R k N σ n)) σ ∈ A
    simp only [Prod.mk.injEq, A, Set.mem_setOf_eq, t]
    constructor
    · rintro ⟨ha, hp⟩
      refine ⟨ha, ?_⟩
      simpa only [ha] using hp
    · rintro ⟨ha, hp⟩
      refine ⟨ha, ?_⟩
      simpa only [ha] using hp
  rw [he]
  exact h

end
end FiniteAvalanches.Wilson.Lattice
