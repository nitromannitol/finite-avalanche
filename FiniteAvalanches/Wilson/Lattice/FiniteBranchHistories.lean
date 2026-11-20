import FiniteAvalanches.Wilson.Lattice.StackHistoryComposition
import FiniteAvalanches.Wilson.Lattice.StoppedStackTrace

/-! Independent stack walks along finitely many bounded Wilson branches. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

/-- The recorded finite direction words of an ordered sequence of branches. -/
def BranchHistory : ℕ → Type
  | 0 => Unit
  | n + 1 => BranchHistory n × DirectionHistory

instance (n : ℕ) : Countable (BranchHistory n) := by
  induction n with
  | zero => change Countable Unit; infer_instance
  | succ n ih => change Countable (BranchHistory n × DirectionHistory); infer_instance

variable {V : Type*} [DecidableEq V]

/-- The cursor after consuming every recorded branch. -/
def branchHistoryCursor (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (k : Cursor V) : (n : ℕ) → BranchHistory n → Cursor V
  | 0, _ => k
  | n + 1, h => historyCursor head (x n) (branchHistoryCursor head x k n h.1) h.2

/-- The root set after attaching the erasure of every recorded branch. -/
def branchHistoryRoots (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (R : Set V) : (n : ℕ) → BranchHistory n → Set V
  | 0, _ => R
  | n + 1, h => historyRoots head (x n) (branchHistoryRoots head x R n h.1) h.2

/-- Adaptively read each branch to its root set, capped at a finite horizon. -/
def boundedBranchHistory (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (R : Set V) (k : Cursor V) (N : ℕ) (σ : V × ℕ → FiniteWired.Direction) :
    (n : ℕ) → BranchHistory n
  | 0 => ()
  | n + 1 =>
    let h := boundedBranchHistory head x R k N σ n
    let c := branchHistoryCursor head x k n h
    let S := branchHistoryRoots head x R n h
    (h, stoppedDirectionHistory (boundedWordHit head S (x n) c N)
      (readingLetter head (x n) c σ))

/-- The complete finite branch history is determined by the consumed prefixes
below its final raw cursor. -/
theorem boundedBranchHistory_stable (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (R : Set V) (k : Cursor V) (N : ℕ) (n : ℕ)
    (σ τ : V × ℕ → FiniteWired.Direction)
    (h : ∀ v i, i < branchHistoryCursor head x k n (boundedBranchHistory head x R k N σ n) v →
      τ (v, i) = σ (v, i)) :
    boundedBranchHistory head x R k N τ n = boundedBranchHistory head x R k N σ n := by
  induction n generalizing σ τ with
  | zero => rfl
  | succ n ih =>
    let state := fun ξ => boundedBranchHistory head x R k N ξ n
    let c := branchHistoryCursor head x k n
    let start : BranchHistory n → V := fun _ => x n
    let t : BranchHistory n → WalkDriver → ℕ := fun a =>
      boundedWordHit head (branchHistoryRoots head x R n a) (x n) (c a) N
    have hs : ∀ ξ η, (∀ v i, i < c (state ξ) v → η (v, i) = ξ (v, i)) →
        state η = state ξ := by
      intro ξ η hξη
      exact ih ξ η hξη
    have ht : ∀ a w w', (∀ i < t a w, w' i = w i) → t a w' = t a w := by
      intro a w w' hw
      exact boundedWordHit_stable head (branchHistoryRoots head x R n a) (x n) (c a) N w w' hw
    exact advanceStackHistory_stable head state c start t hs ht σ τ h

/-- After any fixed number of finite-horizon branches, a new stack walk has the
ordinary walk law independently of all recorded branch directions. -/
theorem directionStackLaw_boundedBranchHistory_indep [Fintype V]
    (head : V → FiniteWired.Direction → V) (x : ℕ → V)
    (R : Set V) (k : Cursor V) (N n : ℕ)
    (start : BranchHistory n → V) (P : BranchHistory n → Prop)
    (A : Set WalkDriver) (hA : MeasurableSet A) :
    directionStackLaw V {σ |
      P (boundedBranchHistory head x R k N σ n) ∧
      readingLetter head (start (boundedBranchHistory head x R k N σ n))
        (branchHistoryCursor head x k n (boundedBranchHistory head x R k N σ n)) σ ∈ A} =
    directionStackLaw V {σ | P (boundedBranchHistory head x R k N σ n)} * walkLaw A := by
  exact directionStackLaw_stopping_history_inter_reading V head
    (fun σ => boundedBranchHistory head x R k N σ n) (branchHistoryCursor head x k n) start
    (boundedBranchHistory_stable head x R k N n) P A hA

end
end FiniteAvalanches.Wilson.Lattice
