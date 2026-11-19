import FiniteAvalanches.Wilson.Lattice.StoppedStackReading

/-! Finite first-hit rules for chronological stack-driven walks. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- A word-driven state at time `n` depends only on the first `n` directions. -/
theorem wordState_eq_of_prefix (head : V → FiniteWired.Direction → V) (x : V)
    (k : Cursor V) (w w' : WalkDriver) (n : ℕ)
    (h : ∀ i < n, w' i = w i) : wordState head x k w' n = wordState head x k w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    change (head (wordState head x k w' n).1 (w' n),
      pop (wordState head x k w' n).2 {(wordState head x k w' n).1}) =
      (head (wordState head x k w n).1 (w n),
      pop (wordState head x k w n).2 {(wordState head x k w n).1})
    rw [hs, h n (Nat.lt_succ_self n)]

/-- First visit to the roots, capped at the prescribed finite horizon. -/
def boundedWordHit (head : V → FiniteWired.Direction → V) (R : Set V)
    (x : V) (k : Cursor V) (N : ℕ) (w : WalkDriver) : ℕ :=
  if h : ∃ n < N, (wordState head x k w n).1 ∈ R then Nat.find h else N

/-- The capped first hit never exceeds its horizon. -/
theorem boundedWordHit_le (head : V → FiniteWired.Direction → V) (R : Set V)
    (x : V) (k : Cursor V) (N : ℕ) (w : WalkDriver) :
    boundedWordHit head R x k N w ≤ N := by
  unfold boundedWordHit
  split_ifs with h
  · exact Nat.le_of_lt (Nat.find_spec h).1
  · rfl

/-- No root is visited before the capped first-hit time. -/
theorem boundedWordHit_avoids (head : V → FiniteWired.Direction → V) (R : Set V)
    (x : V) (k : Cursor V) (N : ℕ) (w : WalkDriver) :
    ∀ i < boundedWordHit head R x k N w, (wordState head x k w i).1 ∉ R := by
  unfold boundedWordHit
  split_ifs with h
  · intro i hi hr
    exact Nat.find_min h hi ⟨lt_trans hi (Nat.find_spec h).1, hr⟩
  · intro i hi hr
    exact h ⟨i, hi, hr⟩

/-- If the capped first-hit time is below the horizon, its position is a root. -/
theorem boundedWordHit_mem_of_lt (head : V → FiniteWired.Direction → V) (R : Set V)
    (x : V) (k : Cursor V) (N : ℕ) (w : WalkDriver)
    (h : boundedWordHit head R x k N w < N) :
    (wordState head x k w (boundedWordHit head R x k N w)).1 ∈ R := by
  unfold boundedWordHit at h ⊢
  split_ifs at h ⊢ with hhit
  · exact (Nat.find_spec hhit).2
  · exact (Nat.lt_irrefl N h).elim

/-- The first hit capped at a finite horizon is a finite stopping rule. -/
theorem boundedWordHit_stable (head : V → FiniteWired.Direction → V) (R : Set V)
    (x : V) (k : Cursor V) (N : ℕ) (w w' : WalkDriver)
    (h : ∀ i < boundedWordHit head R x k N w, w' i = w i) :
    boundedWordHit head R x k N w' = boundedWordHit head R x k N w := by
  let t := boundedWordHit head R x k N w
  let t' := boundedWordHit head R x k N w'
  have hpos : ∀ i ≤ t, (wordState head x k w' i).1 = (wordState head x k w i).1 := by
    intro i hi
    exact congrArg Prod.fst (wordState_eq_of_prefix head x k w w' i
      (fun j hj => h j (lt_of_lt_of_le hj hi)))
  have hlt : ¬ t' < t := by
    intro hlt
    have hroot : (wordState head x k w' t').1 ∈ R :=
      boundedWordHit_mem_of_lt head R x k N w' (lt_of_lt_of_le hlt (boundedWordHit_le head R x k N w))
    rw [hpos t' (Nat.le_of_lt hlt)] at hroot
    exact boundedWordHit_avoids head R x k N w t' hlt hroot
  have hgt : ¬ t < t' := by
    intro hgt
    have hroot : (wordState head x k w t).1 ∈ R :=
      boundedWordHit_mem_of_lt head R x k N w (lt_of_lt_of_le hgt (boundedWordHit_le head R x k N w'))
    rw [← hpos t le_rfl] at hroot
    exact boundedWordHit_avoids head R x k N w' t hgt hroot
  exact Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)

/-- A walk started after a finite-horizon root hit has the ordinary independent
walk law, conditional on any event of the stopped direction history. -/
theorem directionStackLaw_boundedHit_reading_indep [Fintype V]
    (head : V → FiniteWired.Direction → V) (R : Set V) (x : V)
    (k : Cursor V) (N : ℕ) (start : DirectionHistory → V)
    (P : DirectionHistory → Prop) (A : Set WalkDriver) (hA : MeasurableSet A) :
    directionStackLaw V {σ |
      P (stoppedDirectionHistory (boundedWordHit head R x k N) (readingLetter head x k σ)) ∧
      readingLetter head
        (start (stoppedDirectionHistory (boundedWordHit head R x k N) (readingLetter head x k σ)))
        (historyCursor head x k
          (stoppedDirectionHistory (boundedWordHit head R x k N) (readingLetter head x k σ))) σ ∈ A} =
    directionStackLaw V {σ |
      P (stoppedDirectionHistory (boundedWordHit head R x k N) (readingLetter head x k σ))} *
      walkLaw A := by
  exact directionStackLaw_stopped_reading_indep head x k (boundedWordHit head R x k N)
    (boundedWordHit_stable head R x k N) start P A hA

end
end FiniteAvalanches.Wilson.Lattice
