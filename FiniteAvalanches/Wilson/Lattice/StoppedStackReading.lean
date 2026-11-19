import FiniteAvalanches.Wilson.CyclePopping.ReadingLocality
import FiniteAvalanches.Wilson.Lattice.StoppingStackHistory

/-! Fresh walks after a finite stopping rule for a stack-driven walk. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

/-- A finite direction word indexed by its length. -/
abbrev DirectionHistory := Σ n : ℕ, Fin n → FiniteWired.Direction

/-- Extend a finite direction history by an arbitrary fixed direction. -/
def DirectionHistory.extend (p : DirectionHistory) : WalkDriver := fun i =>
  if hi : i < p.1 then p.2 ⟨i, hi⟩ else (0, false)

/-- The finite direction history recorded at a finite stopping rule. -/
def stoppedDirectionHistory (t : WalkDriver → ℕ) (w : WalkDriver) : DirectionHistory :=
  ⟨t w, fun i => w i.val⟩

/-- The cursor obtained by reading all directions of a finite history. -/
def historyCursor {V : Type*} [DecidableEq V] (head : V → FiniteWired.Direction → V)
    (x : V) (k : Cursor V) (p : DirectionHistory) : Cursor V :=
  (wordState head x k p.extend p.1).2

/-- The cursor reconstructed from a stopped history is the actual consumed cursor. -/
theorem historyCursor_stoppedDirectionHistory {V : Type*} [DecidableEq V]
    (head : V → FiniteWired.Direction → V) (x : V) (k : Cursor V)
    (t : WalkDriver → ℕ) (σ : V × ℕ → FiniteWired.Direction) :
    historyCursor head x k (stoppedDirectionHistory t (readingLetter head x k σ)) =
      (readingState head x k σ (t (readingLetter head x k σ))).2 := by
  let w := readingLetter head x k σ
  let p := stoppedDirectionHistory t w
  have hp : ∀ i < p.1, readingLetter head x k σ i = p.extend i := by
    intro i hi
    have hi' : i < t (readingLetter head x k σ) := hi
    simp only [p, stoppedDirectionHistory, DirectionHistory.extend, w, dif_pos hi']
  have h := readingState_eq_wordState head x k σ p.extend p.1
    ((reading_prefix_iff head x k σ p.extend p.1).mp hp)
  exact (congrArg Prod.snd h).symm

/-- The finite stopped direction history is determined by the instructions
below the cursor consumed by that history. -/
theorem stoppedDirectionHistory_stable {V : Type*} [DecidableEq V]
    (head : V → FiniteWired.Direction → V) (x : V) (k : Cursor V)
    (t : WalkDriver → ℕ)
    (ht : ∀ w w', (∀ i < t w, w' i = w i) → t w' = t w)
    (σ τ : V × ℕ → FiniteWired.Direction)
    (h : ∀ v i, i < historyCursor head x k
      (stoppedDirectionHistory t (readingLetter head x k σ)) v → τ (v, i) = σ (v, i)) :
    stoppedDirectionHistory t (readingLetter head x k τ) =
      stoppedDirectionHistory t (readingLetter head x k σ) := by
  rw [historyCursor_stoppedDirectionHistory] at h
  have hl := (readingState_eq_of_agree_below head x k σ τ
    (t (readingLetter head x k σ)) h).2
  have he := ht (readingLetter head x k σ) (readingLetter head x k τ) hl
  change (⟨t (readingLetter head x k τ), fun i => readingLetter head x k τ i.val⟩ :
      DirectionHistory) = ⟨t (readingLetter head x k σ), fun i => readingLetter head x k σ i.val⟩
  apply Sigma.ext he
  apply Function.hfunext (congrArg Fin he)
  intro i j hij
  apply heq_of_eq
  have hij' : i.val = j.val := Fin.val_eq_val_of_heq hij
  dsimp only
  rw [hij']
  exact hl j.val j.isLt

/-- After any finite stopping rule, the next walk from the consumed stack
cursor is independent of the stopped history and has the ordinary walk law. -/
theorem directionStackLaw_stopped_reading_indep {V : Type*} [Fintype V] [DecidableEq V]
    (head : V → FiniteWired.Direction → V) (x : V) (k : Cursor V)
    (t : WalkDriver → ℕ)
    (ht : ∀ w w', (∀ i < t w, w' i = w i) → t w' = t w)
    (start : DirectionHistory → V) (P : DirectionHistory → Prop)
    (A : Set WalkDriver) (hA : MeasurableSet A) :
    directionStackLaw V {σ |
      P (stoppedDirectionHistory t (readingLetter head x k σ)) ∧
      readingLetter head (start (stoppedDirectionHistory t (readingLetter head x k σ)))
        (historyCursor head x k (stoppedDirectionHistory t (readingLetter head x k σ))) σ ∈ A} =
    directionStackLaw V {σ | P (stoppedDirectionHistory t (readingLetter head x k σ))} *
      walkLaw A := by
  exact directionStackLaw_stopping_history_inter_reading V head
    (fun σ => stoppedDirectionHistory t (readingLetter head x k σ))
    (historyCursor head x k) start
    (stoppedDirectionHistory_stable head x k t ht) P A hA

end
end FiniteAvalanches.Wilson.Lattice
