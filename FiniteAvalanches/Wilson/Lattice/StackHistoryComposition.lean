import FiniteAvalanches.Wilson.Lattice.StoppedStackReading

/-! Composition of finite stopping histories for successive stack walks. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable {V α : Type*} [DecidableEq V]

/-- The first cursor of a word is below the cursor after its finite history. -/
theorem le_historyCursor (head : V → FiniteWired.Direction → V) (x : V)
    (k : Cursor V) (p : DirectionHistory) : k ≤ historyCursor head x k p := by
  exact wordState_cursor_mono head x k p.extend (Nat.zero_le p.1)

/-- Append the stopped direction history of the next adaptive stack walk. -/
def advanceStackHistory (head : V → FiniteWired.Direction → V)
    (state : (V × ℕ → FiniteWired.Direction) → α) (k : α → Cursor V)
    (x : α → V) (t : α → WalkDriver → ℕ) (σ : V × ℕ → FiniteWired.Direction) :
    α × DirectionHistory :=
  let a := state σ
  (a, stoppedDirectionHistory (t a) (readingLetter head (x a) (k a) σ))

/-- The raw consumed cursor after appending a stopped direction history. -/
def advanceHistoryCursor (head : V → FiniteWired.Direction → V)
    (k : α → Cursor V) (x : α → V) (h : α × DirectionHistory) : Cursor V :=
  historyCursor head (x h.1) (k h.1) h.2

/-- Appending a finite stopped walk preserves the finite-prefix determination
of an adaptively chosen stack history. -/
theorem advanceStackHistory_stable (head : V → FiniteWired.Direction → V)
    (state : (V × ℕ → FiniteWired.Direction) → α) (k : α → Cursor V)
    (x : α → V) (t : α → WalkDriver → ℕ)
    (hstate : ∀ σ τ, (∀ v i, i < k (state σ) v → τ (v, i) = σ (v, i)) →
      state τ = state σ)
    (ht : ∀ a w w', (∀ i < t a w, w' i = w i) → t a w' = t a w)
    (σ τ : V × ℕ → FiniteWired.Direction)
    (h : ∀ v i, i < advanceHistoryCursor head k x (advanceStackHistory head state k x t σ) v →
      τ (v, i) = σ (v, i)) :
    advanceStackHistory head state k x t τ = advanceStackHistory head state k x t σ := by
  have hle : k (state σ) ≤ advanceHistoryCursor head k x
      (advanceStackHistory head state k x t σ) :=
    le_historyCursor head (x (state σ)) (k (state σ)) _
  have hs : state τ = state σ := hstate σ τ (fun v i hi => h v i (lt_of_lt_of_le hi (hle v)))
  have hh := stoppedDirectionHistory_stable head (x (state σ)) (k (state σ))
    (t (state σ)) (ht (state σ)) σ τ h
  simp only [advanceStackHistory, hs, hh]

/-- Any next stack walk is independent of the entire finite history obtained
by appending one more stopped walk. -/
theorem directionStackLaw_advanceHistory_indep [Fintype V] [Countable α]
    (head : V → FiniteWired.Direction → V)
    (state : (V × ℕ → FiniteWired.Direction) → α) (k : α → Cursor V)
    (x : α → V) (t : α → WalkDriver → ℕ)
    (hstate : ∀ σ τ, (∀ v i, i < k (state σ) v → τ (v, i) = σ (v, i)) →
      state τ = state σ)
    (ht : ∀ a w w', (∀ i < t a w, w' i = w i) → t a w' = t a w)
    (start : α × DirectionHistory → V) (P : α × DirectionHistory → Prop)
    (A : Set WalkDriver) (hA : MeasurableSet A) :
    directionStackLaw V {σ |
      P (advanceStackHistory head state k x t σ) ∧
      readingLetter head (start (advanceStackHistory head state k x t σ))
        (advanceHistoryCursor head k x (advanceStackHistory head state k x t σ)) σ ∈ A} =
    directionStackLaw V {σ | P (advanceStackHistory head state k x t σ)} * walkLaw A := by
  exact directionStackLaw_stopping_history_inter_reading V head
    (advanceStackHistory head state k x t) (advanceHistoryCursor head k x) start
    (advanceStackHistory_stable head state k x t hstate ht) P A hA

end
end FiniteAvalanches.Wilson.Lattice
