import FiniteAvalanches.Wilson.CyclePopping.StackReading

/-! Finite dependence of chronological stack readings on consumed instructions. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open scoped Classical

noncomputable section

variable {V D : Type*} [DecidableEq V]

/-- The cursors of a chronological stack reading increase with time. -/
theorem readingState_cursor_mono (head : V → D → V) (x : V) (k : Cursor V)
    (σ : V × ℕ → D) : Monotone (fun n => (readingState head x k σ n).2) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_pop _ _

/-- A chronological reading up to time `n` depends only on the stack entries
strictly below the cursor it has reached at time `n`. -/
theorem readingState_eq_of_agree_below (head : V → D → V) (x : V) (k : Cursor V)
    (σ τ : V × ℕ → D) (n : ℕ)
    (h : ∀ v i, i < (readingState head x k σ n).2 v → τ (v, i) = σ (v, i)) :
    readingState head x k τ n = readingState head x k σ n ∧
      ∀ i < n, readingLetter head x k τ i = readingLetter head x k σ i := by
  induction n with
  | zero =>
    exact ⟨rfl, by simp⟩
  | succ n ih =>
    have hprev : ∀ v i, i < (readingState head x k σ n).2 v → τ (v, i) = σ (v, i) := by
      intro v i hi
      exact h v i (lt_of_lt_of_le hi (readingState_cursor_mono head x k σ (Nat.le_succ n) v))
    obtain ⟨hs, hl⟩ := ih hprev
    have hdepth : (readingState head x k σ n).2 (readingState head x k σ n).1 <
        (readingState head x k σ (n + 1)).2 (readingState head x k σ n).1 := by
      change _ < pop (readingState head x k σ n).2 {(readingState head x k σ n).1} _
      rw [pop_apply_of_mem _ _ (Finset.mem_singleton_self _)]
      exact Nat.lt_succ_self _
    have hletter : readingLetter head x k τ n = readingLetter head x k σ n := by
      simpa only [readingLetter, hs] using
        h (readingState head x k σ n).1
          ((readingState head x k σ n).2 (readingState head x k σ n).1) hdepth
    constructor
    · change (head (readingState head x k τ n).1 (readingLetter head x k τ n),
        pop (readingState head x k τ n).2 {(readingState head x k τ n).1}) =
        (head (readingState head x k σ n).1 (readingLetter head x k σ n),
        pop (readingState head x k σ n).2 {(readingState head x k σ n).1})
      rw [hs, hletter]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hl i hi
      · exact hletter

end
end FiniteAvalanches.Wilson.CyclePopping
