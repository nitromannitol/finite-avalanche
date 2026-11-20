import FiniteAvalanches.Wilson.CyclePopping.TraceReading

/-! Chronological instruction traces reconstructed from their direction words. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver
open scoped Classical

noncomputable section

variable {V D : Type*} [DecidableEq V]

/-- The path of a walk driven by an instruction word, retaining its arrows. -/
def wordTrace (head : V → D → V) (x : V) (w : ℕ → D) :
    letI : Quiver V := instructionQuiver head
    ℕ → Σ y : V, Path x y := by
  letI : Quiver V := instructionQuiver head
  intro n
  induction n with
  | zero => exact ⟨x, .nil⟩
  | succ n q => exact ⟨head q.1 (w n), q.2.cons ⟨w n, rfl⟩⟩

omit [DecidableEq V] in
/-- A finite word trace is determined by the instructions before its endpoint. -/
theorem wordTrace_eq_of_prefix (head : V → D → V) (x : V) (w w' : ℕ → D)
    (n : ℕ) (h : ∀ i < n, w' i = w i) :
    letI : Quiver V := instructionQuiver head
    wordTrace head x w' n = wordTrace head x w n := by
  letI : Quiver V := instructionQuiver head
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    change (let q := wordTrace head x w' n
      (⟨head q.1 (w' n), q.2.cons ⟨w' n, rfl⟩⟩ : Σ y : V, Path x y)) =
      (let q := wordTrace head x w n
      (⟨head q.1 (w n), q.2.cons ⟨w n, rfl⟩⟩ : Σ y : V, Path x y))
    rw [hp, h n (Nat.lt_succ_self n)]

/-- The raw instruction trace is reconstructed exactly from the adaptive
instruction word, including the original arrow labels. -/
theorem instructionTrace_eq_wordTrace (head : V → D → V) (x : V) (k : Cursor V)
    (σ : V × ℕ → D) :
    letI : Quiver V := instructionQuiver head
    ∀ n, instructionTrace head (fun v i => σ (v, i)) k x n =
      wordTrace head x (readingLetter head x k σ) n := by
  letI : Quiver V := instructionQuiver head
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := instructionTrace_eq_readingState head x k σ n
    have ha : σ ((instructionTrace head (fun v i => σ (v, i)) k x n).1,
          consume k (instructionTrace head (fun v i => σ (v, i)) k x n).2
            (instructionTrace head (fun v i => σ (v, i)) k x n).1) =
        readingLetter head x k σ n := by
      simp only [readingLetter, h.1, h.2]
    change (let q := instructionTrace head (fun v i => σ (v, i)) k x n
      let a := σ (q.1, consume k q.2 q.1)
      (⟨head q.1 a, q.2.cons ⟨a, rfl⟩⟩ : Σ y : V, Path x y)) =
      (let q := wordTrace head x (readingLetter head x k σ) n
      (⟨head q.1 (readingLetter head x k σ n),
        q.2.cons ⟨readingLetter head x k σ n, rfl⟩⟩ : Σ y : V, Path x y))
    rw [← ih]
    dsimp only
    rw [ha]

end
end FiniteAvalanches.Wilson.CyclePopping
