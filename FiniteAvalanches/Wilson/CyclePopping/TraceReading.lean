import FiniteAvalanches.Wilson.CyclePopping.InstructionTrace
import FiniteAvalanches.Wilson.CyclePopping.StackReading

/-! The stack exploration trace reads the adaptive driver instruction by instruction. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver
open scoped Classical

noncomputable section

variable {V D : Type*} [DecidableEq V]

/-- The chronological quiver trace and the adaptive reader have the same
position and the same consumed cursors at every time. -/
theorem instructionTrace_eq_readingState (head : V → D → V) (x : V) (k : Cursor V)
    (σ : V × ℕ → D) :
    letI : Quiver V := instructionQuiver head
    ∀ n, (instructionTrace head (fun v i => σ (v, i)) k x n).1 =
        (readingState head x k σ n).1 ∧
      consume k (instructionTrace head (fun v i => σ (v, i)) k x n).2 =
        (readingState head x k σ n).2 := by
  letI : Quiver V := instructionQuiver head
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    constructor
    · change head (instructionTrace head (fun v i => σ (v, i)) k x n).1
          (σ ((instructionTrace head (fun v i => σ (v, i)) k x n).1,
            consume k (instructionTrace head (fun v i => σ (v, i)) k x n).2
              (instructionTrace head (fun v i => σ (v, i)) k x n).1)) =
        head (readingState head x k σ n).1
          (σ ((readingState head x k σ n).1,
            (readingState head x k σ n).2 (readingState head x k σ n).1))
      rw [ih.2, ih.1]
    · change pop (consume k (instructionTrace head (fun v i => σ (v, i)) k x n).2)
        {(instructionTrace head (fun v i => σ (v, i)) k x n).1} =
        pop (readingState head x k σ n).2 {(readingState head x k σ n).1}
      rw [ih.2, ih.1]


/-- The stack trace is the ordinary word-driven walk for the directions it reads. -/
theorem instructionTrace_eq_read_driver (head : V → D → V) (x : V) (k : Cursor V)
    (σ : V × ℕ → D) :
    letI : Quiver V := instructionQuiver head
    ∀ n, (instructionTrace head (fun v i => σ (v, i)) k x n).1 =
        (wordState head x k (readingLetter head x k σ) n).1 ∧
      consume k (instructionTrace head (fun v i => σ (v, i)) k x n).2 =
        (wordState head x k (readingLetter head x k σ) n).2 := by
  letI : Quiver V := instructionQuiver head
  intro n
  have hp : ∀ i < n, σ (wordAddress head x k (readingLetter head x k σ) i) =
      readingLetter head x k σ i :=
    (reading_prefix_iff head x k σ (readingLetter head x k σ) n).mp (fun _ _ => rfl)
  have hstate := readingState_eq_wordState head x k σ (readingLetter head x k σ) n hp
  have htrace := instructionTrace_eq_readingState head x k σ n
  exact ⟨htrace.1.trans (congrArg Prod.fst hstate), htrace.2.trans (congrArg Prod.snd hstate)⟩

end
end FiniteAvalanches.Wilson.CyclePopping
