import FiniteAvalanches.Wilson.Lattice.StackReadingLaw
import FiniteAvalanches.Wilson.CyclePopping.TraceReading

/-! A chronological lattice stack trace has the simple random walk law. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Quiver FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The endpoint reached by a lattice direction. -/
def latticeDirectionHead (x : Site 2) (d : FiniteWired.Direction) : Site 2 :=
  x + FiniteWired.step d

/-- The word-driven lattice stack position is the ordinary lattice walk position. -/
theorem wordState_lattice_position (x : Site 2) (k : Cursor (Site 2)) (w : WalkDriver) :
    ∀ n, (wordState latticeDirectionHead x k w n).1 = position x w n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change latticeDirectionHead (wordState latticeDirectionHead x k w n).1 (w n) =
      position x w n + FiniteWired.step (w n)
    rw [ih]
    rfl

/-- The lattice quiver trace follows the ordinary walk driven by its read directions. -/
theorem lattice_instructionTrace_position (x : Site 2) (k : Cursor (Site 2))
    (σ : Site 2 × ℕ → FiniteWired.Direction) :
    letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
    ∀ n, (instructionTrace latticeDirectionHead (fun v i => σ (v, i)) k x n).1 =
      position x (readingLetter latticeDirectionHead x k σ) n := by
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  intro n
  exact (instructionTrace_eq_read_driver latticeDirectionHead x k σ n).1.trans
    (wordState_lattice_position x k (readingLetter latticeDirectionHead x k σ) n)

/-- The full position process of a stack walk has exactly the simple random walk law. -/
theorem directionStackLaw_lattice_walk (x : Site 2) (k : Cursor (Site 2)) :
    letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
    (directionStackLaw (Site 2)).map
      (fun σ n => (instructionTrace latticeDirectionHead (fun v i => σ (v, i)) k x n).1) =
      walkLaw.map (fun w n => position x w n) := by
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  have he : (fun (σ : Site 2 × ℕ → FiniteWired.Direction) n =>
      (instructionTrace latticeDirectionHead (fun v i => σ (v, i)) k x n).1) =
      (fun w n => position x w n) ∘ (fun σ => readingLetter latticeDirectionHead x k σ) := by
    funext σ n
    exact lattice_instructionTrace_position x k σ n
  rw [he, ← Measure.map_map (measurable_pi_lambda _ (fun n => measurable_position x n))
    (measurable_readingDriver (Site 2) latticeDirectionHead x k),
    directionStackLaw_map_readingDriver]

end
end FiniteAvalanches.Wilson.Lattice
