import FiniteAvalanches.Wilson.CyclePopping.UniformTerminalLaw
import FiniteAvalanches.Wilson.Lattice.SimpleWalk
import Mathlib.Probability.Independence.InfinitePi

/-! Independent uniform lattice directions indexed by vertex and stack depth. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory ProbabilityTheory FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- One independent uniform lattice direction at every vertex and stack depth. -/
def directionStackLaw : Measure (V × ℕ → FiniteAvalanches.Sandpile.FiniteWired.Direction) :=
  Measure.infinitePi (fun _ : V × ℕ => directionLaw)

instance : IsProbabilityMeasure (directionStackLaw V) := by
  unfold directionStackLaw
  infer_instance

omit [Fintype V] [DecidableEq V] in
/-- Every direction in every stack has the same positive mass. -/
theorem directionStackLaw_eval (v : V) (i : ℕ)
    (d : FiniteAvalanches.Sandpile.FiniteWired.Direction) :
    directionStackLaw V {σ | σ (v, i) = d} = 1 / 4 := by
  have he := (measurePreserving_eval_infinitePi (fun _ : V × ℕ => directionLaw) (v, i)).measure_preimage
    (measurableSet_singleton d).nullMeasurableSet
  change directionStackLaw V {σ | σ (v, i) = d} = directionLaw {d} at he
  rw [he, directionLaw, FiniteAvalanches.uniformMeasure_apply]
  simp [Nat.card_eq_fintype_card, FiniteAvalanches.Sandpile.FiniteWired.Direction]

/-- Uniform direction stacks select each cycle-free terminal arrow assignment
with equal probability. -/
theorem directionStackLaw_terminal_uniform (R : Set V)
    (head : V → FiniteAvalanches.Sandpile.FiniteWired.Direction → V)
    (k : Cursor V) (a : GoodArrows R head) :
    directionStackLaw V (terminalOutputEvent R head k (fun v i σ => σ (v, i)) a) =
      1 / (Fintype.card (GoodArrows R head) : ℝ≥0∞) := by
  apply measure_terminalOutput_uniform (directionStackLaw V) R head k (fun v i σ => σ (v, i))
  · exact iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  · intro v i
    exact measurable_pi_apply (v, i)
  · intro v i d
    rw [directionStackLaw_eval V v i d, directionStackLaw_eval V v 0 d]
  · intro v d
    rw [directionStackLaw_eval V v 0 d]
    norm_num
  · intro v d e
    rw [directionStackLaw_eval V v 0 d, directionStackLaw_eval V v 0 e]

end
end FiniteAvalanches.Wilson.Lattice
