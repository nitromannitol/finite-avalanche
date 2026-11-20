import FiniteAvalanches.Wilson.CyclePopping.UniformTerminalLaw
import FiniteAvalanches.Trees.Measure
import Mathlib.Probability.Independence.InfinitePi

/-! Independent uniform instruction stacks with vertex-dependent alphabets. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (A : V → Type*) [∀ v, Fintype (A v)] [∀ v, Nonempty (A v)]
variable [∀ v, MeasurableSpace (A v)] [∀ v, MeasurableSingletonClass (A v)]

/-- Independent uniform instructions, with an alphabet specific to each vertex. -/
def variableStackLaw : Measure ((p : V × ℕ) → A p.1) :=
  Measure.infinitePi (fun p : V × ℕ => FiniteAvalanches.uniformMeasure (A p.1))

instance variableStackLaw_probability : IsProbabilityMeasure (variableStackLaw A) := by
  unfold variableStackLaw
  infer_instance

omit [Fintype V] [DecidableEq V] in
/-- Each stack entry is uniform on its own vertex's instruction alphabet. -/
theorem variableStackLaw_eval (v : V) (i : ℕ) (b : A v) :
    variableStackLaw A {σ | σ (v, i) = b} = 1 / (Nat.card (A v) : ℝ≥0∞) := by
  have he := (measurePreserving_eval_infinitePi
    (fun p : V × ℕ => FiniteAvalanches.uniformMeasure (A p.1)) (v, i)).measure_preimage
      (measurableSet_singleton b).nullMeasurableSet
  change variableStackLaw A {σ | σ (v, i) = b} =
    FiniteAvalanches.uniformMeasure (A v) {b} at he
  rw [he, FiniteAvalanches.uniformMeasure_apply]
  simp [Nat.card_eq_fintype_card]

/-- Uniform stacks choose every cycle-free terminal assignment with equal mass,
even when the numbers of instructions differ from vertex to vertex. -/
theorem variableStackLaw_terminal_uniform (R : Set V)
    (head : (v : V) → A v → V) (k : Cursor V) (a : GoodArrows R head) :
    variableStackLaw A (terminalOutputEvent R head k (fun v i σ => σ (v, i)) a) =
      1 / (Fintype.card (GoodArrows R head) : ℝ≥0∞) := by
  apply measure_terminalOutput_uniform (variableStackLaw A) R head k (fun v i σ => σ (v, i))
  · exact iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  · intro v i
    exact measurable_pi_apply (v, i)
  · intro v i b
    rw [variableStackLaw_eval A v i b, variableStackLaw_eval A v 0 b]
  · intro v b
    rw [variableStackLaw_eval A v 0 b]
    exact ENNReal.div_ne_zero.mpr ⟨by norm_num, by simp⟩
  · intro v b c
    rw [variableStackLaw_eval A v 0 b, variableStackLaw_eval A v 0 c]

/-- If a cycle-free assignment exists, variable-alphabet cycle popping
terminates almost surely. -/
theorem variableStackLaw_ae_terminates (R : Set V)
    (head : (v : V) → A v → V) (k : Cursor V) (a : GoodArrows R head) :
    ∀ᵐ σ ∂variableStackLaw A,
      ∃ l, Relation.ReflTransGen (pop_step R head (fun v i => σ (v, i))) k l ∧
        terminal R head (fun v i => σ (v, i)) l := by
  apply ae_terminalEvent (variableStackLaw A) R head k (fun v i σ => σ (v, i))
  · exact iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  · intro v i
    exact measurable_pi_apply (v, i)
  · intro v i b
    rw [variableStackLaw_eval A v i b, variableStackLaw_eval A v 0 b]
  · apply good_arrow_weight_ne_zero (variableStackLaw A) R head (fun v i σ => σ (v, i)) a
    intro v
    rw [variableStackLaw_eval A v 0 (a.val v)]
    exact ENNReal.div_ne_zero.mpr ⟨by norm_num, by simp⟩

end
end FiniteAvalanches.Wilson.CyclePopping
