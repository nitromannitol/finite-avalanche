import FiniteAvalanches.Wilson.CyclePopping.AlmostSureTermination

/-! Uniform cycle-popping terminal arrows for uniform independent instructions. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A : V → Type*} [∀ v, MeasurableSpace (A v)]
variable [∀ v, MeasurableSingletonClass (A v)] [∀ v, Fintype (A v)]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- With uniform full-support instructions, each cycle-free terminal arrow
assignment has the same mass, the reciprocal of their number. -/
theorem measure_terminalOutput_uniform (R : Set V)
    (head : (v : V) → A v → V) (k : Cursor V)
    (X : (v : V) → ℕ → Ω → A v)
    (hX : iIndepFun (fun p : V × ℕ => X p.1 p.2) μ)
    (hm : ∀ v i, Measurable (X v i))
    (hid : ∀ v i (b : A v), μ {ω | X v i ω = b} = μ {ω | X v 0 ω = b})
    (hfull : ∀ v (b : A v), μ {ω | X v 0 ω = b} ≠ 0)
    (hunif : ∀ v (b c : A v), μ {ω | X v 0 ω = b} = μ {ω | X v 0 ω = c})
    (a : GoodArrows R head) :
    μ (terminalOutputEvent R head k X a) = 1 / (Fintype.card (GoodArrows R head) : ℝ≥0∞) := by
  have hpos := good_arrow_weight_ne_zero μ R head X a (fun v => hfull v (a.val v))
  rw [measure_terminalOutput_eq_of_positive_weight μ R head k X hX hm hid hpos a]
  let p : ℝ≥0∞ := ∏ v, μ {ω | X v 0 ω = a.val v}
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => hfull v (a.val v))
  have hpt : p ≠ ⊤ := ENNReal.prod_ne_top (fun _ _ => measure_ne_top μ _)
  have hw (b : GoodArrows R head) : (∏ v, μ {ω | X v 0 ω = b.val v}) = p := by
    apply Finset.prod_congr rfl
    intro v _
    exact hunif v (b.val v) (a.val v)
  have hs : (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) =
      (Fintype.card (GoodArrows R head) : ℝ≥0∞) * p := by
    simp_rw [hw]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change p / (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) = _
  rw [hs]
  calc
    p / ((Fintype.card (GoodArrows R head) : ℝ≥0∞) * p) =
        (1 * p) / ((Fintype.card (GoodArrows R head) : ℝ≥0∞) * p) := by rw [one_mul]
    _ = 1 / (Fintype.card (GoodArrows R head) : ℝ≥0∞) :=
      ENNReal.mul_div_mul_right 1 _ hp0 hpt

end
end FiniteAvalanches.Wilson.CyclePopping
