import FiniteAvalanches.Wilson.CyclePopping.AlmostSureTermination
import Mathlib.Data.Finset.Max

/-! Finite cycle popping with instructions that can move toward the roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section

variable {V : Type*} {A : V → Type*} [∀ v, Nonempty (A v)]

/-- If every nonroot has an instruction decreasing a natural-valued rank,
there is a cycle-free choice of instructions. -/
theorem exists_goodArrows_of_descent (R : Set V) (head : (v : V) → A v → V)
    (rank : V → ℕ) (h : ∀ v, v ∉ R → ∃ a : A v, rank (head v a) < rank v) :
    Nonempty (GoodArrows R head) := by
  let a : (v : V) → A v := fun v =>
    if hv : v ∉ R then Classical.choose (h v hv) else Classical.choice (inferInstance : Nonempty (A v))
  have ha (v : V) (hv : v ∉ R) : rank (head v (a v)) < rank v := by
    simp only [a, dif_pos hv]
    exact Classical.choose_spec (h v hv)
  refine ⟨⟨a, ?_⟩⟩
  intro c hc
  obtain ⟨v, hv, hmin⟩ := c.exists_min_image rank hc.nonempty
  have hlt := ha v (hc.avoids_roots v hv)
  exact (not_lt_of_ge (hmin _ (hc.maps_to v hv))) hlt

variable [Fintype V] [DecidableEq V] [∀ v, MeasurableSpace (A v)]
variable [∀ v, MeasurableSingletonClass (A v)] [∀ v, Fintype (A v)]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [∀ v, MeasurableSpace (A v)] [∀ v, MeasurableSingletonClass (A v)]
  [IsProbabilityMeasure μ] in
/-- Full support and a rank-decreasing route to the roots imply that a
positive-weight cycle-free arrow assignment exists. -/
theorem good_arrow_weight_ne_zero_of_descent (R : Set V) (head : (v : V) → A v → V)
    (X : (v : V) → ℕ → Ω → A v) (rank : V → ℕ)
    (h : ∀ v, v ∉ R → ∃ a : A v, rank (head v a) < rank v)
    (hfull : ∀ v (a : A v), μ {ω | X v 0 ω = a} ≠ 0) :
    (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) ≠ 0 := by
  obtain ⟨a⟩ := exists_goodArrows_of_descent R head rank h
  exact good_arrow_weight_ne_zero μ R head X a (fun v => hfull v (a.val v))

/-- A finite cycle-popping process with independent stationary full-support
instructions terminates almost surely if every nonroot can move down a rank. -/
theorem ae_terminalEvent_of_descent (R : Set V) (head : (v : V) → A v → V)
    (k : Cursor V) (X : (v : V) → ℕ → Ω → A v)
    (hX : iIndepFun (fun p : V × ℕ => X p.1 p.2) μ)
    (hm : ∀ v i, Measurable (X v i))
    (hid : ∀ v i (b : A v), μ {ω | X v i ω = b} = μ {ω | X v 0 ω = b})
    (rank : V → ℕ) (h : ∀ v, v ∉ R → ∃ a : A v, rank (head v a) < rank v)
    (hfull : ∀ v (a : A v), μ {ω | X v 0 ω = a} ≠ 0) :
    ∀ᵐ ω ∂μ, ω ∈ terminalEvent R head k X :=
  ae_terminalEvent μ R head k X hX hm hid
    (good_arrow_weight_ne_zero_of_descent μ R head X rank h hfull)

end
end FiniteAvalanches.Wilson.CyclePopping
