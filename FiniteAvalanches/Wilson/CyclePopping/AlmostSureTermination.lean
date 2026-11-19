import FiniteAvalanches.Wilson.CyclePopping.TerminalNormalization
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Preorder.Finite

/-! Almost-sure termination of finite cycle popping from a positive terminal weight. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V] {A : V → Type*}

/-- If only finitely many cursors are reachable, a terminal cursor is reachable. -/
theorem exists_terminal_run_of_finite (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (k : Cursor V)
    (hfin : {l | Relation.ReflTransGen (pop_step R head σ) k l}.Finite) :
    ∃ l, Relation.ReflTransGen (pop_step R head σ) k l ∧ terminal R head σ l := by
  obtain ⟨l, hl, hmax⟩ := hfin.exists_maximal ⟨k, Relation.ReflTransGen.refl⟩
  refine ⟨l, hl, ?_⟩
  intro c hc
  have hrun : Relation.ReflTransGen (pop_step R head σ) k (pop l c) :=
    hl.tail ⟨c, hc, rfl⟩
  have hle : pop l c ≤ l := hmax hrun (le_pop l c)
  obtain ⟨v, hv⟩ := hc.nonempty
  have hvle := hle v
  rw [pop_apply_of_mem l c hv] at hvle
  exact Nat.not_succ_le_self (l v) hvle

variable [Fintype V] [∀ v, MeasurableSpace (A v)]
variable [∀ v, MeasurableSingletonClass (A v)] [∀ v, Fintype (A v)]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A positive total weight of cycle-free arrows implies almost-sure termination
of legal cycle popping. -/
theorem ae_terminalEvent (R : Set V) (head : (v : V) → A v → V)
    (k : Cursor V) (X : (v : V) → ℕ → Ω → A v)
    (hX : iIndepFun (fun p : V × ℕ => X p.1 p.2) μ)
    (hm : ∀ v i, Measurable (X v i))
    (hid : ∀ v i (b : A v), μ {ω | X v i ω = b} = μ {ω | X v 0 ω = b})
    (hpos : (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) ≠ 0) :
    ∀ᵐ ω ∂μ, ω ∈ terminalEvent R head k X := by
  have hmul :
      (∑' l : Cursor V, μ {ω |
        Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l}) *
      (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) ≠ ⊤ := by
    rw [← measure_terminalEvent_eq μ R head k X hX hm hid]
    exact measure_ne_top μ _
  have hsum : (∑' l : Cursor V, μ {ω |
      Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l}) ≠ ⊤ :=
    ne_of_lt (ENNReal.lt_top_of_mul_ne_top_left hmul hpos)
  have hfin := ae_finite_setOf_mem hsum
  filter_upwards [hfin] with ω hω
  exact exists_terminal_run_of_finite R head (fun v i => X v i ω) k hω

omit [∀ v, MeasurableSpace (A v)] [∀ v, MeasurableSingletonClass (A v)] in
/-- The total initial weight of good arrows is finite under any probability law. -/
theorem good_arrow_weight_ne_top (R : Set V) (head : (v : V) → A v → V)
    (X : (v : V) → ℕ → Ω → A v) :
    (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro b _
  apply ENNReal.prod_ne_top
  intro v _
  exact measure_ne_top μ _

omit [∀ v, MeasurableSpace (A v)] [∀ v, MeasurableSingletonClass (A v)]
  [IsProbabilityMeasure μ] in
/-- One good arrow assignment of positive product weight makes the total weight positive. -/
theorem good_arrow_weight_ne_zero (R : Set V) (head : (v : V) → A v → V)
    (X : (v : V) → ℕ → Ω → A v) (a : GoodArrows R head)
    (ha : ∀ v, μ {ω | X v 0 ω = a.val v} ≠ 0) :
    (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) ≠ 0 := by
  have hprod : (∏ v, μ {ω | X v 0 ω = a.val v}) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    exact fun v _ => ha v
  have hle : (∏ v, μ {ω | X v 0 ω = a.val v}) ≤
      ∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v} :=
    Finset.single_le_sum (f := fun b : GoodArrows R head =>
      ∏ v, μ {ω | X v 0 ω = b.val v}) (fun _ _ => bot_le) (Finset.mem_univ a)
  intro hz
  rw [hz] at hle
  exact hprod (nonpos_iff_eq_zero.mp hle)

/-- With positive good-arrow weight, cycle popping has the normalized product law. -/
theorem measure_terminalOutput_eq_of_positive_weight (R : Set V)
    (head : (v : V) → A v → V) (k : Cursor V)
    (X : (v : V) → ℕ → Ω → A v)
    (hX : iIndepFun (fun p : V × ℕ => X p.1 p.2) μ)
    (hm : ∀ v i, Measurable (X v i))
    (hid : ∀ v i (b : A v), μ {ω | X v i ω = b} = μ {ω | X v 0 ω = b})
    (hpos : (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) ≠ 0)
    (a : GoodArrows R head) :
    μ (terminalOutputEvent R head k X a) =
      (∏ v, μ {ω | X v 0 ω = a.val v}) /
        (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) := by
  have ht : MeasurableSet (terminalEvent R head k X) := by
    rw [terminalEvent_eq_iUnion R head k X]
    exact MeasurableSet.iUnion (measurableSet_terminalOutputEvent R head k X hm)
  have hterm : μ (terminalEvent R head k X) = 1 :=
    (mem_ae_iff_prob_eq_one ht).mp (ae_terminalEvent μ R head k X hX hm hid hpos)
  exact measure_terminalOutput_eq μ R head k X hX hm hid hterm hpos
    (good_arrow_weight_ne_top μ R head X) a

end
end FiniteAvalanches.Wilson.CyclePopping
