import FiniteAvalanches.Wilson.CyclePopping.TerminalProbability

/-! Normalization of the terminal cycle-popping arrow weights. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open MeasureTheory ProbabilityTheory Function
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A : V → Type*} [∀ v, MeasurableSpace (A v)]
variable [∀ v, MeasurableSingletonClass (A v)] [∀ v, Fintype (A v)]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A terminal arrow assignment contains no directed cycle away from the roots. -/
def GoodArrows (R : Set V) (head : (v : V) → A v → V) :=
  {a : (v : V) → A v // ∀ c : Finset V, ¬ IsCycle R (fun v => head v (a v)) c}

instance (R : Set V) (head : (v : V) → A v → V) : Fintype (GoodArrows R head) := by
  unfold GoodArrows
  infer_instance

/-- The event that some finite legal run reaches a terminal cursor. -/
def terminalEvent (R : Set V) (head : (v : V) → A v → V) (k : Cursor V)
    (X : (v : V) → ℕ → Ω → A v) : Set Ω :=
  {ω | ∃ l, Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l ∧
    terminal R head (fun v i => X v i ω) l}

/-- The event that a finite legal run reaches the given good arrow assignment. -/
def terminalOutputEvent (R : Set V) (head : (v : V) → A v → V) (k : Cursor V)
    (X : (v : V) → ℕ → Ω → A v) (a : GoodArrows R head) : Set Ω :=
  {ω | ∃ l, Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l ∧
    ∀ v, X v (l v) ω = a.val v}

/-- The event of a specified terminal arrow assignment is measurable. -/
theorem measurableSet_terminalOutputEvent (R : Set V) (head : (v : V) → A v → V)
    (k : Cursor V) (X : (v : V) → ℕ → Ω → A v)
    (hm : ∀ v i, Measurable (X v i)) (a : GoodArrows R head) :
    MeasurableSet (terminalOutputEvent R head k X a) := by
  have he : terminalOutputEvent R head k X a = ⋃ l : Cursor V,
      ({ω | Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l} ∩
       ⋂ v, {ω | X v (l v) ω = a.val v}) := by
    ext ω
    simp only [terminalOutputEvent, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter]
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  exact (measurableSet_pop_run R head k l X hm).inter
    (MeasurableSet.iInter fun v => (hm v (l v)) (measurableSet_singleton (a.val v)))

omit [Fintype V] [∀ v, MeasurableSpace (A v)] [∀ v, MeasurableSingletonClass (A v)]
  [∀ v, Fintype (A v)] [MeasurableSpace Ω] in
/-- Distinct good arrow assignments have disjoint terminal output events. -/
theorem disjoint_terminalOutputEvent (R : Set V) (head : (v : V) → A v → V)
    (k : Cursor V) (X : (v : V) → ℕ → Ω → A v) :
    Pairwise (Disjoint on terminalOutputEvent R head k X) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro ω hωa hωb
  obtain ⟨l, hl, hla⟩ := hωa
  obtain ⟨m, hm, hmb⟩ := hωb
  have he : l = m := terminal_cursor_eq R head (fun v i => X v i ω) hl hm
    (terminal_of_top_eq R head _ l a.val a.property hla)
    (terminal_of_top_eq R head _ m b.val b.property hmb)
  subst m
  apply hab
  apply Subtype.ext
  funext v
  exact (hla v).symm.trans (hmb v)

omit [Fintype V] [∀ v, MeasurableSpace (A v)] [∀ v, MeasurableSingletonClass (A v)]
  [∀ v, Fintype (A v)] [MeasurableSpace Ω] in
/-- Terminality is partitioned by the resulting good arrow assignment. -/
theorem terminalEvent_eq_iUnion (R : Set V) (head : (v : V) → A v → V)
    (k : Cursor V) (X : (v : V) → ℕ → Ω → A v) :
    terminalEvent R head k X = ⋃ a : GoodArrows R head, terminalOutputEvent R head k X a := by
  ext ω
  simp only [terminalEvent, terminalOutputEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨l, hl, ht⟩
    let a : (v : V) → A v := fun v => X v (l v) ω
    have ha : ∀ c : Finset V, ¬ IsCycle R (fun v => head v (a v)) c := ht
    exact ⟨⟨a, ha⟩, l, hl, fun _ => rfl⟩
  · rintro ⟨a, l, hl, htop⟩
    exact ⟨l, hl, terminal_of_top_eq R head _ l a.val a.property htop⟩

/-- Total terminal mass is the common cycle-popping factor times the total
product weight of all cycle-free arrow assignments. -/
theorem measure_terminalEvent_eq (μ : Measure Ω) (R : Set V)
    (head : (v : V) → A v → V) (k : Cursor V)
    (X : (v : V) → ℕ → Ω → A v)
    (hX : iIndepFun (fun p : V × ℕ => X p.1 p.2) μ)
    (hm : ∀ v i, Measurable (X v i))
    (hid : ∀ v i (b : A v), μ {ω | X v i ω = b} = μ {ω | X v 0 ω = b}) :
    μ (terminalEvent R head k X) =
      (∑' l : Cursor V, μ {ω |
        Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l}) *
      ∑ a : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = a.val v} := by
  rw [terminalEvent_eq_iUnion R head k X,
    measure_iUnion (disjoint_terminalOutputEvent R head k X)
      (measurableSet_terminalOutputEvent R head k X hm), tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact measure_terminal_top_eq μ R head k X hX hm a.val a.property
    (fun v i => hid v i (a.val v))


/-- The terminal output mass has the same relative weights as the independent
initial arrow assignment, even when termination has mass less than one. -/
theorem measure_terminalOutput_mul_weight (μ : Measure Ω) (R : Set V)
    (head : (v : V) → A v → V) (k : Cursor V)
    (X : (v : V) → ℕ → Ω → A v)
    (hX : iIndepFun (fun p : V × ℕ => X p.1 p.2) μ)
    (hm : ∀ v i, Measurable (X v i))
    (hid : ∀ v i (b : A v), μ {ω | X v i ω = b} = μ {ω | X v 0 ω = b})
    (a : GoodArrows R head) :
    μ (terminalOutputEvent R head k X a) *
      (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) =
    μ (terminalEvent R head k X) * ∏ v, μ {ω | X v 0 ω = a.val v} := by
  rw [measure_terminalEvent_eq μ R head k X hX hm hid]
  change μ {ω | ∃ l : Cursor V,
      Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l ∧
      ∀ v, X v (l v) ω = a.val v} * _ = _
  rw [measure_terminal_top_eq μ R head k X hX hm a.val a.property
    (fun v i => hid v i (a.val v))]
  ac_rfl

/-- Almost-sure termination gives the normalized product law on good arrows. -/
theorem measure_terminalOutput_eq (μ : Measure Ω) (R : Set V)
    (head : (v : V) → A v → V) (k : Cursor V)
    (X : (v : V) → ℕ → Ω → A v)
    (hX : iIndepFun (fun p : V × ℕ => X p.1 p.2) μ)
    (hm : ∀ v i, Measurable (X v i))
    (hid : ∀ v i (b : A v), μ {ω | X v i ω = b} = μ {ω | X v 0 ω = b})
    (hterm : μ (terminalEvent R head k X) = 1)
    (hpos : (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) ≠ 0)
    (hfinite : (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) ≠ ⊤)
    (a : GoodArrows R head) :
    μ (terminalOutputEvent R head k X a) =
      (∏ v, μ {ω | X v 0 ω = a.val v}) /
        (∑ b : GoodArrows R head, ∏ v, μ {ω | X v 0 ω = b.val v}) := by
  apply (ENNReal.eq_div_iff hpos hfinite).mpr
  have h := measure_terminalOutput_mul_weight μ R head k X hX hm hid a
  rw [hterm, one_mul] at h
  simpa only [mul_comm] using h

end
end FiniteAvalanches.Wilson.CyclePopping
