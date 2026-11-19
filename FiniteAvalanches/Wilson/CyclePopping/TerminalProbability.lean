import FiniteAvalanches.Wilson.CyclePopping.StackProbability

/-! The mass of each cycle-free terminal arrow configuration. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open MeasureTheory ProbabilityTheory Function
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A : V → Type*} [∀ v, MeasurableSpace (A v)]
variable [∀ v, MeasurableSingletonClass (A v)] [∀ v, Fintype (A v)]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Reachability of a fixed cursor is measurable for finite-valued measurable stacks. -/
theorem measurableSet_pop_run (R : Set V) (head : (v : V) → A v → V)
    (k l : Cursor V) (X : (v : V) → ℕ → Ω → A v)
    (hm : ∀ v i, Measurable (X v i)) :
    MeasurableSet {ω | Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l} := by
  let f : Ω → ((p : prefixIndices l) → A p.val.1) := fun ω p => X p.val.1 p.val.2 ω
  have hf : Measurable f := measurable_pi_lambda _ (fun p => hm p.val.1 p.val.2)
  have hs : MeasurableSet (prefixRunEvent R head k l) :=
    (Set.toFinite (prefixRunEvent R head k l)).measurableSet
  have he : f ⁻¹' prefixRunEvent R head k l =
      {ω | Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l} := by
    ext ω
    exact mem_prefixRunEvent_iff R head k l (fun v i => X v i ω)
  rw [← he]
  exact hf hs

omit [Fintype V] [DecidableEq V] [∀ v, MeasurableSpace (A v)]
  [∀ v, MeasurableSingletonClass (A v)]
  [∀ v, Fintype (A v)] in
/-- Selecting cycle-free arrows at a cursor makes that cursor terminal. -/
theorem terminal_of_top_eq (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) (l : Cursor V) (a : (v : V) → A v)
    (ha : ∀ c : Finset V, ¬ IsCycle R (fun v => head v (a v)) c)
    (htop : ∀ v, σ v (l v) = a v) : terminal R head σ l := by
  intro c hc
  apply ha c
  apply hc.congr
  intro v _
  simp only [next, top, htop v]

/-- The masses of cycle-free terminal configurations are a common factor times
the product of their instruction masses. No termination assumption is needed. -/
theorem measure_terminal_top_eq (μ : Measure Ω) (R : Set V)
    (head : (v : V) → A v → V) (k : Cursor V)
    (X : (v : V) → ℕ → Ω → A v)
    (hX : iIndepFun (fun p : V × ℕ => X p.1 p.2) μ)
    (hm : ∀ v i, Measurable (X v i)) (a : (v : V) → A v)
    (ha : ∀ c : Finset V, ¬ IsCycle R (fun v => head v (a v)) c)
    (hid : ∀ v i, μ {ω | X v i ω = a v} = μ {ω | X v 0 ω = a v}) :
    μ {ω | ∃ l : Cursor V,
      Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l ∧
      ∀ v, X v (l v) ω = a v} =
    (∑' l : Cursor V, μ {ω |
      Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l}) *
      ∏ v, μ {ω | X v 0 ω = a v} := by
  let E : Cursor V → Set Ω := fun l => {ω |
    Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l ∧
      ∀ v, X v (l v) ω = a v}
  have hd : Pairwise (Disjoint on E) := by
    intro l m hne
    apply Set.disjoint_left.mpr
    intro ω hωl hωm
    apply hne
    apply terminal_cursor_eq R head (fun v i => X v i ω) hωl.1 hωm.1
    · exact terminal_of_top_eq R head _ l a ha hωl.2
    · exact terminal_of_top_eq R head _ m a ha hωm.2
  have hmeas : ∀ l, MeasurableSet (E l) := by
    intro l
    apply (measurableSet_pop_run R head k l X hm).inter
    have htop : MeasurableSet (⋂ v, {ω | X v (l v) ω = a v}) :=
      MeasurableSet.iInter (fun v => (hm v (l v)) (measurableSet_singleton (a v)))
    have heq : {ω | ∀ v, X v (l v) ω = a v} =
        ⋂ v, {ω | X v (l v) ω = a v} := by ext ω; simp
    change MeasurableSet ({ω : Ω | ∀ v, X v (l v) ω = a v} : Set Ω)
    rw [heq]
    exact htop
  have he : {ω | ∃ l : Cursor V,
      Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l ∧
      ∀ v, X v (l v) ω = a v} = ⋃ l, E l := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E]
  rw [he, measure_iUnion hd hmeas, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro l
  rw [show μ (E l) = μ {ω | Relation.ReflTransGen
      (pop_step R head (fun v i => X v i ω)) k l} *
      μ {ω | ∀ v, X v (l v) ω = a v} from
    measure_pop_run_inter_top μ R head k l X hX hm a]
  congr 1
  rw [measure_top_eq_prod μ l X hX a]
  exact Finset.prod_congr rfl (fun v _ => hid v (l v))

end
end FiniteAvalanches.Wilson.CyclePopping
