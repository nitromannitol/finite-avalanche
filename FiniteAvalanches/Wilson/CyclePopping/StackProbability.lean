import FiniteAvalanches.Wilson.CyclePopping.StackSplice
import Mathlib.Probability.Independence.Basic

/-! Independence of popped stack instructions and the selected top arrows. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A : V → Type*}

/-- Stack coordinates strictly below a fixed cursor. -/
def prefixIndices (l : Cursor V) : Finset (V × ℕ) :=
  Finset.univ.biUnion fun v => (Finset.range (l v)).image (fun i => (v, i))

/-- Stack coordinates at a fixed cursor. -/
def topIndices (l : Cursor V) : Finset (V × ℕ) :=
  Finset.univ.image fun v => (v, l v)

theorem mem_prefixIndices (l : Cursor V) (v : V) (i : ℕ) :
    (v, i) ∈ prefixIndices l ↔ i < l v := by
  simp [prefixIndices]

theorem mem_topIndices (l : Cursor V) (v : V) (i : ℕ) :
    (v, i) ∈ topIndices l ↔ i = l v := by
  simp [topIndices, eq_comm]

/-- The popped coordinates and terminal coordinates are disjoint. -/
theorem disjoint_prefixIndices_topIndices (l : Cursor V) :
    Disjoint (prefixIndices l) (topIndices l) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨v, i⟩ hi hj
  have hlt := (mem_prefixIndices l v i).mp hi
  have heq := (mem_topIndices l v i).mp hj
  omega

/-- Finite prefix data admitting a legal pop run to the specified cursor. -/
def prefixRunEvent (R : Set V) (head : (v : V) → A v → V) (k l : Cursor V) :
    Set ((p : prefixIndices l) → A p.val.1) :=
  {p | ∃ σ : Stacks A, (∀ q : prefixIndices l, σ q.val.1 q.val.2 = p q) ∧
    Relation.ReflTransGen (pop_step R head σ) k l}

/-- A legal run depends exactly on the stack coordinates below its final cursor. -/
theorem mem_prefixRunEvent_iff (R : Set V) (head : (v : V) → A v → V)
    (k l : Cursor V) (σ : Stacks A) :
    (fun q : prefixIndices l => σ q.val.1 q.val.2) ∈ prefixRunEvent R head k l ↔
      Relation.ReflTransGen (pop_step R head σ) k l := by
  constructor
  · rintro ⟨τ, hτ, hrun⟩
    apply pop_run_congr_below R head hrun
    intro v i hi
    exact hτ ⟨(v, i), (mem_prefixIndices l v i).mpr hi⟩
  · intro hrun
    exact ⟨σ, fun _ => rfl, hrun⟩

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
variable [∀ v, MeasurableSpace (A v)] [∀ v, MeasurableSingletonClass (A v)]
variable [∀ v, Fintype (A v)]

/-- For independent stack entries, the event that a given cursor is reached is
independent of the instructions selected at that cursor. -/
theorem measure_pop_run_inter_top (R : Set V) (head : (v : V) → A v → V)
    (k l : Cursor V) (X : (v : V) → ℕ → Ω → A v)
    (hX : iIndepFun (fun p : V × ℕ => X p.1 p.2) μ)
    (hm : ∀ v i, Measurable (X v i)) (a : (v : V) → A v) :
    μ {ω | Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l ∧
      ∀ v, X v (l v) ω = a v} =
    μ {ω | Relation.ReflTransGen (pop_step R head (fun v i => X v i ω)) k l} *
      μ {ω | ∀ v, X v (l v) ω = a v} := by
  let S := prefixIndices l
  let T := topIndices l
  let f : Ω → ((p : S) → A p.val.1) := fun ω p => X p.val.1 p.val.2 ω
  let g : Ω → ((p : T) → A p.val.1) := fun ω p => X p.val.1 p.val.2 ω
  let P : Set ((p : S) → A p.val.1) := prefixRunEvent R head k l
  let Q : Set ((p : T) → A p.val.1) := {b | ∀ p, b p = a p.val.1}
  have hP : f ⁻¹' P = {ω | Relation.ReflTransGen
      (pop_step R head (fun v i => X v i ω)) k l} := by
    ext ω
    exact mem_prefixRunEvent_iff R head k l (fun v i => X v i ω)
  have hQ : g ⁻¹' Q = {ω | ∀ v, X v (l v) ω = a v} := by
    ext ω
    constructor
    · intro h v
      exact h ⟨(v, l v), (mem_topIndices l v (l v)).mpr rfl⟩
    · intro h p
      obtain ⟨⟨v, i⟩, hp⟩ := p
      have hi := (mem_topIndices l v i).mp hp
      subst i
      exact h v
  have hind := hX.indepFun_finset S T (disjoint_prefixIndices_topIndices l)
    (fun p => hm p.1 p.2)
  have hp : MeasurableSet P := (Set.toFinite P).measurableSet
  have hq : MeasurableSet Q := (Set.toFinite Q).measurableSet
  have he := hind.measure_inter_preimage_eq_mul P Q hp hq
  rw [hP, hQ] at he
  exact he


omit [DecidableEq V] [∀ v, Fintype (A v)] in
/-- A fixed collection of top instructions has the product of its marginal masses. -/
theorem measure_top_eq_prod (l : Cursor V) (X : (v : V) → ℕ → Ω → A v)
    (hX : iIndepFun (fun p : V × ℕ => X p.1 p.2) μ)
    (a : (v : V) → A v) :
    μ {ω | ∀ v, X v (l v) ω = a v} = ∏ v, μ {ω | X v (l v) ω = a v} := by
  have hi : Function.Injective (fun v => (v, l v)) := by
    intro v w h
    exact congrArg Prod.fst h
  have hind := hX.precomp hi
  have h := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun v => {a v}) (fun v _ => measurableSet_singleton (a v))
  simpa only [Finset.mem_univ, Set.iInter_true, Set.preimage, Set.mem_singleton_iff,
    Set.setOf_forall] using h

end
end FiniteAvalanches.Wilson.CyclePopping
