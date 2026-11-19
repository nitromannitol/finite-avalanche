import FiniteAvalanches.Wilson.Lattice.StackReadingLaw
import FiniteAvalanches.Wilson.CyclePopping.StackProbability

/-! A stack-walk prefix is independent of fixed previously consumed prefixes. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory ProbabilityTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- The directions read from a deterministic cursor are independent of all
prescribed stack entries below that cursor. -/
theorem directionStackLaw_prefix_inter_reading (head : V → FiniteWired.Direction → V)
    (x : V) (k : Cursor V) (τ : V × ℕ → FiniteWired.Direction)
    (w : ℕ → FiniteWired.Direction) (n : ℕ) :
    directionStackLaw V {σ | (∀ v i, i < k v → σ (v, i) = τ (v, i)) ∧
      ∀ i < n, readingLetter head x k σ i = w i} =
    directionStackLaw V {σ | ∀ v i, i < k v → σ (v, i) = τ (v, i)} * (1 / 4 : ℝ≥0∞) ^ n := by
  let P := prefixIndices k
  let T := (Finset.range n).image (wordAddress head x k w)
  have hdis : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro q hqP hqT
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hqT
    have hlt := (mem_prefixIndices k _ _).mp hqP
    have hge := wordAddress_depth_ge head x k w i
    change (wordState head x k w i).2 (wordState head x k w i).1 <
      k (wordState head x k w i).1 at hlt
    change k (wordState head x k w i).1 ≤
      (wordState head x k w i).2 (wordState head x k w i).1 at hge
    exact (Nat.not_lt_of_ge hge) hlt
  let f : (V × ℕ → FiniteWired.Direction) → (P → FiniteWired.Direction) :=
    fun σ q => σ q.val
  let g : (V × ℕ → FiniteWired.Direction) → (T → FiniteWired.Direction) :=
    fun σ q => σ q.val
  let A : Set (P → FiniteWired.Direction) := {fun q => τ q.val}
  let B : Set (T → FiniteWired.Direction) := {b | ∀ (i : Fin n),
    b ⟨wordAddress head x k w i.val, Finset.mem_image.mpr
      ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩⟩ = w i.val}
  have hA : f ⁻¹' A = {σ | ∀ v i, i < k v → σ (v, i) = τ (v, i)} := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h v i hi
      exact congrFun h ⟨(v, i), (mem_prefixIndices k v i).mpr hi⟩
    · intro h
      funext q
      obtain ⟨⟨v, i⟩, hq⟩ := q
      exact h v i ((mem_prefixIndices k v i).mp hq)
  have hB : g ⁻¹' B = {σ | ∀ i < n, readingLetter head x k σ i = w i} := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [reading_prefix_iff]
    constructor
    · intro h i hi
      exact h ⟨i, hi⟩
    · intro h i
      exact h i.val i.isLt
  have hbase : iIndepFun (fun q : V × ℕ =>
      fun σ : V × ℕ → FiniteWired.Direction => σ q) (directionStackLaw V) := by
    exact iIndepFun_infinitePi (X := fun (_ : V × ℕ) (d : FiniteWired.Direction) => d)
      (fun _ => measurable_id)
  have hind := hbase.indepFun_finset P T hdis (fun q => measurable_pi_apply q)
  have hmA : MeasurableSet A := measurableSet_singleton _
  have hmB : MeasurableSet B := (Set.toFinite B).measurableSet
  have he := hind.measure_inter_preimage_eq_mul A B hmA hmB
  rw [hA, hB, directionStackLaw_reading_prefix] at he
  exact he


/-- Conditioned on a fixed finite stack-prefix history, the next adaptively
read driver has the ordinary independent walk law. -/
theorem directionStackLaw_restrict_prefix_map (head : V → FiniteWired.Direction → V)
    (x : V) (k : Cursor V) (τ : V × ℕ → FiniteWired.Direction) :
    ((directionStackLaw V).restrict {σ | ∀ v i, i < k v → σ (v, i) = τ (v, i)}).map
        (fun σ => readingLetter head x k σ) =
      (directionStackLaw V {σ | ∀ v i, i < k v → σ (v, i) = τ (v, i)}) • walkLaw := by
  let H : Set (V × ℕ → FiniteWired.Direction) :=
    {σ | ∀ v i, i < k v → σ (v, i) = τ (v, i)}
  have hm := measurable_readingDriver V head x k
  haveI : IsFiniteMeasure (((directionStackLaw V).restrict H).map
      (fun σ => readingLetter head x k σ)) :=
    ((directionStackLaw V).restrict H).isFiniteMeasure_map _
  apply measure_eq_of_prefix_patterns
  intro n w
  have hw : MeasurableSet {ξ : WalkDriver | ∀ i < n, ξ i = w i} := by
    have he : {ξ : WalkDriver | ∀ i < n, ξ i = w i} =
        ⋂ i : Fin n, {ξ | ξ i.val = w i.val} := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h i
        exact h i.val i.isLt
      · intro h i hi
        exact h ⟨i, hi⟩
    rw [he]
    exact MeasurableSet.iInter fun i =>
      (show Measurable (fun ξ : WalkDriver => ξ i.val) from measurable_pi_apply _)
        (measurableSet_singleton (w i.val))
  rw [Measure.map_apply hm hw, Measure.restrict_apply (hm hw), Measure.smul_apply, smul_eq_mul,
    walkLaw_prefix]
  have heq : (fun σ : V × ℕ → FiniteWired.Direction => readingLetter head x k σ) ⁻¹'
        {ξ : WalkDriver | ∀ i < n, ξ i = w i} ∩ H =
      {σ | (∀ v i, i < k v → σ (v, i) = τ (v, i)) ∧
        ∀ i < n, readingLetter head x k σ i = w i} := by
    ext σ
    simp only [H, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, and_comm]
  rw [heq]
  exact directionStackLaw_prefix_inter_reading V head x k τ w n


/-- Every measurable event of the next read driver is independent of a fixed
finite stack-prefix history. -/
theorem directionStackLaw_prefix_indep_event (head : V → FiniteWired.Direction → V)
    (x : V) (k : Cursor V) (τ : V × ℕ → FiniteWired.Direction)
    (A : Set WalkDriver) (hA : MeasurableSet A) :
    directionStackLaw V {σ | (∀ v i, i < k v → σ (v, i) = τ (v, i)) ∧
      readingLetter head x k σ ∈ A} =
    directionStackLaw V {σ | ∀ v i, i < k v → σ (v, i) = τ (v, i)} * walkLaw A := by
  let H : Set (V × ℕ → FiniteWired.Direction) :=
    {σ | ∀ v i, i < k v → σ (v, i) = τ (v, i)}
  let f : (V × ℕ → FiniteWired.Direction) → WalkDriver :=
    fun σ => readingLetter head x k σ
  have hm : Measurable f := measurable_readingDriver V head x k
  have h := congrArg (fun μ : Measure WalkDriver => μ A)
    (directionStackLaw_restrict_prefix_map V head x k τ)
  change ((directionStackLaw V).restrict H).map f A = _ at h
  rw [Measure.map_apply hm hA, Measure.restrict_apply (hm hA), Measure.smul_apply, smul_eq_mul] at h
  have he : {σ | (∀ v i, i < k v → σ (v, i) = τ (v, i)) ∧
      readingLetter head x k σ ∈ A} = f ⁻¹' A ∩ H := by
    ext σ
    simp only [H, f, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff, and_comm]
  rw [he]
  exact h

end
end FiniteAvalanches.Wilson.Lattice
