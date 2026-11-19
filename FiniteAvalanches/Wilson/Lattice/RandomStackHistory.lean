import FiniteAvalanches.Wilson.Lattice.StackPrefixIndependence

/-! Fresh stack walks after a countable family of disjoint finite histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile Function
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- A countable disjoint family of finite stack histories retains the ordinary
walk law when the next starting point and cursor depend on the history. -/
theorem directionStackLaw_iUnion_prefix_inter_reading
    {ι : Type*} [Countable ι] (head : V → FiniteWired.Direction → V)
    (x : ι → V) (k : ι → Cursor V) (τ : ι → V × ℕ → FiniteWired.Direction)
    (hdis : Pairwise (Disjoint on fun j : ι =>
      {σ : V × ℕ → FiniteWired.Direction | ∀ v i, i < k j v → σ (v, i) = τ j (v, i)}))
    (A : Set WalkDriver) (hA : MeasurableSet A) :
    directionStackLaw V (⋃ j : ι, {σ | (∀ v i, i < k j v → σ (v, i) = τ j (v, i)) ∧
      readingLetter head (x j) (k j) σ ∈ A}) =
    directionStackLaw V (⋃ j : ι, {σ | ∀ v i, i < k j v → σ (v, i) = τ j (v, i)}) *
      walkLaw A := by
  let H : ι → Set (V × ℕ → FiniteWired.Direction) := fun j =>
    {σ | ∀ v i, i < k j v → σ (v, i) = τ j (v, i)}
  let E : ι → Set (V × ℕ → FiniteWired.Direction) := fun j =>
    {σ | (∀ v i, i < k j v → σ (v, i) = τ j (v, i)) ∧
      readingLetter head (x j) (k j) σ ∈ A}
  have hH : ∀ j, MeasurableSet (H j) := by
    intro j
    have he : H j = ⋂ v, ⋂ i : Fin (k j v),
        {σ | σ (v, i.val) = τ j (v, i.val)} := by
      ext σ
      simp only [H, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h v i
        exact h v i.val i.isLt
      · intro h v i hi
        exact h v ⟨i, hi⟩
    rw [he]
    apply MeasurableSet.iInter
    intro v
    apply MeasurableSet.iInter
    intro i
    have hm : Measurable (fun σ : V × ℕ → FiniteWired.Direction => σ (v, i.val)) :=
      measurable_pi_apply _
    exact hm (measurableSet_singleton (τ j (v, i.val)))
  have hE : ∀ j, MeasurableSet (E j) := by
    intro j
    exact (hH j).inter ((measurable_readingDriver V head (x j) (k j)) hA)
  have hdisE : Pairwise (Disjoint on E) := by
    intro i j hij
    exact (hdis hij).mono (fun _ h => h.1) (fun _ h => h.1)
  change directionStackLaw V (⋃ j, E j) = directionStackLaw V (⋃ j, H j) * walkLaw A
  rw [measure_iUnion hdisE hE, measure_iUnion hdis hH, ← ENNReal.tsum_mul_right]
  exact tsum_congr fun j => directionStackLaw_prefix_indep_event V head (x j) (k j) (τ j) A hA

end
end FiniteAvalanches.Wilson.Lattice
