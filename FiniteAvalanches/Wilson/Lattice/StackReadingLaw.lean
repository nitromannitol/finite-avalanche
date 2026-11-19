import FiniteAvalanches.Wilson.CyclePopping.StackReading
import FiniteAvalanches.Wilson.Lattice.StackLaw

/-! Finite-prefix law of a walk reading independent lattice direction stacks. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory ProbabilityTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable (V : Type*) [DecidableEq V]

/-- Every prescribed prefix of an adaptive stack walk has the ordinary
independent uniform direction probability. -/
theorem directionStackLaw_reading_prefix (head : V → FiniteWired.Direction → V)
    (x : V) (k : Cursor V) (w : ℕ → FiniteWired.Direction) (n : ℕ) :
    directionStackLaw V {σ | ∀ i < n, readingLetter head x k σ i = w i} = (1 / 4 : ℝ≥0∞) ^ n := by
  have he : {σ : V × ℕ → FiniteWired.Direction |
      ∀ i < n, readingLetter head x k σ i = w i} =
      ⋂ i : Fin n, {σ | σ (wordAddress head x k w i.val) = w i.val} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [reading_prefix_iff]
    constructor
    · intro h i
      exact h i.val i.isLt
    · intro h i hi
      exact h ⟨i, hi⟩
  rw [he]
  have hinj : Function.Injective (fun i : Fin n => wordAddress head x k w i.val) := by
    intro i j h
    exact Fin.ext (wordAddress_injective head x k w h)
  have hind : iIndepFun (fun i : Fin n => fun σ : V × ℕ → FiniteWired.Direction =>
      σ (wordAddress head x k w i.val)) (directionStackLaw V) := by
    have hbase : iIndepFun (fun p : V × ℕ =>
        fun σ : V × ℕ → FiniteWired.Direction => σ p) (directionStackLaw V) := by
      exact iIndepFun_infinitePi (X := fun (_ : V × ℕ) (a : FiniteWired.Direction) => a)
        (fun _ => measurable_id)
    exact hbase.precomp hinj
  have hh := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i => {w i.val}) (fun i _ => measurableSet_singleton (w i.val))
  have hp : directionStackLaw V (⋂ i : Fin n,
      {σ | σ (wordAddress head x k w i.val) = w i.val}) =
      ∏ i : Fin n, directionStackLaw V {σ | σ (wordAddress head x k w i.val) = w i.val} := by
    simpa only [Finset.mem_univ, Set.iInter_true, Set.preimage, Set.mem_singleton_iff] using hh
  rw [hp]
  have hcoord (i : Fin n) : directionStackLaw V
      {σ | σ (wordAddress head x k w i.val) = w i.val} = 1 / 4 := by
    simpa only [Prod.mk.eta] using directionStackLaw_eval V
      (wordAddress head x k w i.val).1 (wordAddress head x k w i.val).2 (w i.val)
  simp only [hcoord, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end
end FiniteAvalanches.Wilson.Lattice
