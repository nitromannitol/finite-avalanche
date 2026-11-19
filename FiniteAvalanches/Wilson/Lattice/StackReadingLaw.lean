import FiniteAvalanches.Wilson.CyclePopping.StackReading
import FiniteAvalanches.Wilson.Lattice.StackLaw
import FiniteAvalanches.Wilson.Lattice.PrefixMeasure

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


/-- A prescribed adaptive reading prefix is a measurable stack event. -/
theorem measurableSet_reading_prefix (head : V → FiniteWired.Direction → V)
    (x : V) (k : Cursor V) (w : ℕ → FiniteWired.Direction) (n : ℕ) :
    MeasurableSet {σ : V × ℕ → FiniteWired.Direction |
      ∀ i < n, readingLetter head x k σ i = w i} := by
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
  apply MeasurableSet.iInter
  intro i
  have hm : Measurable (fun σ : V × ℕ → FiniteWired.Direction =>
      σ (wordAddress head x k w i.val)) := measurable_pi_apply _
  exact hm (measurableSet_singleton (w i.val))

/-- Every adaptive stack instruction is measurable. -/
theorem measurable_readingLetter (head : V → FiniteWired.Direction → V)
    (x : V) (k : Cursor V) (n : ℕ) :
    Measurable (fun σ : V × ℕ → FiniteWired.Direction => readingLetter head x k σ n) := by
  apply measurable_to_countable'
  intro d
  let extend : (Fin (n + 1) → FiniteWired.Direction) → ℕ → FiniteWired.Direction :=
    fun p i => if hi : i < n + 1 then p ⟨i, hi⟩ else (0, false)
  have he : (fun σ : V × ℕ → FiniteWired.Direction => readingLetter head x k σ n) ⁻¹' {d} =
      ⋃ p : Fin (n + 1) → FiniteWired.Direction,
        if p ⟨n, Nat.lt_succ_self n⟩ = d then
          {σ | ∀ i < n + 1, readingLetter head x k σ i = extend p i} else ∅ := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
    constructor
    · intro hn
      let p : Fin (n + 1) → FiniteWired.Direction := fun i => readingLetter head x k σ i.val
      refine ⟨p, ?_⟩
      have hp : p ⟨n, Nat.lt_succ_self n⟩ = d := hn
      simp only [hp, if_true, Set.mem_setOf_eq]
      intro i hi
      simp only [extend, dif_pos hi, p]
    · rintro ⟨p, hp⟩
      split_ifs at hp with hpd
      · have hn := hp n (Nat.lt_succ_self n)
        simp only [extend, dif_pos (Nat.lt_succ_self n)] at hn
        exact hn.trans hpd
      · exact hp.elim
  rw [he]
  apply MeasurableSet.iUnion
  intro p
  split_ifs
  · exact measurableSet_reading_prefix V head x k (extend p) (n + 1)
  · exact MeasurableSet.empty

/-- The full driver read from stacks is measurable. -/
theorem measurable_readingDriver (head : V → FiniteWired.Direction → V)
    (x : V) (k : Cursor V) :
    Measurable (fun σ : V × ℕ → FiniteWired.Direction => readingLetter head x k σ) :=
  measurable_pi_lambda _ (fun n => measurable_readingLetter V head x k n)


/-- The ordinary independent direction driver has the same finite-prefix mass. -/
theorem walkLaw_prefix (w : WalkDriver) (n : ℕ) :
    walkLaw {ξ | ∀ i < n, ξ i = w i} = (1 / 4 : ℝ≥0∞) ^ n := by
  have hind : iIndepFun (fun i : Fin n => fun ξ : WalkDriver => ξ i.val) walkLaw := by
    have hb : iIndepFun (fun i : ℕ => fun ξ : WalkDriver => ξ i) walkLaw := by
      exact iIndepFun_infinitePi (X := fun (_ : ℕ) (a : FiniteWired.Direction) => a)
        (fun _ => measurable_id)
    exact hb.precomp Fin.val_injective
  have hh := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i => {w i.val}) (fun i _ => measurableSet_singleton (w i.val))
  have he : {ξ : WalkDriver | ∀ i < n, ξ i = w i} =
      ⋂ i : Fin n, {ξ | ξ i.val = w i.val} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h i
      exact h i.val i.isLt
    · intro h i hi
      exact h ⟨i, hi⟩
  have hp : walkLaw (⋂ i : Fin n, {ξ | ξ i.val = w i.val}) =
      ∏ i : Fin n, walkLaw {ξ | ξ i.val = w i.val} := by
    simpa only [Finset.mem_univ, Set.iInter_true, Set.preimage, Set.mem_singleton_iff] using hh
  rw [he, hp]
  have hcoord (i : Fin n) : walkLaw {ξ | ξ i.val = w i.val} = 1 / 4 := by
    have h := (measurePreserving_eval_infinitePi (fun _ : ℕ => directionLaw) i.val).measure_preimage
      (measurableSet_singleton (w i.val)).nullMeasurableSet
    change walkLaw {ξ | ξ i.val = w i.val} = directionLaw {w i.val} at h
    rw [h, directionLaw, FiniteAvalanches.uniformMeasure_apply]
    simp [Nat.card_eq_fintype_card, FiniteWired.Direction]
  simp only [hcoord, Finset.prod_const, Finset.card_univ, Fintype.card_fin]


/-- Reading a walk chronologically from independent vertex stacks produces
exactly the ordinary independent direction-driver law. -/
theorem directionStackLaw_map_readingDriver (head : V → FiniteWired.Direction → V)
    (x : V) (k : Cursor V) :
    (directionStackLaw V).map (fun σ => readingLetter head x k σ) = walkLaw := by
  have hm := measurable_readingDriver V head x k
  haveI : IsProbabilityMeasure ((directionStackLaw V).map (fun σ => readingLetter head x k σ)) :=
    (directionStackLaw V).isProbabilityMeasure_map hm.aemeasurable
  apply measure_eq_of_prefix_patterns
  intro n w
  have hprefix : MeasurableSet {ξ : WalkDriver | ∀ i < n, ξ i = w i} := by
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
    apply MeasurableSet.iInter
    intro i
    have hi : Measurable (fun ξ : WalkDriver => ξ i.val) := measurable_pi_apply _
    exact hi (measurableSet_singleton (w i.val))
  rw [Measure.map_apply hm hprefix]
  exact (directionStackLaw_reading_prefix V head x k w n).trans (walkLaw_prefix w n).symm

end
end FiniteAvalanches.Wilson.Lattice
