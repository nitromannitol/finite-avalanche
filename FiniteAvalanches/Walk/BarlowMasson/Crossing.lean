import FiniteAvalanches.Walk.BarlowMasson.Basic

/-!
# The Beurling estimate for sets crossing an annulus

A set `A` crosses the annuli `j ≤ |z - y| < j + 1` around `y` for `j₀ ≤ j < j₁` when it meets
each of them. The Beurling estimate of Lawler and Limic (2004), Theorem 1, applied to `A` and
completed by points of the real axis in the other annuli, bounds the probability that the walk
started at `y` reaches distance `2 j₁` from `y` before a positive-time visit to `A` by
`c √(j₀ / j₁)`.

A nearest-neighbour chain crosses every annulus between its two ends (`exists_annulus_of_chain`).

## Main statements

* `beurling_crossing`: the Beurling estimate for a crossing set.
* `exists_annulus_of_chain`: a chain whose distance to `y` changes by at most one at each step
  meets every annulus between its ends.
-/

noncomputable section

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory FiniteAvalanches.Walk.Beurling

/-- The walk from `y` reaches distance `r` from `y` with no visit to `A` at the times
`1, …, t`. -/
def escapesFrom (r : ℝ) (A : Set (Site 2)) (y : Site 2) : Set (ℕ → Dir 2) :=
  {ω | ∃ t, r ≤ euclidNorm (walkPos y ω t - y) ∧ ∀ s, 1 ≤ s → s ≤ t → walkPos y ω s ∉ A}

theorem measurableSet_escapesFrom (r : ℝ) (A : Set (Site 2)) (y : Site 2) :
    MeasurableSet (escapesFrom r A y) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    (measurable_walkPos_pred y (fun z => r ≤ euclidNorm (z - y)) t).and <|
      Measurable.forall fun s =>
        measurable_walkPos_pred y (fun z => 1 ≤ s → s ≤ t → z ∉ A) s

theorem escapesFrom_anti {A A' : Set (Site 2)} (h : A ⊆ A') (r : ℝ) (y : Site 2) :
    escapesFrom r A' y ⊆ escapesFrom r A y :=
  fun _ ⟨t, ht, hs⟩ => ⟨t, ht, fun s h1 h2 hA => hs s h1 h2 (h hA)⟩

theorem escapesFrom_mono {r r' : ℝ} (h : r ≤ r') (A : Set (Site 2)) (y : Site 2) :
    escapesFrom r' A y ⊆ escapesFrom r A y :=
  fun _ ⟨t, ht, hs⟩ => ⟨t, h.trans ht, hs⟩

private theorem euclidNorm_axisPt_nat (j : ℕ) : euclidNorm (axisPt (j : ℤ)) = j := by
  simp [euclidNorm, axisPt, Fin.sum_univ_two]

/-- **The Beurling estimate for a crossing set.** If `A` meets every annulus
`j ≤ |z - y| < j + 1` with `j₀ ≤ j < j₁`, the walk from `y` reaches distance `2 j₁` from `y`
before a positive-time visit to `A` with probability at most `c √(j₀ / j₁)`. -/
theorem beurling_crossing : ∃ c : ℝ, 0 < c ∧ ∀ (A : Set (Site 2)) (y : Site 2) (j₀ j₁ : ℕ),
    0 < j₀ → j₀ < j₁ →
    (∀ j : ℕ, j₀ ≤ j → j < j₁ → ∃ z ∈ A, (j : ℝ) ≤ euclidNorm (z - y) ∧
      euclidNorm (z - y) < j + 1) →
    prob (escapesFrom (2 * j₁) A y) ≤ c * Real.sqrt ((j₀ : ℝ) / j₁) := by
  classical
  obtain ⟨c, hc, h⟩ := lawler_limic_beurling
  refine ⟨c, hc, fun A y j₀ j₁ hj₀ hj hcross => ?_⟩
  set A' : Set (Site 2) := {z | y + z ∈ A ∧ (j₀ : ℝ) ≤ euclidNorm z ∧ euclidNorm z < j₁} ∪
    {z | ∃ j : ℕ, (j < j₀ ∨ j₁ ≤ j) ∧ z = axisPt (j : ℤ)} with hA'
  have hdense : IsDense A' := by
    intro j
    by_cases hj' : j₀ ≤ j ∧ j < j₁
    · obtain ⟨z, hzA, hz1, hz2⟩ := hcross j hj'.1 hj'.2
      refine ⟨z - y, Or.inl ⟨by simpa using hzA, ?_, ?_⟩, hz1, hz2⟩
      · have : (j₀ : ℝ) ≤ j := by exact_mod_cast hj'.1
        linarith
      · have : (j : ℝ) + 1 ≤ j₁ := by exact_mod_cast hj'.2
        linarith
    · refine ⟨axisPt (j : ℤ), Or.inr ⟨j, by omega, rfl⟩, ?_, ?_⟩
      · rw [euclidNorm_axisPt_nat]
      · rw [euclidNorm_axisPt_nat]
        linarith
  have hsub : escapesFrom (2 * j₁) A y ⊆ exitsBefore (2 * j₁) (shellPart A' j₀ j₁) 0 := by
    rintro ω ⟨t, ht, hs⟩
    refine ⟨t, ?_, fun s hs1 hs2 hmem => hs s hs1 hs2 ?_⟩
    · rwa [walkPos_eq_add y, add_sub_cancel_left] at ht
    · obtain ⟨hA'', hk, hn⟩ := hmem
      rw [walkPos_eq_add y]
      rcases hA'' with ⟨hA, -, -⟩ | ⟨j, hj', he⟩
      · exact hA
      · exfalso
        rw [he, euclidNorm_axisPt_nat] at hk hn
        rcases hj' with hj' | hj'
        · have : (j : ℝ) < j₀ := by exact_mod_cast hj'
          linarith
        · have : (j₁ : ℝ) ≤ j := by exact_mod_cast hj'
          linarith
  have hb := h A' hdense j₀ j₁ hj₀ hj
  calc prob (escapesFrom (2 * j₁) A y) ≤ prob (exitsBefore (2 * j₁) (shellPart A' j₀ j₁) 0) :=
        prob_mono hsub
    _ ≤ c * Real.sqrt ((j₀ : ℝ) / j₁) :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) hb

/-- A sequence whose distance to `y` increases by at most one at each step meets every annulus
`j ≤ |z - y| < j + 1` between its distances at the two ends. -/
theorem exists_annulus_of_chain (f : ℕ → Site 2) (y : Site 2) (m : ℕ)
    (hstep : ∀ i < m, euclidNorm (f (i + 1) - y) ≤ euclidNorm (f i - y) + 1) (j : ℕ)
    (h0 : euclidNorm (f 0 - y) < j + 1) (hm : (j : ℝ) ≤ euclidNorm (f m - y)) :
    ∃ i ≤ m, (j : ℝ) ≤ euclidNorm (f i - y) ∧ euclidNorm (f i - y) < j + 1 := by
  classical
  have hex : ∃ i, (j : ℝ) ≤ euclidNorm (f i - y) := ⟨m, hm⟩
  set i := Nat.find hex with hi
  have hspec : (j : ℝ) ≤ euclidNorm (f i - y) := Nat.find_spec hex
  have him : i ≤ m := Nat.find_min' hex hm
  refine ⟨i, him, hspec, ?_⟩
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h]
    exact h0
  · obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hlt : euclidNorm (f i' - y) < j := by
      have := Nat.find_min hex (show i' < i by omega)
      exact not_le.1 this
    have := hstep i' (by omega)
    rw [hi'] at hspec ⊢
    linarith

end FiniteAvalanches.Walk.BarlowMasson
