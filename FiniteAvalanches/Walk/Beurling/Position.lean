import FiniteAvalanches.Walk.Beurling.Estimate
import FiniteAvalanches.Wilson.Lattice.BeurlingGeometry

/-!
# The Beurling estimate for the position process of the lattice walk

`lawler_limic_beurling` stated for the position process `position 0 ω` of the walk driven by the
directions `ω`, the form in which the finite-avalanche argument uses it.

## Main statements

* `position_eq_walkPos`: the position process is the walk `walkPos`.
* `lawler_limic_beurling_position`: Lawler and Limic (2004), Theorem 1 with `κ = 1`, for the
  position process.
-/

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice

/-- The position process of the walk driven by `ω` is the walk `walkPos`. -/
theorem position_eq_walkPos (x : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    position x ω t = walkPos x ω t :=
  FiniteAvalanches.External.Beurling.position_sum x ω t

/-- **Lawler and Limic (2004), Theorem 1**, for the position process of the simple random walk
on `ℤ²` and `κ = 1`. -/
theorem lawler_limic_beurling_position :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : Set (Site 2),
        (∀ j : ℕ, ∃ z ∈ A, (j : ℝ) ≤ euclidNorm z ∧ euclidNorm z < (j : ℝ) + 1) →
        ∀ k n : ℕ, 0 < k → k < n →
          pathLaw 2
            {ω | ∃ t : ℕ, 2 * (n : ℝ) ≤ euclidNorm (position 0 ω t) ∧
              ∀ s : ℕ, 1 ≤ s → s ≤ t →
                position 0 ω s ∉ {z | z ∈ A ∧ (k : ℝ) ≤ euclidNorm z ∧ euclidNorm z < n}} ≤
            ENNReal.ofReal (c * Real.sqrt ((k : ℝ) / n)) := by
  obtain ⟨c, hc, h⟩ := lawler_limic_beurling
  refine ⟨c, hc, fun A hA k n hk hkn => ?_⟩
  have hset : {ω : ℕ → Dir 2 | ∃ t : ℕ, 2 * (n : ℝ) ≤ euclidNorm (position 0 ω t) ∧
      ∀ s : ℕ, 1 ≤ s → s ≤ t →
        position 0 ω s ∉ {z | z ∈ A ∧ (k : ℝ) ≤ euclidNorm z ∧ euclidNorm z < n}} =
      exitsBefore (2 * n) (shellPart A k n) 0 := by
    ext ω
    simp only [exitsBefore, shellPart, position_eq_walkPos, Set.mem_setOf_eq]
  rw [hset]
  exact h A hA k n hk hkn

end FiniteAvalanches.Walk.Beurling
