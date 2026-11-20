/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/ConditionalBeurling.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added.
-/
import FiniteAvalanches.Walk.Beurling.MainLarge
import FiniteAvalanches.Walk.Beurling.Main

/-!
# The Beurling estimate from the shifted half-line estimate

Lawler and Limic (2004), Theorem 1, for simple random walk on `ℤ²`, derived from the estimate
`P(τ_n < T_{-j+ℕ}) ≤ C / √(j n)` for `1 ≤ j ≤ n` (their Proposition 12 (e), with `j ≤ n`), which is
taken here as an explicit hypothesis.
-/

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

/-- The Beurling estimate (Lawler-Limic (2004), Theorem 1), assuming the shifted half-line
estimate for `1 ≤ j ≤ n`. -/
theorem lawler_limic_beurling_of_shiftedHalfLine
    (he : ∃ C : ℝ, ∀ j n : ℕ, 1 ≤ j → 1 ≤ n → j ≤ n →
      prob (exitsBefore n (axisSet {i | -(j : ℤ) ≤ i}) 0) ≤ C / Real.sqrt (j * n)) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Set (Site 2), IsDense A → ∀ k n : ℕ, 0 < k → k < n →
      pathLaw 2 (exitsBefore (2 * n) (shellPart A k n) 0) ≤
        ENNReal.ofReal (c * Real.sqrt ((k : ℝ) / n)) :=
  lawler_limic_beurling_of_far_escape (far_escape_minimal_of_shiftedHalfLine he)

end FiniteAvalanches.Walk.Beurling
