import FiniteAvalanches.Walk.Beurling.ConditionalBeurling
import FiniteAvalanches.Walk.Beurling.HalfLineShift

/-!
# The Beurling estimate for the simple random walk on `ℤ²`

Lawler and Limic (2004), Theorem 1, for the simple random walk on `ℤ²` and `κ = 1`: there is
`c > 0` such that, for every set `A` that meets each annulus `j ≤ |z| < j + 1` and all
`0 < k < n`, the walk started at the origin reaches `|z| ≥ 2 n` before its first positive-time
visit to `A ∩ {k ≤ |z| < n}` with probability at most `c √(k / n)`.

The theorem combines `lawler_limic_beurling_of_shiftedHalfLine` with Proposition 12 (e) for
`j ≤ n`, `exitsBefore_shiftedHalfLine_le`.

G. F. Lawler and V. Limic, *The Beurling estimate for a class of random walks*, Electron. J.
Probab. 9 (2004), Theorem 1.

## Main statements

* `lawler_limic_beurling`: Theorem 1 with `κ = 1`.
-/

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

/-- **Lawler and Limic (2004), Theorem 1**, for the simple random walk on `ℤ²` and `κ = 1`. -/
theorem lawler_limic_beurling :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Set (Site 2), IsDense A → ∀ k n : ℕ, 0 < k → k < n →
      pathLaw 2 (exitsBefore (2 * n) (shellPart A k n) 0) ≤
        ENNReal.ofReal (c * Real.sqrt ((k : ℝ) / n)) :=
  lawler_limic_beurling_of_shiftedHalfLine exitsBefore_shiftedHalfLine_le

end FiniteAvalanches.Walk.Beurling
