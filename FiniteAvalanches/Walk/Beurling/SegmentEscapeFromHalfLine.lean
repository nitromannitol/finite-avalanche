import FiniteAvalanches.Walk.Beurling.HalfLineHitConsequences
import FiniteAvalanches.Walk.Beurling.SegmentEscapeConditional

/-!
# Escape from a segment of the real axis, from the entrance estimate of a shifted half-line

Let `0 ≤ k ≤ n / 2`, let the simple random walk on `ℤ²` start at a point `j` of the segment
`{k, …, n - 1}` of the real axis, and let `m = n⁴`. The probability that the walk reaches the
circle of radius `m` before it returns to the segment is at most
`c / √n * (1 / √(j - k + 1) + 1 / √(n - j + 1)) * (1 / log n)`
(Lawler and Limic, 2004, Lemma 14).

`prob_exitsBefore_segment_le_of_halfLine` derives this estimate from Proposition 12 (d) and (e)
of the same paper, both taken as hypotheses. Part (d) is proved in
`exitsBefore_halfLine_le`, so the statement here keeps only the hypothesis on part (e), in the
range `j ≤ n` in which the conditional statement uses it.

G. F. Lawler and V. Limic, *The Beurling estimate for a class of random walks*, Electron. J.
Probab. 9 (2004), Lemma 14 and Proposition 12.

## Main statements

* `prob_exitsBefore_segment_le_of_shiftedHalfLine`: Lemma 14, given Proposition 12 (e) for
  `j ≤ n`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

/-- **Lawler and Limic (2004), Lemma 14, given Proposition 12 (e) for `j ≤ n`.** Let `0 ≤ k ≤ n / 2`,
`k ≤ j < n` and `m = n⁴`. From the point `(j, 0)` the probability that the walk reaches the circle
of radius `m` before a positive-time visit to the segment `{(i, 0) : k ≤ i < n}` is at most
`c / √n * (1 / √(j - k + 1) + 1 / √(n - j + 1)) * (1 / log n)`.

The hypothesis is Proposition 12 (e) in the range `1 ≤ j ≤ n`: from the origin the walk leaves the
disk of radius `n` before a positive-time visit to `{(i, 0) : i ≥ -j}` with probability at most
`C / √(j n)`. Proposition 12 (d) is `exitsBefore_halfLine_le`. -/
theorem prob_exitsBefore_segment_le_of_shiftedHalfLine
    (he : ∃ C : ℝ, ∀ j n : ℕ, 1 ≤ j → 1 ≤ n → j ≤ n →
      prob (exitsBefore n (axisSet {i | -(j : ℤ) ≤ i}) 0) ≤ C / Real.sqrt (j * n)) :
    ∃ c : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k j : ℕ, k ≤ n / 2 → k ≤ j → j < n →
      prob (exitsBefore ((n : ℝ) ^ 4) (axisSet (Set.Ico (k : ℤ) n)) (axisPt j)) ≤
        c / Real.sqrt n * (1 / Real.sqrt (j - k + 1) + 1 / Real.sqrt (n - j + 1)) *
          (1 / Real.log n) :=
  prob_exitsBefore_segment_le_of_halfLine exitsBefore_halfLine_le he

end FiniteAvalanches.Walk.Beurling
