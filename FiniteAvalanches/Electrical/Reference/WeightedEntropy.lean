import FiniteAvalanches.Electrical.Green.WeightedLog
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Reference
open scoped BigOperators

/-- The finite Jensen entropy bound retains every zero weight and the original
cardinality. This is the canonical weighted-log theorem at parameter two. -/
theorem weighted_log_two_div_le {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hmean : 0 < ∑ i, p i) :
    ∑ i, p i * Real.log (2 / p i) ≤
      (∑ i, p i) * Real.log (2 * (m : ℝ) / (∑ i, p i)) := by
  simpa only [Fintype.card_fin, mul_comm (m : ℝ) 2] using
    WeightedLog.sum_mul_log_div_le_of_sum_pos p hp (θ := 2) (by norm_num) hmean

/-- A checked numerical absorption of the split and arc coefficients. -/
theorem reference_variance_constant (mean L : ℝ) (hmean : 0 ≤ mean) (hL : 0 ≤ L) :
    7 * mean + 23328 * mean * (1 + Real.log 2 + L) ≤
      40000 * mean * (1 + L) := by
  have hlog : Real.log 2 ≤ (7 / 10 : ℝ) := by
    linarith only [Real.log_two_lt_d9]
  have hc : 7 + 23328 * (1 + Real.log 2) ≤ (40000 : ℝ) := by
    linarith only [hlog]
  have hc' := mul_le_mul_of_nonneg_right hc hmean
  have hml := mul_nonneg hmean hL
  nlinarith only [hc', hml]

end FiniteAvalanches.Electrical.Reference
