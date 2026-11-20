import FiniteAvalanches.Support.Plane.EndpointLocalConnectivity
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Infinite concatenation of shrinking plane paths

A summable family of paths approaching a common endpoint can be concatenated
on successive dyadic time intervals.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Metric Filter

/-- The parameter of the `n`th path in a dyadic concatenation. -/
def endpointPathClock (n : ℕ) (t : ℝ) : ℝ :=
  2 - 2 ^ (n + 1) * (1 - t)

/-- The series defining a dyadic concatenation of paths. -/
noncomputable def endpointPathSeries (z : ℕ → ℝ × ℝ)
    (q : ∀ n, Path (z n) (z (n + 1))) (t : ℝ) : ℝ × ℝ :=
  z 0 + ∑' n, ((q n).extend (endpointPathClock n t) - z n)

/-- The dyadic concatenation series converges to a continuous function. -/
theorem continuous_endpointPathSeries {x : ℝ × ℝ}
    (z : ℕ → ℝ × ℝ) (q : ∀ n, Path (z n) (z (n + 1)))
    (hq : ∀ n, range (q n) ⊆ ball x ((1 / 2 : ℝ) ^ n)) :
    Continuous (endpointPathSeries z q) := by
  apply continuous_const.add
  apply continuous_tsum (u := fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n)
  · intro n
    exact ((q n).continuous_extend.comp (by unfold endpointPathClock; fun_prop)).sub continuous_const
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 2
  · intro n t
    have hqt : (q n).extend (endpointPathClock n t) ∈ ball x ((1 / 2 : ℝ) ^ n) :=
      hq n ((q n).extend_range ▸ mem_range_self _)
    have hz : z n ∈ ball x ((1 / 2 : ℝ) ^ n) := hq n (q n).source_mem_range
    have hdist := dist_triangle ((q n).extend (endpointPathClock n t)) x (z n)
    rw [mem_ball] at hqt hz
    rw [dist_comm x (z n)] at hdist
    rw [dist_eq_norm] at hdist
    linarith

/-- A dyadic concatenation starts at the first source point. -/
theorem endpointPathSeries_zero (z : ℕ → ℝ × ℝ)
    (q : ∀ n, Path (z n) (z (n + 1))) : endpointPathSeries z q 0 = z 0 := by
  have hzero : ∀ n, (q n).extend (endpointPathClock n 0) - z n = 0 := by
    intro n
    rw [(q n).extend_of_le_zero, sub_self]
    unfold endpointPathClock
    have hpow : (2 : ℝ) ≤ 2 ^ (n + 1) := by
      calc
        (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ) := by norm_num
        _ ≤ (2 : ℝ) ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  simp only [endpointPathSeries, hzero, tsum_zero, add_zero]

end FiniteAvalanches.Electrical.StatementGeometry
