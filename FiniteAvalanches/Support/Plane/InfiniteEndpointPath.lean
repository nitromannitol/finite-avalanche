import FiniteAvalanches.Support.Plane.EndpointLocalConnectivity
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Infinite concatenation of shrinking plane paths

A summable family of paths approaching a common endpoint can be concatenated
on successive dyadic time intervals.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Metric Filter
open scoped Topology

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

/-- A dyadic concatenation of paths in geometrically shrinking balls ends at
their common center. -/
theorem endpointPathSeries_one {x : ℝ × ℝ}
    (z : ℕ → ℝ × ℝ) (q : ∀ n, Path (z n) (z (n + 1)))
    (hq : ∀ n, range (q n) ⊆ ball x ((1 / 2 : ℝ) ^ n)) :
    endpointPathSeries z q 1 = x := by
  have hz : ∀ n, dist (z n) x < (1 / 2 : ℝ) ^ n := by
    intro n
    exact hq n (q n).source_mem_range
  have hzlim : Tendsto z atTop (𝓝 x) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hp := (Metric.tendsto_atTop.mp
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))) ε hε
    obtain ⟨N, hN⟩ := hp
    refine ⟨N, fun n hn => ?_⟩
    have hh := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hh
    exact (hz n).trans hh
  have hbound : ∀ n, ‖z (n + 1) - z n‖ ≤ 2 * (1 / 2 : ℝ) ^ n := by
    intro n
    have h1 : dist (z (n + 1)) x < (1 / 2 : ℝ) ^ n :=
      hq n (q n).target_mem_range
    have h2 := hz n
    have h := dist_triangle (z (n + 1)) x (z n)
    rw [dist_comm x (z n), dist_eq_norm] at h
    linarith
  have hsumnorm : Summable (fun n => ‖z (n + 1) - z n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _ ) hbound
    exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 2
  have hsum : HasSum (fun n => z (n + 1) - z n) (x - z 0) := by
    apply (hasSum_iff_tendsto_nat_of_summable_norm hsumnorm).mpr
    simpa only [Finset.sum_range_sub] using hzlim.sub tendsto_const_nhds
  have hterms : ∀ n, (q n).extend (endpointPathClock n 1) - z n = z (n + 1) - z n := by
    intro n
    rw [(q n).extend_of_one_le]
    unfold endpointPathClock
    simp
  simp only [endpointPathSeries, hterms, hsum.tsum_eq]
  abel

end FiniteAvalanches.Electrical.StatementGeometry
