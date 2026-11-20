import FiniteAvalanches.Support.Plane.ArcAccess.EndpointLocalConnectivity
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Infinite concatenation of shrinking plane paths

A summable family of paths approaching a common endpoint can be concatenated
on successive dyadic time intervals.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.ArcAccess

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

/-- When earlier clocks have finished and later clocks have not started, the
concatenation equals the current path value. -/
theorem endpointPathSeries_eq_of_clock_bounds
    (z : ℕ → ℝ × ℝ) (q : ∀ n, Path (z n) (z (n + 1))) (n : ℕ) (t : ℝ)
    (hprev : ∀ m < n, 1 ≤ endpointPathClock m t)
    (hnext : ∀ m > n, endpointPathClock m t ≤ 0) :
    endpointPathSeries z q t = (q n).extend (endpointPathClock n t) := by
  have htail : ∀ m ∉ Finset.range (n + 1),
      (q m).extend (endpointPathClock m t) - z m = 0 := by
    intro m hm
    have hnm : n < m := by
      simp only [Finset.mem_range, not_lt] at hm
      omega
    rw [(q m).extend_of_le_zero (hnext m hnm), sub_self]
  rw [endpointPathSeries, tsum_eq_sum htail, Finset.sum_range_succ]
  have hsum : (∑ m ∈ Finset.range n,
      ((q m).extend (endpointPathClock m t) - z m)) = z n - z 0 := by
    calc
      _ = ∑ m ∈ Finset.range n, (z (m + 1) - z m) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [(q m).extend_of_one_le (hprev m (Finset.mem_range.mp hm))]
      _ = z n - z 0 := Finset.sum_range_sub z n
  rw [hsum]
  abel

/-- Every time before one belongs to a dyadic concatenation stage. -/
theorem exists_endpointPathClock_stage {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ n : ℕ, 0 ≤ endpointPathClock n t ∧ endpointPathClock n t ≤ 1 ∧
      (∀ m < n, 1 ≤ endpointPathClock m t) ∧
      ∀ m > n, endpointPathClock m t ≤ 0 := by
  let u : ℝ := 1 - t
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hu0 hu1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hinv : ∀ k : ℕ, (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
    intro k
    rw [← mul_pow]
    norm_num
  have hupper : (2 : ℝ) ^ n * u ≤ 1 := by
    calc
      _ ≤ (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hnhi (by positivity)
      _ = 1 := hinv n
  have hlower : 1 < (2 : ℝ) ^ (n + 1) * u := by
    calc
      1 = (2 : ℝ) ^ (n + 1) * (1 / 2 : ℝ) ^ (n + 1) := (hinv (n + 1)).symm
      _ < (2 : ℝ) ^ (n + 1) * u := mul_lt_mul_of_pos_left hnlo (by positivity)
  have hstep : (2 : ℝ) ^ (n + 1) * u = 2 * ((2 : ℝ) ^ n * u) := by
    rw [pow_succ]
    ring
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · unfold endpointPathClock
    change 0 ≤ 2 - (2 : ℝ) ^ (n + 1) * u
    rw [hstep]
    linarith
  · unfold endpointPathClock
    change 2 - (2 : ℝ) ^ (n + 1) * u ≤ 1
    linarith
  · intro m hm
    have hpow : (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ n :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hmul := mul_le_mul_of_nonneg_right hpow hu0.le
    unfold endpointPathClock
    change 1 ≤ 2 - (2 : ℝ) ^ (m + 1) * u
    linarith
  · intro m hm
    have hpow : (2 : ℝ) ^ (n + 2) ≤ (2 : ℝ) ^ (m + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hmul := mul_le_mul_of_nonneg_right hpow hu0.le
    have hstep' : (2 : ℝ) ^ (n + 2) * u = 2 * ((2 : ℝ) ^ (n + 1) * u) := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      ring
    unfold endpointPathClock
    change 2 - (2 : ℝ) ^ (m + 1) * u ≤ 0
    rw [hstep'] at hmul
    linarith

/-- Each endpoint of a simple plane arc can be reached by a path whose other
points avoid the arc. -/
theorem exists_path_to_arc_endpoint
    {x y : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p) :
    ∃ a : ℝ × ℝ, ∃ q : Path a x, ∀ t : unitInterval, t ≠ 1 → q t ∉ range p := by
  let r : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hr : ∀ n, 0 < r n := fun n => pow_pos (by norm_num) n
  have hrmono : Antitone r := fun _ _ h =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  obtain ⟨z, hz, _, hpaths⟩ := exists_endpoint_paths_in_nested_balls p hp r hr hrmono
  choose q hq using hpaths
  have hqball : ∀ n, range (q n) ⊆ ball x ((1 / 2 : ℝ) ^ n) :=
    fun n => (hq n).trans sdiff_subset
  let Q : Path (z 0) x := {
    toFun := fun t => endpointPathSeries z q t.val
    continuous_toFun := (continuous_endpointPathSeries z q hqball).comp continuous_subtype_val
    source' := endpointPathSeries_zero z q
    target' := endpointPathSeries_one z q hqball }
  refine ⟨z 0, Q, ?_⟩
  intro t ht
  have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
    (fun heq => ht (Subtype.ext heq))
  obtain ⟨n, hn0, hn1, hprev, hnext⟩ := exists_endpointPathClock_stage t.property.1 ht1
  have hstage := endpointPathSeries_eq_of_clock_bounds z q n t.val hprev hnext
  have hmem : (q n).extend (endpointPathClock n t.val) ∈ range (q n) :=
    (q n).extend_range ▸ mem_range_self _
  change endpointPathSeries z q t.val ∉ range p
  rw [hstage]
  exact (hq n hmem).2

end FiniteAvalanches.Electrical.StatementGeometry.ArcAccess
