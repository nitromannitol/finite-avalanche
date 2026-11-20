import FiniteAvalanches.Walk.Beurling.DiskGreenBasic
import FiniteAvalanches.Walk.Beurling.GreenPotential

/-!
# Asymptotics of the Green function of a disk

For the simple random walk on `ℤ²` and the disk `C_n = {z : |z| < n}`, the Green function
`G_n = green n` (the expected number of visits before leaving `C_n`) satisfies
`(π/2) G_n(0, z) = log n - log |z| + O(|z|⁻¹ + n^{-1/3})` for `0 < |z| < n` and
`(π/2) G_n(0, 0) = log n + O(1)` (Lawler and Limic (2004), Lemma 3).

By symmetry `G_n(0, z) = G_n(z, 0)`, and `G_n(z, 0) = E^z[a(S_τ)] - a(z)` with the potential
kernel `a` and the exit time `τ` of `C_n` (`killedGreenReal_eq_potentialKernel`). The planar
asymptotics `a(x) = (2/π) log |x| + κ + O(|x|⁻²)` (`exists_abs_potentialKernel_sub_log_le`) and
the bound `n ≤ |S_τ| < n + 1`, which holds because one step changes the Euclidean norm by at
most one, give the result.

## Main results

* `FiniteAvalanches.Walk.Beurling.green_asymptotics`: Lawler and Limic (2004), Lemma 3, the estimates of
  `G_n(0, z)` and `G_n(0, 0)` for the simple random walk.
-/

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

private theorem mem_diskFinset_iff {r : ℝ} {y : Site 2} :
    y ∈ diskFinset r ↔ euclidNorm y < r := by
  rw [diskFinset, Finset.mem_filter, mem_ballFinset_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

private theorem measurable_exitIdx (B : Finset (Site 2)) (w : Site 2) :
    Measurable (exitIdx B w) := by
  refine measurable_to_countable' fun n => ?_
  have he : exitIdx B w ⁻¹' {n} =
      {ω | (walkPos w ω n ∉ B ∧ ∀ k, k < n → walkPos w ω k ∈ B) ∨
        (n = 0 ∧ ∀ t, walkPos w ω t ∈ B)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    unfold exitIdx
    split_ifs with h
    · rw [Nat.find_eq_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact Or.inl ⟨h1, fun k hk => not_not.1 (h2 k hk)⟩
      · rintro (⟨h1, h2⟩ | ⟨-, h3⟩)
        · exact ⟨h1, fun k hk => not_not.2 (h2 k hk)⟩
        · obtain ⟨t, ht⟩ := h
          exact absurd (h3 t) ht
    · push Not at h
      constructor
      · rintro rfl
        exact Or.inr ⟨rfl, h⟩
      · rintro (⟨h1, -⟩ | ⟨rfl, -⟩)
        · exact absurd (h n) h1
        · rfl
  rw [he]
  exact measurableSet_setOf.2 (((measurable_walkPos_pred w (· ∉ B) n).and
    (Measurable.forall fun k => measurable_walkPos_pred w (fun y => k < n → y ∈ B) k)).or
    (measurable_const.and (Measurable.forall fun t => measurable_walkPos_pred w (· ∈ B) t)))

private theorem measurable_walkPos_exitIdx (B : Finset (Site 2)) (w : Site 2) :
    Measurable fun ω => walkPos w ω (exitIdx B w ω) :=
  (measurable_from_prod_countable_left (f := fun p : (ℕ → Dir 2) × ℕ => walkPos w p.1 p.2)
    fun t => measurable_walkPos w t).comp (measurable_id.prodMk (measurable_exitIdx B w))

/-- The walk leaves the finite set `B` almost surely. -/
private theorem ae_exists_walkPos_notMem (B : Finset (Site 2)) (w : Site 2) :
    ∀ᵐ ω ∂pathLaw 2, ∃ t, walkPos w ω t ∉ B := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) B
  have hm : MeasurableSet
      {ξ : ℕ → Dir 2 | ∃ n : ℕ, w + ∑ j ∈ Finset.range n, dirVec (ξ j) = q} :=
    measurableSet_setOf.2 (Measurable.exists fun n => measurable_walkPos_pred w (· = q) n)
  have h : ∀ᵐ ξ ∂pathLaw 2, ∃ n : ℕ, w + ∑ j ∈ Finset.range n, dirVec (ξ j) = q :=
    (mem_ae_iff_prob_eq_one hm).2 (pathLaw_two_dim_hit_site w q)
  filter_upwards [h] with ξ hξ
  obtain ⟨n, hn⟩ := hξ
  refine ⟨n, ?_⟩
  rw [walkPos, hn]
  exact hq

private theorem exitIdx_spec {B : Finset (Site 2)} {w : Site 2} {ω : ℕ → Dir 2}
    (h : ∃ t, walkPos w ω t ∉ B) :
    walkPos w ω (exitIdx B w ω) ∉ B ∧ ∀ j < exitIdx B w ω, walkPos w ω j ∈ B := by
  unfold exitIdx
  split_ifs
  exact ⟨Nat.find_spec h, fun j hj => not_not.1 (Nat.find_min h hj)⟩

/-- A walk started in `C_r` leaves it at a site `x` with `r ≤ |x| < r + 1`. -/
private theorem exit_mem_annulus {r : ℝ} {w : Site 2} (hw : w ∈ diskFinset r)
    {ω : ℕ → Dir 2} (h : ∃ t, walkPos w ω t ∉ diskFinset r) :
    r ≤ euclidNorm (walkPos w ω (exitIdx (diskFinset r) w ω)) ∧
      euclidNorm (walkPos w ω (exitIdx (diskFinset r) w ω)) < r + 1 := by
  obtain ⟨hout, hmin⟩ := exitIdx_spec h
  refine ⟨not_lt.1 fun hlt => hout (mem_diskFinset_iff.2 hlt), ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, exitIdx (diskFinset r) w ω = m + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => hout ?_
    rw [h0]
    simpa [walkPos] using hw
  have hin := mem_diskFinset_iff.1 (hmin m (by omega))
  rw [hm]
  exact (euclidNorm_walkPos_succ_le w ω m).trans_lt (by linarith)

/-- The planar potential kernel asymptotics in the form
`|(π/2) a(x) - (log |x| + (π/2) κ)| ≤ K / |x|` for every `x ≠ 0`. -/
private theorem exists_abs_potentialKernel_sub_log_le_div :
    ∃ κ K : ℝ, 0 ≤ K ∧ ∀ x : Site 2, x ≠ 0 →
      |Real.pi / 2 * potentialKernel x - (Real.log (euclidNorm x) + Real.pi / 2 * κ)|
        ≤ K / euclidNorm x := by
  obtain ⟨κ, C, R, hR, hC⟩ := exists_abs_potentialKernel_sub_log_le
  set M := ∑ y ∈ ballFinset 2 R,
    |Real.pi / 2 * potentialKernel y - (Real.log (euclidNorm y) + Real.pi / 2 * κ)| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hR0 : 0 < R := by linarith
  refine ⟨κ, Real.pi / 2 * |C| + M * R, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < euclidNorm x := ContinuousTime.euclidNorm_pos hx
  have hpi : 0 < Real.pi / 2 := by positivity
  rcases le_or_gt R (euclidNorm x) with hRx | hRx
  · have hx1 : 1 ≤ euclidNorm x := hR.trans hRx
    have hpow : euclidNorm x ^ (-2 : ℝ) ≤ 1 / euclidNorm x := by
      rw [Real.rpow_neg hx0.le, Real.rpow_two, one_div]
      exact inv_anti₀ hx0 (by nlinarith)
    have heq : Real.pi / 2 * potentialKernel x - (Real.log (euclidNorm x) + Real.pi / 2 * κ) =
        Real.pi / 2 * (potentialKernel x - (2 / Real.pi * Real.log (euclidNorm x) + κ)) := by
      field_simp
    calc |Real.pi / 2 * potentialKernel x - (Real.log (euclidNorm x) + Real.pi / 2 * κ)|
        = Real.pi / 2 * |potentialKernel x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| := by
          rw [heq, abs_mul, abs_of_pos hpi]
      _ ≤ Real.pi / 2 * (|C| * (1 / euclidNorm x)) := by
          gcongr
          exact (hC x hRx).trans ((mul_le_mul_of_nonneg_right (le_abs_self C)
            (Real.rpow_nonneg hx0.le _)).trans (mul_le_mul_of_nonneg_left hpow (abs_nonneg C)))
      _ ≤ (Real.pi / 2 * |C| + M * R) / euclidNorm x := by
          rw [← mul_assoc, ← div_eq_mul_one_div]
          gcongr
          nlinarith
  · have hmem : x ∈ ballFinset 2 R := mem_ballFinset_iff.2 hRx.le
    have h1 : |Real.pi / 2 * potentialKernel x - (Real.log (euclidNorm x) + Real.pi / 2 * κ)|
        ≤ M :=
      Finset.single_le_sum (f := fun y =>
        |Real.pi / 2 * potentialKernel y - (Real.log (euclidNorm y) + Real.pi / 2 * κ)|)
        (fun _ _ => abs_nonneg _) hmem
    refine h1.trans ?_
    rw [le_div_iff₀ hx0]
    nlinarith [abs_nonneg C]

/-- The exit term: `|(π/2) E^w[a(S_τ)] - (log r + (π/2) κ)| ≤ (K + 1) / r` for the exit time
`τ` of `C_r` and every `w ∈ C_r`. -/
private theorem abs_integral_exit_sub_log_le {κ K : ℝ} (hK : 0 ≤ K)
    (hpk : ∀ x : Site 2, x ≠ 0 →
      |Real.pi / 2 * potentialKernel x - (Real.log (euclidNorm x) + Real.pi / 2 * κ)|
        ≤ K / euclidNorm x)
    {r : ℝ} (hr : 0 < r) {w : Site 2} (hw : w ∈ diskFinset r) :
    |Real.pi / 2 * ∫ ω, potentialKernel (walkPos w ω (exitIdx (diskFinset r) w ω)) ∂pathLaw 2
      - (Real.log r + Real.pi / 2 * κ)| ≤ (K + 1) / r := by
  set c := Real.log r + Real.pi / 2 * κ with hc
  set g := fun ω => potentialKernel (walkPos w ω (exitIdx (diskFinset r) w ω)) with hg
  have hpi : 0 < Real.pi / 2 := by positivity
  have hbound : ∀ᵐ ω ∂pathLaw 2, ‖Real.pi / 2 * g ω - c‖ ≤ (K + 1) / r := by
    filter_upwards [ae_exists_walkPos_notMem (diskFinset r) w] with ω hω
    obtain ⟨h1, h2⟩ := exit_mem_annulus hw hω
    set x := walkPos w ω (exitIdx (diskFinset r) w ω) with hx
    have hx0 : 0 < euclidNorm x := hr.trans_le h1
    have hxne : x ≠ 0 := by
      intro h
      rw [h, euclidNorm_zero] at hx0
      exact lt_irrefl _ hx0
    have hlog0 : 0 ≤ Real.log (euclidNorm x) - Real.log r :=
      sub_nonneg.2 (Real.log_le_log hr h1)
    have hlog1 : Real.log (euclidNorm x) - Real.log r ≤ 1 / r := by
      rw [← Real.log_div hx0.ne' hr.ne']
      calc Real.log (euclidNorm x / r) ≤ euclidNorm x / r - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
        _ ≤ 1 / r := by
            rw [div_sub_one hr.ne']
            exact div_le_div_of_nonneg_right (by linarith) hr.le
    have hK' : K / euclidNorm x ≤ K / r := div_le_div_of_nonneg_left hK hr h1
    have hax := hpk x hxne
    rw [Real.norm_eq_abs]
    calc |Real.pi / 2 * g ω - c|
        = |(Real.pi / 2 * potentialKernel x - (Real.log (euclidNorm x) + Real.pi / 2 * κ))
            + (Real.log (euclidNorm x) - Real.log r)| := by
          rw [hc]
          congr 1
          ring
      _ ≤ |Real.pi / 2 * potentialKernel x - (Real.log (euclidNorm x) + Real.pi / 2 * κ)|
            + |Real.log (euclidNorm x) - Real.log r| := abs_add_le _ _
      _ ≤ K / r + 1 / r := by
          rw [abs_of_nonneg hlog0]
          linarith
      _ = (K + 1) / r := by ring
  have hmeas : Measurable g :=
    (measurable_of_countable potentialKernel).comp (measurable_walkPos_exitIdx _ w)
  have hint : Integrable g (pathLaw 2) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable
      (2 / Real.pi * ((K + 1) / r + |c|)) ?_
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs] at hω ⊢
    have h3 : Real.pi / 2 * |g ω| ≤ (K + 1) / r + |c| := by
      have := abs_sub_abs_le_abs_sub (Real.pi / 2 * g ω) c
      rw [abs_mul, abs_of_pos hpi] at this
      linarith
    calc |g ω| = 2 / Real.pi * (Real.pi / 2 * |g ω|) := by field_simp
      _ ≤ 2 / Real.pi * ((K + 1) / r + |c|) := by gcongr
  have heq : Real.pi / 2 * ∫ ω, g ω ∂pathLaw 2 - c =
      ∫ ω, (Real.pi / 2 * g ω - c) ∂pathLaw 2 := by
    rw [integral_sub (hint.const_mul _) (integrable_const _), integral_const_mul]
    simp
  have key := norm_integral_le_of_norm_le_const hbound
  rw [← heq, Real.norm_eq_abs] at key
  simpa using key

/-- **Lawler and Limic (2004), Lemma 3**, the estimates of `G_n(0, z)` and `G_n(0, 0)` for the
simple random walk on `ℤ²`: there is `C` with
`|(π/2) G_n(0, z) - (log n - log |z|)| ≤ C (|z|⁻¹ + n^{-1/3})` for `0 < |z| < n` and
`|(π/2) G_n(0, 0) - log n| ≤ C`, for all `n ≥ 2`. -/
theorem green_asymptotics : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → (∀ z : Site 2, z ≠ 0 → euclidNorm z < n →
    |Real.pi / 2 * green n 0 z - (Real.log n - Real.log (euclidNorm z))| ≤
      C * (1 / euclidNorm z + (n : ℝ) ^ (-(1/3 : ℝ)))) ∧
    |Real.pi / 2 * green n 0 0 - Real.log n| ≤ C := by
  obtain ⟨κ, K, hK, hpk⟩ := exists_abs_potentialKernel_sub_log_le_div
  refine ⟨K + 1 + |Real.pi / 2 * κ|, fun n hn => ?_⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h0 : (0 : Site 2) ∈ diskFinset (n : ℝ) := mem_diskFinset_iff.2 (by simpa using hn0)
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) (diskFinset (n : ℝ))
  have hG := Graph.Zd.latticeConnected 2
  have hinv : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-(1/3 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hκ := abs_nonneg (Real.pi / 2 * κ)
  constructor
  · intro z hz hzn
    have hzB : z ∈ diskFinset (n : ℝ) := mem_diskFinset_iff.2 hzn
    have hgreen : green n 0 z = ∫ ω, potentialKernel
        (walkPos z ω (exitIdx (diskFinset n) z ω)) ∂pathLaw 2 - potentialKernel z := by
      rw [green, Network.killedGreenReal_symm hG _ hq 0 z,
        killedGreenReal_eq_potentialKernel _ hzB h0]
      simp only [sub_zero]
    have hE := abs_integral_exit_sub_log_le hK hpk hn0 hzB
    have hz0 := hpk z hz
    have hzpos : 0 < euclidNorm z := ContinuousTime.euclidNorm_pos hz
    have h1 : (K + 1) / n ≤ (K + 1 + |Real.pi / 2 * κ|) * (n : ℝ) ^ (-(1/3 : ℝ)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul (by linarith) hinv (by positivity) (by positivity)
    have h2 : K / euclidNorm z ≤ (K + 1 + |Real.pi / 2 * κ|) * (1 / euclidNorm z) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    rw [hgreen]
    calc |Real.pi / 2 * (∫ ω, potentialKernel
          (walkPos z ω (exitIdx (diskFinset n) z ω)) ∂pathLaw 2 - potentialKernel z)
          - (Real.log n - Real.log (euclidNorm z))|
        = |(Real.pi / 2 * ∫ ω, potentialKernel
            (walkPos z ω (exitIdx (diskFinset n) z ω)) ∂pathLaw 2
              - (Real.log n + Real.pi / 2 * κ))
            - (Real.pi / 2 * potentialKernel z
              - (Real.log (euclidNorm z) + Real.pi / 2 * κ))| := by
          congr 1
          ring
      _ ≤ |Real.pi / 2 * ∫ ω, potentialKernel
            (walkPos z ω (exitIdx (diskFinset n) z ω)) ∂pathLaw 2
              - (Real.log n + Real.pi / 2 * κ)|
            + |Real.pi / 2 * potentialKernel z
              - (Real.log (euclidNorm z) + Real.pi / 2 * κ)| := abs_sub _ _
      _ ≤ (K + 1) / n + K / euclidNorm z := add_le_add hE hz0
      _ ≤ (K + 1 + |Real.pi / 2 * κ|) * (1 / euclidNorm z + (n : ℝ) ^ (-(1/3 : ℝ))) := by
          rw [mul_add]
          linarith
  · have hgreen : green n 0 0 = ∫ ω, potentialKernel
        (walkPos 0 ω (exitIdx (diskFinset n) 0 ω)) ∂pathLaw 2 := by
      rw [green, killedGreenReal_eq_potentialKernel _ h0 h0]
      simp only [sub_zero, potentialKernel_zero]
    have hE := abs_integral_exit_sub_log_le hK hpk hn0 h0
    have h1 : (K + 1) / (n : ℝ) ≤ K + 1 := div_le_self (by linarith) (by linarith)
    rw [hgreen]
    calc |Real.pi / 2 * ∫ ω, potentialKernel
          (walkPos 0 ω (exitIdx (diskFinset n) 0 ω)) ∂pathLaw 2 - Real.log n|
        = |(Real.pi / 2 * ∫ ω, potentialKernel
            (walkPos 0 ω (exitIdx (diskFinset n) 0 ω)) ∂pathLaw 2
              - (Real.log n + Real.pi / 2 * κ)) + Real.pi / 2 * κ| := by
          congr 1
          ring
      _ ≤ |Real.pi / 2 * ∫ ω, potentialKernel
            (walkPos 0 ω (exitIdx (diskFinset n) 0 ω)) ∂pathLaw 2
              - (Real.log n + Real.pi / 2 * κ)| + |Real.pi / 2 * κ| := abs_add_le _ _
      _ ≤ K + 1 + |Real.pi / 2 * κ| := by linarith

end FiniteAvalanches.Walk.Beurling
