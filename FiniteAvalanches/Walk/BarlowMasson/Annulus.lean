import FiniteAvalanches.Walk.BarlowMasson.Basic

/-!
# Crossing an annulus

For the simple random walk on `ℤ²` started at `y` with `ρ < |y| < m`, the probability of reaching
the circle `{|z| ≥ m}` before the closed disk `{|z| ≤ ρ}` is
`(log |y| - log ρ) / (log m - log ρ)` up to errors of order `1 / ρ`. The proof compares this
probability, which is the mean of its neighbouring values in the annulus, with affine functions
of the potential kernel `a(x) = (2/π) log |x| + κ + O(|x|⁻²)`, by the maximum principle.

## Main statements

* `exitsAvoiding_le_log`: the upper bound
  `(log (|y| / (ρ - 1)) + D / (ρ - 1)) / log (m / (ρ - 1))`.
* `log_le_exitsAvoiding`: the lower bound `(log (|y| / ρ) - D / (ρ - 1)) / log ((m + 1) / ρ)`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory FiniteAvalanches.Walk.Beurling

/-- The event of reaching the circle of radius `m` before the closed disk of radius `ρ`. -/
def crosses (ρ m : ℝ) (y : Site 2) : Set (ℕ → Dir 2) :=
  reaches {z | m ≤ euclidNorm z} {z | euclidNorm z ≤ ρ} y

/-- The potential kernel is `c₀ log |x| + κ` up to `C / |x|`, with `c₀ = 2 / π`. -/
theorem potentialKernel_log_approx :
    ∃ κ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ x : Site 2, R ≤ euclidNorm x →
      |potentialKernel x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| ≤ C / euclidNorm x := by
  obtain ⟨κ, C, R, hR, h⟩ := exists_abs_potentialKernel_sub_log_le
  refine ⟨κ, max C 0, R, le_max_right _ _, hR, fun x hx => ?_⟩
  have hxpos : 0 < euclidNorm x := by linarith
  refine (h x hx).trans ?_
  have h2 : euclidNorm x ^ (-2 : ℝ) ≤ 1 / euclidNorm x := by
    rw [Real.rpow_neg hxpos.le, Real.rpow_two, one_div]
    exact inv_anti₀ hxpos (by nlinarith)
  calc C * euclidNorm x ^ (-2 : ℝ) ≤ max C 0 * euclidNorm x ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 / euclidNorm x) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = max C 0 / euclidNorm x := by ring

theorem potentialKernel_mean {y : Site 2} (hy : y ≠ 0) :
    (∑ a : Dir 2, potentialKernel (y + dirVec a)) / 4 = potentialKernel y := by
  have h := walkOp_potentialKernel_sub y
  have h0 : (if y = 0 then (1 : ℝ) else 0) = 0 := by simp [hy]
  rw [h0, sub_eq_zero, walkOp_eq_mean] at h
  exact h

/-- The sites of the annulus `ρ < |z| < m`. -/
def annulusFinset (ρ m : ℝ) : Finset (Site 2) := by
  classical exact (diskFinset m).filter fun z => ρ < euclidNorm z

theorem mem_annulusFinset {ρ m : ℝ} {z : Site 2} :
    z ∈ annulusFinset ρ m ↔ ρ < euclidNorm z ∧ euclidNorm z < m := by
  classical
  unfold annulusFinset
  rw [Finset.mem_filter, diskFinset, Finset.mem_filter, mem_ballFinset_iff]
  constructor
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2.le, h2⟩, h1⟩

theorem annulus_boundary {ρ m : ℝ} {z : Site 2} (hz : z ∈ annulusFinset ρ m) (a : Dir 2)
    (hza : z + dirVec a ∉ annulusFinset ρ m) :
    (ρ - 1 < euclidNorm (z + dirVec a) ∧ euclidNorm (z + dirVec a) ≤ ρ) ∨
      (m ≤ euclidNorm (z + dirVec a) ∧ euclidNorm (z + dirVec a) < m + 1) := by
  obtain ⟨hz1, hz2⟩ := mem_annulusFinset.1 hz
  have h1 := le_euclidNorm_add_dirVec z a
  have h2 := euclidNorm_add_dirVec_le z a
  rw [mem_annulusFinset] at hza
  by_cases h : ρ < euclidNorm (z + dirVec a)
  · right
    exact ⟨not_lt.1 fun h' => hza ⟨h, h'⟩, by linarith⟩
  · left
    exact ⟨by linarith, not_lt.1 h⟩

theorem prob_crosses_of_le {ρ m : ℝ} {y : Site 2} (hy : euclidNorm y ≤ ρ) :
    prob (crosses ρ m y) = 0 := by
  rw [crosses, reaches_eq_empty (show y ∈ {z : Site 2 | euclidNorm z ≤ ρ} from hy), prob,
    measure_empty, ENNReal.toReal_zero]

theorem prob_crosses_of_ge {ρ m : ℝ} {y : Site 2} (hρm : ρ < m) (hy : m ≤ euclidNorm y) :
    prob (crosses ρ m y) = 1 := by
  rw [crosses, reaches_eq_univ (show y ∈ {z : Site 2 | m ≤ euclidNorm z} from hy)
    (show y ∉ {z : Site 2 | euclidNorm z ≤ ρ} by simp only [Set.mem_setOf_eq, not_le]; linarith),
    prob_univ]

theorem prob_crosses_step {ρ m : ℝ} {y : Site 2} (hy : y ∈ annulusFinset ρ m) :
    prob (crosses ρ m y) = (∑ a : Dir 2, prob (crosses ρ m (y + dirVec a))) / 4 := by
  obtain ⟨h1, h2⟩ := mem_annulusFinset.1 hy
  exact prob_reaches_step (by simp only [Set.mem_setOf_eq, not_le]; exact h2)
    (by simp only [Set.mem_setOf_eq, not_le]; exact h1)

/-- Comparison of the crossing probability with an affine function of the potential kernel. -/
theorem crosses_le_affine {ρ m lo hi : ℝ} (hρ : 0 ≤ ρ) (hlohi : lo < hi)
    (hlo : ∀ z : Site 2, ρ - 1 < euclidNorm z → euclidNorm z ≤ ρ → lo ≤ potentialKernel z)
    (hhi : ∀ z : Site 2, m ≤ euclidNorm z → euclidNorm z < m + 1 → hi ≤ potentialKernel z)
    {y : Site 2} (hyρ : ρ < euclidNorm y) (hym : euclidNorm y < m) :
    prob (crosses ρ m y) ≤ (potentialKernel y - lo) / (hi - lo) := by
  have hd : 0 < hi - lo := sub_pos.2 hlohi
  have hρm : ρ < m := hyρ.trans hym
  refine le_of_mean_compare (annulusFinset ρ m) (fun z => prob (crosses ρ m z))
    (fun z => (potentialKernel z - lo) / (hi - lo)) (fun z hz => prob_crosses_step hz)
    (fun z hz => ?_) (fun z hz a ha => ?_) y (mem_annulusFinset.2 ⟨hyρ, hym⟩)
  · obtain ⟨hz1, _⟩ := mem_annulusFinset.1 hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
    have hm := potentialKernel_mean hz0
    have hs : ∑ a : Dir 2, (potentialKernel (z + dirVec a) - lo) = 4 * (potentialKernel z - lo) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card (Dir 2) : ℝ) = 4 := by simp
      rw [hcard]
      linarith
    rw [← Finset.sum_div, hs]
    ring
  · rcases annulus_boundary hz a ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [prob_crosses_of_le h2]
      exact div_nonneg (sub_nonneg.2 (hlo _ h1 h2)) hd.le
    · rw [prob_crosses_of_ge hρm h1, le_div_iff₀ hd]
      linarith [hhi _ h1 h2]

theorem affine_le_crosses {ρ m lo hi : ℝ} (hρ : 0 ≤ ρ) (hlohi : lo < hi)
    (hlo : ∀ z : Site 2, ρ - 1 < euclidNorm z → euclidNorm z ≤ ρ → potentialKernel z ≤ lo)
    (hhi : ∀ z : Site 2, m ≤ euclidNorm z → euclidNorm z < m + 1 → potentialKernel z ≤ hi)
    {y : Site 2} (hyρ : ρ < euclidNorm y) (hym : euclidNorm y < m) :
    (potentialKernel y - lo) / (hi - lo) ≤ prob (crosses ρ m y) := by
  have hd : 0 < hi - lo := sub_pos.2 hlohi
  have hρm : ρ < m := hyρ.trans hym
  refine le_of_mean_compare (annulusFinset ρ m)
    (fun z => (potentialKernel z - lo) / (hi - lo)) (fun z => prob (crosses ρ m z))
    (fun z hz => ?_) (fun z hz => prob_crosses_step hz) (fun z hz a ha => ?_) y
    (mem_annulusFinset.2 ⟨hyρ, hym⟩)
  · obtain ⟨hz1, _⟩ := mem_annulusFinset.1 hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
    have hm := potentialKernel_mean hz0
    have hs : ∑ a : Dir 2, (potentialKernel (z + dirVec a) - lo) = 4 * (potentialKernel z - lo) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card (Dir 2) : ℝ) = 4 := by simp
      rw [hcard]
      linarith
    rw [← Finset.sum_div, hs]
    ring
  · rcases annulus_boundary hz a ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [prob_crosses_of_le h2, div_le_iff₀ hd]
      linarith [hlo _ h1 h2]
    · rw [prob_crosses_of_ge hρm h1, div_le_iff₀ hd]
      linarith [hhi _ h1 h2]

/-- The upper bound for crossing an annulus. -/
theorem exitsAvoiding_le_log : ∃ D ρ₀ : ℝ, 0 ≤ D ∧ 2 ≤ ρ₀ ∧ ∀ ρ m : ℝ, ρ₀ ≤ ρ →
    ∀ y : Site 2, ρ < euclidNorm y → euclidNorm y < m →
      prob (crosses ρ m y) ≤
        (Real.log (euclidNorm y / (ρ - 1)) + D / (ρ - 1)) / Real.log (m / (ρ - 1)) := by
  obtain ⟨κ, C, R, hC, hR, hpk⟩ := potentialKernel_log_approx
  have hc₀ : 0 < 2 / Real.pi := div_pos two_pos Real.pi_pos
  refine ⟨2 * C / (2 / Real.pi), R + 2, by positivity, by linarith, fun ρ m hρ y hyρ hym => ?_⟩
  set c₀ := 2 / Real.pi
  have hρ1 : 0 < ρ - 1 := by linarith
  have hRρ : R ≤ ρ - 1 := by linarith
  have hy0 : 0 < euclidNorm y := by linarith
  have hm0 : 0 < m := by linarith
  set lo := c₀ * Real.log (ρ - 1) + κ - C / (ρ - 1)
  set hi := c₀ * Real.log m + κ - C / m
  have hlogm : Real.log (ρ - 1) < Real.log m := Real.log_lt_log hρ1 (by linarith)
  have hCm : C / m ≤ C / (ρ - 1) := div_le_div_of_nonneg_left hC hρ1 (by linarith)
  have hlohi : lo < hi := by
    have := mul_lt_mul_of_pos_left hlogm hc₀
    simp only [lo, hi]
    linarith
  have hmain := crosses_le_affine (ρ := ρ) (m := m) (lo := lo) (hi := hi) (by linarith) hlohi
    (fun z hz1 _ => by
      have h := (abs_le.1 (hpk z (by linarith))).1
      have hz0 : 0 < euclidNorm z := by linarith
      have h1 := mul_le_mul_of_nonneg_left (Real.log_le_log hρ1 hz1.le) hc₀.le
      have h2 : C / euclidNorm z ≤ C / (ρ - 1) := div_le_div_of_nonneg_left hC hρ1 hz1.le
      simp only [lo]
      linarith)
    (fun z hz1 _ => by
      have h := (abs_le.1 (hpk z (by linarith))).1
      have h1 := mul_le_mul_of_nonneg_left (Real.log_le_log hm0 hz1) hc₀.le
      have h2 : C / euclidNorm z ≤ C / m := div_le_div_of_nonneg_left hC hm0 hz1
      simp only [hi]
      linarith)
    hyρ hym
  refine hmain.trans ?_
  have hnum : potentialKernel y - lo ≤
      c₀ * (Real.log (euclidNorm y / (ρ - 1)) + 2 * C / c₀ / (ρ - 1)) := by
    have h := (abs_le.1 (hpk y (by linarith))).2
    have h1 : C / euclidNorm y ≤ C / (ρ - 1) := div_le_div_of_nonneg_left hC hρ1 (by linarith)
    have e : c₀ * (2 * C / c₀ / (ρ - 1)) = 2 * C / (ρ - 1) := by
      field_simp
    rw [mul_add, e, Real.log_div hy0.ne' hρ1.ne', mul_sub]
    have e2 : 2 * C / (ρ - 1) = C / (ρ - 1) + C / (ρ - 1) := by ring
    simp only [lo]
    linarith
  have hnum0 : 0 ≤ potentialKernel y - lo := by
    have h := (abs_le.1 (hpk y (by linarith))).1
    have h1 : C / euclidNorm y ≤ C / (ρ - 1) := div_le_div_of_nonneg_left hC hρ1 (by linarith)
    have h2 := mul_le_mul_of_nonneg_left (Real.log_le_log hρ1 (by linarith : ρ - 1 ≤ euclidNorm y))
      hc₀.le
    simp only [lo]
    linarith
  have hden : c₀ * Real.log (m / (ρ - 1)) ≤ hi - lo := by
    rw [Real.log_div hm0.ne' hρ1.ne']
    simp only [hi, lo]
    nlinarith
  have hden0 : 0 < c₀ * Real.log (m / (ρ - 1)) := by
    apply mul_pos hc₀
    exact Real.log_pos ((one_lt_div hρ1).2 (by linarith))
  calc (potentialKernel y - lo) / (hi - lo) ≤ (potentialKernel y - lo) / (c₀ * Real.log (m / (ρ - 1))) :=
        div_le_div_of_nonneg_left hnum0 hden0 hden
    _ ≤ c₀ * (Real.log (euclidNorm y / (ρ - 1)) + 2 * C / c₀ / (ρ - 1)) /
          (c₀ * Real.log (m / (ρ - 1))) := div_le_div_of_nonneg_right hnum hden0.le
    _ = (Real.log (euclidNorm y / (ρ - 1)) + 2 * C / c₀ / (ρ - 1)) / Real.log (m / (ρ - 1)) := by
        rw [mul_div_mul_left _ _ hc₀.ne']

/-- The lower bound for crossing an annulus. -/
theorem log_le_exitsAvoiding : ∃ D ρ₀ : ℝ, 0 ≤ D ∧ 2 ≤ ρ₀ ∧ ∀ ρ m : ℝ, ρ₀ ≤ ρ →
    ∀ y : Site 2, ρ < euclidNorm y → euclidNorm y < m →
      (Real.log (euclidNorm y / ρ) - D / (ρ - 1)) / Real.log ((m + 1) / ρ) ≤
        prob (crosses ρ m y) := by
  obtain ⟨κ, C, R, hC, hR, hpk⟩ := potentialKernel_log_approx
  have hc₀ : 0 < 2 / Real.pi := div_pos two_pos Real.pi_pos
  refine ⟨2 * C / (2 / Real.pi), R + 2, by positivity, by linarith, fun ρ m hρ y hyρ hym => ?_⟩
  set c₀ := 2 / Real.pi
  have hρ1 : 0 < ρ - 1 := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hy0 : 0 < euclidNorm y := by linarith
  have hm0 : 0 < m := by linarith
  have hlogpos : 0 < Real.log ((m + 1) / ρ) :=
    Real.log_pos ((one_lt_div hρ0).2 (by linarith))
  set N₀ := Real.log (euclidNorm y / ρ) - 2 * C / c₀ / (ρ - 1)
  by_cases hN : N₀ ≤ 0
  · exact (div_nonpos_of_nonpos_of_nonneg hN hlogpos.le).trans (prob_nonneg _)
  push Not at hN
  set lo := c₀ * Real.log ρ + κ + C / (ρ - 1)
  set hi := c₀ * Real.log (m + 1) + κ + C / m
  have hlogy : Real.log (euclidNorm y / ρ) ≤ Real.log ((m + 1) / ρ) :=
    Real.log_le_log (div_pos hy0 hρ0) (div_le_div_of_nonneg_right (by linarith) hρ0.le)
  have hCm : C / m ≤ C / (ρ - 1) := div_le_div_of_nonneg_left hC hρ1 (by linarith)
  have hlohi : lo < hi := by
    have h1 : 0 < Real.log ((m + 1) / ρ) - 2 * C / c₀ / (ρ - 1) := by linarith
    have h2 := mul_pos hc₀ h1
    rw [Real.log_div (by linarith) hρ0.ne'] at h2
    have e : c₀ * (2 * C / c₀ / (ρ - 1)) = 2 * C / (ρ - 1) := by
      field_simp
    have hCm0 : 0 ≤ C / m := by positivity
    have hCρ : 0 ≤ C / (ρ - 1) := by positivity
    rw [mul_sub, mul_sub, e] at h2
    have e2 : 2 * C / (ρ - 1) = C / (ρ - 1) + C / (ρ - 1) := by ring
    simp only [lo, hi]
    linarith
  have hmain := affine_le_crosses (ρ := ρ) (m := m) (lo := lo) (hi := hi) (by linarith) hlohi
    (fun z hz1 hz2 => by
      have hz0 : 0 < euclidNorm z := by linarith
      have h := (abs_le.1 (hpk z (by linarith))).2
      have h1 := mul_le_mul_of_nonneg_left (Real.log_le_log hz0 hz2) hc₀.le
      have h2 : C / euclidNorm z ≤ C / (ρ - 1) := div_le_div_of_nonneg_left hC hρ1 hz1.le
      simp only [lo]
      linarith)
    (fun z hz1 hz2 => by
      have hz0 : 0 < euclidNorm z := by linarith
      have h := (abs_le.1 (hpk z (by linarith))).2
      have h1 := mul_le_mul_of_nonneg_left (Real.log_le_log hz0 hz2.le) hc₀.le
      have h2 : C / euclidNorm z ≤ C / m := div_le_div_of_nonneg_left hC hm0 hz1
      simp only [hi]
      linarith)
    hyρ hym
  refine le_trans ?_ hmain
  have hnum : c₀ * N₀ ≤ potentialKernel y - lo := by
    have h := (abs_le.1 (hpk y (by linarith))).1
    have h1 : C / euclidNorm y ≤ C / (ρ - 1) := div_le_div_of_nonneg_left hC hρ1 (by linarith)
    have e : c₀ * (2 * C / c₀ / (ρ - 1)) = 2 * C / (ρ - 1) := by
      field_simp
    simp only [N₀, lo]
    rw [mul_sub, e, Real.log_div hy0.ne' hρ0.ne', mul_sub]
    have e2 : 2 * C / (ρ - 1) = C / (ρ - 1) + C / (ρ - 1) := by ring
    linarith
  have hden : hi - lo ≤ c₀ * Real.log ((m + 1) / ρ) := by
    rw [Real.log_div (by linarith) hρ0.ne']
    simp only [hi, lo]
    nlinarith
  have hden0 : 0 < hi - lo := sub_pos.2 hlohi
  calc N₀ / Real.log ((m + 1) / ρ) = c₀ * N₀ / (c₀ * Real.log ((m + 1) / ρ)) := by
        rw [mul_div_mul_left _ _ hc₀.ne']
    _ ≤ c₀ * N₀ / (hi - lo) := div_le_div_of_nonneg_left (by positivity) hden0 hden
    _ ≤ (potentialKernel y - lo) / (hi - lo) := div_le_div_of_nonneg_right hnum hden0.le

end FiniteAvalanches.Walk.BarlowMasson
