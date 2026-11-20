import FiniteAvalanches.Walk.BarlowMasson.Comparison

/-!
# The inward Beurling estimate

For the data of the reentry estimate (`ReentryData`), the walk started at distance at least
`k / 2 - 2` from the origin reaches the disk `{|w| < r}` before the path `α` and the far set `K`
with probability at most `C √(r / k)`. Barlow and Masson (2011, proof of Lemma 2.4) quote this
from the Beurling estimates of Lawler and Limic (2010), Theorem 6.8.1; here it is derived from
the outward estimate (`beurling_crossing`) by reversing the walk.

## Proof

Let `D` be the set of sites at distance less than `ρ₂` that are not in `α`, `K` or the disk. By
the first-entrance decomposition and the symmetry of the expected visits, the probability is
`∑_y visits D y v · n(y) / 4`, a sum over the sites `y` next to the disk. The function
`y ↦ visits D y v` is harmonic on `D` inside the disk of radius `k / 4`, so it is at most its
largest value `M` on the circle of radius `k / 4` times the probability of reaching that circle
before `α`, `K` and the disk. That probability is at most the probability of reaching the circle
of radius `2r` before the disk times `C √(r / k)` (outward Beurling estimate around a point of
that circle). The escape probabilities of the disk sum to at most `4 / c` over its outer
neighbours, by the last-exit decomposition of the walk from the origin and the lower bound `c`
for the Green function of the disk of radius `2r` (Lawler and Limic (2004), (8) and Lemma 3).
Finally `M` is bounded (`visits_far_le`): by the potential kernel formula
`visits D w v = E^w[a(S_τ - v)] - a(w - v)`, the exit through `α` contributes `log(3k)`, the exit
through `K` contributes `log ρ₂` times the probability `O(1 / log(ρ₁ / k))` of reaching `K`
before `α`, and `a(w - v) ≥ (2/π) log(k / 8) - O(1)`.

## Main statements

* `visits_far_le`: the bound on the expected visits between distant points.
* `prob_reaches_disk_inward_le`: the inward Beurling estimate.
-/

noncomputable section

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory FiniteAvalanches.Walk.Beurling

/-- An upper bound for the potential kernel at every site. -/
theorem potentialKernel_le_log_succ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Site 2,
    potentialKernel x ≤ 2 / Real.pi * Real.log (euclidNorm x + 1) + C := by
  classical
  obtain ⟨κ, C, R, hC, hR, hpk⟩ := potentialKernel_log_approx
  set M := ∑ v ∈ ballFinset 2 R, |potentialKernel v| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨|κ| + C + M, by positivity, fun x => ?_⟩
  have hlog0 : 0 ≤ Real.log (euclidNorm x + 1) :=
    Real.log_nonneg (by linarith [euclidNorm_nonneg x])
  have hc₀ : 0 ≤ 2 / Real.pi := by positivity
  by_cases hx : R ≤ euclidNorm x
  · have h := (abs_le.1 (hpk x hx)).2
    have hxpos : 0 < euclidNorm x := by linarith
    have h1 : Real.log (euclidNorm x) ≤ Real.log (euclidNorm x + 1) :=
      Real.log_le_log hxpos (by linarith)
    have h2 : C / euclidNorm x ≤ C := div_le_self hC (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h1 hc₀
    linarith [le_abs_self κ]
  · have h := Finset.single_le_sum (f := fun v => |potentialKernel v|)
      (fun _ _ => abs_nonneg _) (mem_ballFinset_iff.2 (not_le.1 hx).le)
    have h' := le_abs_self (potentialKernel x)
    have : 0 ≤ 2 / Real.pi * Real.log (euclidNorm x + 1) := mul_nonneg hc₀ hlog0
    linarith [abs_nonneg κ]

/-- The walk leaves every finite set almost surely. -/
theorem ae_exists_walkPos_not_mem (D : Finset (Site 2)) (w : Site 2) :
    ∀ᵐ ω ∂pathLaw 2, ∃ t, walkPos w ω t ∉ D := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) D
  have hm : MeasurableSet
      {ξ : ℕ → Dir 2 | ∃ n : ℕ, w + ∑ j ∈ Finset.range n, dirVec (ξ j) = q} :=
    measurableSet_setOf.2 (Measurable.exists fun n => measurable_walkPos_pred w (· = q) n)
  have h : ∀ᵐ ξ ∂pathLaw 2, ∃ n : ℕ, w + ∑ j ∈ Finset.range n, dirVec (ξ j) = q :=
    (mem_ae_iff_prob_eq_one hm).2 (pathLaw_two_dim_hit_site w q)
  filter_upwards [h] with ξ hξ
  obtain ⟨n, hn⟩ := hξ
  exact ⟨n, by rw [walkPos, hn]; exact hq⟩

theorem exitIdx_spec {D : Finset (Site 2)} {w : Site 2} {ω : ℕ → Dir 2}
    (h : ∃ t, walkPos w ω t ∉ D) :
    walkPos w ω (exitIdx D w ω) ∉ D ∧ ∀ s < exitIdx D w ω, walkPos w ω s ∈ D := by
  classical
  have he : exitIdx D w ω = Nat.find h := by
    unfold exitIdx
    rw [dif_pos h]
  rw [he]
  exact ⟨Nat.find_spec h, fun s hs => not_not.1 (Nat.find_min h hs)⟩

private theorem log_far_bound {k ρ₁ ρ₂ : ℝ} (hk : 40 ≤ k) (hρ₁ : k ^ 2 ≤ ρ₁)
    (hρ₂ : ρ₂ ≤ 4 * ρ₁) (hρ₂' : 0 ≤ ρ₂) :
    1 ≤ Real.log (ρ₁ / (2 * k)) ∧ Real.log (ρ₂ + 2 * k + 2) ≤ 4 * Real.log (ρ₁ / (2 * k)) := by
  set q := ρ₁ / (2 * k) with hqdef
  have hk0 : 0 < k := by linarith
  have hρq : ρ₁ = 2 * k * q := by rw [hqdef]; field_simp
  have hkq : k / 2 ≤ q := by
    rw [hqdef, le_div_iff₀ (by linarith)]
    nlinarith
  have hq20 : 20 ≤ q := by linarith
  have hlogq : 1 ≤ Real.log q := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  refine ⟨hlogq, ?_⟩
  have h1 : ρ₂ + 2 * k + 2 ≤ q ^ 4 := by
    have h5 : ρ₂ ≤ 8 * k * q := by rw [hρq] at hρ₂; linarith
    have h6 : 8 * k * q ≤ 16 * q ^ 2 := by nlinarith
    have hq2 : 20 ≤ q ^ 2 := by nlinarith
    have h7 : 20 * q ^ 2 ≤ q ^ 4 := by
      have := mul_le_mul_of_nonneg_left hq2 (sq_nonneg q)
      nlinarith
    have h8 : 4 * q + 2 ≤ 4 * q ^ 2 := by nlinarith
    nlinarith
  have h2 := Real.log_le_log (by linarith) h1
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith

/-- **The expected visits between distant points.** Before the walk leaves the sites at distance
less than `ρ₂` outside `α ∪ K`, the expected number of visits to `v` from `w` is bounded when
`|w| < 2k + 1`, `|v| ≤ 2k` and `|w - v| ≥ k / 8`. -/
theorem visits_far_le : ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ S : ReentryData, k₀ ≤ S.k →
    ∀ w v : Site 2, euclidNorm w < 2 * S.k + 1 → euclidNorm v ≤ 2 * S.k →
      (S.k : ℝ) / 8 ≤ euclidNorm (w - v) →
        visits (diskMinus S.ρ₂ (S.α ∪ S.K)) w v ≤ C := by
  classical
  obtain ⟨c, hc, k₁, hF⟩ := prob_reaches_disk_le
  obtain ⟨C₁, hC₁, hup⟩ := potentialKernel_le_log_succ
  obtain ⟨κ, C, R, hC, hR, hpk⟩ := potentialKernel_log_approx
  set c₀ : ℝ := 2 / Real.pi with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  have hc₀1 : c₀ ≤ 1 := by
    rw [hc₀def, div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (8 * R + 40)
  refine ⟨47 + C₁ + |κ| + C + (4 + C₁) / c, by positivity, max k₁ N₀, fun S hk w v hw hv hwv => ?_⟩
  have hk₁ : k₁ ≤ S.k := le_of_max_le_left hk
  have hkN : (N₀ : ℝ) ≤ S.k := by exact_mod_cast le_of_max_le_right hk
  set k : ℝ := (S.k : ℝ) with hkdef
  have hk40 : 40 ≤ k := by linarith
  have hRk : R ≤ k / 8 := by linarith
  have hρ₁ : k ^ 2 ≤ S.ρ₁ := S.sq_le_ρ₁
  set D' := diskMinus S.ρ₂ (S.α ∪ S.K) with hD'
  have hbound0 : 0 ≤ 47 + C₁ + |κ| + C + (4 + C₁) / c := by positivity
  by_cases hwD : w ∉ D'
  · rw [visits_eq_zero_left hwD]
    exact hbound0
  by_cases hvD : v ∉ D'
  · rw [visits_eq_zero_right hvD]
    exact hbound0
  push Not at hwD hvD
  set E := reaches S.K S.α w with hE
  set Aα : ℝ := c₀ * Real.log (3 * k + 3) + C₁ with hAα
  set AK : ℝ := c₀ * Real.log (S.ρ₂ + 2 * k + 2) + C₁ with hAK
  have hk3 : 0 ≤ Real.log (3 * k + 3) := Real.log_nonneg (by linarith)
  have hAα0 : 0 ≤ Aα := by positivity
  have hρ₂ : 2 * k + 2 ≤ S.ρ₂ := by nlinarith [S.ρ₁_le]
  have hAK0 : 0 ≤ AK := by
    have : 0 ≤ Real.log (S.ρ₂ + 2 * k + 2) := Real.log_nonneg (by linarith)
    positivity
  have hpt : ∀ᵐ ω ∂pathLaw 2,
      potentialKernel (walkPos w ω (exitIdx D' w ω) - v) ≤ Aα + E.indicator (fun _ => AK) ω := by
    filter_upwards [ae_exists_walkPos_not_mem D' w] with ω hω
    obtain ⟨hout, hin⟩ := exitIdx_spec hω
    set t := exitIdx D' w ω
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, walkPos_zero'] at hout
      exact hout hwD
    obtain ⟨t', ht'⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hprev := hin t' (by omega)
    have hprev' := (mem_diskMinus.1 hprev).1
    have hstep : euclidNorm (walkPos w ω t) ≤ euclidNorm (walkPos w ω t') + 1 := by
      rw [ht']
      exact euclidNorm_walkPos_succ_le' w ω t'
    have hnorm : euclidNorm (walkPos w ω t - v) ≤ euclidNorm (walkPos w ω t) + 2 * k := by
      have := euclidNorm_add_le (walkPos w ω t) (-v)
      rw [euclidNorm_neg, ← sub_eq_add_neg] at this
      linarith
    have hind0 : 0 ≤ E.indicator (fun _ => AK) ω := Set.indicator_nonneg (fun _ _ => hAK0) ω
    have hcases : walkPos w ω t ∈ S.α ∨ walkPos w ω t ∈ S.K := by
      by_contra hcon
      push Not at hcon
      by_cases hlt : euclidNorm (walkPos w ω t) < S.ρ₂
      · exact hout (mem_diskMinus.2 ⟨hlt, fun h => h.elim hcon.1 hcon.2⟩)
      · exact hcon.2 (S.mem_K _ (not_lt.1 hlt))
    rcases hcases with hα | hK
    · have h1 := S.norm_lt_succ hα
      have h2 := hup (walkPos w ω t - v)
      have h3 : Real.log (euclidNorm (walkPos w ω t - v) + 1) ≤ Real.log (3 * k + 3) :=
        Real.log_le_log (by linarith [euclidNorm_nonneg (walkPos w ω t - v)]) (by linarith)
      have h4 := mul_le_mul_of_nonneg_left h3 hc₀.le
      simp only [hAα]
      linarith
    · have hmemE : ω ∈ E := by
        refine ⟨t, hK, fun s hs h => ?_⟩
        rcases lt_or_eq_of_le hs with hs | hs
        · exact (mem_diskMinus.1 (hin s hs)).2 (Or.inl h)
        · rw [hs] at h
          exact hout (by
            exfalso
            have := S.norm_lt_succ h
            have := S.le_norm_K _ hK
            nlinarith)
      rw [Set.indicator_of_mem hmemE]
      have h2 := hup (walkPos w ω t - v)
      have h3 : Real.log (euclidNorm (walkPos w ω t - v) + 1) ≤ Real.log (S.ρ₂ + 2 * k + 2) :=
        Real.log_le_log (by linarith [euclidNorm_nonneg (walkPos w ω t - v)]) (by linarith)
      have h4 := mul_le_mul_of_nonneg_left h3 hc₀.le
      simp only [hAK]
      linarith
  have hEm : MeasurableSet E := measurableSet_reaches _ _ _
  have hint : ∫ ω, potentialKernel (walkPos w ω (exitIdx D' w ω) - v) ∂pathLaw 2 ≤
      Aα + AK * prob E := by
    have hg : Integrable (fun ω => Aα + E.indicator (fun _ => AK) ω) (pathLaw 2) :=
      (integrable_const Aα).add ((integrable_const AK).indicator hEm)
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
      potentialKernel_nonneg _) hg hpt).trans (le_of_eq ?_)
    rw [integral_add (integrable_const Aα) ((integrable_const AK).indicator hEm),
      integral_const, integral_indicator_const _ hEm, probReal_univ, one_smul,
      smul_eq_mul, prob, measureReal_def]
    ring
  have hFw := hF S hk₁ w hw
  have hlow := (abs_le.1 (hpk (w - v) (by linarith))).1
  have hlogwv : Real.log (k / 8) ≤ Real.log (euclidNorm (w - v)) :=
    Real.log_le_log (by linarith) hwv
  have hCwv : C / euclidNorm (w - v) ≤ C := div_le_self hC (by linarith)
  obtain ⟨hlogq, hlogK⟩ := log_far_bound hk40 hρ₁ S.ρ₂_le (by linarith)
  have hlog24 : Real.log (3 * k + 3) - Real.log (k / 8) ≤ 47 := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (3 * k + 3) / (k / 8) from by positivity)
    have h2 : (3 * k + 3) / (k / 8) ≤ 48 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  have hc₀log : c₀ * Real.log (3 * k + 3) - c₀ * Real.log (k / 8) ≤ 47 := by
    rw [← mul_sub]
    rcases le_or_gt 0 (Real.log (3 * k + 3) - Real.log (k / 8)) with h | h
    · calc c₀ * (Real.log (3 * k + 3) - Real.log (k / 8)) ≤
            1 * (Real.log (3 * k + 3) - Real.log (k / 8)) := mul_le_mul_of_nonneg_right hc₀1 h
        _ ≤ 47 := by linarith
    · have : c₀ * (Real.log (3 * k + 3) - Real.log (k / 8)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc₀.le h.le
      linarith
  have hlogwv' := mul_le_mul_of_nonneg_left hlogwv hc₀.le
  have hAKF : AK * prob E ≤ (4 + C₁) / c := by
    have hpE0 : 0 ≤ prob E := prob_nonneg _
    have h1 : AK * prob E ≤ AK * (1 / (c * Real.log (S.ρ₁ / (2 * k)))) :=
      mul_le_mul_of_nonneg_left hFw hAK0
    refine h1.trans ?_
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hc]
    have h2 : AK ≤ (4 + C₁) * Real.log (S.ρ₁ / (2 * k)) := by
      have h3 := mul_le_mul_of_nonneg_left hlogK hc₀.le
      have h4 : c₀ * (4 * Real.log (S.ρ₁ / (2 * k))) ≤ 4 * Real.log (S.ρ₁ / (2 * k)) := by
        have := mul_le_mul_of_nonneg_right hc₀1 (by linarith : (0 : ℝ) ≤ 4 * Real.log (S.ρ₁ / (2 * k)))
        linarith
      have h5 : C₁ ≤ C₁ * Real.log (S.ρ₁ / (2 * k)) := le_mul_of_one_le_right hC₁ hlogq
      simp only [hAK]
      linarith
    calc AK * c ≤ (4 + C₁) * Real.log (S.ρ₁ / (2 * k)) * c :=
          mul_le_mul_of_nonneg_right h2 hc.le
      _ = (4 + C₁) * (c * Real.log (S.ρ₁ / (2 * k))) := by ring
  have hκ := neg_abs_le κ
  rw [visits_eq_potentialKernel D' hwD hvD]
  simp only [hAα] at hint
  linarith

theorem mem_diskFinset {r : ℝ} {y : Site 2} : y ∈ diskFinset r ↔ euclidNorm y < r := by
  rw [diskFinset, Finset.mem_filter, mem_ballFinset_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem exitsBefore_eq_reachesAfter {r : ℝ} {B : Set (Site 2)} {u : Site 2}
    (hu : euclidNorm u < r) :
    exitsBefore r B u = reachesAfter {y | r ≤ euclidNorm y} B u := by
  ext ω
  simp only [exitsBefore, reachesAfter, reaches, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht, hs⟩
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · rw [walkPos_zero'] at ht
      exact absurd ht (not_le.2 hu)
    · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
      refine ⟨t', by rwa [← walkPos_one_add], fun s hs' => ?_⟩
      rw [← walkPos_one_add]
      exact hs (1 + s) (by omega) (by omega)
  · rintro ⟨t, ht, hs⟩
    refine ⟨1 + t, by rwa [walkPos_one_add], fun s hs1 hs2 => ?_⟩
    obtain ⟨s', rfl⟩ : ∃ s', s = 1 + s' := ⟨s - 1, by omega⟩
    rw [walkPos_one_add]
    exact hs s' (by omega)

/-- **The escape capacity of a disk.** The probabilities of leaving the disk of radius `2r`
before returning to the disk of radius `r`, summed over the sites of the smaller disk, are at most
`1 / c`. -/
theorem sum_escape_le : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ r : ℕ, 1 ≤ r → N ≤ 2 * r →
    ∑ u ∈ diskFinset r, prob (reachesAfter {y | 2 * (r : ℝ) ≤ euclidNorm y}
      {y | euclidNorm y < r} u) ≤ 1 / c := by
  obtain ⟨c, hc, N, hg⟩ := green_lower (3 / 4) (by norm_num) (by norm_num)
  refine ⟨c, hc, N, fun r hr1 hr => ?_⟩
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hB' : ∀ w ∈ diskFinset (r : ℝ), euclidNorm w < 2 * (r : ℝ) := by
    intro w hw
    have := mem_diskFinset.1 hw
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hsum := hitsBefore_eq_sum_green_mul (2 * (r : ℝ)) (diskFinset r) hB' 0
  have hset : ((diskFinset (r : ℝ) : Finset (Site 2)) : Set (Site 2)) = {y | euclidNorm y < r} := by
    ext y
    simp only [Finset.mem_coe, Set.mem_setOf_eq]
    exact mem_diskFinset
  have hterm : ∀ u ∈ diskFinset (r : ℝ), c * prob (reachesAfter {y | 2 * (r : ℝ) ≤ euclidNorm y}
      {y | euclidNorm y < r} u) ≤ Beurling.green (2 * (r : ℝ)) 0 u *
        prob (exitsBefore (2 * (r : ℝ)) (diskFinset (r : ℝ) : Set (Site 2)) u) := by
    intro u hu
    have hu' := mem_diskFinset.1 hu
    rw [hset, exitsBefore_eq_reachesAfter (by linarith [Nat.cast_nonneg (α := ℝ) r] : euclidNorm u < 2 * (r : ℝ))]
    refine mul_le_mul_of_nonneg_right ?_ (prob_nonneg _)
    have h := hg (2 * r) hr 0 u (by rw [euclidNorm_zero]; push_cast; linarith)
      (by push_cast; linarith)
    push_cast at h
    exact h
  have h1 : c * ∑ u ∈ diskFinset (r : ℝ), prob (reachesAfter {y | 2 * (r : ℝ) ≤ euclidNorm y}
      {y | euclidNorm y < r} u) ≤ 1 := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← hsum]
    exact prob_le_one' _
  rw [le_div_iff₀ hc]
  linarith

/-- The outward Beurling estimate from the circle of radius `2r`. -/
theorem prob_reaches_quarter_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ S : ReentryData, ∀ r : ℕ, 1 ≤ r →
    64 * r ≤ S.k → ∀ w : Site 2, 2 * (r : ℝ) ≤ euclidNorm w → euclidNorm w < 2 * r + 1 →
      prob (reaches {y | (S.k : ℝ) / 4 ≤ euclidNorm y} S.α w) ≤ C * Real.sqrt ((r : ℝ) / S.k) := by
  obtain ⟨c, hc, hB⟩ := beurling_crossing
  refine ⟨8 * c, by positivity, fun S r hr hrk w hw1 hw2 => ?_⟩
  set k : ℝ := (S.k : ℝ)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrk' : 64 * (r : ℝ) ≤ k := by
    have : ((64 * r : ℕ) : ℝ) ≤ S.k := by exact_mod_cast hrk
    push_cast at this
    exact this
  set j₁ : ℕ := ⌊(k / 4 - 2 * r - 1) / 2⌋₊ with hj₁
  have hj₁le : (j₁ : ℝ) ≤ (k / 4 - 2 * r - 1) / 2 := Nat.floor_le (by linarith)
  have hj₁gt : (k / 4 - 2 * r - 1) / 2 - 1 < (j₁ : ℝ) := by
    have := Nat.lt_floor_add_one ((k / 4 - 2 * r - 1) / 2)
    rw [← hj₁] at this
    linarith
  have hj₁ge : k / 16 ≤ (j₁ : ℝ) := by linarith
  have hj₀ : 2 * r + 2 < j₁ := by
    have : (2 * (r : ℝ) + 2) < j₁ := by linarith
    exact_mod_cast this
  have hsub : reaches {y | k / 4 ≤ euclidNorm y} S.α w ⊆ escapesFrom (2 * (j₁ : ℝ)) S.α w := by
    rintro ω ⟨t, ht, hs⟩
    refine ⟨t, ?_, fun s _ hs2 => hs s hs2⟩
    have h := euclidNorm_sub_le (walkPos w ω t) w
    simp only [Set.mem_setOf_eq] at ht
    linarith
  have hcross : ∀ j : ℕ, 2 * r + 2 ≤ j → j < j₁ → ∃ a ∈ S.α,
      (j : ℝ) ≤ euclidNorm (a - w) ∧ euclidNorm (a - w) < j + 1 := by
    intro j hj1 hj2
    have hj1' : (2 * (r : ℝ) + 2) ≤ j := by exact_mod_cast hj1
    have hj2' : (j : ℝ) < j₁ := by exact_mod_cast hj2
    refine S.crossing_around w j ?_ ?_
    · rw [zero_sub, euclidNorm_neg]
      linarith
    · have h := euclidNorm_sub_le S.z w
      linarith [S.le_norm_z]
  have hb := hB S.α w (2 * r + 2) j₁ (by omega) hj₀ hcross
  refine (prob_mono hsub).trans (hb.trans ?_)
  suffices key : Real.sqrt (((2 * r + 2 : ℕ) : ℝ) / j₁) ≤ 8 * Real.sqrt ((r : ℝ) / k) by
    calc c * Real.sqrt (((2 * r + 2 : ℕ) : ℝ) / j₁) ≤ c * (8 * Real.sqrt ((r : ℝ) / k)) :=
          mul_le_mul_of_nonneg_left key hc.le
      _ = 8 * c * Real.sqrt ((r : ℝ) / k) := by ring
  have hk0 : 0 < k := by linarith
  have hj₁pos : (0 : ℝ) < j₁ := by linarith
  have h1 : ((2 * r + 2 : ℕ) : ℝ) / j₁ ≤ 64 * ((r : ℝ) / k) := by
    rw [div_le_iff₀ hj₁pos]
    push_cast
    have : (r : ℝ) / k * k = r := div_mul_cancel₀ _ hk0.ne'
    nlinarith
  calc Real.sqrt (((2 * r + 2 : ℕ) : ℝ) / j₁) ≤ Real.sqrt (64 * ((r : ℝ) / k)) :=
        Real.sqrt_le_sqrt h1
    _ = 8 * Real.sqrt ((r : ℝ) / k) := by
        rw [Real.sqrt_mul (by norm_num), show (64 : ℝ) = 8 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]

/-- The sum over a finite set of the values of an indicator at the translates by a fixed step is
at most the sum over the disk. -/
theorem sum_indicator_translate_le (D : Finset (Site 2)) (r : ℝ) (f : Site 2 → ℝ)
    (hf : ∀ u, 0 ≤ f u) (e : Site 2) :
    ∑ y ∈ D, {u : Site 2 | euclidNorm u < r}.indicator f (y + e) ≤ ∑ u ∈ diskFinset r, f u := by
  classical
  have h1 : ∑ y ∈ D, {u : Site 2 | euclidNorm u < r}.indicator f (y + e) =
      ∑ y ∈ D.filter (fun y => euclidNorm (y + e) < r), f (y + e) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : euclidNorm (y + e) < r
    · rw [Set.indicator_of_mem (show y + e ∈ {u : Site 2 | euclidNorm u < r} from h), if_pos h]
    · rw [Set.indicator_of_notMem (show y + e ∉ {u : Site 2 | euclidNorm u < r} from h), if_neg h]
  rw [h1]
  have h2 : ∑ y ∈ D.filter (fun y => euclidNorm (y + e) < r), f (y + e) =
      ∑ u ∈ (D.filter (fun y => euclidNorm (y + e) < r)).map (addRightEmbedding e), f u := by
    rw [Finset.sum_map]
    rfl
  rw [h2]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun u _ _ => hf u
  intro u hu
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hu
  exact mem_diskFinset.2 (Finset.mem_filter.1 hy).2

/-- **The inward Beurling estimate.** From distance between `k / 2 - 2` and `2k`, the walk reaches
the disk of radius `r` before `α ∪ K` with probability at most `C √(r / k)`. -/
theorem prob_reaches_disk_inward_le : ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ r₀ : ℕ, ∀ S : ReentryData,
    k₀ ≤ S.k → ∀ r : ℕ, r₀ ≤ r → 64 * r ≤ S.k → ∀ v : Site 2,
      (S.k : ℝ) / 2 - 2 ≤ euclidNorm v → euclidNorm v ≤ 2 * S.k →
        prob (reaches {w | euclidNorm w < r} (S.α ∪ S.K) v) ≤ C * Real.sqrt ((r : ℝ) / S.k) := by
  classical
  obtain ⟨CG, hCG, kG, hG⟩ := visits_far_le
  obtain ⟨ccap, hccap, Ncap, hcap⟩ := sum_escape_le
  obtain ⟨CQ, hCQ, hQ⟩ := prob_reaches_quarter_le
  refine ⟨4 * CG * CQ / ccap, by positivity, max kG 64, max Ncap 1,
    fun S hk r hr hrk v hv1 hv2 => ?_⟩
  have hkG : kG ≤ S.k := le_of_max_le_left hk
  have hk64 : (64 : ℝ) ≤ S.k := by exact_mod_cast le_of_max_le_right hk
  have hr1 : 1 ≤ r := le_of_max_le_right hr
  have hrN : Ncap ≤ 2 * r := by have := le_of_max_le_left hr; omega
  set k : ℝ := (S.k : ℝ) with hkdef
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrk' : 64 * (r : ℝ) ≤ k := by
    have : ((64 * r : ℕ) : ℝ) ≤ S.k := by exact_mod_cast hrk
    push_cast at this
    exact this
  set A : Set (Site 2) := {w | euclidNorm w < r} with hA
  set B : Set (Site 2) := S.α ∪ S.K with hB
  set D := diskMinus S.ρ₂ (B ∪ A) with hD
  set sq := Real.sqrt ((r : ℝ) / k) with hsq
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hρ₁ : k ^ 2 ≤ S.ρ₁ := S.sq_le_ρ₁
  have hvA : v ∉ A := by
    simp only [hA, Set.mem_setOf_eq, not_lt]
    linarith
  by_cases hvD : v ∉ D
  · have hvB : v ∈ B := by
      by_contra hvB
      by_cases hlt : euclidNorm v < S.ρ₂
      · exact hvD (mem_diskMinus.2 ⟨hlt, fun h => h.elim hvB hvA⟩)
      · exact hvB (Or.inr (S.mem_K v (not_lt.1 hlt)))
    rw [reaches_eq_empty hvB, prob_empty]
    positivity
  push Not at hvD
  have hDA : ∀ y ∈ D, y ∉ A := fun y hy h => (mem_diskMinus.1 hy).2 (Or.inr h)
  have hDB : ∀ y ∈ D, y ∉ B := fun y hy h => (mem_diskMinus.1 hy).2 (Or.inl h)
  have hout : ∀ y, y ∉ D → y ∈ A ∨ y ∈ B := by
    intro y hy
    by_contra hcon
    push Not at hcon
    by_cases hlt : euclidNorm y < S.ρ₂
    · exact hy (mem_diskMinus.2 ⟨hlt, fun h => h.elim hcon.2 hcon.1⟩)
    · exact hcon.2 (Or.inr (S.mem_K y (not_lt.1 hlt)))
  rw [prob_reaches_eq_sum_visits D A B hDA hDB hout hvD]
  -- the escape from the circle of radius `k / 4`
  have hesc : ∀ y ∈ D, euclidNorm y < k / 4 →
      visits D y v ≤ CG * prob (reaches {w | k / 4 ≤ euclidNorm w} (B ∪ A) y) := by
    intro y hy hyk
    refine le_of_mean_compare (D.filter fun y => euclidNorm y < k / 4) (fun y => visits D y v)
      (fun y => CG * prob (reaches {w | k / 4 ≤ euclidNorm w} (B ∪ A) y)) (fun y hy' => ?_)
      (fun y hy' => ?_) (fun y hy' a ha => ?_) y (Finset.mem_filter.2 ⟨hy, hyk⟩)
    · obtain ⟨hyD, hyk'⟩ := Finset.mem_filter.1 hy'
      have hyv : y ≠ v := by
        intro h
        rw [h] at hyk'
        linarith
      rw [visits_mean hyD v, if_neg hyv, add_zero]
    · obtain ⟨hyD, hyk'⟩ := Finset.mem_filter.1 hy'
      have hyB : y ∉ B ∪ A := fun h => h.elim (hDB y hyD) (hDA y hyD)
      rw [prob_reaches_step (by simpa using hyk') hyB, mul_div_assoc', Finset.mul_sum]
    · by_cases hD' : y + dirVec a ∈ D
      · have hk' : k / 4 ≤ euclidNorm (y + dirVec a) := by
          by_contra hlt
          exact ha (Finset.mem_filter.2 ⟨hD', not_le.1 hlt⟩)
        have hyk' := (Finset.mem_filter.1 hy').2
        have hlt : euclidNorm (y + dirVec a) < k / 4 + 1 := by
          have := euclidNorm_add_dirVec_le y a
          linarith
        have hyB : y + dirVec a ∉ B ∪ A := fun h => h.elim (hDB _ hD') (hDA _ hD')
        rw [reaches_eq_univ (show y + dirVec a ∈ {w | k / 4 ≤ euclidNorm w} from hk') hyB,
          prob_univ, mul_one]
        refine (visits_mono (fun x hx => ?_) _ _).trans (hG S hkG _ v (by linarith) hv2 ?_)
        · obtain ⟨h1, h2⟩ := mem_diskMinus.1 hx
          exact mem_diskMinus.2 ⟨h1, fun h => h2 (Or.inl h)⟩
        · have := euclidNorm_sub_le v (y + dirVec a)
          rw [euclidNorm_sub_comm] at this
          linarith
      · rw [visits_eq_zero_left hD']
        exact mul_nonneg hCG (prob_nonneg _)
  -- the escape from the circle of radius `2r`
  have hesc2 : ∀ y, euclidNorm y < 2 * r → y ∉ B ∪ A →
      prob (reaches {w | k / 4 ≤ euclidNorm w} (B ∪ A) y) ≤
        CQ * sq * prob (reaches {w | 2 * (r : ℝ) ≤ euclidNorm w} A y) := by
    intro y hy hyBA
    refine le_of_mean_compare (diskMinus (2 * r) (B ∪ A))
      (fun y => prob (reaches {w | k / 4 ≤ euclidNorm w} (B ∪ A) y))
      (fun y => CQ * sq * prob (reaches {w | 2 * (r : ℝ) ≤ euclidNorm w} A y))
      (fun y hy' => ?_) (fun y hy' => ?_) (fun y hy' a ha => ?_) y
      (mem_diskMinus.2 ⟨hy, hyBA⟩)
    · obtain ⟨h1, h2⟩ := mem_diskMinus.1 hy'
      exact prob_reaches_step (by simp only [Set.mem_setOf_eq, not_le]; linarith) h2
    · obtain ⟨h1, h2⟩ := mem_diskMinus.1 hy'
      rw [prob_reaches_step (by simpa using h1) (fun h => h2 (Or.inr h)), mul_div_assoc',
        Finset.mul_sum]
    · by_cases hBA : y + dirVec a ∈ B ∪ A
      · rw [reaches_eq_empty hBA, prob_empty]
        exact mul_nonneg (mul_nonneg hCQ hsq0) (prob_nonneg _)
      · have h2r : 2 * (r : ℝ) ≤ euclidNorm (y + dirVec a) := by
          by_contra hlt
          exact ha (mem_diskMinus.2 ⟨not_le.1 hlt, hBA⟩)
        have hlt : euclidNorm (y + dirVec a) < 2 * r + 1 := by
          have := euclidNorm_add_dirVec_le y a
          linarith [(mem_diskMinus.1 hy').1]
        rw [reaches_eq_univ (show y + dirVec a ∈ {w | 2 * (r : ℝ) ≤ euclidNorm w} from h2r)
          (fun h => hBA (Or.inr h)), prob_univ, mul_one]
        refine (prob_mono (reaches_mono subset_rfl (fun x hx => Or.inl (Or.inl hx)) _)).trans ?_
        exact hQ S r hr1 hrk _ h2r hlt
  set ep : Site 2 → ℝ := fun u =>
    prob (reachesAfter {w | 2 * (r : ℝ) ≤ euclidNorm w} A u) with hep
  have hep0 : ∀ u, 0 ≤ ep u := fun u => prob_nonneg _
  -- the bound for each term
  have hterm : ∀ y ∈ D, visits D v y * stepInto A B y ≤
      ∑ a : Dir 2, A.indicator (fun u => CG * (CQ * sq) * ep u) (y + dirVec a) := by
    intro y hy
    rw [visits_symm]
    have hstep : stepInto A B y ≤ (∑ a : Dir 2, A.indicator (fun _ => (1 : ℝ)) (y + dirVec a)) / 4 := by
      rw [stepInto]
      refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => ?_) (by norm_num)
      exact Set.indicator_le_indicator_of_subset Set.sdiff_subset (fun _ => zero_le_one) _
    by_cases hnear : ∃ a : Dir 2, y + dirVec a ∈ A
    · obtain ⟨a₀, ha₀⟩ := hnear
      have hyr : euclidNorm y < r + 1 := by
        have h1 := le_euclidNorm_add_dirVec y a₀
        have h2 : euclidNorm (y + dirVec a₀) < r := ha₀
        linarith
      have hv' : visits D y v ≤ CG * (CQ * sq) * prob (reaches {w | 2 * (r : ℝ) ≤ euclidNorm w} A y) := by
        refine (hesc y hy (by linarith)).trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hesc2 y (by linarith)
          (fun h => h.elim (hDB y hy) (hDA y hy))) hCG
      have hvis0 : 0 ≤ visits D y v := visits_nonneg _ _ _
      calc visits D y v * stepInto A B y ≤ visits D y v *
            ((∑ a : Dir 2, A.indicator (fun _ => (1 : ℝ)) (y + dirVec a)) / 4) :=
            mul_le_mul_of_nonneg_left hstep hvis0
        _ = ∑ a : Dir 2, A.indicator (fun _ => visits D y v / 4) (y + dirVec a) := by
            rw [mul_div_assoc', Finset.mul_sum, Finset.sum_div]
            refine Finset.sum_congr rfl fun a _ => ?_
            by_cases h : y + dirVec a ∈ A
            · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
            · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero, zero_div]
        _ ≤ ∑ a : Dir 2, A.indicator (fun u => CG * (CQ * sq) * ep u) (y + dirVec a) := by
            refine Finset.sum_le_sum fun a _ => ?_
            by_cases h : y + dirVec a ∈ A
            · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
              have he : prob (reaches {w | 2 * (r : ℝ) ≤ euclidNorm w} A y) ≤ 4 * ep (y + dirVec a) := by
                simp only [hep]
                rw [prob_reachesAfter]
                have hy' : y + dirVec a + dirVec (negDir a) = y := by
                  rw [dirVec_negDir, add_neg_cancel_right]
                have := Finset.single_le_sum (f := fun b => prob (reaches
                  {w | 2 * (r : ℝ) ≤ euclidNorm w} A (y + dirVec a + dirVec b)))
                  (fun _ _ => prob_nonneg _) (Finset.mem_univ (negDir a))
                simp only [hy'] at this
                linarith
              have hc0 : 0 ≤ CG * (CQ * sq) := by positivity
              nlinarith [mul_le_mul_of_nonneg_left he hc0]
            · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    · push Not at hnear
      have h0 : stepInto A B y = 0 := by
        have hz : ∀ a : Dir 2, (A \ B).indicator (fun _ => (1 : ℝ)) (y + dirVec a) = 0 :=
          fun a => Set.indicator_of_notMem (fun h => hnear a h.1) _
        rw [stepInto, Finset.sum_congr rfl fun a _ => hz a, Finset.sum_const_zero, zero_div]
      rw [h0, mul_zero]
      exact Finset.sum_nonneg fun a _ => Set.indicator_nonneg (fun u _ => by
        have := hep0 u
        positivity) _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_comm]
  have hdisk : ∀ a : Dir 2, ∑ y ∈ D, A.indicator (fun u => CG * (CQ * sq) * ep u) (y + dirVec a) ≤
      CG * (CQ * sq) * (1 / ccap) := by
    intro a
    refine (sum_indicator_translate_le D r (fun u => CG * (CQ * sq) * ep u)
      (fun u => by have := hep0 u; positivity) (dirVec a)).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hcap r hr1 hrN) (by positivity)
  calc ∑ a : Dir 2, ∑ y ∈ D, A.indicator (fun u => CG * (CQ * sq) * ep u) (y + dirVec a) ≤
        ∑ _a : Dir 2, CG * (CQ * sq) * (1 / ccap) := Finset.sum_le_sum fun a _ => hdisk a
    _ = 4 * CG * CQ / ccap * sq := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcard : (Fintype.card (Dir 2) : ℝ) = 4 := by simp
        rw [hcard]
        field_simp

end FiniteAvalanches.Walk.BarlowMasson
