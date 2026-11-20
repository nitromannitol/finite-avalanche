import FiniteAvalanches.Walk.BarlowMasson.Cone
import FiniteAvalanches.Walk.BarlowMasson.Crossing
import FiniteAvalanches.Walk.BarlowMasson.Green

/-!
# Reaching a far set before a crossing path

The data of the reentry estimate of Barlow and Masson (2011), Lemma 2.4: a scale `k`, a set `α`
of sites in the disk of radius `k` together with a site `z` at distance in `[k, k + 1)`, with `α`
containing a chain with steps of length at most one from the origin to `z`, and a set `K` that
contains every site at distance at least `ρ₂` and no site at distance less than `ρ₁`, where
`k² ≤ ρ₁ ≤ ρ₂ ≤ 4 ρ₁`.

Let `F(w)` be the probability that the walk from `w` reaches `K` before `α`. On the disk of
radius `2k + 1` it is at most `1 / (c log (ρ₁ / 2k))`, and on the layer `2k ≤ |y| < 2k + 1` it
is at least `1 / (2 log ((ρ₂ + 1) / (k + 1)))`. Hence all its values on the disk are at most a
constant multiple of each of its values on the layer, which replaces the discrete Harnack
inequality in Barlow and Masson's proof. The upper bound uses the uniform lower bound for
hitting a dense set (Lawler and Limic (2004), Lemma 7): from the disk of radius `3k / 2` the walk
hits `α` before leaving the disk of radius `2k` with probability at least `c`.

## Main statements

* `ReentryData`: the data above.
* `prob_reaches_disk_le`: `F(w) ≤ 1 / (c log (ρ₁ / 2k))` for `|w| < 2k + 1`.
* `prob_reaches_layer_ge`: the lower bound on the layer.
* `prob_reaches_le_mul`: `F(w) ≤ C F(y)` for `|w| < 2k + 1` and `y` on the layer.
-/

noncomputable section

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory FiniteAvalanches.Walk.Beurling

/-- The data of the reentry estimate. -/
structure ReentryData where
  /-- The scale. -/
  k : ℕ
  /-- The first site of the path outside the disk of radius `k`. -/
  z : Site 2
  /-- The path up to `z`. -/
  α : Set (Site 2)
  /-- The far set. -/
  K : Set (Site 2)
  /-- The inner radius of the far set. -/
  ρ₁ : ℝ
  /-- The outer radius of the far set. -/
  ρ₂ : ℝ
  z_mem : z ∈ α
  le_norm_z : (k : ℝ) ≤ euclidNorm z
  norm_z_lt : euclidNorm z < k + 1
  norm_lt : ∀ a ∈ α, a ≠ z → euclidNorm a < k
  /-- The number of steps of a chain in `α` from the origin to `z`. -/
  len : ℕ
  /-- A chain in `α` from the origin to `z` with steps of length at most one. -/
  path : ℕ → Site 2
  path_zero : path 0 = 0
  path_len : path len = z
  path_step : ∀ i < len, euclidNorm (path (i + 1) - path i) ≤ 1
  path_mem : ∀ i ≤ len, path i ∈ α
  mem_K : ∀ w, ρ₂ ≤ euclidNorm w → w ∈ K
  le_norm_K : ∀ w ∈ K, ρ₁ ≤ euclidNorm w
  sq_le_ρ₁ : (k : ℝ) ^ 2 ≤ ρ₁
  ρ₁_le : ρ₁ ≤ ρ₂
  ρ₂_le : ρ₂ ≤ 4 * ρ₁

namespace ReentryData

variable (S : ReentryData)

theorem norm_lt_succ {a : Site 2} (ha : a ∈ S.α) : euclidNorm a < S.k + 1 := by
  by_cases h : a = S.z
  · rw [h]
    exact S.norm_z_lt
  · linarith [S.norm_lt a ha h]

theorem not_mem_K_of_norm_lt {w : Site 2} (hw : euclidNorm w < S.ρ₁) : w ∉ S.K :=
  fun h => absurd (S.le_norm_K w h) (not_le.2 hw)

/-- The path meets every annulus `j ≤ |a - c| < j + 1` between its distances to `c` at its two
ends. -/
theorem crossing_around (c : Site 2) (j : ℕ) (h0 : euclidNorm (0 - c) < j + 1)
    (hz : (j : ℝ) ≤ euclidNorm (S.z - c)) :
    ∃ a ∈ S.α, (j : ℝ) ≤ euclidNorm (a - c) ∧ euclidNorm (a - c) < j + 1 := by
  have hstep : ∀ i < S.len, euclidNorm (S.path (i + 1) - c) ≤ euclidNorm (S.path i - c) + 1 := by
    intro i hi
    have h := euclidNorm_add_le (S.path (i + 1) - S.path i) (S.path i - c)
    rw [sub_add_sub_cancel] at h
    linarith [S.path_step i hi]
  obtain ⟨i, hi, h1, h2⟩ := exists_annulus_of_chain S.path c S.len hstep j
    (by rw [S.path_zero]; exact h0) (by rw [S.path_len]; exact hz)
  exact ⟨S.path i, S.path_mem i hi, h1, h2⟩

theorem crossing (j : ℕ) (hj : j < S.k) :
    ∃ a ∈ S.α, (j : ℝ) ≤ euclidNorm a ∧ euclidNorm a < j + 1 := by
  obtain ⟨a, ha, h1, h2⟩ := S.crossing_around 0 j (by simp; positivity)
    (by rw [sub_zero]; have : (j : ℝ) + 1 ≤ S.k := by exact_mod_cast hj
        linarith [S.le_norm_z])
  exact ⟨a, ha, by simpa using h1, by simpa using h2⟩

theorem zero_mem : (0 : Site 2) ∈ S.α := by
  have h := S.path_mem 0 (Nat.zero_le _)
  rwa [S.path_zero] at h

/-- The path together with the axis points beyond `k` is dense. -/
def padded : Set (Site 2) := S.α ∪ {w | ∃ j : ℕ, S.k ≤ j ∧ w = axisPt (j : ℤ)}

private theorem euclidNorm_axisPt_nat (j : ℕ) : euclidNorm (axisPt (j : ℤ)) = j := by
  simp [euclidNorm, axisPt, Fin.sum_univ_two]

theorem isDense_padded : IsDense S.padded := by
  intro j
  by_cases hj : j < S.k
  · obtain ⟨a, ha, h1, h2⟩ := S.crossing j hj
    exact ⟨a, Or.inl ha, h1, h2⟩
  · refine ⟨axisPt (j : ℤ), Or.inr ⟨j, not_lt.1 hj, rfl⟩, ?_, ?_⟩
    · rw [euclidNorm_axisPt_nat]
    · rw [euclidNorm_axisPt_nat]
      linarith

theorem shellPart_padded_subset :
    shellPart S.padded (((2 * S.k : ℕ) : ℝ) / 4) (((2 * S.k : ℕ) : ℝ) / 2) ⊆ S.α := by
  rintro w ⟨hw | ⟨j, hj, rfl⟩, _, h2⟩
  · exact hw
  · exfalso
    rw [euclidNorm_axisPt_nat] at h2
    have : (S.k : ℝ) ≤ j := by exact_mod_cast hj
    push_cast at h2
    linarith

end ReentryData

/-- From the disk of radius `3k / 2`, the walk reaches distance `2k` before `α` with probability
at most `1 - c`. -/
theorem prob_reaches_far_le_one_sub : ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ S : ReentryData,
    k₀ ≤ S.k → ∀ w : Site 2, euclidNorm w < 3 * S.k / 2 →
      prob (reaches {y | 2 * (S.k : ℝ) ≤ euclidNorm y} S.α w) ≤ 1 - c := by
  obtain ⟨c, hc, N, h⟩ := hit_shellPart_lower
  refine ⟨c, hc, N, fun S hk w hw => ?_⟩
  have hN : N ≤ 2 * S.k := by omega
  have hw' : euclidNorm w < 3 * ((2 * S.k : ℕ) : ℝ) / 4 := by push_cast; linarith
  have hhit := h (2 * S.k) hN S.padded S.isDense_padded w hw'
  have hdisj : Disjoint (reaches {y | 2 * (S.k : ℝ) ≤ euclidNorm y} S.α w)
      (hitsBefore (shellPart S.padded (((2 * S.k : ℕ) : ℝ) / 4) (((2 * S.k : ℕ) : ℝ) / 2))
        ((2 * S.k : ℕ) : ℝ) w) := by
    rw [Set.disjoint_left]
    rintro ω ⟨t, ht, hs⟩ ⟨t', ht', hs'⟩
    by_cases htt : t' ≤ t
    · exact hs t' htt (S.shellPart_padded_subset ht')
    · have := hs' t (by omega)
      push_cast at this
      simp only [Set.mem_setOf_eq] at ht
      linarith
  have hsum : prob (reaches {y | 2 * (S.k : ℝ) ≤ euclidNorm y} S.α w) +
      prob (hitsBefore (shellPart S.padded (((2 * S.k : ℕ) : ℝ) / 4) (((2 * S.k : ℕ) : ℝ) / 2))
        ((2 * S.k : ℕ) : ℝ) w) ≤ 1 := by
    have hu := prob_le_one' (reaches {y | 2 * (S.k : ℝ) ≤ euclidNorm y} S.α w ∪
      hitsBefore (shellPart S.padded (((2 * S.k : ℕ) : ℝ) / 4) (((2 * S.k : ℕ) : ℝ) / 2))
        ((2 * S.k : ℕ) : ℝ) w)
    unfold prob at hu ⊢
    rw [measure_union hdisj (measurableSet_hitsBefore _ _ _),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hu
    exact hu
  linarith

/-- The layer of sites at distance in `[2k, 2k + 1)`. -/
def layer (k : ℕ) : Finset (Site 2) := by
  classical exact (diskFinset (2 * k + 1)).filter fun y => 2 * (k : ℝ) ≤ euclidNorm y

theorem mem_layer {k : ℕ} {y : Site 2} :
    y ∈ layer k ↔ 2 * (k : ℝ) ≤ euclidNorm y ∧ euclidNorm y < 2 * k + 1 := by
  classical
  unfold layer
  rw [Finset.mem_filter, diskFinset, Finset.mem_filter, mem_ballFinset_iff]
  constructor
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2.le, h2⟩, h1⟩

private theorem euclidNorm_axisPt_nat' (j : ℕ) : euclidNorm (axisPt (j : ℤ)) = j := by
  simp [euclidNorm, axisPt, Fin.sum_univ_two]

theorem layer_nonempty (k : ℕ) : (layer k).Nonempty :=
  ⟨axisPt ((2 * k : ℕ) : ℤ), mem_layer.2 ⟨by rw [euclidNorm_axisPt_nat']; push_cast; rfl,
    by rw [euclidNorm_axisPt_nat']; push_cast; linarith⟩⟩

/-- The open disk of radius `ρ` minus a set, as a finite set. -/
def diskMinus (ρ : ℝ) (B : Set (Site 2)) : Finset (Site 2) := by
  classical exact (diskFinset ρ).filter fun y => y ∉ B

theorem mem_diskMinus {ρ : ℝ} {B : Set (Site 2)} {y : Site 2} :
    y ∈ diskMinus ρ B ↔ euclidNorm y < ρ ∧ y ∉ B := by
  classical
  unfold diskMinus
  rw [Finset.mem_filter, diskFinset, Finset.mem_filter, mem_ballFinset_iff]
  constructor
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.le, h1⟩, h2⟩

theorem prob_reaches_mono_target {A A' B : Set (Site 2)} (h : A ⊆ A') (y : Site 2) :
    prob (reaches A B y) ≤ prob (reaches A' B y) :=
  prob_mono (reaches_mono h subset_rfl y)

/-- Comparison inside a disk: a probability of reaching a set beyond the disk is at most its
largest value on the exit layer times the probability of leaving the disk. -/
theorem reaches_le_mul_exit {A B : Set (Site 2)} {ρ M : ℝ}
    (hA : ∀ y, euclidNorm y < ρ → y ∉ A)
    (hlayer : ∀ y, ρ ≤ euclidNorm y → euclidNorm y < ρ + 1 → prob (reaches A B y) ≤ M)
    {w : Site 2} (hw : euclidNorm w < ρ) :
    prob (reaches A B w) ≤ M * prob (reaches {y | ρ ≤ euclidNorm y} B w) := by
  by_cases hwB : w ∈ B
  · rw [reaches_eq_empty hwB, reaches_eq_empty hwB, prob_empty, mul_zero]
  refine le_of_mean_compare (diskMinus ρ B) (fun y => prob (reaches A B y))
    (fun y => M * prob (reaches {y | ρ ≤ euclidNorm y} B y)) (fun y hy => ?_) (fun y hy => ?_)
    (fun y hy a ha => ?_) w (mem_diskMinus.2 ⟨hw, hwB⟩)
  · obtain ⟨h1, h2⟩ := mem_diskMinus.1 hy
    exact prob_reaches_step (hA y h1) h2
  · obtain ⟨h1, h2⟩ := mem_diskMinus.1 hy
    rw [prob_reaches_step (show y ∉ {y | ρ ≤ euclidNorm y} by simpa using h1) h2,
      mul_div_assoc', Finset.mul_sum]
  · obtain ⟨h1, _⟩ := mem_diskMinus.1 hy
    by_cases hB : y + dirVec a ∈ B
    · simp only [reaches_eq_empty hB, prob_empty, mul_zero, le_refl]
    · have hρ : ρ ≤ euclidNorm (y + dirVec a) := by
        by_contra hlt
        exact ha (mem_diskMinus.2 ⟨not_le.1 hlt, hB⟩)
      have hlt : euclidNorm (y + dirVec a) < ρ + 1 := by
        have := euclidNorm_add_dirVec_le y a
        linarith
      rw [reaches_eq_univ (show y + dirVec a ∈ {y | ρ ≤ euclidNorm y} from hρ) hB, prob_univ,
        mul_one]
      exact hlayer _ hρ hlt

/-- **The upper bound on the disk.** The probability of reaching `K` before `α` from the disk of
radius `2k + 1` is at most `1 / (c log (ρ₁ / 2k))`. -/
theorem prob_reaches_disk_le : ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ S : ReentryData, k₀ ≤ S.k →
    ∀ w : Site 2, euclidNorm w < 2 * S.k + 1 →
      prob (reaches S.K S.α w) ≤ 1 / (c * Real.log (S.ρ₁ / (2 * S.k))) := by
  classical
  obtain ⟨c, hc, k₁, hfar⟩ := prob_reaches_far_le_one_sub
  obtain ⟨D, ρ₀, hD, hρ₀, hup⟩ := exitsAvoiding_le_log
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (ρ₀ + 2 * D + 25)
  refine ⟨c, hc, max k₁ N₀, fun S hk w hw => ?_⟩
  have hk₁ : k₁ ≤ S.k := le_of_max_le_left hk
  have hkN : (N₀ : ℝ) ≤ S.k := by exact_mod_cast le_of_max_le_right hk
  set k : ℝ := (S.k : ℝ) with hkdef
  have hk25 : 25 ≤ k := by linarith
  have hkρ₀ : ρ₀ ≤ 7 * k / 5 := by linarith
  have hkD : 2 * D ≤ 7 * k / 5 - 1 := by linarith
  have hρ₁ : k ^ 2 ≤ S.ρ₁ := S.sq_le_ρ₁
  have h2kρ : 2 * k + 1 < S.ρ₁ := by nlinarith
  set g : Site 2 → ℝ := fun y => prob (reaches {y | S.ρ₁ ≤ euclidNorm y} S.α y) with hg
  set Ψ : Site 2 → ℝ := fun y => prob (reaches {y | 2 * k ≤ euclidNorm y} S.α y) with hΨ
  obtain ⟨ys, hys, hmax⟩ := (layer S.k).exists_max_image g (layer_nonempty S.k)
  set M := g ys with hMdef
  have hM0 : 0 ≤ M := prob_nonneg _
  have hdisk : ∀ y, euclidNorm y < 2 * k → g y ≤ M * Ψ y := by
    intro y hy
    exact reaches_le_mul_exit (fun y hy => by simp only [Set.mem_setOf_eq, not_le]; linarith)
      (fun y h1 h2 => hmax y (mem_layer.2 ⟨h1, h2⟩)) hy
  have hle_M : ∀ y, euclidNorm y < 2 * k + 1 → g y ≤ M := by
    intro y hy
    by_cases hy2 : euclidNorm y < 2 * k
    · exact (hdisk y hy2).trans (mul_le_of_le_one_right hM0 (prob_le_one' _))
    · exact hmax y (mem_layer.2 ⟨not_lt.1 hy2, hy⟩)
  have hinner : ∀ y, euclidNorm y < 3 * k / 2 → g y ≤ (1 - c) * M := by
    intro y hy
    have h1 := hdisk y (by linarith)
    have h2 : Ψ y ≤ 1 - c := hfar S hk₁ y hy
    calc g y ≤ M * Ψ y := h1
      _ ≤ M * (1 - c) := mul_le_mul_of_nonneg_left h2 hM0
      _ = (1 - c) * M := by ring
  have hys' := mem_layer.1 hys
  have hcross : g ys ≤ prob (crosses (7 * k / 5) S.ρ₁ ys) + (1 - c) * M := by
    refine le_of_mean_compare (annulusFinset (7 * k / 5) S.ρ₁) g
      (fun y => prob (crosses (7 * k / 5) S.ρ₁ y) + (1 - c) * M) (fun y hy => ?_)
      (fun y hy => ?_) (fun y hy a ha => ?_) ys
      (mem_annulusFinset.2 ⟨by linarith, by linarith⟩)
    · obtain ⟨h1, h2⟩ := mem_annulusFinset.1 hy
      refine prob_reaches_step (by simp only [Set.mem_setOf_eq, not_le]; exact h2) fun hα => ?_
      have := S.norm_lt_succ hα
      linarith
    · rw [prob_crosses_step hy, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card (Dir 2) : ℝ) = 4 := by simp
      rw [hcard]
      ring
    · rcases annulus_boundary hy a ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [prob_crosses_of_le h2, zero_add]
        exact hinner _ (by linarith)
      · rw [prob_crosses_of_ge (by linarith) h1]
        have := prob_le_one' (reaches {y | S.ρ₁ ≤ euclidNorm y} S.α (y + dirVec a))
        have : 0 ≤ (1 - c) * M := mul_nonneg (by linarith [hfar S hk₁ 0 (by
          rw [euclidNorm_zero]; linarith), prob_nonneg (reaches {y | 2 * k ≤ euclidNorm y} S.α 0)])
          hM0
        simp only [hg]
        linarith
  have hU := hup (7 * k / 5) S.ρ₁ hkρ₀ ys (by linarith) (by linarith)
  have hd1 : 0 < 7 * k / 5 - 1 := by linarith
  have hnum : Real.log (euclidNorm ys / (7 * k / 5 - 1)) + D / (7 * k / 5 - 1) ≤ 1 := by
    have hpos : 0 < euclidNorm ys / (7 * k / 5 - 1) := div_pos (by linarith) hd1
    have h1 := Real.log_le_sub_one_of_pos hpos
    have h2 : euclidNorm ys / (7 * k / 5 - 1) ≤ 3 / 2 := by
      rw [div_le_iff₀ hd1]
      linarith
    have h3 : D / (7 * k / 5 - 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ hd1]
      linarith
    linarith
  have hlogpos : 0 < Real.log (S.ρ₁ / (2 * k)) :=
    Real.log_pos ((one_lt_div (by linarith)).2 (by linarith))
  have hden : Real.log (S.ρ₁ / (2 * k)) ≤ Real.log (S.ρ₁ / (7 * k / 5 - 1)) :=
    Real.log_le_log (div_pos (by linarith) (by linarith))
      (div_le_div_of_nonneg_left (by linarith) hd1 (by linarith))
  have hU' : prob (crosses (7 * k / 5) S.ρ₁ ys) ≤ 1 / Real.log (S.ρ₁ / (2 * k)) := by
    refine hU.trans ?_
    calc (Real.log (euclidNorm ys / (7 * k / 5 - 1)) + D / (7 * k / 5 - 1)) /
          Real.log (S.ρ₁ / (7 * k / 5 - 1)) ≤ 1 / Real.log (S.ρ₁ / (7 * k / 5 - 1)) :=
          div_le_div_of_nonneg_right hnum (hlogpos.le.trans hden)
      _ ≤ 1 / Real.log (S.ρ₁ / (2 * k)) := one_div_le_one_div_of_le hlogpos hden
  have hMbound : M ≤ 1 / (c * Real.log (S.ρ₁ / (2 * k))) := by
    have hcM : c * M ≤ 1 / Real.log (S.ρ₁ / (2 * k)) := by
      have := hcross
      simp only [hMdef] at this ⊢
      linarith
    rw [le_div_iff₀ (mul_pos hc hlogpos)]
    rw [le_div_iff₀ hlogpos] at hcM
    nlinarith
  calc prob (reaches S.K S.α w) ≤ g w :=
        prob_reaches_mono_target (fun y hy => S.le_norm_K y hy) w
    _ ≤ M := hle_M w hw
    _ ≤ 1 / (c * Real.log (S.ρ₁ / (2 * k))) := hMbound

/-- **The lower bound on the layer.** From the layer `2k ≤ |y| < 2k + 1`, the probability of
reaching `K` before `α` is at least `1 / (4 log ((ρ₂ + 1) / (k + 1)))`. -/
theorem prob_reaches_layer_ge : ∃ k₀ : ℕ, ∀ S : ReentryData, k₀ ≤ S.k →
    ∀ y : Site 2, 2 * (S.k : ℝ) ≤ euclidNorm y → euclidNorm y < 2 * S.k + 1 →
      1 / (4 * Real.log ((S.ρ₂ + 1) / (S.k + 1))) ≤ prob (reaches S.K S.α y) := by
  obtain ⟨D, ρ₀, hD, hρ₀, hlow⟩ := log_le_exitsAvoiding
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (ρ₀ + 7 * D + 25)
  refine ⟨N₀, fun S hk y hy1 hy2 => ?_⟩
  have hkN : (N₀ : ℝ) ≤ S.k := by exact_mod_cast hk
  set k : ℝ := (S.k : ℝ)
  have hk25 : 25 ≤ k := by linarith
  have hρ₁ : k ^ 2 ≤ S.ρ₁ := S.sq_le_ρ₁
  have hρ₂ : 2 * k + 1 < S.ρ₂ := by nlinarith [S.ρ₁_le]
  have hsub : crosses (k + 1) S.ρ₂ y ⊆ reaches S.K S.α y :=
    reaches_mono (fun w hw => S.mem_K w hw) (fun a ha => by
      simp only [Set.mem_setOf_eq]
      exact (S.norm_lt_succ ha).le) y
  have hL := hlow (k + 1) S.ρ₂ (by linarith) y (by linarith) (by linarith)
  have hlogpos : 0 < Real.log ((S.ρ₂ + 1) / (k + 1)) :=
    Real.log_pos ((one_lt_div (by linarith)).2 (by linarith))
  have hnum : 1 / 4 ≤ Real.log (euclidNorm y / (k + 1)) - D / (k + 1 - 1) := by
    have hpos : 0 < euclidNorm y / (k + 1) := div_pos (by linarith) (by linarith)
    have h1 := Real.one_sub_inv_le_log_of_pos hpos
    have h2 : (euclidNorm y / (k + 1))⁻¹ ≤ 3 / 5 := by
      rw [inv_div, div_le_iff₀ (by linarith)]
      linarith
    have h3 : D / (k + 1 - 1) ≤ 1 / 7 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  calc 1 / (4 * Real.log ((S.ρ₂ + 1) / (k + 1))) =
        (1 / 4) / Real.log ((S.ρ₂ + 1) / (k + 1)) := by rw [div_div]
    _ ≤ (Real.log (euclidNorm y / (k + 1)) - D / (k + 1 - 1)) /
        Real.log ((S.ρ₂ + 1) / (k + 1)) := div_le_div_of_nonneg_right hnum hlogpos.le
    _ ≤ prob (crosses (k + 1) S.ρ₂ y) := hL
    _ ≤ prob (reaches S.K S.α y) := prob_mono hsub

/-- **The comparison.** All values on the disk of radius `2k + 1` of the probability of reaching
`K` before `α` are at most `C` times each of its values on the layer `2k ≤ |y| < 2k + 1`. -/
theorem prob_reaches_le_mul : ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, ∀ S : ReentryData, k₀ ≤ S.k →
    ∀ w y : Site 2, euclidNorm w < 2 * S.k + 1 → 2 * (S.k : ℝ) ≤ euclidNorm y →
      euclidNorm y < 2 * S.k + 1 →
        prob (reaches S.K S.α w) ≤ C * prob (reaches S.K S.α y) := by
  obtain ⟨c, hc, k₁, hup⟩ := prob_reaches_disk_le
  obtain ⟨k₂, hlow⟩ := prob_reaches_layer_ge
  refine ⟨8 / c, by positivity, max (max k₁ k₂) 25, fun S hk w y hw hy1 hy2 => ?_⟩
  have hk₁ : k₁ ≤ S.k := le_trans (le_max_left _ _) (le_of_max_le_left hk)
  have hk₂ : k₂ ≤ S.k := le_trans (le_max_right _ _) (le_of_max_le_left hk)
  have hk25 : (25 : ℝ) ≤ S.k := by exact_mod_cast le_of_max_le_right hk
  set k : ℝ := (S.k : ℝ)
  have hρ₁ : k ^ 2 ≤ S.ρ₁ := S.sq_le_ρ₁
  have hA := hup S hk₁ w hw
  have hB := hlow S hk₂ y hy1 hy2
  have hL1 : 0 < Real.log (S.ρ₁ / (2 * k)) :=
    Real.log_pos ((one_lt_div (by linarith)).2 (by nlinarith))
  have hratio : Real.log ((S.ρ₂ + 1) / (k + 1)) ≤ 2 * Real.log (S.ρ₁ / (2 * k)) := by
    set q := S.ρ₁ / (2 * k) with hqdef
    have hq : S.ρ₁ = 2 * k * q := by rw [hqdef]; field_simp
    have h10 : 10 ≤ q := by
      rw [hqdef, le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k) (by linarith : (0 : ℝ) ≤ k - 20)]
    have h1 : (S.ρ₂ + 1) / (k + 1) ≤ q * q := by
      rw [div_le_iff₀ (by linarith)]
      have h2 := S.ρ₂_le
      rw [hq] at h2
      nlinarith [mul_le_mul_of_nonneg_right h10 (by positivity : (0 : ℝ) ≤ q * (k + 1))]
    have hρpos : 0 < S.ρ₂ + 1 := by nlinarith [S.ρ₁_le, sq_nonneg k]
    have h2 := Real.log_le_log (div_pos hρpos (by linarith)) h1
    rw [Real.log_mul (by linarith) (by linarith)] at h2
    linarith
  have hL2 : 0 < Real.log ((S.ρ₂ + 1) / (k + 1)) :=
    Real.log_pos ((one_lt_div (by linarith)).2 (by nlinarith [S.ρ₁_le]))
  calc prob (reaches S.K S.α w) ≤ 1 / (c * Real.log (S.ρ₁ / (2 * k))) := hA
    _ ≤ 8 / c * (1 / (4 * Real.log ((S.ρ₂ + 1) / (k + 1)))) := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ ≤ 8 / c * prob (reaches S.K S.α y) := mul_le_mul_of_nonneg_left hB (by positivity)

end FiniteAvalanches.Walk.BarlowMasson
