import FiniteAvalanches.Walk.BarlowMasson.Inward

/-!
# The reentry ratio for one prefix

For the data of the reentry estimate (`ReentryData`), compare, for the walk started at `z` and
looking only at positive times,

* the probability that it reaches the disk `{|w| < r}` before `α ∪ K` and then `K` before `α`,
* the probability that it reaches `K` before `α`.

The first is at most `C r / k` times the second (Barlow and Masson (2011), proof of Lemma 2.4,
inequality (2.10)).

## Proof

Let `F(w)` be the probability of reaching `K` before `α`. The first probability is at most the
largest value of `F` on the disk of radius `r` times the probability of reaching that disk before
`α ∪ K`, by the maximum principle. On the disk, `F` is at most its largest value on the layer of
radius `2k` times the probability of reaching that layer before `α`, which is `O(√(r / k))` by
the outward Beurling estimate. The probability of reaching the disk of radius `r` is at most the
probability `V` of leaving the disk of radius `k / 2` around `z` before `α` times `O(√(r / k))`,
by the inward Beurling estimate on the exit layer. In the other direction, the second
probability is at least the smallest value of `F` on the layer of radius `2k` times the
probability of reaching that layer before `α`, which is at least `c` times the probability of
leaving the disk around `z` through the forward cone, hence at least `c V / 17`
(`escape_le_cone_escape`). The largest and smallest values of `F` on the layer are comparable
(`prob_reaches_le_mul`).

## Main statements

* `reachesThen`: reaching one set before another and then a third before a fourth.
* `reentry_ratio_le`: the comparison.
-/

noncomputable section

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory FiniteAvalanches.Walk.Beurling

/-- The walk from `y` reaches `A₁` at a time `t₁` avoiding `B₁` up to `t₁`, and then reaches `A₂`
at a time `t₂ ≥ t₁` avoiding `B₂` between `t₁` and `t₂`. -/
def reachesThen (A₁ B₁ A₂ B₂ : Set (Site 2)) (y : Site 2) : Set (ℕ → Dir 2) :=
  {ω | ∃ t₁ t₂, t₁ ≤ t₂ ∧ walkPos y ω t₁ ∈ A₁ ∧ (∀ s ≤ t₁, walkPos y ω s ∉ B₁) ∧
    walkPos y ω t₂ ∈ A₂ ∧ ∀ s, t₁ ≤ s → s ≤ t₂ → walkPos y ω s ∉ B₂}

theorem measurableSet_reachesThen (A₁ B₁ A₂ B₂ : Set (Site 2)) (y : Site 2) :
    MeasurableSet (reachesThen A₁ B₁ A₂ B₂ y) := by
  have h : reachesThen A₁ B₁ A₂ B₂ y = ⋃ t₁ : ℕ, ⋃ t₂ : ℕ,
      {ω | t₁ ≤ t₂ ∧ walkPos y ω t₁ ∈ A₁ ∧ (∀ s ≤ t₁, walkPos y ω s ∉ B₁) ∧
        walkPos y ω t₂ ∈ A₂ ∧ ∀ s, t₁ ≤ s → s ≤ t₂ → walkPos y ω s ∉ B₂} := by
    ext ω
    simp [reachesThen]
  rw [h]
  refine MeasurableSet.iUnion fun t₁ => MeasurableSet.iUnion fun t₂ => ?_
  refine measurableSet_setOf.2 ((measurable_const (a := t₁ ≤ t₂)).and
    ((measurable_walkPos_pred y (· ∈ A₁) t₁).and ((Measurable.forall fun s =>
      measurable_walkPos_pred y (fun z => s ≤ t₁ → z ∉ B₁) s).and
      ((measurable_walkPos_pred y (· ∈ A₂) t₂).and (Measurable.forall fun s =>
        measurable_walkPos_pred y (fun z => t₁ ≤ s → s ≤ t₂ → z ∉ B₂) s)))))

theorem reachesThen_subset {A₁ B₁ A₂ B₂ : Set (Site 2)} (h : B₂ ⊆ B₁) (y : Site 2) :
    reachesThen A₁ B₁ A₂ B₂ y ⊆ reaches A₂ B₂ y := by
  rintro ω ⟨t₁, t₂, h12, -, hB₁, hA₂, hB₂⟩
  refine ⟨t₂, hA₂, fun s hs => ?_⟩
  by_cases hst : t₁ ≤ s
  · exact hB₂ s hst hs
  · exact fun hB => hB₁ s (by omega) (h hB)

theorem reachesThen_eq_empty {A₁ B₁ A₂ B₂ : Set (Site 2)} {y : Site 2} (hy : y ∈ B₁) :
    reachesThen A₁ B₁ A₂ B₂ y = ∅ := by
  ext ω
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨t₁, t₂, -, -, hB₁, -⟩
  exact hB₁ 0 (Nat.zero_le _) (by rwa [walkPos_zero'])

theorem prob_reachesThen_step {A₁ B₁ A₂ B₂ : Set (Site 2)} {y : Site 2} (hyA : y ∉ A₁)
    (hyB : y ∉ B₁) :
    prob (reachesThen A₁ B₁ A₂ B₂ y) =
      (∑ a : Dir 2, prob (reachesThen A₁ B₁ A₂ B₂ (y + dirVec a))) / 4 := by
  have hset : reachesThen A₁ B₁ A₂ B₂ y =
      {ω | shiftBy 1 ω ∈ reachesThen A₁ B₁ A₂ B₂ (y + dirVec (ω 0))} := by
    ext ω
    simp only [reachesThen, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t₁, t₂, h12, hA₁, hB₁, hA₂, hB₂⟩
      rcases Nat.eq_zero_or_pos t₁ with h0 | hpos
      · rw [h0, walkPos_zero'] at hA₁
        exact absurd hA₁ hyA
      obtain ⟨t₁', rfl⟩ : ∃ t, t₁ = 1 + t := ⟨t₁ - 1, by omega⟩
      obtain ⟨t₂', rfl⟩ : ∃ t, t₂ = 1 + t := ⟨t₂ - 1, by omega⟩
      refine ⟨t₁', t₂', by omega, by rwa [← walkPos_one_add], fun s hs => ?_,
        by rwa [← walkPos_one_add], fun s hs1 hs2 => ?_⟩
      · rw [← walkPos_one_add]
        exact hB₁ (1 + s) (by omega)
      · rw [← walkPos_one_add]
        exact hB₂ (1 + s) (by omega) (by omega)
    · rintro ⟨t₁, t₂, h12, hA₁, hB₁, hA₂, hB₂⟩
      refine ⟨1 + t₁, 1 + t₂, by omega, by rwa [walkPos_one_add], fun s hs => ?_,
        by rwa [walkPos_one_add], fun s hs1 hs2 => ?_⟩
      · rcases Nat.eq_zero_or_pos s with rfl | hpos
        · rwa [walkPos_zero']
        · obtain ⟨s', rfl⟩ : ∃ s', s = 1 + s' := ⟨s - 1, by omega⟩
          rw [walkPos_one_add]
          exact hB₁ s' (by omega)
      · obtain ⟨s', rfl⟩ : ∃ s', s = 1 + s' := ⟨s - 1, by omega⟩
        rw [walkPos_one_add]
        exact hB₂ s' (by omega) (by omega)
  rw [hset, prob_firstStep (fun a => reachesThen A₁ B₁ A₂ B₂ (y + dirVec a))
    (fun a => measurableSet_reachesThen _ _ _ _ _), ← Finset.mul_sum]
  ring

/-- The sites at distance less than `R` from `z` outside `B`, as a finite set. -/
def ballMinus (z : Site 2) (R : ℝ) (B : Set (Site 2)) : Finset (Site 2) := by
  classical exact ((ballFinset 2 R).image (fun x => z + x)).filter fun w =>
    euclidNorm (w - z) < R ∧ w ∉ B

theorem mem_ballMinus {z : Site 2} {R : ℝ} {B : Set (Site 2)} {w : Site 2} :
    w ∈ ballMinus z R B ↔ euclidNorm (w - z) < R ∧ w ∉ B := by
  classical
  unfold ballMinus
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · exact fun h => h.2
  · intro hw
    exact ⟨⟨w - z, mem_ballFinset_iff.2 hw.1.le, by abel⟩, hw⟩

/-- Comparison of two probabilities of reaching a set outside a disk around `z`, through their
values on the exit layer and on `B`. -/
theorem le_of_ball_compare {z : Site 2} {R : ℝ} {B : Set (Site 2)} (f g : Site 2 → ℝ)
    (hf : ∀ y, euclidNorm (y - z) < R → y ∉ B → f y = (∑ a : Dir 2, f (y + dirVec a)) / 4)
    (hg : ∀ y, euclidNorm (y - z) < R → y ∉ B → g y = (∑ a : Dir 2, g (y + dirVec a)) / 4)
    (hB : ∀ y ∈ B, f y ≤ g y)
    (hout : ∀ y, R ≤ euclidNorm (y - z) → euclidNorm (y - z) < R + 1 → y ∉ B → f y ≤ g y)
    {y : Site 2} (hy : euclidNorm (y - z) < R) : f y ≤ g y := by
  by_cases hyB : y ∈ B
  · exact hB y hyB
  refine le_of_mean_compare (ballMinus z R B) f g (fun w hw => ?_) (fun w hw => ?_)
    (fun w hw a ha => ?_) y (mem_ballMinus.2 ⟨hy, hyB⟩)
  · obtain ⟨h1, h2⟩ := mem_ballMinus.1 hw
    exact hf w h1 h2
  · obtain ⟨h1, h2⟩ := mem_ballMinus.1 hw
    exact hg w h1 h2
  · obtain ⟨h1, _⟩ := mem_ballMinus.1 hw
    by_cases hB' : w + dirVec a ∈ B
    · exact hB _ hB'
    · have hR : R ≤ euclidNorm (w + dirVec a - z) := by
        by_contra hlt
        exact ha (mem_ballMinus.2 ⟨not_le.1 hlt, hB'⟩)
      have hlt : euclidNorm (w + dirVec a - z) < R + 1 := by
        have := euclidNorm_add_dirVec_le (w - z) a
        rw [sub_add_eq_add_sub] at this
        linarith
      exact hout _ hR hlt hB'

theorem prob_firstStep_le {f g : Site 2 → Set (ℕ → Dir 2)} {z : Site 2} {c : ℝ}
    (h : ∀ a : Dir 2, prob (f (z + dirVec a)) ≤ c * prob (g (z + dirVec a)))
    (hf : ∀ y, MeasurableSet (f y)) (hg : ∀ y, MeasurableSet (g y)) :
    prob {ω | shiftBy 1 ω ∈ f (z + dirVec (ω 0))} ≤
      c * prob {ω | shiftBy 1 ω ∈ g (z + dirVec (ω 0))} := by
  rw [prob_firstStep (fun a => f (z + dirVec a)) (fun a => hf _),
    prob_firstStep (fun a => g (z + dirVec a)) (fun a => hg _), Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have := h a
  nlinarith

/-- The unit vector along `z` puts the path `α`, apart from `z`, behind `z`. -/
theorem ReentryData.coordAlong_neg (S : ReentryData) {a : Site 2} (ha : a ∈ S.α) (haz : a ≠ S.z) :
    coordAlong S.z ((S.z 0 : ℝ) / euclidNorm S.z) ((S.z 1 : ℝ) / euclidNorm S.z) a < 0 := by
  have ha' := S.norm_lt a ha haz
  have hk0 : (0 : ℝ) < S.k := lt_of_le_of_lt (euclidNorm_nonneg a) ha'
  have hz : 0 < euclidNorm S.z := lt_of_lt_of_le hk0 S.le_norm_z
  have hza := S.le_norm_z
  have hz2 := euclidNorm_sub_sq S.z 0
  have ha2 := euclidNorm_sub_sq a 0
  simp only [sub_zero, Pi.zero_apply, Int.cast_zero] at hz2 ha2
  have hcs : ((S.z 0 : ℝ) * (a 0 : ℝ) + (S.z 1 : ℝ) * (a 1 : ℝ)) ≤ euclidNorm S.z * euclidNorm a := by
    have h1 : ((S.z 0 : ℝ) * (a 0 : ℝ) + (S.z 1 : ℝ) * (a 1 : ℝ)) ^ 2 ≤
        (euclidNorm S.z * euclidNorm a) ^ 2 := by
      rw [mul_pow, hz2, ha2]
      nlinarith [sq_nonneg ((S.z 0 : ℝ) * (a 1 : ℝ) - (S.z 1 : ℝ) * (a 0 : ℝ))]
    exact abs_le_of_sq_le_sq' h1 (mul_nonneg (euclidNorm_nonneg _) (euclidNorm_nonneg _)) |>.2
  rw [coordAlong]
  have e : (S.z 0 : ℝ) / euclidNorm S.z * ((a 0 : ℝ) - (S.z 0 : ℝ)) +
      (S.z 1 : ℝ) / euclidNorm S.z * ((a 1 : ℝ) - (S.z 1 : ℝ)) =
      ((S.z 0 : ℝ) * (a 0 : ℝ) + (S.z 1 : ℝ) * (a 1 : ℝ) - euclidNorm S.z ^ 2) /
        euclidNorm S.z := by
    rw [hz2]
    field_simp
    ring
  rw [e, div_neg_iff]
  right
  refine ⟨?_, hz⟩
  nlinarith

/-- From a cone exit point of the disk of radius `k / 2` around `z`, the walk reaches distance
`2k` before `α` with probability at least `c`. -/
theorem cone_exit_lower : ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ S : ReentryData, k₀ ≤ S.k →
    ∀ y : Site 2, (S.k : ℝ) / 2 ≤ euclidNorm (y - S.z) → euclidNorm (y - S.z) < S.k / 2 + 1 →
      euclidNorm (y - S.z) <
        4 * coordAlong S.z ((S.z 0 : ℝ) / euclidNorm S.z) ((S.z 1 : ℝ) / euclidNorm S.z) y →
      c ≤ prob (reaches {w | 2 * (S.k : ℝ) ≤ euclidNorm w} S.α y) := by
  obtain ⟨D, ρ₀, hD, hρ₀, hlow⟩ := log_le_exitsAvoiding
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (ρ₀ + 14 * D + 40)
  refine ⟨1 / 14, by norm_num, N₀, fun S hk y hy1 hy2 hcone => ?_⟩
  have hkN : (N₀ : ℝ) ≤ S.k := by exact_mod_cast hk
  set k : ℝ := (S.k : ℝ)
  have hk40 : 40 ≤ k := by linarith
  have hz := S.le_norm_z
  have hz1 := S.norm_z_lt
  have hz0 : 0 < euclidNorm S.z := by linarith
  set c := coordAlong S.z ((S.z 0 : ℝ) / euclidNorm S.z) ((S.z 1 : ℝ) / euclidNorm S.z) y
  have hc : (S.z 0 : ℝ) * ((y 0 : ℝ) - (S.z 0 : ℝ)) + (S.z 1 : ℝ) * ((y 1 : ℝ) - (S.z 1 : ℝ)) =
      euclidNorm S.z * c := by
    simp only [c, coordAlong]
    field_simp
  have hy2' := euclidNorm_sub_sq y 0
  have hz2 := euclidNorm_sub_sq S.z 0
  have hyz2 := euclidNorm_sub_sq y S.z
  simp only [sub_zero, Pi.zero_apply, Int.cast_zero] at hy2' hz2
  have hsq : euclidNorm y ^ 2 = euclidNorm S.z ^ 2 + 2 * (euclidNorm S.z * c) +
      euclidNorm (y - S.z) ^ 2 := by
    rw [hy2', hz2, hyz2, ← hc]
    ring
  have hcpos : euclidNorm (y - S.z) / 4 < c := by linarith
  have hylow : (6 / 5 * k) ^ 2 ≤ euclidNorm y ^ 2 := by
    rw [hsq]
    have h1 : k ^ 2 ≤ euclidNorm S.z ^ 2 := by nlinarith
    have h2 : k * (k / 2) / 4 ≤ euclidNorm S.z * c := by
      have := mul_le_mul hz (show k / 2 / 4 ≤ c by linarith) (by positivity) hz0.le
      linarith
    have h3 : (k / 2) ^ 2 ≤ euclidNorm (y - S.z) ^ 2 := by nlinarith
    nlinarith
  have hy65 : 6 / 5 * k ≤ euclidNorm y := (abs_le_of_sq_le_sq' hylow (euclidNorm_nonneg _)).2
  have hyup : euclidNorm y < 2 * k := by
    have := euclidNorm_add_le (y - S.z) S.z
    rw [sub_add_cancel] at this
    linarith
  have hsub : crosses (k + 1) (2 * k) y ⊆ reaches {w | 2 * k ≤ euclidNorm w} S.α y :=
    reaches_mono subset_rfl (fun a ha => by
      simp only [Set.mem_setOf_eq]
      exact (S.norm_lt_succ ha).le) y
  have hL := hlow (k + 1) (2 * k) (by linarith) y (by linarith) hyup
  have hnum : 1 / 14 ≤ Real.log (euclidNorm y / (k + 1)) - D / (k + 1 - 1) := by
    have hpos : 0 < euclidNorm y / (k + 1) := div_pos (by linarith) (by linarith)
    have h1 := Real.one_sub_inv_le_log_of_pos hpos
    have h2 : (euclidNorm y / (k + 1))⁻¹ ≤ 6 / 7 := by
      rw [inv_div, div_le_iff₀ (by linarith)]
      linarith
    have h3 : D / (k + 1 - 1) ≤ 1 / 14 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  have hden0 : 0 < Real.log ((2 * k + 1) / (k + 1)) :=
    Real.log_pos ((one_lt_div (by linarith)).2 (by linarith))
  have hden1 : Real.log ((2 * k + 1) / (k + 1)) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < (2 * k + 1) / (k + 1) by positivity)
    have h2 : (2 * k + 1) / (k + 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  calc (1 : ℝ) / 14 ≤ (1 / 14) / Real.log ((2 * k + 1) / (k + 1)) := by
        rw [le_div_iff₀ hden0]
        nlinarith
    _ ≤ (Real.log (euclidNorm y / (k + 1)) - D / (k + 1 - 1)) /
        Real.log ((2 * k + 1) / (k + 1)) := div_le_div_of_nonneg_right hnum hden0.le
    _ ≤ prob (crosses (k + 1) (2 * k) y) := hL
    _ ≤ prob (reaches {w | 2 * k ≤ euclidNorm w} S.α y) := prob_mono hsub

/-- The outward Beurling estimate from the disk of radius `r`: the walk reaches distance `2k`
before `α` with probability at most `C √(r / k)`. -/
theorem prob_reaches_far_from_disk_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ S : ReentryData, ∀ r : ℕ, 1 ≤ r →
    64 * r ≤ S.k → ∀ u : Site 2, euclidNorm u < r →
      prob (reaches {y | 2 * (S.k : ℝ) ≤ euclidNorm y} S.α u) ≤ C * Real.sqrt ((r : ℝ) / S.k) := by
  obtain ⟨c, hc, hB⟩ := beurling_crossing
  refine ⟨3 * c, by positivity, fun S r hr hrk u hu => ?_⟩
  set k : ℝ := (S.k : ℝ)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrk' : 64 * (r : ℝ) ≤ k := by
    have : ((64 * r : ℕ) : ℝ) ≤ S.k := by exact_mod_cast hrk
    push_cast at this
    exact this
  set j₁ : ℕ := ⌊(k - r - 1) / 2⌋₊ with hj₁
  have hj₁le : (j₁ : ℝ) ≤ (k - r - 1) / 2 := Nat.floor_le (by linarith)
  have hj₁gt : (k - r - 1) / 2 - 1 < (j₁ : ℝ) := by
    have := Nat.lt_floor_add_one ((k - r - 1) / 2)
    rw [← hj₁] at this
    linarith
  have hj₀ : r + 1 < j₁ := by
    have : (r : ℝ) + 1 < j₁ := by linarith
    exact_mod_cast this
  have hsub : reaches {y | 2 * k ≤ euclidNorm y} S.α u ⊆ escapesFrom (2 * (j₁ : ℝ)) S.α u := by
    rintro ω ⟨t, ht, hs⟩
    refine ⟨t, ?_, fun s _ hs2 => hs s hs2⟩
    have h := euclidNorm_sub_le (walkPos u ω t) u
    simp only [Set.mem_setOf_eq] at ht
    linarith
  have hcross : ∀ j : ℕ, r + 1 ≤ j → j < j₁ → ∃ a ∈ S.α,
      (j : ℝ) ≤ euclidNorm (a - u) ∧ euclidNorm (a - u) < j + 1 := by
    intro j hj1 hj2
    have hj1' : ((r : ℝ) + 1) ≤ j := by exact_mod_cast hj1
    have hj2' : (j : ℝ) < j₁ := by exact_mod_cast hj2
    refine S.crossing_around u j ?_ ?_
    · rw [zero_sub, euclidNorm_neg]
      linarith
    · have h := euclidNorm_sub_le S.z u
      linarith [S.le_norm_z]
  have hb := hB S.α u (r + 1) j₁ (by omega) hj₀ hcross
  refine (prob_mono hsub).trans (hb.trans ?_)
  suffices key : Real.sqrt (((r + 1 : ℕ) : ℝ) / j₁) ≤ 3 * Real.sqrt ((r : ℝ) / k) by
    calc c * Real.sqrt (((r + 1 : ℕ) : ℝ) / j₁) ≤ c * (3 * Real.sqrt ((r : ℝ) / k)) :=
          mul_le_mul_of_nonneg_left key hc.le
      _ = 3 * c * Real.sqrt ((r : ℝ) / k) := by ring
  have hk0 : 0 < k := by linarith
  have hj₁pos : (0 : ℝ) < j₁ := by linarith
  have h1 : ((r + 1 : ℕ) : ℝ) / j₁ ≤ 9 * ((r : ℝ) / k) := by
    rw [div_le_iff₀ hj₁pos]
    push_cast
    have : (r : ℝ) / k * k = r := div_mul_cancel₀ _ hk0.ne'
    nlinarith
  calc Real.sqrt (((r + 1 : ℕ) : ℝ) / j₁) ≤ Real.sqrt (9 * ((r : ℝ) / k)) :=
        Real.sqrt_le_sqrt h1
    _ = 3 * Real.sqrt ((r : ℝ) / k) := by
        rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]

/-- Comparison from below inside the disk of radius `ρ`. -/
theorem mul_exit_le_reaches {A B : Set (Site 2)} {ρ m : ℝ}
    (hA : ∀ y, euclidNorm y < ρ → y ∉ A)
    (hlayer : ∀ y, ρ ≤ euclidNorm y → euclidNorm y < ρ + 1 → y ∉ B → m ≤ prob (reaches A B y))
    {w : Site 2} (hw : euclidNorm w < ρ) :
    m * prob (reaches {y | ρ ≤ euclidNorm y} B w) ≤ prob (reaches A B w) := by
  by_cases hwB : w ∈ B
  · rw [reaches_eq_empty hwB, reaches_eq_empty hwB, prob_empty, mul_zero]
  refine le_of_mean_compare (diskMinus ρ B) (fun y => m * prob (reaches {y | ρ ≤ euclidNorm y} B y))
    (fun y => prob (reaches A B y)) (fun y hy => ?_) (fun y hy => ?_) (fun y hy a ha => ?_) w
    (mem_diskMinus.2 ⟨hw, hwB⟩)
  · obtain ⟨h1, h2⟩ := mem_diskMinus.1 hy
    rw [prob_reaches_step (show y ∉ {y | ρ ≤ euclidNorm y} by simpa using h1) h2,
      mul_div_assoc', Finset.mul_sum]
  · obtain ⟨h1, h2⟩ := mem_diskMinus.1 hy
    exact prob_reaches_step (hA y h1) h2
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
      exact hlayer _ hρ hlt hB

theorem prob_firstStep_mul_le {f g : Site 2 → Set (ℕ → Dir 2)} {z : Site 2} {c : ℝ}
    (h : ∀ a : Dir 2, c * prob (f (z + dirVec a)) ≤ prob (g (z + dirVec a)))
    (hf : ∀ y, MeasurableSet (f y)) (hg : ∀ y, MeasurableSet (g y)) :
    c * prob {ω | shiftBy 1 ω ∈ f (z + dirVec (ω 0))} ≤
      prob {ω | shiftBy 1 ω ∈ g (z + dirVec (ω 0))} := by
  rw [prob_firstStep (fun a => f (z + dirVec a)) (fun a => hf _),
    prob_firstStep (fun a => g (z + dirVec a)) (fun a => hg _), Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have := h a
  nlinarith

/-- **The reentry ratio** (Barlow and Masson (2011), proof of Lemma 2.4). For the walk from `z` at
positive times, reaching the disk of radius `r` before `α ∪ K` and then `K` before `α` has
probability at most `C r / k` times the probability of reaching `K` before `α`. -/
theorem reentry_ratio_le : ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ r₀ : ℕ, ∀ S : ReentryData, k₀ ≤ S.k →
    ∀ r : ℕ, r₀ ≤ r → 64 * r ≤ S.k →
      prob {ω | shiftBy 1 ω ∈ reachesThen {w | euclidNorm w < r} (S.α ∪ S.K) S.K S.α
          (S.z + dirVec (ω 0))} ≤
        C * ((r : ℝ) / S.k) * prob (reachesAfter S.K S.α S.z) := by
  classical
  obtain ⟨Cf, hCf, kf, hFcmp⟩ := prob_reaches_le_mul
  obtain ⟨Co, hCo, hout⟩ := prob_reaches_far_from_disk_le
  obtain ⟨Cin, hCin, kin, rin, hin⟩ := prob_reaches_disk_inward_le
  obtain ⟨cL, hcL, kL, hcone⟩ := cone_exit_lower
  refine ⟨Cf * Co * Cin * 17 / cL, by positivity, max (max kf kin) (max kL 64), max rin 1,
    fun S hk r hr hrk => ?_⟩
  have hkf : kf ≤ S.k := le_trans (le_max_left _ _) (le_of_max_le_left hk)
  have hkin : kin ≤ S.k := le_trans (le_max_right _ _) (le_of_max_le_left hk)
  have hkL : kL ≤ S.k := le_trans (le_max_left _ _) (le_of_max_le_right hk)
  have hk64 : (64 : ℝ) ≤ S.k := by exact_mod_cast le_trans (le_max_right _ _) (le_of_max_le_right hk)
  have hrin : rin ≤ r := le_of_max_le_left hr
  have hr1 : 1 ≤ r := le_of_max_le_right hr
  set k : ℝ := (S.k : ℝ) with hkdef
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrk' : 64 * (r : ℝ) ≤ k := by
    have : ((64 * r : ℕ) : ℝ) ≤ S.k := by exact_mod_cast hrk
    push_cast at this
    exact this
  have hρ₁ : k ^ 2 ≤ S.ρ₁ := S.sq_le_ρ₁
  have hz := S.le_norm_z
  have hz1 := S.norm_z_lt
  have hz0 : 0 < euclidNorm S.z := by linarith
  set sq := Real.sqrt ((r : ℝ) / k) with hsq
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hsqsq : sq * sq = (r : ℝ) / k := Real.mul_self_sqrt (by positivity)
  set A₁ : Set (Site 2) := {w | euclidNorm w < r} with hA₁
  set B₁ : Set (Site 2) := S.α ∪ S.K with hB₁
  set R : ℝ := k / 2 with hR
  set F : Site 2 → ℝ := fun y => prob (reaches S.K S.α y) with hF
  set Ψ : Site 2 → ℝ := fun y => prob (reaches {w | 2 * k ≤ euclidNorm w} S.α y) with hΨ
  have hKfar : ∀ y, euclidNorm y < 2 * k + 2 → y ∉ S.K :=
    fun y hy => S.not_mem_K_of_norm_lt (by nlinarith)
  obtain ⟨yM, hyM, hmax⟩ := (layer S.k).exists_max_image F (layer_nonempty S.k)
  obtain ⟨ym, hym, hmin⟩ := (layer S.k).exists_min_image F (layer_nonempty S.k)
  have hyM' := mem_layer.1 hyM
  have hym' := mem_layer.1 hym
  have hFratio : F yM ≤ Cf * F ym := hFcmp S hkf yM ym hyM'.2 hym'.1 hym'.2
  have hFyM0 : 0 ≤ F yM := prob_nonneg _
  have hFym0 : 0 ≤ F ym := prob_nonneg _
  -- the values of `F` on the disk of radius `r`
  have hFdisk : ∀ u, euclidNorm u < r → F u ≤ F yM * (Co * sq) := by
    intro u hu
    have h1 : F u ≤ F yM * Ψ u :=
      reaches_le_mul_exit (fun y hy => hKfar y (by linarith))
        (fun y h1 h2 => hmax y (mem_layer.2 ⟨h1, h2⟩)) (by linarith)
    exact h1.trans (mul_le_mul_of_nonneg_left (hout S r hr1 hrk u hu) hFyM0)
  set M₁ := F yM * (Co * sq) with hM₁
  have hM₁0 : 0 ≤ M₁ := by positivity
  -- the numerator
  have hG : ∀ y, prob (reachesThen A₁ B₁ S.K S.α y) ≤ M₁ * prob (reaches A₁ B₁ y) := by
    have hbd : ∀ y, (y ∈ A₁ ∨ y ∈ B₁) →
        prob (reachesThen A₁ B₁ S.K S.α y) ≤ M₁ * prob (reaches A₁ B₁ y) := by
      intro y hy
      by_cases hyB : y ∈ B₁
      · rw [reachesThen_eq_empty hyB, prob_empty]
        exact mul_nonneg hM₁0 (prob_nonneg _)
      · have hyA : y ∈ A₁ := hy.resolve_right hyB
        rw [reaches_eq_univ hyA hyB, prob_univ, mul_one]
        exact (prob_mono (reachesThen_subset Set.subset_union_left y)).trans (hFdisk y hyA)
    intro y
    by_cases hyAB : y ∈ A₁ ∨ y ∈ B₁
    · exact hbd y hyAB
    push Not at hyAB
    have hyρ : euclidNorm y < S.ρ₂ := by
      by_contra h
      exact hyAB.2 (Or.inr (S.mem_K y (not_lt.1 h)))
    refine le_of_mean_compare (diskMinus S.ρ₂ (B₁ ∪ A₁))
      (fun y => prob (reachesThen A₁ B₁ S.K S.α y)) (fun y => M₁ * prob (reaches A₁ B₁ y))
      (fun y hy => ?_) (fun y hy => ?_) (fun y hy a ha => ?_) y
      (mem_diskMinus.2 ⟨hyρ, fun h => h.elim hyAB.2 hyAB.1⟩)
    · obtain ⟨_, h2⟩ := mem_diskMinus.1 hy
      exact prob_reachesThen_step (fun h => h2 (Or.inr h)) (fun h => h2 (Or.inl h))
    · obtain ⟨_, h2⟩ := mem_diskMinus.1 hy
      rw [prob_reaches_step (fun h => h2 (Or.inr h)) (fun h => h2 (Or.inl h)), mul_div_assoc',
        Finset.mul_sum]
    · refine hbd _ ?_
      by_contra hcon
      push Not at hcon
      by_cases hlt : euclidNorm (y + dirVec a) < S.ρ₂
      · exact ha (mem_diskMinus.2 ⟨hlt, fun h => h.elim hcon.2 hcon.1⟩)
      · exact hcon.2 (Or.inr (S.mem_K _ (not_lt.1 hlt)))
  -- the probability of reaching the disk of radius `r`
  set Out : Set (Site 2) := {w | R ≤ euclidNorm (w - S.z)} with hOut
  have hH : ∀ y, euclidNorm (y - S.z) < R →
      prob (reaches A₁ B₁ y) ≤ Cin * sq * prob (reaches Out S.α y) := by
    intro y hy
    refine le_of_ball_compare (B := S.α) (fun y => prob (reaches A₁ B₁ y))
      (fun y => Cin * sq * prob (reaches Out S.α y)) (fun y hy1 hy2 => ?_) (fun y hy1 hy2 => ?_)
      (fun y hy' => ?_) (fun y hy1 hy2 hy3 => ?_) hy
    · have hyn : R < euclidNorm y := by
        have := euclidNorm_sub_le S.z y
        rw [euclidNorm_sub_comm] at this
        linarith
      refine prob_reaches_step (fun h => ?_) (fun h => h.elim hy2 (hKfar y (by
        have := euclidNorm_add_le (y - S.z) S.z
        rw [sub_add_cancel] at this
        linarith)))
      have : euclidNorm y < r := h
      linarith
    · rw [prob_reaches_step (show y ∉ Out by simpa [hOut] using hy1) hy2, mul_div_assoc',
        Finset.mul_sum]
    · rw [reaches_eq_empty (Or.inl hy' : y ∈ B₁), prob_empty]
      exact mul_nonneg (mul_nonneg hCin hsq0) (prob_nonneg _)
    · rw [reaches_eq_univ (show y ∈ Out from hy1) hy3, prob_univ, mul_one]
      refine hin S hkin r hrin hrk y ?_ ?_
      · have := euclidNorm_sub_le S.z y
        rw [euclidNorm_sub_comm] at this
        linarith
      · have := euclidNorm_add_le (y - S.z) S.z
        rw [sub_add_cancel] at this
        linarith
  -- the denominator
  set u₁ := (S.z 0 : ℝ) / euclidNorm S.z
  set u₂ := (S.z 1 : ℝ) / euclidNorm S.z
  have hu : u₁ ^ 2 + u₂ ^ 2 = 1 := by
    have hz2 := euclidNorm_sub_sq S.z 0
    simp only [sub_zero, Pi.zero_apply, Int.cast_zero] at hz2
    simp only [u₁, u₂, div_pow]
    rw [← add_div, ← hz2, div_self (by positivity)]
  set Cone : Set (Site 2) :=
    {w | R ≤ euclidNorm (w - S.z) ∧ euclidNorm (w - S.z) < 4 * coordAlong S.z u₁ u₂ w}
  set Non : Set (Site 2) :=
    {w | R ≤ euclidNorm (w - S.z) ∧ 4 * coordAlong S.z u₁ u₂ w ≤ euclidNorm (w - S.z)}
  have hΨcone : ∀ y, euclidNorm (y - S.z) < R →
      cL * prob (reaches Cone (S.α ∪ Non) y) ≤ Ψ y := by
    intro y hy
    refine le_of_ball_compare (B := S.α) (fun y => cL * prob (reaches Cone (S.α ∪ Non) y)) Ψ
      (fun y hy1 hy2 => ?_) (fun y hy1 hy2 => ?_)
      (fun y hy' => ?_) (fun y hy1 hy2 hy3 => ?_) hy
    · rw [prob_reaches_step (fun h => absurd h.1 (not_le.2 hy1))
        (fun h => h.elim hy2 (fun h' => absurd h'.1 (not_le.2 hy1))), mul_div_assoc',
        Finset.mul_sum]
    · refine prob_reaches_step (fun h => ?_) hy2
      have : 2 * k ≤ euclidNorm y := h
      have := euclidNorm_add_le (y - S.z) S.z
      rw [sub_add_cancel] at this
      linarith
    · rw [reaches_eq_empty (Or.inl hy' : y ∈ S.α ∪ Non), prob_empty, mul_zero]
      exact prob_nonneg _
    · by_cases hc : euclidNorm (y - S.z) < 4 * coordAlong S.z u₁ u₂ y
      · rw [reaches_eq_univ (show y ∈ Cone from ⟨hy1, hc⟩)
          (fun h => h.elim hy3 (fun h' => absurd h'.2 (not_le.2 hc))), prob_univ, mul_one]
        exact hcone S hkL y hy1 hy2 hc
      · rw [reaches_eq_empty (Or.inr ⟨hy1, not_lt.1 hc⟩ : y ∈ S.α ∪ Non), prob_empty, mul_zero]
        exact prob_nonneg _
  have hstepR : ∀ a : Dir 2, euclidNorm (S.z + dirVec a - S.z) < R := by
    intro a
    rw [add_sub_cancel_left, euclidNorm_dirVec]
    linarith
  have hN := prob_firstStep_le (f := reachesThen A₁ B₁ S.K S.α) (g := reaches A₁ B₁) (z := S.z)
    (c := M₁) (fun a => hG _) (fun _ => measurableSet_reachesThen _ _ _ _ _)
    (fun _ => measurableSet_reaches _ _ _)
  have hHa := prob_firstStep_le (f := reaches A₁ B₁) (g := reaches Out S.α) (z := S.z)
    (c := Cin * sq) (fun a => hH _ (hstepR a)) (fun _ => measurableSet_reaches _ _ _)
    (fun _ => measurableSet_reaches _ _ _)
  have hDa := prob_firstStep_mul_le (f := reaches {w | 2 * k ≤ euclidNorm w} S.α)
    (g := reaches S.K S.α) (z := S.z) (c := F ym) (fun a => mul_exit_le_reaches
      (fun y hy => hKfar y (by linarith)) (fun y h1 h2 _ => hmin y (mem_layer.2 ⟨h1, h2⟩)) (by
        have := euclidNorm_add_dirVec_le S.z a
        linarith)) (fun _ => measurableSet_reaches _ _ _) (fun _ => measurableSet_reaches _ _ _)
  have hCa := prob_firstStep_mul_le (f := reaches Cone (S.α ∪ Non))
    (g := reaches {w | 2 * k ≤ euclidNorm w} S.α) (z := S.z) (c := cL)
    (fun a => hΨcone _ (hstepR a)) (fun _ => measurableSet_reaches _ _ _)
    (fun _ => measurableSet_reaches _ _ _)
  have hcone17 := escape_le_cone_escape (z := S.z) (R := R) hu (by linarith)
    (α := S.α) (fun w hw hwz => S.coordAlong_neg hw hwz)
  -- assembly
  set G := prob {ω | shiftBy 1 ω ∈ reachesThen A₁ B₁ S.K S.α (S.z + dirVec (ω 0))}
  set Hp := prob {ω | shiftBy 1 ω ∈ reaches A₁ B₁ (S.z + dirVec (ω 0))}
  set V := prob (reachesAfter Out S.α S.z)
  set U := prob (reachesAfter Cone (S.α ∪ Non) S.z)
  set Pa := prob {ω | shiftBy 1 ω ∈ reaches {w | 2 * k ≤ euclidNorm w} S.α (S.z + dirVec (ω 0))}
  set Da := prob (reachesAfter S.K S.α S.z)
  change G ≤ M₁ * Hp at hN
  change Hp ≤ Cin * sq * V at hHa
  change F ym * Pa ≤ Da at hDa
  change cL * U ≤ Pa at hCa
  change V ≤ 17 * U at hcone17
  change G ≤ Cf * Co * Cin * 17 / cL * ((r : ℝ) / k) * Da
  have hV0 : 0 ≤ V := prob_nonneg _
  have hU0 : 0 ≤ U := prob_nonneg _
  have h1 : G ≤ F yM * (Co * sq) * (Cin * sq * V) :=
    hN.trans (mul_le_mul_of_nonneg_left hHa hM₁0)
  have h2 : F yM * (Co * sq) * (Cin * sq * V) = F yM * Co * Cin * ((r : ℝ) / k) * V := by
    rw [← hsqsq]
    ring
  have h3 : F yM * Co * Cin * ((r : ℝ) / k) * V ≤ Cf * F ym * Co * Cin * ((r : ℝ) / k) * (17 * U) := by
    have hrk0 : 0 ≤ (r : ℝ) / k := by positivity
    have := mul_le_mul hFratio hcone17 hV0 (by positivity)
    calc F yM * Co * Cin * ((r : ℝ) / k) * V = (F yM * V) * (Co * Cin * ((r : ℝ) / k)) := by ring
      _ ≤ (Cf * F ym * (17 * U)) * (Co * Cin * ((r : ℝ) / k)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  have h4 : F ym * U ≤ Da / cL := by
    rw [le_div_iff₀ hcL]
    have := mul_le_mul_of_nonneg_left hCa hFym0
    nlinarith
  calc G ≤ Cf * F ym * Co * Cin * ((r : ℝ) / k) * (17 * U) := by linarith
    _ = Cf * Co * Cin * 17 * ((r : ℝ) / k) * (F ym * U) := by ring
    _ ≤ Cf * Co * Cin * 17 * ((r : ℝ) / k) * (Da / cL) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = Cf * Co * Cin * 17 / cL * ((r : ℝ) / k) * Da := by ring

end FiniteAvalanches.Walk.BarlowMasson
