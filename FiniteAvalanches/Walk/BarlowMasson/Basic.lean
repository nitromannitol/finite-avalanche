import FiniteAvalanches.Walk.Beurling.Estimate

/-!
# Hitting events of the planar simple random walk

Elementary tools for the estimates of Barlow and Masson (2011), Section 2, for the simple random
walk on `ℤ²` driven by independent uniform directions.

* `reaches A B y`: the walk started at `y` visits `A` at some time `t` and avoids `B` at all
  times `s ≤ t`, time `0` included. Its probability is the mean of its values at the four
  neighbours of every site outside `A ∪ B` (`prob_reaches_step`).
* `reachesAfter A B y`: the same event for the walk after its first step, so that `B` is avoided
  at the positive times only.
* `le_of_mean`: the maximum principle on a finite set of sites.
* `exitsAvoiding_le_log` and `log_le_exitsAvoiding`: two-sided bounds, by logarithms, for the
  probability of reaching the circle of radius `m` before the closed disk of radius `ρ`.

M. T. Barlow and R. Masson, *Exponential tail bounds for loop-erased random walk in two
dimensions*, Ann. Probab. 38 (2010); *Spectral dimension and random walks on the two dimensional
uniform spanning tree*, Comm. Math. Phys. 305 (2011).
-/

noncomputable section

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory FiniteAvalanches.Walk.Beurling

/-! ### Probabilities -/

theorem prob_nonneg (E : Set (ℕ → Dir 2)) : 0 ≤ prob E := ENNReal.toReal_nonneg

theorem prob_mono {E F : Set (ℕ → Dir 2)} (h : E ⊆ F) : prob E ≤ prob F :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h)

theorem prob_le_one' (E : Set (ℕ → Dir 2)) : prob E ≤ 1 := by
  have h : pathLaw 2 E ≤ 1 := MeasureTheory.prob_le_one
  simpa [prob] using ENNReal.toReal_mono ENNReal.one_ne_top h

theorem prob_union_le (E F : Set (ℕ → Dir 2)) : prob (E ∪ F) ≤ prob E + prob F := by
  unfold prob
  rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
    (measure_union_le _ _)

/-! ### Positions of the walk -/

theorem walkPos_zero' (y : Site 2) (ω : ℕ → Dir 2) : walkPos y ω 0 = y := by
  simp [walkPos]

theorem walkPos_one_add (y : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos y ω (1 + t) = walkPos (y + dirVec (ω 0)) (shiftBy 1 ω) t := by
  simp [walkPos, shiftBy, Finset.sum_range_add, add_assoc]

theorem walkPos_add_left (c y : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos (c + y) ω t = c + walkPos y ω t := by
  simp [walkPos, add_assoc]

theorem walkPos_eq_add (y : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos y ω t = y + walkPos 0 ω t := by
  simp [walkPos]

theorem walkPos_add_shiftBy (x : Site 2) (ω : ℕ → Dir 2) (j t : ℕ) :
    walkPos x ω (j + t) = walkPos (walkPos x ω j) (shiftBy j ω) t := by
  simp only [walkPos, shiftBy, Finset.sum_range_add, add_assoc]

theorem walkPos_congr_of_le (x : Site 2) {ω ω' : ℕ → Dir 2} {j : ℕ}
    (h : ∀ i < j, ω i = ω' i) {t : ℕ} (ht : t ≤ j) : walkPos x ω t = walkPos x ω' t := by
  unfold walkPos
  congr 1
  exact Finset.sum_congr rfl fun i hi => by rw [h i (by have := Finset.mem_range.mp hi; omega)]

/-! ### Reaching a set while avoiding another -/

/-- The walk started at `y` visits `A` at some time `t` and avoids `B` at all times `s ≤ t`,
time `0` included. -/
def reaches (A B : Set (Site 2)) (y : Site 2) : Set (ℕ → Dir 2) :=
  {ω | ∃ t, walkPos y ω t ∈ A ∧ ∀ s ≤ t, walkPos y ω s ∉ B}

/-- The event `reaches A B` for the walk after its first step: `B` is avoided at the positive
times up to the visit to `A`, and the visit happens at a positive time. -/
def reachesAfter (A B : Set (Site 2)) (y : Site 2) : Set (ℕ → Dir 2) :=
  {ω | shiftBy 1 ω ∈ reaches A B (y + dirVec (ω 0))}

theorem measurableSet_reaches (A B : Set (Site 2)) (y : Site 2) :
    MeasurableSet (reaches A B y) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    (measurable_walkPos_pred y (· ∈ A) t).and <| Measurable.forall fun s =>
      measurable_walkPos_pred y (fun z => s ≤ t → z ∉ B) s

theorem reaches_eq_empty {A B : Set (Site 2)} {y : Site 2} (hy : y ∈ B) :
    reaches A B y = ∅ := by
  ext ω
  simp only [reaches, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
    not_forall, not_not]
  exact fun t _ => ⟨0, Nat.zero_le _, by rwa [walkPos_zero']⟩

theorem reaches_eq_univ {A B : Set (Site 2)} {y : Site 2} (hyA : y ∈ A) (hyB : y ∉ B) :
    reaches A B y = Set.univ := by
  ext ω
  simp only [reaches, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  refine ⟨0, by rwa [walkPos_zero'], fun s hs => ?_⟩
  obtain rfl : s = 0 := by omega
  rwa [walkPos_zero']

theorem reaches_mono {A A' B B' : Set (Site 2)} (hA : A ⊆ A') (hB : B' ⊆ B) (y : Site 2) :
    reaches A B y ⊆ reaches A' B' y :=
  fun _ ⟨t, ht, hs⟩ => ⟨t, hA ht, fun s hst hB' => hs s hst (hB hB')⟩

theorem reaches_eq_firstStep {A B : Set (Site 2)} {y : Site 2} (hyA : y ∉ A) (hyB : y ∉ B) :
    reaches A B y = reachesAfter A B y := by
  ext ω
  simp only [reaches, reachesAfter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht, hs⟩
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · exact absurd (by rwa [walkPos_zero'] at ht) hyA
    · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
      refine ⟨t', by rwa [← walkPos_one_add], fun s hs' => ?_⟩
      rw [← walkPos_one_add]
      exact hs (1 + s) (by omega)
  · rintro ⟨t, ht, hs⟩
    refine ⟨1 + t, by rwa [walkPos_one_add], fun s hs' => ?_⟩
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · rwa [walkPos_zero']
    · obtain ⟨s', rfl⟩ : ∃ s', s = 1 + s' := ⟨s - 1, by omega⟩
      rw [walkPos_one_add]
      exact hs s' (by omega)

/-- The probability of `reachesAfter` is the mean of the probabilities of `reaches` at the four
neighbours. -/
theorem prob_reachesAfter (A B : Set (Site 2)) (y : Site 2) :
    prob (reachesAfter A B y) = (∑ a : Dir 2, prob (reaches A B (y + dirVec a))) / 4 := by
  rw [reachesAfter, prob_firstStep (fun a => reaches A B (y + dirVec a))
    (fun a => measurableSet_reaches _ _ _), ← Finset.mul_sum]
  ring

/-- Away from `A ∪ B`, the probability of `reaches A B` is the mean over the four neighbours. -/
theorem prob_reaches_step {A B : Set (Site 2)} {y : Site 2} (hyA : y ∉ A) (hyB : y ∉ B) :
    prob (reaches A B y) = (∑ a : Dir 2, prob (reaches A B (y + dirVec a))) / 4 := by
  rw [reaches_eq_firstStep hyA hyB, prob_reachesAfter]

theorem reaches_translate (A B : Set (Site 2)) (c y : Site 2) :
    reaches A B (c + y) = reaches {z | c + z ∈ A} {z | c + z ∈ B} y := by
  ext ω
  simp only [reaches, Set.mem_setOf_eq, walkPos_add_left]

/-! ### The maximum principle -/

theorem walkOp_eq_mean (u : Site 2 → ℝ) (y : Site 2) :
    walkOp u y = (∑ a : Dir 2, u (y + dirVec a)) / 4 := by
  rw [walkOp, nbrSum, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, dirVec_eq_unit, dirVec_eq_neg_unit, ← sub_eq_add_neg]
  norm_num

/-- The maximum principle on a finite set: a function that is the mean of its four neighbouring
values at every site of `Λ` is bounded on `Λ` by its bound at the neighbours outside `Λ`. -/
theorem le_of_mean (Λ : Finset (Site 2)) (g : Site 2 → ℝ) (M : ℝ)
    (hharm : ∀ y ∈ Λ, g y = (∑ a : Dir 2, g (y + dirVec a)) / 4)
    (hbd : ∀ y ∈ Λ, ∀ a : Dir 2, y + dirVec a ∉ Λ → g (y + dirVec a) ≤ M) :
    ∀ y ∈ Λ, g y ≤ M := by
  classical
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset Λ
  set g' : Site 2 → ℝ := fun x =>
    if x ∈ Λ ∨ ∃ y ∈ Λ, ∃ a : Dir 2, x = y + dirVec a then g x else M with hg'
  have hnear : ∀ y ∈ Λ, ∀ a : Dir 2, g' (y + dirVec a) = g (y + dirVec a) := fun y hy a => by
    have h : y + dirVec a ∈ Λ ∨ ∃ y' ∈ Λ, ∃ a' : Dir 2, y + dirVec a = y' + dirVec a' :=
      Or.inr ⟨y, hy, a, rfl⟩
    simp only [hg', h, ↓reduceIte]
  have hin : ∀ y ∈ Λ, g' y = g y := fun y hy => by
    simp only [hg', hy, true_or, ↓reduceIte]
  have key := le_of_harmonic_on_box (d := 2) (by norm_num) Λ ∅ g' M hq
    (fun y hy _ => by
      rw [walkOp_eq_mean, hin y hy, hharm y hy]
      congr 1
      exact Finset.sum_congr rfl fun a _ => hnear y hy a)
    (fun x hx => by
      by_cases h : x ∈ Λ ∨ ∃ y ∈ Λ, ∃ a : Dir 2, x = y + dirVec a
      · have hx' : g' x = g x := by simp only [hg', h, ↓reduceIte]
        rw [hx']
        rcases h with h | ⟨y, hy, a, rfl⟩
        · exact absurd h hx
        · exact hbd y hy a hx
      · have hx' : g' x = M := by simp only [hg', h, ↓reduceIte]
        rw [hx'])
    (fun x hx => absurd hx (Set.notMem_empty x))
  intro y hy
  rw [← hin y hy]
  exact key y

/-- The comparison principle on a finite set. -/
theorem le_of_mean_compare (Λ : Finset (Site 2)) (f g : Site 2 → ℝ)
    (hf : ∀ y ∈ Λ, f y = (∑ a : Dir 2, f (y + dirVec a)) / 4)
    (hg : ∀ y ∈ Λ, g y = (∑ a : Dir 2, g (y + dirVec a)) / 4)
    (hbd : ∀ y ∈ Λ, ∀ a : Dir 2, y + dirVec a ∉ Λ → f (y + dirVec a) ≤ g (y + dirVec a)) :
    ∀ y ∈ Λ, f y ≤ g y := by
  have h := le_of_mean Λ (fun y => f y - g y) 0
    (fun y hy => by
      simp only [Finset.sum_sub_distrib]
      rw [hf y hy, hg y hy]
      ring)
    (fun y hy a ha => by simpa using hbd y hy a ha)
  intro y hy
  linarith [h y hy]

/-! ### Euclidean norms -/

theorem euclidNorm_add_le (y z : Site 2) :
    euclidNorm (y + z) ≤ euclidNorm y + euclidNorm z := by
  have hnorm : ∀ x : Site 2,
      euclidNorm x = ‖(WithLp.toLp 2 fun i => ((x i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2))‖ :=
    fun x => by simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, euclidNorm]
  have hadd : (WithLp.toLp 2 fun i => (((y + z) i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2)) =
      (WithLp.toLp 2 fun i => ((y i : ℤ) : ℝ)) +
        (WithLp.toLp 2 fun i => ((z i : ℤ) : ℝ)) := by
    ext i
    simp
  rw [hnorm (y + z), hnorm y, hnorm z, hadd]
  exact norm_add_le _ _

theorem euclidNorm_neg (y : Site 2) : euclidNorm (-y) = euclidNorm y := by
  simp [euclidNorm]

theorem euclidNorm_sub_comm (y z : Site 2) : euclidNorm (y - z) = euclidNorm (z - y) := by
  rw [← neg_sub, euclidNorm_neg]

theorem euclidNorm_sub_le (y z : Site 2) : euclidNorm y - euclidNorm z ≤ euclidNorm (y - z) := by
  have h := euclidNorm_add_le (y - z) z
  rw [sub_add_cancel] at h
  linarith

theorem euclidNorm_dirVec (a : Dir 2) : euclidNorm (dirVec a) = 1 := by
  rcases a with ⟨i, b⟩
  fin_cases i <;> cases b <;> simp [euclidNorm, dirVec]

theorem euclidNorm_add_dirVec_le (y : Site 2) (a : Dir 2) :
    euclidNorm (y + dirVec a) ≤ euclidNorm y + 1 := by
  simpa [euclidNorm_dirVec] using euclidNorm_add_le y (dirVec a)

theorem le_euclidNorm_add_dirVec (y : Site 2) (a : Dir 2) :
    euclidNorm y ≤ euclidNorm (y + dirVec a) + 1 := by
  have h := euclidNorm_add_le (y + dirVec a) (-dirVec a)
  rwa [add_neg_cancel_right, euclidNorm_neg, euclidNorm_dirVec] at h

theorem euclidNorm_walkPos_succ_le' (y : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    euclidNorm (walkPos y ω (t + 1)) ≤ euclidNorm (walkPos y ω t) + 1 := by
  have h : walkPos y ω (t + 1) = walkPos y ω t + dirVec (ω t) := by
    simp [walkPos, Finset.sum_range_succ, add_assoc]
  rw [h]
  exact euclidNorm_add_dirVec_le _ _

end FiniteAvalanches.Walk.BarlowMasson
