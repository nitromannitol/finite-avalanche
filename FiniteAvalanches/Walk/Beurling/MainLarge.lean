/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/MainLarge.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added;
`Set.mem_ofPred_eq` replaced by `Set.mem_setOf_eq` (6 times); `measurableSet_setOfPred` replaced by
`measurableSet_setOf` (once); `ite_eq_left` replaced by `if_pos` (5 times); `ite_eq_right` replaced
by `if_neg` (2 times).
-/
import FiniteAvalanches.Walk.Beurling.SegmentEscapeFromHalfLine
import FiniteAvalanches.Walk.Beurling.DiskGreenFar
import FiniteAvalanches.Walk.Beurling.LastExit

/-!
# The Beurling estimate for large `n`, given the shifted half-line estimate

Let `A` be a minimal dense set of the plane, with one point `w j` in each annulus
`j ≤ |z| < j + 1`, let `1 ≤ k ≤ n / 2` and `m = n⁴`. The probability that the simple random walk
started at `0` reaches the circle of radius `m` before a positive-time visit to
`A[k, n) = {w j : k ≤ j < n}` is at most `c √k / (√n log n)`
(Lawler and Limic, 2004, Section 5, equations (30) to (34)).

The proof compares `A[k, n)` with the segment `{(j, 0) : k ≤ j < n}` of the real axis.

1. For the segment, Proposition 12 (d) bounds the probability of leaving the disk of radius `n - 1`
   before a visit to the half-line `{(i, 0) : i ≥ k}` by `C √(k / n)`. Lemma 13 (ii) bounds the
   probability of reaching the circle of radius `m` from a point at distance `2n` by `c / log n`.
   The maximum principle combines the two.
2. By the last-exit decomposition (8), the difference of the two probabilities is the sum of
   `∑_j (G_m(0, j) - G_m(0, w_j)) P_j(τ_m < T)` and the value at `0` of
   `f(z) = ∑_j G_m(z, w_j) (P_j(τ_m < T) - P_{w_j}(τ_m < T̂))`.
3. The first sum is bounded by Lemma 4 for the Green function and by Lemma 14.
4. The function `f` is harmonic off `A[k, n)` and vanishes off `C_m`. By the maximum principle its
   value at `0` is at most its largest value on `A[k, n)`, which (8) and Lemma 4 bound as in 3.

Lemma 14 enters through `prob_exitsBefore_segment_le_of_shiftedHalfLine`, so the statement
carries Proposition 12 (e), in the range `j ≤ n` in which it is used, as a hypothesis.

G. F. Lawler and V. Limic, *The Beurling estimate for a class of random walks*, Electron. J.
Probab. 9 (2004), Section 5.

## Main statements

* `far_escape_minimal_of_shiftedHalfLine`: the estimate of Section 5 for large `n`, given
  Proposition 12 (e) for `j ≤ n`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

section Aux

private theorem prob_nonneg (E : Set (ℕ → Dir 2)) : 0 ≤ prob E := ENNReal.toReal_nonneg

private theorem prob_mono {E F : Set (ℕ → Dir 2)} (h : E ⊆ F) : prob E ≤ prob F :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h)

private theorem prob_le_one (E : Set (ℕ → Dir 2)) : prob E ≤ 1 :=
  prob_univ ▸ prob_mono (Set.subset_univ E)

private theorem mem_diskFinset_iff' {r : ℝ} {y : Site 2} :
    y ∈ diskFinset r ↔ euclidNorm y < r := by
  rw [diskFinset, Finset.mem_filter, mem_ballFinset_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

private theorem green_symm (r : ℝ) (x y : Site 2) : green r x y = green r y x := by
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset (diskFinset r)
  rw [green, green, Network.killedGreenReal_symm (Graph.Zd.latticeConnected 2) _ hq x y]

private theorem green_nonneg (r : ℝ) (x y : Site 2) : 0 ≤ green r x y := by
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset (diskFinset r)
  exact mul_nonneg (by norm_num)
    (Network.killedGreenReal_nonneg (Graph.Zd.latticeConnected 2) (diskFinset r) hq x y)

private theorem green_eq_zero_of_le {r : ℝ} (x : Site 2) {y : Site 2} (hy : r ≤ euclidNorm y) :
    green r x y = 0 := by
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset (diskFinset r)
  rw [green, Network.killedGreenReal_eq_zero_of_not_mem (Graph.Zd.latticeConnected 2) _ hq
    (fun h => absurd (mem_diskFinset_iff'.1 h) (not_lt.2 hy)), mul_zero]

/-- The Green function is the mean of its values at the four neighbours of a site `z` of the disk,
plus `1` when `z` is the source. -/
private theorem green_eq_mean_add (r : ℝ) {y z : Site 2} (hy : euclidNorm y < r)
    (hz : euclidNorm z < r) :
    green r y z = (∑ a : Dir 2, green r y (z + dirVec a)) / 4 + if z = y then 1 else 0 := by
  classical
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset (diskFinset r)
  have hl := Network.laplacian_killedGreenReal (Graph.Zd.latticeConnected 2) (diskFinset r)
    (mem_diskFinset_iff'.2 hy) hq (v := z) (by exact_mod_cast mem_diskFinset_iff'.2 hz)
  rw [laplacian_eq_nbrSum_sub (d := 2) (by norm_num), nbrSum_eq_sum_dir] at hl
  simp only [green, ← Finset.mul_sum]
  push_cast at hl
  split_ifs at hl ⊢ <;> linarith

private theorem euclidNorm_add_le' (y z : Site 2) :
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

private theorem euclidNorm_dirVec (a : Dir 2) : euclidNorm (dirVec a) = 1 := by
  rcases a with ⟨i, b⟩
  fin_cases i <;> cases b <;> simp [euclidNorm, dirVec]

private theorem euclidNorm_neg' (y : Site 2) : euclidNorm (-y) = euclidNorm y := by
  simp [euclidNorm]

/-- One step changes the Euclidean norm by at most one. -/
private theorem euclidNorm_add_dirVec_le (y : Site 2) (a : Dir 2) :
    euclidNorm (y + dirVec a) ≤ euclidNorm y + 1 := by
  simpa [euclidNorm_dirVec] using euclidNorm_add_le' y (dirVec a)

private theorem euclidNorm_of_eq_zero {z : Site 2} (h : z 1 = 0) :
    euclidNorm z = |((z 0 : ℤ) : ℝ)| := by
  simp [euclidNorm, Fin.sum_univ_two, h, Real.sqrt_sq_eq_abs]

private theorem axisPt_apply_zero (i : ℤ) : axisPt i 0 = i := by simp [axisPt]

private theorem axisPt_apply_one (i : ℤ) : axisPt i 1 = 0 := by simp [axisPt]

private theorem euclidNorm_axisPt (i : ℤ) : euclidNorm (axisPt i) = |(i : ℝ)| := by
  rw [euclidNorm_of_eq_zero (axisPt_apply_one i), axisPt_apply_zero]

private theorem axisPt_nat_injective : Function.Injective (fun j : ℕ => axisPt (j : ℤ)) := by
  intro a b h
  have := congrArg (fun z : Site 2 => z 0) h
  simpa [axisPt_apply_zero] using this

/-- Visiting `B` before leaving `C_r`, and leaving `C_r` before a positive-time visit to `B`, are
disjoint events when the walk does not start in `B`. -/
private theorem prob_exitsBefore_add_hitsBefore_le (r : ℝ) (B : Set (Site 2)) {x : Site 2}
    (hx : x ∉ B) : prob (exitsBefore r B x) + prob (hitsBefore B r x) ≤ 1 := by
  have hd : Disjoint (exitsBefore r B x) (hitsBefore B r x) := by
    rw [Set.disjoint_left]
    rintro ω ⟨t₁, ht₁, hB₁⟩ ⟨t₂, hB₂, hr₂⟩
    have ht : t₂ < t₁ := by
      by_contra h
      exact absurd (hr₂ t₁ (not_lt.1 h)) (not_lt.2 ht₁)
    have h1 : 1 ≤ t₂ := by
      rcases Nat.eq_zero_or_pos t₂ with h | h
      · subst h
        exact absurd (by simpa [walkPos] using hB₂) hx
      · exact h
    exact hB₁ t₂ h1 ht.le hB₂
  have h : prob (exitsBefore r B x ∪ hitsBefore B r x) =
      prob (exitsBefore r B x) + prob (hitsBefore B r x) :=
    measureReal_union hd (measurableSet_hitsBefore B r x)
  rw [← h]
  exact prob_le_one _

/-- The walk either visits `B ⊆ C_r` before leaving `C_r`, or leaves `C_r` before a positive-time
visit to `B`, almost surely. -/
private theorem one_le_prob_exitsBefore_add_hitsBefore (r : ℝ) (B : Set (Site 2))
    (hB : ∀ y ∈ B, euclidNorm y < r) (x : Site 2) :
    1 ≤ prob (exitsBefore r B x) + prob (hitsBefore B r x) := by
  classical
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset (diskFinset r)
  have hq' : r ≤ euclidNorm q := not_lt.1 fun h => hq (mem_diskFinset_iff'.2 h)
  have hsub : {ξ : ℕ → Dir 2 | ∃ n : ℕ, x + ∑ j ∈ Finset.range n, dirVec (ξ j) = q} ⊆
      exitsBefore r B x ∪ hitsBefore B r x := by
    rintro ω ⟨n, hn⟩
    have hu : ∃ u, r ≤ euclidNorm (walkPos x ω u) := ⟨n, by
      have : walkPos x ω n = q := hn
      rw [this]
      exact hq'⟩
    have hu₀r : r ≤ euclidNorm (walkPos x ω (Nat.find hu)) := Nat.find_spec hu
    have hlt : ∀ s < Nat.find hu, euclidNorm (walkPos x ω s) < r := fun s hs =>
      not_le.1 (Nat.find_min hu hs)
    by_cases h : ∃ s, 1 ≤ s ∧ s ≤ Nat.find hu ∧ walkPos x ω s ∈ B
    · obtain ⟨s, hs1, hsu, hsB⟩ := h
      have hsu' : s < Nat.find hu := lt_of_le_of_ne hsu fun he => by
        rw [he] at hsB
        exact absurd hu₀r (not_le.2 (hB _ hsB))
      exact Or.inr ⟨s, hsB, fun s' hs' => hlt s' (lt_of_le_of_lt hs' hsu')⟩
    · push Not at h
      exact Or.inl ⟨Nat.find hu, hu₀r, fun s h1 h2 => h s h1 h2⟩
  have h1 : pathLaw 2 {ξ : ℕ → Dir 2 | ∃ n : ℕ, x + ∑ j ∈ Finset.range n, dirVec (ξ j) = q} = 1 :=
    pathLaw_two_dim_hit_site x q
  calc (1 : ℝ) = prob {ξ : ℕ → Dir 2 | ∃ n : ℕ, x + ∑ j ∈ Finset.range n, dirVec (ξ j) = q} := by
        rw [prob, h1]
        simp
    _ ≤ prob (exitsBefore r B x ∪ hitsBefore B r x) := prob_mono hsub
    _ ≤ prob (exitsBefore r B x) + prob (hitsBefore B r x) := measureReal_union_le _ _

/-- The last-exit decomposition (8) for a set indexed injectively by a finite set of integers. -/
private theorem prob_hitsBefore_eq_sum_image (r : ℝ) (J : Finset ℕ) (ι : ℕ → Site 2)
    (hι : Set.InjOn ι J) (hr : ∀ j ∈ J, euclidNorm (ι j) < r) (z : Site 2) :
    prob (hitsBefore ((J.image ι : Finset (Site 2)) : Set (Site 2)) r z) =
      ∑ j ∈ J, green r z (ι j) *
        prob (exitsBefore r ((J.image ι : Finset (Site 2)) : Set (Site 2)) (ι j)) := by
  classical
  rw [hitsBefore_eq_sum_green_mul r _ (fun y hy => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    exact hr j hj) z, Finset.sum_image hι]

/-- A point of the obstacle is visited at time `0`. -/
private theorem prob_hitsBefore_self (r : ℝ) (B : Set (Site 2)) {x : Site 2} (hx : x ∈ B)
    (hr : euclidNorm x < r) : prob (hitsBefore B r x) = 1 := by
  have h : hitsBefore B r x = Set.univ := by
    ext ω
    simp only [Set.mem_univ, iff_true]
    refine ⟨0, ?_, ?_⟩
    · simpa [walkPos] using hx
    · intro s hs
      obtain rfl : s = 0 := by omega
      simpa [walkPos] using hr
  rw [h, prob, measure_univ, ENNReal.toReal_one]

private theorem measurableSet_exitsAvoiding (r : ℝ) (B : Set (Site 2)) (y : Site 2) :
    MeasurableSet (exitsAvoiding r B y) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    (measurable_walkPos_pred y (fun z => r ≤ euclidNorm z) t).and <| Measurable.forall fun s =>
      measurable_walkPos_pred y (fun z => s ≤ t → z ∉ B) s

private theorem exitsAvoiding_eq_empty {r : ℝ} {B : Set (Site 2)} {y : Site 2} (hy : y ∈ B) :
    exitsAvoiding r B y = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => ?_
  obtain ⟨t, -, hs⟩ := hω
  exact hs 0 (Nat.zero_le _) (by simpa [walkPos] using hy)

private theorem exitsAvoiding_eq_univ {r : ℝ} {B : Set (Site 2)} {y : Site 2} (hy : y ∉ B)
    (hr : r ≤ euclidNorm y) : exitsAvoiding r B y = Set.univ := by
  ext ω
  simp only [exitsAvoiding, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  refine ⟨0, by simpa [walkPos] using hr, fun s hs => ?_⟩
  obtain rfl : s = 0 := by omega
  simpa [walkPos] using hy

private theorem exitsAvoiding_eq_exitsBefore {r : ℝ} {B : Set (Site 2)} {y : Site 2}
    (hy : y ∉ B) : exitsAvoiding r B y = exitsBefore r B y := by
  ext ω
  simp only [exitsAvoiding, exitsBefore, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht, hs⟩
    exact ⟨t, ht, fun s _ hst => hs s hst⟩
  · rintro ⟨t, ht, hs⟩
    refine ⟨t, ht, fun s hst => ?_⟩
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · simpa [walkPos] using hy
    · exact hs s hpos hst

private theorem walkPos_one_add (y : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos y ω (1 + t) = walkPos (y + dirVec (ω 0)) (shiftBy 1 ω) t := by
  simp [walkPos, shiftBy, Finset.sum_range_add, add_assoc]

private theorem exitsAvoiding_eq_firstStep {r : ℝ} {B : Set (Site 2)} {y : Site 2} (hyB : y ∉ B)
    (hyr : euclidNorm y < r) :
    exitsAvoiding r B y = {ω | shiftBy 1 ω ∈ exitsAvoiding r B (y + dirVec (ω 0))} := by
  ext ω
  simp only [exitsAvoiding, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht, hs⟩
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · exfalso
      simp only [walkPos, Finset.range_zero, Finset.sum_empty, add_zero] at ht
      linarith
    · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
      refine ⟨t', by rwa [← walkPos_one_add], fun s hs' => ?_⟩
      rw [← walkPos_one_add]
      exact hs (1 + s) (by omega)
  · rintro ⟨t, ht, hs⟩
    refine ⟨1 + t, by rwa [walkPos_one_add], fun s hs' => ?_⟩
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · simpa [walkPos] using hyB
    · obtain ⟨s', rfl⟩ : ∃ s', s = 1 + s' := ⟨s - 1, by omega⟩
      rw [walkPos_one_add]
      exact hs s' (by omega)

/-- The probability of `exitsAvoiding` at a site outside `B` and inside the disk is the mean over
the four neighbours. -/
private theorem prob_exitsAvoiding_step {r : ℝ} {B : Set (Site 2)} {y : Site 2} (hyB : y ∉ B)
    (hyr : euclidNorm y < r) :
    prob (exitsAvoiding r B y) = (∑ a : Dir 2, prob (exitsAvoiding r B (y + dirVec a))) / 4 := by
  rw [exitsAvoiding_eq_firstStep hyB hyr]
  rw [prob_firstStep (fun a => exitsAvoiding r B (y + dirVec a))
    (fun a => measurableSet_exitsAvoiding _ _ _), ← Finset.mul_sum]
  ring

private theorem walkOp_eq_sum (u : Site 2 → ℝ) (y : Site 2) :
    walkOp u y = (∑ a : Dir 2, u (y + dirVec a)) / 4 := by
  rw [walkOp_eq_sum_dir]
  norm_num

/-- The positive half-axis `{(i, 0) : i ≥ 0}` meets every annulus `j ≤ |z| < j + 1`. -/
private theorem isDense_axisSet_nonneg : IsDense (axisSet {i : ℤ | 0 ≤ i}) := by
  intro j
  refine ⟨axisPt j, ?_, ?_⟩
  · simp [axisSet, axisPt]
  · rw [euclidNorm_axisPt]
    simp

/-- Up to the first exit from the disk of radius `n - 1`, the segment `{(i, 0) : k ≤ i < n}` and
the half-line `{(i, 0) : i ≥ k}` agree. -/
private theorem exitsBefore_segment_subset_halfLine {k n : ℕ} (hk : 1 ≤ k) (hn : 2 ≤ n) :
    exitsBefore (2 * (n : ℝ)) (axisSet (Set.Ico (k : ℤ) n)) 0 ⊆
      exitsBefore ((n - 1 : ℕ) : ℝ) (axisSet {i : ℤ | (k : ℤ) ≤ i}) 0 := by
  rintro ω ⟨t, ht, hs⟩
  have hr₁ : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hex : ∃ u, ((n - 1 : ℕ) : ℝ) ≤ euclidNorm (walkPos 0 ω u) :=
    ⟨t, by rw [hr₁]; linarith⟩
  have hτt : Nat.find hex ≤ t := Nat.find_min' hex (by rw [hr₁]; linarith)
  have hτr : ((n - 1 : ℕ) : ℝ) ≤ euclidNorm (walkPos 0 ω (Nat.find hex)) := Nat.find_spec hex
  have hlt : ∀ s < Nat.find hex, euclidNorm (walkPos 0 ω s) < ((n - 1 : ℕ) : ℝ) := fun s hs' =>
    not_le.1 (Nat.find_min hex hs')
  have hτpos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso
      rw [h] at hτr
      have h0 : euclidNorm (walkPos 0 ω 0) = 0 := by simp [walkPos, euclidNorm]
      rw [h0, hr₁] at hτr
      linarith
    · exact h
  have hlt_n : ∀ s, 1 ≤ s → s ≤ Nat.find hex → euclidNorm (walkPos 0 ω s) < n := by
    intro s h1 hsτ
    rcases lt_or_eq_of_le hsτ with h | h
    · have := hlt s h
      rw [hr₁] at this
      linarith
    · obtain ⟨u, hu⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
      have h1' := euclidNorm_walkPos_succ_le 0 ω u
      have h2 := hlt u (by omega)
      rw [hr₁] at h2
      rw [hu]
      linarith
  refine ⟨Nat.find hex, hτr, fun s h1 hsτ hH => ?_⟩
  obtain ⟨hH1, hH0⟩ := hH
  have hlt' := hlt_n s h1 hsτ
  have hk0 : (0 : ℤ) ≤ walkPos 0 ω s 0 := by
    have : (k : ℤ) ≤ walkPos 0 ω s 0 := hH0
    omega
  have hnorm : euclidNorm (walkPos 0 ω s) = ((walkPos 0 ω s 0 : ℤ) : ℝ) := by
    rw [euclidNorm_of_eq_zero hH1, abs_of_nonneg (by exact_mod_cast hk0)]
  have hlt0 : walkPos 0 ω s 0 < n := by
    rw [hnorm] at hlt'
    exact_mod_cast hlt'
  exact hs s h1 (le_trans hsτ hτt) ⟨hH1, hH0, hlt0⟩

end Aux

section Segment

/-- **The escape bound for the segment, from the origin.** For `1 ≤ k ≤ n / 2` and `m = n⁴`, the
probability that the walk started at `0` reaches the circle of radius `m` before a positive-time
visit to `{(i, 0) : k ≤ i < n}` is at most `c √k / (√n log n)`. -/
private theorem exitsBefore_axisSegment_le : ∃ c : ℝ, ∃ N : ℕ, ∀ n k : ℕ, N ≤ n → 1 ≤ k →
    k ≤ n / 2 → prob (exitsBefore ((n : ℝ) ^ 4) (axisSet (Set.Ico (k : ℤ) n)) 0) ≤
      c * Real.sqrt k / (Real.sqrt n * Real.log n) := by
  classical
  obtain ⟨Cd, hCd⟩ := exitsBefore_halfLine_le
  obtain ⟨K, N₁, hK⟩ := exitsBefore_shellPart_far
  refine ⟨2 * max K 0 * max Cd 0, max N₁ 4, fun n k hn hk hkn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (k : ℝ) ≤ (n : ℝ) / 2 :=
    calc (k : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hkn
      _ ≤ (n : ℝ) / 2 := Nat.cast_div_le
  set B : Set (Site 2) := axisSet (Set.Ico (k : ℤ) n) with hB
  have hBmem : ∀ z, z ∈ B ↔ z 1 = 0 ∧ (k : ℤ) ≤ z 0 ∧ z 0 < n := fun z => by
    simp only [hB, axisSet, Set.mem_setOf_eq, Set.mem_Ico]
  have hBnorm : ∀ z ∈ B, euclidNorm z < n := fun z hz => by
    obtain ⟨h1, h2, h3⟩ := (hBmem z).1 hz
    rw [euclidNorm_of_eq_zero h1, abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ z 0))]
    exact_mod_cast h3
  have h0B : (0 : Site 2) ∉ B := fun h => by
    have := ((hBmem 0).1 h).2.1
    simp only [Pi.zero_apply] at this
    omega
  have hshell : shellPart (axisSet {i : ℤ | 0 ≤ i}) ((n : ℝ) / 2) n ⊆ B := by
    rintro z ⟨⟨hz1, hz0⟩, hzl, hzu⟩
    have hz0' : (0 : ℤ) ≤ z 0 := hz0
    rw [euclidNorm_of_eq_zero hz1, abs_of_nonneg (by exact_mod_cast hz0')] at hzl hzu
    refine (hBmem z).2 ⟨hz1, ?_, by exact_mod_cast hzu⟩
    have : (k : ℝ) ≤ ((z 0 : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  set Q : ℝ := max K 0 / Real.log n with hQ
  have hQ0 : 0 ≤ Q := div_nonneg (le_max_right _ _) hlog.le
  set m : ℝ := (n : ℝ) ^ 4 with hm
  have hm2n : 2 * (n : ℝ) + 1 < m := by
    have : (n : ℝ) ^ 4 = n * (n * (n * n)) := by ring
    nlinarith [mul_pos hn0 hn0, mul_pos hn0 (mul_pos hn0 hn0)]
  have hφ : ∀ y : Site 2, euclidNorm y < 4 * n → prob (exitsAvoiding m B y) ≤ Q := by
    intro y hy
    by_cases hyB : y ∈ B
    · rw [exitsAvoiding_eq_empty hyB, prob, measure_empty]
      simpa using hQ0
    · rw [exitsAvoiding_eq_exitsBefore hyB]
      calc prob (exitsBefore m B y)
          ≤ prob (exitsBefore m (shellPart (axisSet {i : ℤ | 0 ≤ i}) ((n : ℝ) / 2) n) y) :=
            prob_mono (exitsBefore_anti hshell _ _)
        _ ≤ K / Real.log n := hK n hn1 _ isDense_axisSet_nonneg y hy
        _ ≤ Q := div_le_div_of_nonneg_right (le_max_left _ _) hlog.le
  set φ : Site 2 → ℝ := fun y => prob (exitsAvoiding m B y) with hφdef
  set ψ : Site 2 → ℝ := fun y => prob (exitsAvoiding (2 * (n : ℝ)) B y) with hψdef
  set g : Site 2 → ℝ := fun y =>
    if euclidNorm y < 2 * n + 1 then φ y - Q * ψ y else 0 with hg
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset (diskFinset (2 * (n : ℝ)))
  have key := le_of_harmonic_on_box (d := 2) (by norm_num) (diskFinset (2 * (n : ℝ))) B g 0 hq
    (fun x hxC hxB => by
      have hx : euclidNorm x < 2 * n := mem_diskFinset_iff'.1 hxC
      have hnb : ∀ a : Dir 2, euclidNorm (x + dirVec a) < 2 * n + 1 := fun a => by
        have := euclidNorm_add_dirVec_le x a
        linarith
      have e1 : φ x = (∑ a : Dir 2, φ (x + dirVec a)) / 4 :=
        prob_exitsAvoiding_step hxB (by linarith)
      have e2 : ψ x = (∑ a : Dir 2, ψ (x + dirVec a)) / 4 := prob_exitsAvoiding_step hxB hx
      have hsum : ∑ a : Dir 2, g (x + dirVec a) =
          ∑ a : Dir 2, (φ (x + dirVec a) - Q * ψ (x + dirVec a)) :=
        Finset.sum_congr rfl fun a _ => by simp only [hg, if_pos (hnb a)]
      have hgx : g x = φ x - Q * ψ x := by
        simp only [hg, if_pos (by linarith : euclidNorm x < 2 * n + 1)]
      rw [walkOp_eq_sum, hsum, hgx, Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2]
      ring)
    (fun x hxC => by
      have hx : 2 * (n : ℝ) ≤ euclidNorm x := not_lt.1 fun h => hxC (mem_diskFinset_iff'.2 h)
      by_cases hx1 : euclidNorm x < 2 * n + 1
      · have hxB : x ∉ B := fun h => absurd (hBnorm x h) (by linarith)
        have hψ1 : ψ x = 1 := by
          simp only [hψdef]
          rw [exitsAvoiding_eq_univ hxB hx, prob_univ]
        have := hφ x (by linarith)
        simp only [hg, if_pos hx1]
        rw [hψ1]
        linarith
      · simp only [hg, if_neg hx1, le_refl])
    (fun x hxB => by
      have h1 : φ x = 0 := by
        simp only [hφdef]
        rw [exitsAvoiding_eq_empty hxB, prob, measure_empty]
        simp
      have h2 : ψ x = 0 := by
        simp only [hψdef]
        rw [exitsAvoiding_eq_empty hxB, prob, measure_empty]
        simp
      simp only [hg]
      split_ifs <;> simp [h1, h2])
  have h0 := key 0
  have hn2 : 2 ≤ n := by omega
  have hnorm0 : euclidNorm (0 : Site 2) = 0 := by simp [euclidNorm]
  simp only [hg, hnorm0, if_pos (by linarith : (0 : ℝ) < 2 * n + 1)] at h0
  have hφ0 : φ 0 = prob (exitsBefore m B 0) := by
    simp only [hφdef]
    rw [exitsAvoiding_eq_exitsBefore h0B]
  have hψ0 : ψ 0 = prob (exitsBefore (2 * (n : ℝ)) B 0) := by
    simp only [hψdef]
    rw [exitsAvoiding_eq_exitsBefore h0B]
  have hψle : ψ 0 ≤ max Cd 0 * Real.sqrt ((k : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
    rw [hψ0]
    calc prob (exitsBefore (2 * (n : ℝ)) B 0)
        ≤ prob (exitsBefore ((n - 1 : ℕ) : ℝ) (axisSet {i : ℤ | (k : ℤ) ≤ i}) 0) :=
          prob_mono (exitsBefore_segment_subset_halfLine hk hn2)
      _ ≤ Cd * Real.sqrt ((k : ℝ) / ((n - 1 : ℕ) : ℝ)) := hCd k (n - 1) hk (by omega)
      _ ≤ max Cd 0 * Real.sqrt ((k : ℝ) / ((n - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  have hn1' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hsq : Real.sqrt ((k : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ 2 * Real.sqrt k / Real.sqrt n := by
    have hs1 : Real.sqrt n ≤ 2 * Real.sqrt ((n : ℝ) - 1) := by
      rw [show (2 : ℝ) * Real.sqrt ((n : ℝ) - 1) = Real.sqrt (4 * ((n : ℝ) - 1)) by
        rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hpos : 0 < Real.sqrt ((n : ℝ) - 1) := Real.sqrt_pos.2 (by linarith)
    rw [hn1', Real.sqrt_div (Nat.cast_nonneg k), div_le_div_iff₀ hpos (Real.sqrt_pos.2 hn0)]
    nlinarith [mul_le_mul_of_nonneg_left hs1 (Real.sqrt_nonneg (k : ℝ))]
  have hCd0 : 0 ≤ max Cd 0 := le_max_right _ _
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  calc prob (exitsBefore m B 0) = φ 0 := hφ0.symm
    _ ≤ Q * ψ 0 := by linarith
    _ ≤ Q * (max Cd 0 * (2 * Real.sqrt k / Real.sqrt n)) :=
        mul_le_mul_of_nonneg_left (hψle.trans (mul_le_mul_of_nonneg_left hsq hCd0)) hQ0
    _ = 2 * max K 0 * max Cd 0 * Real.sqrt k / (Real.sqrt n * Real.log n) := by
        simp only [hQ]
        field_simp

end Segment

section GreenDiff

private theorem euclidNorm_nonneg' (x : Site 2) : 0 ≤ euclidNorm x := Real.sqrt_nonneg _

private theorem euclidNorm_eq_norm (y : Site 2) :
    euclidNorm y = ‖(WithLp.toLp 2 fun i => ((y i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2))‖ := by
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, euclidNorm]

private theorem toLp_sub (a b : Site 2) :
    (WithLp.toLp 2 fun i => (((a - b) i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2)) =
      (WithLp.toLp 2 fun i => ((a i : ℤ) : ℝ)) - (WithLp.toLp 2 fun i => ((b i : ℤ) : ℝ)) := by
  ext i
  simp

private theorem abs_euclidNorm_sub_le (a b : Site 2) :
    |euclidNorm a - euclidNorm b| ≤ euclidNorm (a - b) := by
  rw [euclidNorm_eq_norm (a - b), euclidNorm_eq_norm a, euclidNorm_eq_norm b, toLp_sub]
  exact abs_norm_sub_norm_le _ _

private theorem one_le_euclidNorm {y : Site 2} (hy : y ≠ 0) : 1 ≤ euclidNorm y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
  have h1 : 1 ≤ supNorm y :=
    (Int.natAbs_pos.2 hi).trans_le (Finset.le_sup (f := fun i => (y i).natAbs) (Finset.mem_univ i))
  exact (by exact_mod_cast h1 : (1 : ℝ) ≤ supNorm y).trans (supNorm_le_euclidNorm y)

private theorem rpow_le_inv {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 / (n : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [one_div, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)

/-- Lemma 4 for `m = n⁴`, with a nonnegative constant. -/
private theorem green_far_n4 : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ z w : Site 2, z ≠ w →
    euclidNorm z ≤ n → euclidNorm w ≤ n →
    |Real.pi / 2 * green ((n : ℝ) ^ 4) z w -
        (Real.log ((n : ℝ) ^ 4) - Real.log (euclidNorm (z - w)))| ≤
      C * (1 / euclidNorm (z - w) + (n : ℝ) ^ (-(4 / 3 : ℝ))) := by
  obtain ⟨C, hC⟩ := green_far_asymptotics
  refine ⟨|C|, abs_nonneg C, fun n hn z w hzw hz hw => ?_⟩
  have h := hC n (n ^ 4) hn le_rfl z w hzw hz hw
  push_cast at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C)
    (add_nonneg (div_nonneg zero_le_one (euclidNorm_nonneg' _))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)))

/-- Two applications of Lemma 4, for pairs at distances `e` and `d` with `d - 1 < e`. -/
private theorem sided_aux {C d e t X Y L : ℝ} (hC : 0 ≤ C) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hed : d - 1 < e) (htd : t ≤ 1 / d)
    (hX : |X - (L - Real.log e)| ≤ C * (1 / e + t))
    (hY : |Y - (L - Real.log d)| ≤ C * (1 / d + t)) : X - Y ≤ (9 * C + 3) / (d + 1) := by
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have h1 : 1 / e ≤ 3 / (d + 1) := by
    rw [div_le_div_iff₀ he0 (by linarith)]
    linarith
  have h2 : 1 / d ≤ 2 / (d + 1) := by
    rw [div_le_div_iff₀ hd0 (by linarith)]
    linarith
  have hlog : Real.log d - Real.log e ≤ 1 / e := by
    have h := Real.log_le_sub_one_of_pos (div_pos hd0 he0)
    rw [Real.log_div hd0.ne' he0.ne'] at h
    have : d / e - 1 ≤ 1 / e := by
      rw [div_sub_one he0.ne', div_le_div_iff_of_pos_right he0]
      linarith
    linarith
  have hX' := (abs_le.1 hX).2
  have hY' := (abs_le.1 hY).1
  have hD : (9 * C + 3) / (d + 1) = C * (3 / (d + 1) + 2 / (d + 1)) + C * (2 / (d + 1) +
      2 / (d + 1)) + 3 / (d + 1) := by
    field_simp
    ring
  have hc1 : C * (1 / e + t) ≤ C * (3 / (d + 1) + 2 / (d + 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have hc2 : C * (1 / d + t) ≤ C * (2 / (d + 1) + 2 / (d + 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have h3 : 1 / e ≤ 3 / (d + 1) := h1
  linarith

/-- Lemma 4 compares the Green function from the origin at the minimal point `w j` with the one
at the axis point `(j, 0)`. -/
private theorem green_origin_diff_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ w : ℕ → Site 2,
    (∀ j : ℕ, (j : ℝ) ≤ euclidNorm (w j) ∧ euclidNorm (w j) < j + 1) → ∀ j : ℕ, 1 ≤ j →
    j < n → |green ((n : ℝ) ^ 4) 0 (axisPt j) - green ((n : ℝ) ^ 4) 0 (w j)| ≤ C / j := by
  obtain ⟨C, hC0, hC⟩ := green_far_n4
  refine ⟨9 * C + 3, by positivity, fun n hn w hw j hj hjn => ?_⟩
  have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
  have hnorm_p : euclidNorm (axisPt (j : ℤ)) = j := by
    rw [euclidNorm_axisPt]
    simp
  obtain ⟨hw1, hw2⟩ := hw j
  have hnorm0 : euclidNorm (0 : Site 2) = 0 := by simp [euclidNorm]
  have hq_ne : (0 : Site 2) ≠ w j := fun h => by
    rw [← h, hnorm0] at hw1
    linarith
  have hp_ne : (0 : Site 2) ≠ axisPt (j : ℤ) := fun h => by
    rw [← h, hnorm0] at hnorm_p
    linarith
  have hA := hC n hn 0 (axisPt j) hp_ne (by rw [hnorm0]; positivity)
    (by rw [hnorm_p]; linarith)
  have hB := hC n hn 0 (w j) hq_ne (by rw [hnorm0]; positivity) (by linarith)
  rw [zero_sub, euclidNorm_neg', hnorm_p] at hA
  rw [zero_sub, euclidNorm_neg'] at hB
  have hn1 : (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 / (n : ℝ) := rpow_le_inv (by omega)
  have hd1 : 1 / (n : ℝ) ≤ 1 / euclidNorm (w j) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hd2 : 1 / (n : ℝ) ≤ 1 / (j : ℝ) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have h1 := sided_aux hC0 (by linarith : (1 : ℝ) ≤ euclidNorm (w j)) hj0 (by linarith)
    (hn1.trans hd1) hA hB
  have h2 := sided_aux hC0 hj0 (by linarith : (1 : ℝ) ≤ euclidNorm (w j)) (by linarith)
    (hn1.trans hd2) hB hA
  have hdiv1 : (9 * C + 3) / (euclidNorm (w j) + 1) ≤ (9 * C + 3) / j :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hdiv2 : (9 * C + 3) / ((j : ℝ) + 1) ≤ (9 * C + 3) / j :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hpi : 1 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  set Gp := green ((n : ℝ) ^ 4) 0 (axisPt j) with hGp
  set Gq := green ((n : ℝ) ^ 4) 0 (w j) with hGq
  have hmul : |Gp - Gq| ≤ |Real.pi / 2 * Gp - Real.pi / 2 * Gq| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by linarith : 0 < Real.pi / 2)]
    nlinarith [abs_nonneg (Gp - Gq)]
  refine hmul.trans (abs_le.2 ⟨?_, ?_⟩) <;> linarith

/-- The diagonal values of the Green function of the disk of radius `n⁴`, at a minimal point and at
the axis point of the same index, differ by a bounded amount. -/
private theorem green_diag_diff_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ w : ℕ → Site 2,
    (∀ j : ℕ, (j : ℝ) ≤ euclidNorm (w j) ∧ euclidNorm (w j) < j + 1) → ∀ ℓ : ℕ, ℓ < n →
    green ((n : ℝ) ^ 4) (w ℓ) (w ℓ) - green ((n : ℝ) ^ 4) (axisPt ℓ) (axisPt ℓ) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := green_far_n4
  refine ⟨2 + 4 * C, by positivity, fun n hn w hw ℓ hℓ => ?_⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ' : (ℓ : ℝ) + 1 ≤ n := by exact_mod_cast hℓ
  obtain ⟨hw1, hw2⟩ := hw ℓ
  have hnorm_p : euclidNorm (axisPt (ℓ : ℤ)) = ℓ := by
    rw [euclidNorm_axisPt]
    simp
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ n := by linarith
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ this (by norm_num)
  have hqm : euclidNorm (w ℓ) < (n : ℝ) ^ 4 := by linarith
  have hpm : euclidNorm (axisPt (ℓ : ℤ)) < (n : ℝ) ^ 4 := by rw [hnorm_p]; linarith
  have e1 := green_eq_mean_add ((n : ℝ) ^ 4) hqm hqm
  have e2 := green_eq_mean_add ((n : ℝ) ^ 4) hpm hpm
  rw [if_pos rfl] at e1 e2
  have hstep : ∀ a : Dir 2, green ((n : ℝ) ^ 4) (w ℓ) (w ℓ + dirVec a) -
      green ((n : ℝ) ^ 4) (axisPt ℓ) (axisPt ℓ + dirVec a) ≤ 2 + 4 * C := by
    intro a
    have hd1 : euclidNorm (dirVec a) = 1 := euclidNorm_dirVec a
    have hne : ∀ x : Site 2, x ≠ x + dirVec a := fun x h => by
      have : dirVec a = 0 := by
        have := congrArg (fun y => y - x) h
        simpa using this.symm
      rw [this] at hd1
      simp [euclidNorm] at hd1
    have hdist : ∀ x : Site 2, euclidNorm (x - (x + dirVec a)) = 1 := fun x => by
      rw [sub_add_cancel_left, euclidNorm_neg', hd1]
    -- the lower bound at scale `n`
    have hpa : euclidNorm (axisPt (ℓ : ℤ) + dirVec a) ≤ n := by
      have := euclidNorm_add_dirVec_le (axisPt (ℓ : ℤ)) a
      rw [hnorm_p] at this
      linarith
    have hL := hC n hn (axisPt ℓ) (axisPt ℓ + dirVec a) (hne _)
      (by rw [hnorm_p]; linarith) hpa
    rw [hdist, Real.log_one] at hL
    -- the upper bound at scale `n + 1`
    have hN : (2 : ℕ) ≤ n + 1 := by omega
    have hqa : euclidNorm (w ℓ + dirVec a) ≤ ((n + 1 : ℕ) : ℝ) := by
      have := euclidNorm_add_dirVec_le (w ℓ) a
      push_cast
      linarith
    have hU := hC (n + 1) hN (w ℓ) (w ℓ + dirVec a) (hne _)
      (by push_cast; linarith) hqa
    rw [hdist, Real.log_one] at hU
    have hmono : green ((n : ℝ) ^ 4) (w ℓ) (w ℓ + dirVec a) ≤
        green (((n + 1 : ℕ) : ℝ) ^ 4) (w ℓ) (w ℓ + dirVec a) :=
      green_mono (pow_le_pow_left₀ (Nat.cast_nonneg n) (by push_cast; linarith) 4) _ _
    have ht1 : (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have ht2 : ((n + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by push_cast; linarith) (by norm_num)
    have hlogd : Real.log (((n + 1 : ℕ) : ℝ) ^ 4) - Real.log ((n : ℝ) ^ 4) ≤ 2 := by
      have h0 : (0 : ℝ) < n := by linarith
      rw [Real.log_pow, Real.log_pow]
      have h := Real.log_le_sub_one_of_pos (div_pos (by push_cast; linarith : (0 : ℝ) <
        ((n + 1 : ℕ) : ℝ)) h0)
      rw [Real.log_div (by push_cast; linarith) h0.ne'] at h
      have : ((n + 1 : ℕ) : ℝ) / n - 1 ≤ 1 / 2 := by
        push_cast
        rw [add_div, div_self h0.ne', add_sub_cancel_left, div_le_div_iff₀ h0 (by norm_num)]
        linarith
      push_cast at h this ⊢
      linarith
    have hCt1 : C * (1 / 1 + (n : ℝ) ^ (-(4 / 3 : ℝ))) ≤ C * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    have hCt2 : C * (1 / 1 + ((n + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))) ≤ C * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    have hpi : 1 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
    have hX := (abs_le.1 hU).2
    have hY := (abs_le.1 hL).1
    set T := green ((n : ℝ) ^ 4) (w ℓ) (w ℓ + dirVec a) -
      green ((n : ℝ) ^ 4) (axisPt ℓ) (axisPt ℓ + dirVec a) with hT
    have hmono' := mul_le_mul_of_nonneg_left hmono (by linarith : 0 ≤ Real.pi / 2)
    have hTpi : Real.pi / 2 * T ≤ 2 + 4 * C := by
      rw [hT, mul_sub]
      linarith
    by_cases hT0 : 0 ≤ T
    · nlinarith
    · linarith
  have hsum : ∑ a : Dir 2, (green ((n : ℝ) ^ 4) (w ℓ) (w ℓ + dirVec a) -
      green ((n : ℝ) ^ 4) (axisPt ℓ) (axisPt ℓ + dirVec a)) ≤ ∑ _a : Dir 2, (2 + 4 * C) :=
    Finset.sum_le_sum fun a _ => hstep a
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ] at hsum
  have hcard : Fintype.card (Dir 2) = 4 := by simp
  rw [hcard] at hsum
  simp only [nsmul_eq_mul] at hsum
  push_cast at hsum
  linarith

/-- The Green function of the disk of radius `n⁴` between two minimal points exceeds the one
between the corresponding axis points by at most a multiple of `1 / (|ℓ - j| + 1)`. -/
private theorem green_pair_diff_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ w : ℕ → Site 2,
    (∀ j : ℕ, (j : ℝ) ≤ euclidNorm (w j) ∧ euclidNorm (w j) < j + 1) → ∀ ℓ j : ℕ, ℓ < n →
    j < n → green ((n : ℝ) ^ 4) (w ℓ) (w j) - green ((n : ℝ) ^ 4) (axisPt ℓ) (axisPt j) ≤
      C / (|(ℓ : ℝ) - j| + 1) := by
  obtain ⟨C, hC0, hC⟩ := green_far_n4
  obtain ⟨Cd, hCd0, hCd⟩ := green_diag_diff_le
  refine ⟨9 * C + 3 + Cd, by positivity, fun n hn w hw ℓ j hℓ hj => ?_⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ' : (ℓ : ℝ) + 1 ≤ n := by exact_mod_cast hℓ
  have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  obtain ⟨hwℓ1, hwℓ2⟩ := hw ℓ
  obtain ⟨hwj1, hwj2⟩ := hw j
  by_cases hlj : ℓ = j
  · subst hlj
    have := hCd n hn w hw ℓ hℓ
    rw [sub_self, abs_zero, zero_add, div_one]
    linarith
  · have hd1 : 1 ≤ |(ℓ : ℝ) - j| := by
      rcases lt_or_gt_of_ne hlj with h | h
      · have : (ℓ : ℝ) + 1 ≤ j := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]
        linarith
      · have : (j : ℝ) + 1 ≤ ℓ := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]
        linarith
    have hdn : |(ℓ : ℝ) - j| ≤ n := by
      rw [abs_le]
      constructor <;> linarith
    have hpn : euclidNorm (axisPt (ℓ : ℤ) - axisPt (j : ℤ)) = |(ℓ : ℝ) - j| := by
      rw [euclidNorm_of_eq_zero (by simp [axisPt])]
      simp [axisPt]
    have hp_ne : axisPt (ℓ : ℤ) ≠ axisPt (j : ℤ) := fun h => hlj (axisPt_nat_injective h)
    have hnorm_p : ∀ i : ℕ, euclidNorm (axisPt (i : ℤ)) = i := fun i => by
      rw [euclidNorm_axisPt]
      simp
    have hq_ne : w ℓ ≠ w j := fun h => by
      rw [h] at hwℓ1 hwℓ2
      have h1 : (ℓ : ℝ) < j + 1 := by linarith
      have h2 : (j : ℝ) < ℓ + 1 := by linarith
      have h1' : ℓ < j + 1 := by exact_mod_cast h1
      have h2' : j < ℓ + 1 := by exact_mod_cast h2
      omega
    have he1 : 1 ≤ euclidNorm (w ℓ - w j) := one_le_euclidNorm (sub_ne_zero.2 hq_ne)
    have hed : |(ℓ : ℝ) - j| - 1 < euclidNorm (w ℓ - w j) := by
      have h := abs_euclidNorm_sub_le (w ℓ) (w j)
      rcases lt_or_gt_of_ne hlj with h' | h'
      · have : (ℓ : ℝ) + 1 ≤ j := by exact_mod_cast h'
        rw [abs_of_neg (by linarith)]
        have := neg_abs_le (euclidNorm (w ℓ) - euclidNorm (w j))
        linarith
      · have : (j : ℝ) + 1 ≤ ℓ := by exact_mod_cast h'
        rw [abs_of_pos (by linarith)]
        have := le_abs_self (euclidNorm (w ℓ) - euclidNorm (w j))
        linarith
    have hX := hC n hn (w ℓ) (w j) hq_ne (by linarith) (by linarith)
    have hY := hC n hn (axisPt ℓ) (axisPt j) hp_ne (by rw [hnorm_p]; linarith)
      (by rw [hnorm_p]; linarith)
    rw [hpn] at hY
    have ht := (rpow_le_inv (by omega : 1 ≤ n)).trans
      (one_div_le_one_div_of_le (by linarith) (by linarith : |(ℓ : ℝ) - j| ≤ n))
    have hs := sided_aux hC0 hd1 he1 hed ht hX hY
    have hpi : 1 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
    set Δ := green ((n : ℝ) ^ 4) (w ℓ) (w j) - green ((n : ℝ) ^ 4) (axisPt ℓ) (axisPt j) with hΔ
    have hdiv : (9 * C + 3) / (|(ℓ : ℝ) - j| + 1) ≤ (9 * C + 3 + Cd) / (|(ℓ : ℝ) - j| + 1) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hnn : 0 ≤ (9 * C + 3) / (|(ℓ : ℝ) - j| + 1) := by positivity
    by_cases hΔ0 : 0 ≤ Δ
    · have : Real.pi / 2 * Δ ≤ (9 * C + 3) / (|(ℓ : ℝ) - j| + 1) := by
        rw [hΔ, mul_sub]
        linarith
      nlinarith
    · linarith

end GreenDiff

section Sums

/-- The terms `1 / ((i + 1) √(i + 1))`, which are summable. -/
private def tail (i : ℕ) : ℝ := 1 / (((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1))

private theorem tail_nonneg (i : ℕ) : 0 ≤ tail i := by
  unfold tail
  positivity

private theorem summable_tail : Summable tail := by
  have h := (summable_nat_add_iff 1).2
    (Real.summable_nat_rpow.2 (by norm_num : (-(3 / 2 : ℝ)) < -1))
  refine h.congr fun i => ?_
  have hx : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  show ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) = tail i
  simp only [tail, Nat.cast_add, Nat.cast_one]
  rw [Real.rpow_neg hx.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]

private theorem natAbs_cast (j ℓ : ℕ) :
    ((Int.natAbs ((j : ℤ) - ℓ) : ℕ) : ℝ) = |(j : ℝ) - ℓ| := by
  have h := Int.natCast_natAbs ((j : ℤ) - ℓ)
  have h2 : ((Int.natAbs ((j : ℤ) - ℓ) : ℕ) : ℝ) =
      (((Int.natAbs ((j : ℤ) - ℓ) : ℕ) : ℤ) : ℝ) := by simp
  rw [h2, h]
  push_cast
  rfl

/-- A sum of a nonnegative summable function of the distance to `ℓ` is bounded by twice the full
sum. -/
private theorem sum_shift_le (J : Finset ℕ) (ℓ : ℕ) (h : ℕ → ℝ) (hn : ∀ i, 0 ≤ h i)
    (hs : Summable h) : ∑ j ∈ J, h (Int.natAbs ((j : ℤ) - ℓ)) ≤ 2 * ∑' i, h i := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not J (fun j => ℓ ≤ j)]
  have h1 : ∑ j ∈ J.filter (fun j => ℓ ≤ j), h (Int.natAbs ((j : ℤ) - ℓ)) ≤ ∑' i, h i := by
    have hc : ∀ j ∈ J.filter (fun j => ℓ ≤ j), h (Int.natAbs ((j : ℤ) - ℓ)) = h (j - ℓ) :=
      fun j hj => by
        have := (Finset.mem_filter.1 hj).2
        congr 1
        omega
    have hinj : Set.InjOn (fun j : ℕ => j - ℓ) ↑(J.filter (fun j => ℓ ≤ j)) := by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
      have hb' := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
      simp only at hab
      omega
    calc ∑ j ∈ J.filter (fun j => ℓ ≤ j), h (Int.natAbs ((j : ℤ) - ℓ))
        = ∑ j ∈ J.filter (fun j => ℓ ≤ j), h (j - ℓ) := Finset.sum_congr rfl hc
      _ = ∑ i ∈ (J.filter (fun j => ℓ ≤ j)).image (fun j => j - ℓ), h i :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑' i, h i := hs.sum_le_tsum _ (fun i _ => hn i)
  have h2 : ∑ j ∈ J.filter (fun j => ¬ℓ ≤ j), h (Int.natAbs ((j : ℤ) - ℓ)) ≤ ∑' i, h i := by
    have hc : ∀ j ∈ J.filter (fun j => ¬ℓ ≤ j), h (Int.natAbs ((j : ℤ) - ℓ)) = h (ℓ - j) :=
      fun j hj => by
        have := (Finset.mem_filter.1 hj).2
        congr 1
        omega
    have hinj : Set.InjOn (fun j : ℕ => ℓ - j) ↑(J.filter (fun j => ¬ℓ ≤ j)) := by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
      have hb' := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
      simp only at hab
      omega
    calc ∑ j ∈ J.filter (fun j => ¬ℓ ≤ j), h (Int.natAbs ((j : ℤ) - ℓ))
        = ∑ j ∈ J.filter (fun j => ¬ℓ ≤ j), h (ℓ - j) := Finset.sum_congr rfl hc
      _ = ∑ i ∈ (J.filter (fun j => ¬ℓ ≤ j)).image (fun j => ℓ - j), h i :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑' i, h i := hs.sum_le_tsum _ (fun i _ => hn i)
  linarith

private theorem inv_mul_inv_sqrt_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 / (x * Real.sqrt y) ≤ 1 / (x * Real.sqrt x) + 1 / (y * Real.sqrt y) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have h1 : 0 ≤ 1 / (x * Real.sqrt x) := by positivity
  have h2 : 0 ≤ 1 / (y * Real.sqrt y) := by positivity
  rcases le_total x y with h | h
  · have : 1 / (x * Real.sqrt y) ≤ 1 / (x * Real.sqrt x) :=
      one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) hx0.le)
    linarith
  · have : 1 / (x * Real.sqrt y) ≤ 1 / (y * Real.sqrt y) :=
      one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg y))
    linarith

private theorem sum_inv_le : ∃ S : ℝ, 0 ≤ S ∧ ∀ (J : Finset ℕ) (ℓ a : ℕ),
    ∑ j ∈ J, 1 / ((|(j : ℝ) - ℓ| + 1) * Real.sqrt (|(j : ℝ) - a| + 1)) ≤ S := by
  have hT : 0 ≤ ∑' i, tail i := tsum_nonneg tail_nonneg
  refine ⟨4 * ∑' i, tail i, by positivity, fun J ℓ a => ?_⟩
  have hpt : ∀ j ∈ J, 1 / ((|(j : ℝ) - ℓ| + 1) * Real.sqrt (|(j : ℝ) - a| + 1)) ≤
      tail (Int.natAbs ((j : ℤ) - ℓ)) + tail (Int.natAbs ((j : ℤ) - a)) := fun j _ => by
    have := inv_mul_inv_sqrt_le (x := |(j : ℝ) - ℓ| + 1) (y := |(j : ℝ) - a| + 1)
      (by linarith [abs_nonneg ((j : ℝ) - ℓ)]) (by linarith [abs_nonneg ((j : ℝ) - a)])
    simp only [tail, natAbs_cast]
    exact this
  calc ∑ j ∈ J, 1 / ((|(j : ℝ) - ℓ| + 1) * Real.sqrt (|(j : ℝ) - a| + 1))
      ≤ ∑ j ∈ J, (tail (Int.natAbs ((j : ℤ) - ℓ)) + tail (Int.natAbs ((j : ℤ) - a))) :=
        Finset.sum_le_sum hpt
    _ = ∑ j ∈ J, tail (Int.natAbs ((j : ℤ) - ℓ)) + ∑ j ∈ J, tail (Int.natAbs ((j : ℤ) - a)) :=
        Finset.sum_add_distrib
    _ ≤ 2 * ∑' i, tail i + 2 * ∑' i, tail i :=
        add_le_add (sum_shift_le J ℓ tail tail_nonneg summable_tail)
          (sum_shift_le J a tail tail_nonneg summable_tail)
    _ = 4 * ∑' i, tail i := by ring

/-- The sum in (30). -/
private theorem sum_origin_le : ∃ S : ℝ, 0 ≤ S ∧ ∀ n k : ℕ, 1 ≤ k →
    ∑ j ∈ Finset.Ico k n, 1 / (j : ℝ) *
      (1 / Real.sqrt ((j : ℝ) - k + 1) + 1 / Real.sqrt ((n : ℝ) - j + 1)) ≤ S := by
  obtain ⟨S, hS0, hS⟩ := sum_inv_le
  refine ⟨2 * S, by positivity, fun n k hk => ?_⟩
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  calc ∑ j ∈ Finset.Ico k n, 1 / (j : ℝ) *
        (1 / Real.sqrt ((j : ℝ) - k + 1) + 1 / Real.sqrt ((n : ℝ) - j + 1))
      ≤ ∑ j ∈ Finset.Ico k n, (1 / ((|(j : ℝ) - k| + 1) * Real.sqrt (|(j : ℝ) - k| + 1)) +
          1 / ((|(j : ℝ) - k| + 1) * Real.sqrt (|(j : ℝ) - n| + 1))) := by
        refine Finset.sum_le_sum fun j hj => ?_
        obtain ⟨hjk, hjn⟩ := Finset.mem_Ico.1 hj
        have hjk' : (k : ℝ) ≤ j := by exact_mod_cast hjk
        have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (j : ℝ) - k),
          abs_of_neg (by linarith : (j : ℝ) - n < 0),
          show -((j : ℝ) - n) + 1 = (n : ℝ) - j + 1 by ring]
        have hpos : 0 < (j : ℝ) - k + 1 := by linarith
        have h1 : 1 / (j : ℝ) ≤ 1 / ((j : ℝ) - k + 1) :=
          one_div_le_one_div_of_le hpos (by linarith)
        calc 1 / (j : ℝ) * (1 / Real.sqrt ((j : ℝ) - k + 1) + 1 / Real.sqrt ((n : ℝ) - j + 1))
            ≤ 1 / ((j : ℝ) - k + 1) *
                (1 / Real.sqrt ((j : ℝ) - k + 1) + 1 / Real.sqrt ((n : ℝ) - j + 1)) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = 1 / (((j : ℝ) - k + 1) * Real.sqrt ((j : ℝ) - k + 1)) +
                1 / (((j : ℝ) - k + 1) * Real.sqrt ((n : ℝ) - j + 1)) := by
              rw [mul_add, one_div_mul_one_div, one_div_mul_one_div]
    _ = ∑ j ∈ Finset.Ico k n, 1 / ((|(j : ℝ) - k| + 1) * Real.sqrt (|(j : ℝ) - k| + 1)) +
          ∑ j ∈ Finset.Ico k n, 1 / ((|(j : ℝ) - k| + 1) * Real.sqrt (|(j : ℝ) - n| + 1)) :=
        Finset.sum_add_distrib
    _ ≤ S + S := add_le_add (hS _ k k) (hS _ k n)
    _ = 2 * S := by ring

/-- The sum in (34). -/
private theorem sum_pair_le : ∃ S : ℝ, 0 ≤ S ∧ ∀ n k ℓ : ℕ,
    ∑ j ∈ Finset.Ico k n, 1 / (|(ℓ : ℝ) - j| + 1) *
      (1 / Real.sqrt ((j : ℝ) - k + 1) + 1 / Real.sqrt ((n : ℝ) - j + 1)) ≤ S := by
  obtain ⟨S, hS0, hS⟩ := sum_inv_le
  refine ⟨2 * S, by positivity, fun n k ℓ => ?_⟩
  calc ∑ j ∈ Finset.Ico k n, 1 / (|(ℓ : ℝ) - j| + 1) *
        (1 / Real.sqrt ((j : ℝ) - k + 1) + 1 / Real.sqrt ((n : ℝ) - j + 1))
      = ∑ j ∈ Finset.Ico k n, (1 / ((|(j : ℝ) - ℓ| + 1) * Real.sqrt (|(j : ℝ) - k| + 1)) +
          1 / ((|(j : ℝ) - ℓ| + 1) * Real.sqrt (|(j : ℝ) - n| + 1))) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨hjk, hjn⟩ := Finset.mem_Ico.1 hj
        have hjk' : (k : ℝ) ≤ j := by exact_mod_cast hjk
        have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
        rw [abs_sub_comm (ℓ : ℝ) j, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (j : ℝ) - k),
          abs_of_neg (by linarith : (j : ℝ) - n < 0),
          show -((j : ℝ) - n) + 1 = (n : ℝ) - j + 1 by ring, mul_add, one_div_mul_one_div,
          one_div_mul_one_div]
    _ = ∑ j ∈ Finset.Ico k n, 1 / ((|(j : ℝ) - ℓ| + 1) * Real.sqrt (|(j : ℝ) - k| + 1)) +
          ∑ j ∈ Finset.Ico k n, 1 / ((|(j : ℝ) - ℓ| + 1) * Real.sqrt (|(j : ℝ) - n| + 1)) :=
        Finset.sum_add_distrib
    _ ≤ S + S := add_le_add (hS _ ℓ k) (hS _ ℓ n)
    _ = 2 * S := by ring

end Sums

/-- **Lawler and Limic (2004), Section 5, the estimate for large `n`, given Proposition 12 (e) for
`j ≤ n`.** Let `w` be a minimal dense set, with one point in each annulus `j ≤ |z| < j + 1`, let
`1 ≤ k ≤ n / 2` and `m = n⁴`. The probability that the walk started at `0` reaches the circle of
radius `m` before a positive-time visit to `{w j : k ≤ j < n}` is at most
`c √k / (√n log n)`.

The hypothesis is Proposition 12 (e) in the range `1 ≤ j ≤ n`: from the origin the walk leaves
the disk of radius `n` before a positive-time visit to `{(i, 0) : i ≥ -j}` with probability at most
`C / √(j n)`. -/
theorem far_escape_minimal_of_shiftedHalfLine
    (he : ∃ C : ℝ, ∀ j n : ℕ, 1 ≤ j → 1 ≤ n → j ≤ n →
      prob (exitsBefore n (axisSet {i | -(j : ℤ) ≤ i}) 0) ≤ C / Real.sqrt (j * n)) :
    ∃ c : ℝ, ∃ N : ℕ, ∀ n k : ℕ, N ≤ n → 1 ≤ k → k ≤ n / 2 → ∀ w : ℕ → Site 2,
      (∀ j : ℕ, (j : ℝ) ≤ euclidNorm (w j) ∧ euclidNorm (w j) < j + 1) →
      prob (exitsBefore ((n : ℝ) ^ 4) (shellPart (Set.range w) k n) 0) ≤
        c * Real.sqrt k / (Real.sqrt n * Real.log n) := by
  classical
  obtain ⟨c₁, N₁, hR14⟩ := prob_exitsBefore_segment_le_of_shiftedHalfLine he
  obtain ⟨c₀, N₂, hZ⟩ := exitsBefore_axisSegment_le
  obtain ⟨C₁, hC₁0, hG1⟩ := green_origin_diff_le
  obtain ⟨C₂, hC₂0, hG2⟩ := green_pair_diff_le
  obtain ⟨S₁, hS₁0, hS₁⟩ := sum_origin_le
  obtain ⟨S₂, hS₂0, hS₂⟩ := sum_pair_le
  refine ⟨max c₀ 0 + max c₁ 0 * (C₁ * S₁ + C₂ * S₂), max (max N₁ N₂) 8,
    fun n k hn hk hkn w hw => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn8 : 8 ≤ n := le_trans (le_max_right _ _) hn
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hD : 0 < Real.sqrt n * Real.log n := mul_pos (Real.sqrt_pos.2 hn0) hlog
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 4 := by
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  obtain ⟨Bax, hBax⟩ : ∃ B : Finset (Site 2),
      B = (Finset.Ico k n).image (fun j : ℕ => axisPt (j : ℤ)) := ⟨_, rfl⟩
  obtain ⟨Bw, hBw⟩ : ∃ B : Finset (Site 2), B = (Finset.Ico k n).image w := ⟨_, rfl⟩
  have hBaxset : (Bax : Set (Site 2)) = axisSet (Set.Ico (k : ℤ) n) := by
    ext z
    simp only [hBax, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Ico, axisSet,
      Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      rw [axisPt_apply_one, axisPt_apply_zero]
      exact ⟨rfl, by exact_mod_cast hj1, by exact_mod_cast hj2⟩
    · rintro ⟨h1, h2, h3⟩
      have hcast : (((z 0).toNat : ℕ) : ℤ) = z 0 := Int.toNat_of_nonneg (by omega)
      refine ⟨(z 0).toNat, ⟨by omega, by omega⟩, ?_⟩
      ext i
      fin_cases i <;> simp [axisPt, hcast, h1]
  have hBwset : (Bw : Set (Site 2)) = shellPart (Set.range w) k n := by
    ext z
    simp only [hBw, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Ico, shellPart,
      Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      have h1 : (k : ℝ) ≤ j := by exact_mod_cast hj1
      have h2 : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj2
      exact ⟨⟨j, rfl⟩, by linarith [(hw j).1], by linarith [(hw j).2]⟩
    · rintro ⟨⟨i, rfl⟩, h1, h2⟩
      refine ⟨i, ⟨?_, ?_⟩, rfl⟩
      · by_contra hlt
        have : (i : ℝ) + 1 ≤ k := by exact_mod_cast not_le.1 hlt
        linarith [(hw i).2]
      · by_contra hge
        have : (n : ℝ) ≤ i := by exact_mod_cast not_lt.1 hge
        linarith [(hw i).1]
  rw [← hBwset]
  have hwinj : Set.InjOn w ↑(Finset.Ico k n) := by
    intro i _ j _ hij
    obtain ⟨hi1, hi2⟩ := hw i
    obtain ⟨hj1, hj2⟩ := hw j
    rw [hij] at hi1 hi2
    have h1' : i < j + 1 := by exact_mod_cast (by linarith : (i : ℝ) < j + 1)
    have h2' : j < i + 1 := by exact_mod_cast (by linarith : (j : ℝ) < i + 1)
    omega
  have hwnorm : ∀ j ∈ Finset.Ico k n, euclidNorm (w j) < (n : ℝ) ^ 4 := fun j hj => by
    have : (j : ℝ) + 1 ≤ n := by exact_mod_cast (Finset.mem_Ico.1 hj).2
    linarith [(hw j).2]
  have hpnorm : ∀ j ∈ Finset.Ico k n, euclidNorm (axisPt (j : ℤ)) < (n : ℝ) ^ 4 := fun j hj => by
    have : (j : ℝ) + 1 ≤ n := by exact_mod_cast (Finset.mem_Ico.1 hj).2
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    rw [euclidNorm_axisPt, Int.cast_natCast, abs_of_nonneg hj0]
    linarith
  have h0Bw : (0 : Site 2) ∉ (Bw : Set (Site 2)) := by
    rw [hBwset]
    rintro ⟨-, h1, -⟩
    have : euclidNorm (0 : Site 2) = 0 := by simp [euclidNorm]
    rw [this] at h1
    linarith
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ j, a j =
      prob (exitsBefore ((n : ℝ) ^ 4) (Bax : Set (Site 2)) (axisPt j)) := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, ∀ j, b j =
      prob (exitsBefore ((n : ℝ) ^ 4) (Bw : Set (Site 2)) (w j)) := ⟨_, fun _ => rfl⟩
  have ha0 : ∀ j, 0 ≤ a j := fun j => by rw [ha]; exact prob_nonneg _
  have hb0 : ∀ j, 0 ≤ b j := fun j => by rw [hb]; exact prob_nonneg _
  have hi : prob (exitsBefore ((n : ℝ) ^ 4) (Bw : Set (Site 2)) 0) +
      ∑ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) 0 (w j) * b j ≤ 1 := by
    have h1 := prob_exitsBefore_add_hitsBefore_le ((n : ℝ) ^ 4) (Bw : Set (Site 2)) h0Bw
    have h2 := prob_hitsBefore_eq_sum_image ((n : ℝ) ^ 4) (Finset.Ico k n) w hwinj hwnorm 0
    rw [← hBw] at h2
    simp only [← hb] at h2
    linarith
  have hii : 1 ≤ prob (exitsBefore ((n : ℝ) ^ 4) (Bax : Set (Site 2)) 0) +
      ∑ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) 0 (axisPt j) * a j := by
    have h1 := one_le_prob_exitsBefore_add_hitsBefore ((n : ℝ) ^ 4) (Bax : Set (Site 2))
      (fun y hy => by
        have hy' : y ∈ (Finset.Ico k n).image (fun j : ℕ => axisPt (j : ℤ)) := by
          rw [← hBax]
          exact Finset.mem_coe.1 hy
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy'
        exact hpnorm j hj) 0
    have h2 := prob_hitsBefore_eq_sum_image ((n : ℝ) ^ 4) (Finset.Ico k n)
      (fun j : ℕ => axisPt (j : ℤ)) axisPt_nat_injective.injOn hpnorm 0
    rw [← hBax] at h2
    simp only [← ha] at h2
    linarith
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ j, u j =
      1 / Real.sqrt ((j : ℝ) - k + 1) + 1 / Real.sqrt ((n : ℝ) - j + 1) := ⟨_, fun _ => rfl⟩
  have hu0 : ∀ j, 0 ≤ u j := fun j => by
    rw [hu]
    positivity
  have hA : ∀ j ∈ Finset.Ico k n, a j ≤ max c₁ 0 * u j / (Real.sqrt n * Real.log n) := by
    intro j hj
    obtain ⟨hjk, hjn⟩ := Finset.mem_Ico.1 hj
    have h := hR14 n hn1 k j hkn hjk hjn
    rw [ha, hBaxset]
    calc _ ≤ c₁ / Real.sqrt n * (1 / Real.sqrt ((j : ℝ) - k + 1) +
          1 / Real.sqrt ((n : ℝ) - j + 1)) * (1 / Real.log n) := h
      _ = c₁ * u j / (Real.sqrt n * Real.log n) := by
          rw [hu]
          field_simp
      _ ≤ max c₁ 0 * u j / (Real.sqrt n * Real.log n) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (hu0 j)) hD.le
  have h30 : ∑ j ∈ Finset.Ico k n, (green ((n : ℝ) ^ 4) 0 (axisPt j) -
      green ((n : ℝ) ^ 4) 0 (w j)) * a j ≤ C₁ * max c₁ 0 * S₁ / (Real.sqrt n * Real.log n) := by
    have hterm : ∀ j ∈ Finset.Ico k n, (green ((n : ℝ) ^ 4) 0 (axisPt j) -
        green ((n : ℝ) ^ 4) 0 (w j)) * a j ≤
        C₁ * max c₁ 0 / (Real.sqrt n * Real.log n) * (1 / (j : ℝ) * u j) := by
      intro j hj
      obtain ⟨hjk, hjn⟩ := Finset.mem_Ico.1 hj
      have hj1 : 1 ≤ j := le_trans hk hjk
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      calc (green ((n : ℝ) ^ 4) 0 (axisPt j) - green ((n : ℝ) ^ 4) 0 (w j)) * a j
          ≤ |green ((n : ℝ) ^ 4) 0 (axisPt j) - green ((n : ℝ) ^ 4) 0 (w j)| * a j :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (ha0 j)
        _ ≤ (C₁ / j) * (max c₁ 0 * u j / (Real.sqrt n * Real.log n)) :=
            mul_le_mul (hG1 n (by omega) w hw j hj1 hjn) (hA j hj) (ha0 j) (by positivity)
        _ = C₁ * max c₁ 0 / (Real.sqrt n * Real.log n) * (1 / (j : ℝ) * u j) := by
            field_simp
    calc _ ≤ ∑ j ∈ Finset.Ico k n,
          C₁ * max c₁ 0 / (Real.sqrt n * Real.log n) * (1 / (j : ℝ) * u j) :=
          Finset.sum_le_sum hterm
      _ = C₁ * max c₁ 0 / (Real.sqrt n * Real.log n) *
          ∑ j ∈ Finset.Ico k n, 1 / (j : ℝ) * u j := by rw [Finset.mul_sum]
      _ ≤ C₁ * max c₁ 0 / (Real.sqrt n * Real.log n) * S₁ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ∑ j ∈ Finset.Ico k n, 1 / (j : ℝ) * u j
              = ∑ j ∈ Finset.Ico k n, 1 / (j : ℝ) *
                  (1 / Real.sqrt ((j : ℝ) - k + 1) + 1 / Real.sqrt ((n : ℝ) - j + 1)) :=
                Finset.sum_congr rfl fun j _ => by rw [hu]
            _ ≤ S₁ := hS₁ n k hk
      _ = C₁ * max c₁ 0 * S₁ / (Real.sqrt n * Real.log n) := by ring
  obtain ⟨f, hf⟩ : ∃ f : Site 2 → ℝ, ∀ x, f x =
      ∑ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) (w j) x * (a j - b j) := ⟨_, fun _ => rfl⟩
  have hMnn : 0 ≤ C₂ * max c₁ 0 * S₂ / (Real.sqrt n * Real.log n) := by positivity
  have hmem : ∀ ℓ ∈ Finset.Ico k n, w ℓ ∈ (Bw : Set (Site 2)) := fun ℓ hℓ => by
    rw [Finset.mem_coe, hBw]
    exact Finset.mem_image_of_mem w hℓ
  have hmemp : ∀ ℓ ∈ Finset.Ico k n, axisPt (ℓ : ℤ) ∈ (Bax : Set (Site 2)) := fun ℓ hℓ => by
    rw [Finset.mem_coe, hBax]
    exact Finset.mem_image_of_mem (fun j : ℕ => axisPt (j : ℤ)) hℓ
  have hfmax : f 0 ≤ C₂ * max c₁ 0 * S₂ / (Real.sqrt n * Real.log n) := by
    obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset (diskFinset ((n : ℝ) ^ 4))
    refine le_of_harmonic_on_box (d := 2) (by norm_num) (diskFinset ((n : ℝ) ^ 4))
      (Bw : Set (Site 2)) f _ hq ?_ ?_ ?_ 0
    · intro x hxC hxB
      have hx : euclidNorm x < (n : ℝ) ^ 4 := mem_diskFinset_iff'.1 hxC
      have hmean : ∀ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) (w j) x =
          (∑ a' : Dir 2, green ((n : ℝ) ^ 4) (w j) (x + dirVec a')) / 4 := fun j hj => by
        have hxne : x ≠ w j := fun h => hxB (h ▸ hmem j hj)
        have h := green_eq_mean_add ((n : ℝ) ^ 4) (hwnorm j hj) hx
        rwa [if_neg hxne, add_zero] at h
      calc walkOp f x = (∑ a' : Dir 2, f (x + dirVec a')) / 4 := walkOp_eq_sum f x
        _ = (∑ a' : Dir 2, ∑ j ∈ Finset.Ico k n,
              green ((n : ℝ) ^ 4) (w j) (x + dirVec a') * (a j - b j)) / 4 := by
            simp only [hf]
        _ = (∑ j ∈ Finset.Ico k n, ∑ a' : Dir 2,
              green ((n : ℝ) ^ 4) (w j) (x + dirVec a') * (a j - b j)) / 4 := by
            rw [Finset.sum_comm]
        _ = ∑ j ∈ Finset.Ico k n,
              (∑ a' : Dir 2, green ((n : ℝ) ^ 4) (w j) (x + dirVec a')) / 4 * (a j - b j) := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul]; ring
        _ = f x := by
            rw [hf]
            exact Finset.sum_congr rfl fun j hj => by rw [← hmean j hj]
    · intro x hx
      have hxn : (n : ℝ) ^ 4 ≤ euclidNorm x :=
        not_lt.1 fun h => hx (mem_diskFinset_iff'.2 h)
      rw [hf]
      have hz : ∀ j ∈ Finset.Ico k n,
          green ((n : ℝ) ^ 4) (w j) x * (a j - b j) = 0 := fun j _ => by
        rw [green_eq_zero_of_le _ hxn, zero_mul]
      rw [Finset.sum_eq_zero hz]
      exact hMnn
    · intro x hx
      have hx' : x ∈ (Finset.Ico k n).image w := by
        rw [← hBw]
        exact Finset.mem_coe.1 hx
      obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hx'
      have hℓn : ℓ < n := (Finset.mem_Ico.1 hℓ).2
      have e1 : ∑ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) (w ℓ) (w j) * b j = 1 := by
        have h := prob_hitsBefore_eq_sum_image ((n : ℝ) ^ 4) (Finset.Ico k n) w hwinj hwnorm
          (w ℓ)
        rw [← hBw] at h
        simp only [← hb] at h
        rw [← h]
        exact prob_hitsBefore_self _ _ (hmem ℓ hℓ) (hwnorm ℓ hℓ)
      have e2 : ∑ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) (axisPt ℓ) (axisPt j) * a j = 1 := by
        have h := prob_hitsBefore_eq_sum_image ((n : ℝ) ^ 4) (Finset.Ico k n)
          (fun j : ℕ => axisPt (j : ℤ)) axisPt_nat_injective.injOn hpnorm (axisPt ℓ)
        rw [← hBax] at h
        simp only [← ha] at h
        rw [← h]
        exact prob_hitsBefore_self _ _ (hmemp ℓ hℓ) (hpnorm ℓ hℓ)
      have e3 : f (w ℓ) = ∑ j ∈ Finset.Ico k n, (green ((n : ℝ) ^ 4) (w ℓ) (w j) -
          green ((n : ℝ) ^ 4) (axisPt ℓ) (axisPt j)) * a j := by
        rw [hf]
        calc ∑ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) (w j) (w ℓ) * (a j - b j)
            = ∑ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) (w ℓ) (w j) * a j -
                ∑ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) (w ℓ) (w j) * b j := by
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun j _ => by rw [green_symm _ (w j) (w ℓ)]; ring
          _ = ∑ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) (w ℓ) (w j) * a j -
                ∑ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) (axisPt ℓ) (axisPt j) * a j := by
              rw [e1, e2]
          _ = _ := by
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun j _ => by ring
      rw [e3]
      have hterm : ∀ j ∈ Finset.Ico k n, (green ((n : ℝ) ^ 4) (w ℓ) (w j) -
          green ((n : ℝ) ^ 4) (axisPt ℓ) (axisPt j)) * a j ≤
          C₂ * max c₁ 0 / (Real.sqrt n * Real.log n) * (1 / (|(ℓ : ℝ) - j| + 1) * u j) := by
        intro j hj
        have hjn : j < n := (Finset.mem_Ico.1 hj).2
        have hd0 : 0 < |(ℓ : ℝ) - j| + 1 := by positivity
        calc (green ((n : ℝ) ^ 4) (w ℓ) (w j) - green ((n : ℝ) ^ 4) (axisPt ℓ) (axisPt j)) * a j
            ≤ (C₂ / (|(ℓ : ℝ) - j| + 1)) * a j :=
              mul_le_mul_of_nonneg_right (hG2 n (by omega) w hw ℓ j hℓn hjn) (ha0 j)
          _ ≤ (C₂ / (|(ℓ : ℝ) - j| + 1)) * (max c₁ 0 * u j / (Real.sqrt n * Real.log n)) :=
              mul_le_mul_of_nonneg_left (hA j hj) (by positivity)
          _ = C₂ * max c₁ 0 / (Real.sqrt n * Real.log n) * (1 / (|(ℓ : ℝ) - j| + 1) * u j) := by
              field_simp
      calc _ ≤ ∑ j ∈ Finset.Ico k n,
            C₂ * max c₁ 0 / (Real.sqrt n * Real.log n) * (1 / (|(ℓ : ℝ) - j| + 1) * u j) :=
            Finset.sum_le_sum hterm
        _ = C₂ * max c₁ 0 / (Real.sqrt n * Real.log n) *
            ∑ j ∈ Finset.Ico k n, 1 / (|(ℓ : ℝ) - j| + 1) * u j := by rw [Finset.mul_sum]
        _ ≤ C₂ * max c₁ 0 / (Real.sqrt n * Real.log n) * S₂ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc ∑ j ∈ Finset.Ico k n, 1 / (|(ℓ : ℝ) - j| + 1) * u j
                = ∑ j ∈ Finset.Ico k n, 1 / (|(ℓ : ℝ) - j| + 1) *
                    (1 / Real.sqrt ((j : ℝ) - k + 1) + 1 / Real.sqrt ((n : ℝ) - j + 1)) :=
                  Finset.sum_congr rfl fun j _ => by rw [hu]
              _ ≤ S₂ := hS₂ n k ℓ
        _ = C₂ * max c₁ 0 * S₂ / (Real.sqrt n * Real.log n) := by ring
  have hid : ∑ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) 0 (axisPt j) * a j -
      ∑ j ∈ Finset.Ico k n, green ((n : ℝ) ^ 4) 0 (w j) * b j =
      ∑ j ∈ Finset.Ico k n, (green ((n : ℝ) ^ 4) 0 (axisPt j) -
        green ((n : ℝ) ^ 4) 0 (w j)) * a j + f 0 := by
    rw [hf, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [green_symm _ (w j) 0]
    ring
  have hZ' := hZ n k hn2 hk hkn
  rw [← hBaxset] at hZ'
  have hk1 : 1 ≤ Real.sqrt k := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hk'
  have hX : 0 ≤ max c₁ 0 * (C₁ * S₁ + C₂ * S₂) := by positivity
  have hc₀ : c₀ * Real.sqrt k ≤ max c₀ 0 * Real.sqrt k :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  have hXk : max c₁ 0 * (C₁ * S₁ + C₂ * S₂) ≤ max c₁ 0 * (C₁ * S₁ + C₂ * S₂) * Real.sqrt k :=
    le_mul_of_one_le_right hX hk1
  calc prob (exitsBefore ((n : ℝ) ^ 4) (Bw : Set (Site 2)) 0)
      ≤ (c₀ * Real.sqrt k + C₁ * max c₁ 0 * S₁ + C₂ * max c₁ 0 * S₂) /
          (Real.sqrt n * Real.log n) := by
        rw [add_div, add_div]
        have := hZ'
        linarith
    _ ≤ (max c₀ 0 + max c₁ 0 * (C₁ * S₁ + C₂ * S₂)) * Real.sqrt k /
          (Real.sqrt n * Real.log n) := by
        refine div_le_div_of_nonneg_right ?_ hD.le
        nlinarith

end FiniteAvalanches.Walk.Beurling
