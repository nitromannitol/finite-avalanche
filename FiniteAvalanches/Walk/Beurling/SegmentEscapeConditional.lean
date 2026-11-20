import FiniteAvalanches.Walk.Beurling.FarEscape

/-!
# Escape from a segment of the real axis, given the half-line estimates

Let `0 ≤ k ≤ n / 2`, let the simple random walk on `ℤ²` start at a point `j` of the segment
`{k, …, n - 1}` of the real axis, and let `m = n⁴`. The probability that the walk reaches the
circle of radius `m` before it returns to the segment is at most
`c / √n * (1 / √(j - k + 1) + 1 / √(n - j + 1)) * (1 / log n)`
(Lawler and Limic, 2004, Lemma 14). This file derives the estimate from the half-line bounds of
Proposition 12 (d), (e) of the same paper, which enter as hypotheses; part (e) is used only for
`j ≤ n`. The other two inputs are proved: the uniform lower bound for hitting a dense set (Lemma 7,
`hit_shellPart_lower`) and the escape bound (29) (`far_before_radius`).

The proof has three steps.

1. Up to its exit from the disk of radius `r = ⌊n / 8⌋` around `j`, the walk sees the segment as a
   half-line, since one endpoint of the segment is at distance more than `r` from `j`. Hence
   Proposition 12 (d), (e), for the half-line or for its image under `z ↦ -z`, bound the probability
   `b` of leaving the disk of radius `2n` before returning to the segment by
   `C / √n * (1 / √(j - k + 1) + 1 / √(n - j + 1))`.
2. Let `q` be the maximum over the disk of radius `2n + 1` of the probability of reaching the
   circle of radius `m` without a visit to the segment, time `0` included. By the maximum
   principle, from a start in the disk of radius `n` this probability is at most `q` times the
   probability of leaving the disk of radius `2n` before visiting the segment. The latter is at
   most `1 - c` by Lemma 7 for the dense set `{(i, 0) : i ≥ 0}`, whose part in the annulus
   `n / 2 ≤ |z| < n` lies in the segment. The maximum principle once more, with (29), gives
   `q ≤ K / log n + (1 - c) q`.
3. The first step from `j` and the comparison of step 2 bound the probability by `q * b`.

## Main statements

* `prob_exitsBefore_segment_le_of_halfLine`: Lemma 14, given Proposition 12 (d), (e).
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

private theorem measurableSet_exitsAvoiding (r : ℝ) (B : Set (Site 2)) (y : Site 2) :
    MeasurableSet (exitsAvoiding r B y) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    (measurable_walkPos_pred y (fun z => r ≤ euclidNorm z) t).and <| Measurable.forall fun s =>
      measurable_walkPos_pred y (fun z => s ≤ t → z ∉ B) s

private theorem exitsAvoiding_eq_empty {r : ℝ} {B : Set (Site 2)} {y : Site 2} (hy : y ∈ B) :
    exitsAvoiding r B y = ∅ := by
  ext ω
  refine ⟨fun hω => absurd hω ?_, fun hω => absurd hω (Set.notMem_empty ω)⟩
  simp only [exitsAvoiding, Set.mem_setOf_eq, not_exists,
    not_and, not_forall]
  intro t _
  exact ⟨0, Nat.zero_le _, by simpa [walkPos] using not_not.2 hy⟩

private theorem exitsAvoiding_eq_univ {r : ℝ} {B : Set (Site 2)} {y : Site 2} (hy : y ∉ B)
    (hr : r ≤ euclidNorm y) : exitsAvoiding r B y = Set.univ := by
  ext ω
  simp only [exitsAvoiding, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  refine ⟨0, by simpa [walkPos] using hr, fun s hs => ?_⟩
  obtain rfl : s = 0 := by omega
  simpa [walkPos] using hy

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
  rw [walkOp, nbrSum, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, dirVec_eq_unit, dirVec_eq_neg_unit, ← sub_eq_add_neg]
  norm_num

/-- The maximum principle on a finite set of the lattice, for a function that is the mean of
its four neighbouring values on the set. -/
private theorem le_of_neighbour_mean (Λ : Finset (Site 2)) (g : Site 2 → ℝ) (M : ℝ)
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
      rw [walkOp_eq_sum, hin y hy, hharm y hy]
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
private theorem exitsBefore_eq_firstStep {r : ℝ} {B : Set (Site 2)} {y : Site 2}
    (hyr : euclidNorm y < r) :
    exitsBefore r B y = {ω | shiftBy 1 ω ∈ exitsAvoiding r B (y + dirVec (ω 0))} := by
  ext ω
  simp only [exitsBefore, exitsAvoiding, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht, hs⟩
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · exfalso
      simp only [walkPos, Finset.range_zero, Finset.sum_empty, add_zero] at ht
      linarith
    · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
      refine ⟨t', by rwa [← walkPos_one_add], fun s hs' => ?_⟩
      rw [← walkPos_one_add]
      exact hs (1 + s) (by omega) (by omega)
  · rintro ⟨t, ht, hs⟩
    refine ⟨1 + t, by rwa [walkPos_one_add], fun s h1 hs' => ?_⟩
    obtain ⟨s', rfl⟩ : ∃ s', s = 1 + s' := ⟨s - 1, by omega⟩
    rw [walkPos_one_add]
    exact hs s' (by omega)

private theorem prob_exitsBefore_step {r : ℝ} {B : Set (Site 2)} {y : Site 2}
    (hyr : euclidNorm y < r) :
    prob (exitsBefore r B y) = (∑ a : Dir 2, prob (exitsAvoiding r B (y + dirVec a))) / 4 := by
  rw [exitsBefore_eq_firstStep hyr]
  rw [prob_firstStep (fun a => exitsAvoiding r B (y + dirVec a))
    (fun a => measurableSet_exitsAvoiding _ _ _), ← Finset.mul_sum]
  ring

/-- Reaching radius `r` before the walk visits `B`, and hitting `B` before leaving the disk of
radius `r`, are disjoint events. -/
private theorem prob_exitsAvoiding_add_hitsBefore_le (r : ℝ) (B : Set (Site 2)) (y : Site 2) :
    prob (exitsAvoiding r B y) + prob (hitsBefore B r y) ≤ 1 := by
  have hd : Disjoint (exitsAvoiding r B y) (hitsBefore B r y) := by
    rw [Set.disjoint_left]
    rintro ω ⟨t₁, ht₁, hB₁⟩ ⟨t₂, hB₂, hr₂⟩
    have ht : t₂ < t₁ := by
      by_contra h
      exact absurd (hr₂ t₁ (not_lt.1 h)) (not_lt.2 ht₁)
    exact hB₁ t₂ ht.le hB₂
  have h : prob (exitsAvoiding r B y ∪ hitsBefore B r y) =
      prob (exitsAvoiding r B y) + prob (hitsBefore B r y) :=
    measureReal_union hd (measurableSet_hitsBefore B r y)
  rw [← h]
  exact prob_le_one _

private theorem hitsBefore_mono {B B' : Set (Site 2)} (h : B ⊆ B') (r : ℝ) (y : Site 2) :
    hitsBefore B r y ⊆ hitsBefore B' r y :=
  fun _ ⟨t, ht, hs⟩ => ⟨t, h ht, hs⟩

private theorem walkPos_eq_add (x : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos x ω t = x + walkPos 0 ω t := by
  simp [walkPos]

private theorem euclidNorm_of_eq_zero {z : Site 2} (h : z 1 = 0) :
    euclidNorm z = |((z 0 : ℤ) : ℝ)| := by
  simp [euclidNorm, Fin.sum_univ_two, h, Real.sqrt_sq_eq_abs]

private theorem axisPt_apply_zero (i : ℤ) : axisPt i 0 = i := by simp [axisPt]

private theorem axisPt_apply_one (i : ℤ) : axisPt i 1 = 0 := by simp [axisPt]

private theorem euclidNorm_axisPt (i : ℤ) : euclidNorm (axisPt i) = |(i : ℝ)| := by
  rw [euclidNorm_of_eq_zero (axisPt_apply_one i), axisPt_apply_zero]

/-- A point of the real axis in the open disk of radius `r + 1` has first coordinate between `-r`
and `r`. -/
private theorem bounds_of_euclidNorm_lt {z : Site 2} (h1 : z 1 = 0) {r : ℕ}
    (h : euclidNorm z < (r : ℝ) + 1) : -(r : ℤ) ≤ z 0 ∧ z 0 ≤ r := by
  rw [euclidNorm_of_eq_zero h1, abs_lt] at h
  obtain ⟨h₁, h₂⟩ := h
  have h₃ : -(r : ℤ) - 1 < z 0 := by
    have : (-(r : ℝ) - 1) < ((z 0 : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  have h₄ : z 0 < (r : ℤ) + 1 := by exact_mod_cast h₂
  omega

/-- Leaving the disk of radius `R` from `x` requires leaving the disk of radius `r` around `x`
when `r + |x| ≤ R`, and up to the first such exit the walk stays within distance `r + 1` of `x`.
So only the part of the obstacle in that disk matters. -/
private theorem exitsBefore_subset_of_local {R r : ℝ} {B H : Set (Site 2)} {x : Site 2}
    (hR : r + euclidNorm x ≤ R) (hH : ∀ z, z ∈ H → euclidNorm z < r + 1 → x + z ∈ B) :
    exitsBefore R B x ⊆ exitsBefore r H 0 := by
  classical
  rintro ω ⟨t, ht, hs⟩
  have hwt : r ≤ euclidNorm (walkPos 0 ω t) := by
    have h1 := euclidNorm_add_le' x (walkPos 0 ω t)
    rw [walkPos_eq_add] at ht
    linarith
  have hex : ∃ t, r ≤ euclidNorm (walkPos 0 ω t) := ⟨t, hwt⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun s hs1 hs2 hsH => ?_⟩
  have hst : s ≤ t := hs2.trans (Nat.find_min' hex hwt)
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hs' : euclidNorm (walkPos 0 ω s') < r := not_le.1 (Nat.find_min hex (by omega))
  have hlt : euclidNorm (walkPos 0 ω (s' + 1)) < r + 1 := by
    rw [walkPos_zero_succ]
    have := euclidNorm_add_dirVec_le (walkPos 0 ω s') (ω s')
    linarith
  exact hs (s' + 1) hs1 hst (by rw [walkPos_eq_add]; exact hH _ hsH hlt)

private theorem walkPos_negDir (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos 0 (fun i => negDir (ω i)) t = -walkPos 0 ω t := by
  simp [walkPos, dirVec_negDir, Finset.sum_neg_distrib]

private theorem measurePreserving_negDir :
    MeasurePreserving (fun (ω : ℕ → Dir 2) (i : ℕ) => negDir (ω i)) (pathLaw 2) (pathLaw 2) := by
  refine ⟨measurable_pi_lambda _ fun i =>
    (measurable_of_countable negDir).comp (measurable_pi_apply i), ?_⟩
  rw [pathLaw, Measure.infinitePi_map_pi _ (fun _ => measurable_of_countable negDir)]
  simp only [map_negDir]

/-- The law of the walk from the origin is invariant under `z ↦ -z`. -/
private theorem prob_exitsBefore_neg (r : ℝ) (H : Set (Site 2)) :
    prob (exitsBefore r {z | -z ∈ H} 0) = prob (exitsBefore r H 0) := by
  have hpre : (fun (ω : ℕ → Dir 2) (i : ℕ) => negDir (ω i)) ⁻¹' exitsBefore r H 0 =
      exitsBefore r {z | -z ∈ H} 0 := by
    ext ω
    simp only [Set.mem_preimage, exitsBefore, Set.mem_setOf_eq, walkPos_negDir, euclidNorm_neg']
  rw [← hpre, prob, prob, measurePreserving_negDir.measure_preimage
    (measurableSet_exitsBefore r H 0).nullMeasurableSet]

private theorem div_sqrt_le_div_sqrt {M a b c : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 ≤ c) (hba : b ≤ c ^ 2 * a) : M / Real.sqrt a ≤ c * M / Real.sqrt b := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have h1 : Real.sqrt b ≤ c * Real.sqrt a := by
    calc Real.sqrt b ≤ Real.sqrt (c ^ 2 * a) := Real.sqrt_le_sqrt hba
      _ = c * Real.sqrt a := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  rw [div_le_div_iff₀ hsa hsb]
  calc M * Real.sqrt b ≤ M * (c * Real.sqrt a) := mul_le_mul_of_nonneg_left h1 hM
    _ = c * M * Real.sqrt a := by ring

/-- Proposition 12 (d), (e) give a bound for the half-line `{(i, 0) : i ≥ -d}` and every
`d ≤ 36 r - 1`: for `d = 0` by (d) and inclusion, for `1 ≤ d ≤ r` by (e), and for `d > r` by
(e) at `d = r` and inclusion. -/
private theorem prob_exitsBefore_halfLine_le {Cd Ce : ℝ}
    (hd : ∀ j n : ℕ, 1 ≤ j → 1 ≤ n →
      prob (exitsBefore n (axisSet {i | (j : ℤ) ≤ i}) 0) ≤ Cd * Real.sqrt ((j : ℝ) / n))
    (he : ∀ j n : ℕ, 1 ≤ j → 1 ≤ n → j ≤ n →
      prob (exitsBefore n (axisSet {i | -(j : ℤ) ≤ i}) 0) ≤ Ce / Real.sqrt (j * n))
    {d r : ℕ} (hr : 1 ≤ r) (hdr : d + 1 ≤ 36 * r) :
    prob (exitsBefore r (axisSet {i | -(d : ℤ) ≤ i}) 0) ≤
      6 * max (max Cd Ce) 0 / Real.sqrt (r * (d + 1)) := by
  have hM0 : 0 ≤ max (max Cd Ce) 0 := le_max_right _ _
  have hCd : Cd ≤ max (max Cd Ce) 0 := (le_max_left _ _).trans (le_max_left _ _)
  have hCe : Ce ≤ max (max Cd Ce) 0 := (le_max_right _ _).trans (le_max_left _ _)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hb : (0 : ℝ) < r * (d + 1) := mul_pos hr0 (by positivity)
  have hdr' : (d : ℝ) + 1 ≤ 36 * r := by exact_mod_cast hdr
  rcases Nat.eq_zero_or_pos d with hd1 | hd1
  · -- the half-line starts at the origin: compare with the half-line starting at `1`
    subst hd1
    have hsub : axisSet {i | ((1 : ℕ) : ℤ) ≤ i} ⊆ axisSet {i | -((0 : ℕ) : ℤ) ≤ i} := by
      intro z hz
      simp only [axisSet, Set.mem_setOf_eq] at hz ⊢
      exact ⟨hz.1, by omega⟩
    calc prob (exitsBefore r (axisSet {i | -((0 : ℕ) : ℤ) ≤ i}) 0)
        ≤ prob (exitsBefore r (axisSet {i | ((1 : ℕ) : ℤ) ≤ i}) 0) :=
          prob_mono (exitsBefore_anti hsub r 0)
      _ ≤ Cd * Real.sqrt (((1 : ℕ) : ℝ) / r) := hd 1 r le_rfl hr
      _ ≤ max (max Cd Ce) 0 * Real.sqrt (((1 : ℕ) : ℝ) / r) :=
          mul_le_mul_of_nonneg_right hCd (Real.sqrt_nonneg _)
      _ = max (max Cd Ce) 0 / Real.sqrt r := by
          rw [Nat.cast_one, Real.sqrt_div' 1 hr0.le, Real.sqrt_one, mul_one_div]
      _ ≤ 6 * max (max Cd Ce) 0 / Real.sqrt (r * ((0 : ℕ) + 1)) :=
          div_sqrt_le_div_sqrt hM0 hr0 hb (by norm_num) (by push_cast; nlinarith)
  · rcases le_or_gt d r with hdr1 | hdr1
    · -- `1 ≤ d ≤ r`: Proposition 12 (e)
      have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      calc prob (exitsBefore r (axisSet {i | -(d : ℤ) ≤ i}) 0)
          ≤ Ce / Real.sqrt (d * r) := he d r hd1 hr hdr1
        _ ≤ max (max Cd Ce) 0 / Real.sqrt (d * r) :=
            div_le_div_of_nonneg_right hCe (Real.sqrt_nonneg _)
        _ ≤ 6 * max (max Cd Ce) 0 / Real.sqrt (r * (d + 1)) :=
            div_sqrt_le_div_sqrt hM0 (mul_pos (by exact_mod_cast hd1) hr0) hb (by norm_num)
              (by nlinarith [mul_le_mul_of_nonneg_left hd1' hr0.le])
    · -- `d > r`: the half-line starting at `-r` is smaller
      have hsub : axisSet {i | -(r : ℤ) ≤ i} ⊆ axisSet {i | -(d : ℤ) ≤ i} := by
        intro z hz
        simp only [axisSet, Set.mem_setOf_eq] at hz ⊢
        exact ⟨hz.1, by omega⟩
      calc prob (exitsBefore r (axisSet {i | -(d : ℤ) ≤ i}) 0)
          ≤ prob (exitsBefore r (axisSet {i | -(r : ℤ) ≤ i}) 0) :=
            prob_mono (exitsBefore_anti hsub r 0)
        _ ≤ Ce / Real.sqrt (r * r) := he r r hr hr le_rfl
        _ ≤ max (max Cd Ce) 0 / Real.sqrt (r * r) :=
            div_le_div_of_nonneg_right hCe (Real.sqrt_nonneg _)
        _ ≤ 6 * max (max Cd Ce) 0 / Real.sqrt (r * (d + 1)) :=
            div_sqrt_le_div_sqrt hM0 (mul_pos hr0 hr0) hb (by norm_num)
              (by nlinarith [mul_le_mul_of_nonneg_left hdr' hr0.le])

/-- The positive half-axis `{(i, 0) : i ≥ 0}` meets every annulus `j ≤ |z| < j + 1`. -/
private theorem isDense_axisSet_nonneg : IsDense (axisSet {i | 0 ≤ i}) := by
  intro j
  refine ⟨axisPt j, ?_, ?_⟩
  · simp [axisSet, axisPt]
  · rw [euclidNorm_axisPt]
    simp

end Aux

set_option maxHeartbeats 400000 in
/-- **Lawler and Limic (2004), Lemma 14, given Proposition 12 (d), (e).** Let `0 ≤ k ≤ n / 2`,
`k ≤ j < n` and `m = n⁴`. From the point `(j, 0)` the probability that the walk reaches the circle
of radius `m` before a positive-time visit to the segment `{(i, 0) : k ≤ i < n}` is at most
`c / √n * (1 / √(j - k + 1) + 1 / √(n - j + 1)) * (1 / log n)`.

The hypotheses are Proposition 12 (d) and (e); in (e) only the range `j ≤ n` is assumed. -/
theorem prob_exitsBefore_segment_le_of_halfLine
    (hd : ∃ C : ℝ, ∀ j n : ℕ, 1 ≤ j → 1 ≤ n →
      prob (exitsBefore n (axisSet {i | (j : ℤ) ≤ i}) 0) ≤ C * Real.sqrt ((j : ℝ) / n))
    (he : ∃ C : ℝ, ∀ j n : ℕ, 1 ≤ j → 1 ≤ n → j ≤ n →
      prob (exitsBefore n (axisSet {i | -(j : ℤ) ≤ i}) 0) ≤ C / Real.sqrt (j * n)) :
    ∃ c : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k j : ℕ, k ≤ n / 2 → k ≤ j → j < n →
      prob (exitsBefore ((n : ℝ) ^ 4) (axisSet (Set.Ico (k : ℤ) n)) (axisPt j)) ≤
        c / Real.sqrt n * (1 / Real.sqrt (j - k + 1) + 1 / Real.sqrt (n - j + 1)) *
          (1 / Real.log n) := by
  classical
  obtain ⟨Cd, hCd⟩ := hd
  obtain ⟨Ce, hCe⟩ := he
  obtain ⟨cs, hcs, N₁, hhit⟩ := hit_shellPart_lower
  obtain ⟨K, N₂, h29⟩ := far_before_radius
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max (max Cd Ce) 0 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM ▸ le_max_right _ _
  have hK' : 0 ≤ max K 0 := le_max_right _ _
  refine ⟨48 * M * max K 0 / cs, max (max N₁ N₂) 64, fun n hn k j hkn hkj hjn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn64 : 64 ≤ n := le_trans (le_max_right _ _) hn
  have hn64' : (64 : ℝ) ≤ n := by exact_mod_cast hn64
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
  have hkj' : (k : ℝ) ≤ j := by exact_mod_cast hkj
  -- the segment
  generalize hB : axisSet (Set.Ico (k : ℤ) n) = B
  have hBmem : ∀ z, z ∈ B ↔ z 1 = 0 ∧ (k : ℤ) ≤ z 0 ∧ z 0 < n := fun z => by
    rw [← hB]
    simp only [axisSet, Set.mem_setOf_eq, Set.mem_Ico]
  have hBsub : ∀ z, z ∈ B → euclidNorm z < n := fun z hz => by
    obtain ⟨h1, h2, h3⟩ := (hBmem z).1 hz
    rw [euclidNorm_of_eq_zero h1, abs_lt]
    have h4 : (0 : ℝ) ≤ ((z 0 : ℤ) : ℝ) := by exact_mod_cast le_trans (Int.natCast_nonneg k) h2
    have h5 : ((z 0 : ℤ) : ℝ) < n := by exact_mod_cast h3
    constructor <;> linarith
  have hjnorm : euclidNorm (axisPt (j : ℤ)) = j := by
    rw [euclidNorm_axisPt]
    simp
  -- Step 1: leaving the disk of radius `2n` before returning to the segment
  have hbA : prob (exitsBefore (2 * (n : ℝ)) B (axisPt j)) ≤
      48 * M / Real.sqrt n * (1 / Real.sqrt (j - k + 1) + 1 / Real.sqrt (n - j + 1)) := by
    obtain ⟨r, hr⟩ : ∃ r : ℕ, r = n / 8 := ⟨_, rfl⟩
    have hr1 : 1 ≤ r := by omega
    have hnr : n ≤ 16 * r := by omega
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
    have hnr' : (n : ℝ) ≤ 16 * r := by exact_mod_cast hnr
    have hrn' : (r : ℝ) + j ≤ 2 * n := by
      have : r + j ≤ 2 * n := by omega
      exact_mod_cast this
    have hX : 0 ≤ 1 / Real.sqrt (j - k + 1) := by positivity
    have hY : 0 ≤ 1 / Real.sqrt (n - j + 1) := by positivity
    have hMn : 0 ≤ M / Real.sqrt n := div_nonneg hM0 (Real.sqrt_nonneg _)
    have hsplit : ∀ y : ℝ, 0 ≤ y →
        24 * M / Real.sqrt (n * y) = 24 * (M / Real.sqrt n) * (1 / Real.sqrt y) := fun y hy => by
      rw [Real.sqrt_mul hn0.le]
      ring
    have hlocal := fun (d : ℕ) (hdr : d + 1 ≤ 36 * r) =>
      prob_exitsBefore_halfLine_le hCd hCe (d := d) hr1 hdr
    rw [← hM] at hlocal
    rcases le_or_gt (r + j + 1) n with hfar | hnear
    · -- the right endpoint is far: the walk sees the half-line `{i ≥ k}`
      obtain ⟨d, hd⟩ : ∃ d : ℕ, d = j - k := ⟨_, rfl⟩
      have hd' : (d : ℝ) + 1 = j - k + 1 := by
        rw [hd, Nat.cast_sub hkj]
      have hsub : exitsBefore (2 * (n : ℝ)) B (axisPt j) ⊆
          exitsBefore r (axisSet {i | -(d : ℤ) ≤ i}) 0 := by
        refine exitsBefore_subset_of_local (by rw [hjnorm]; exact hrn') fun z hz hzr => ?_
        simp only [axisSet, Set.mem_setOf_eq] at hz
        obtain ⟨hz1, hz0⟩ := hz
        obtain ⟨hl, hu⟩ := bounds_of_euclidNorm_lt hz1 hzr
        refine (hBmem _).2 ⟨?_, ?_, ?_⟩
        · simp [axisPt_apply_one, hz1]
        · simp only [Pi.add_apply, axisPt_apply_zero]
          omega
        · simp only [Pi.add_apply, axisPt_apply_zero]
          omega
      calc prob (exitsBefore (2 * (n : ℝ)) B (axisPt j))
          ≤ prob (exitsBefore r (axisSet {i | -(d : ℤ) ≤ i}) 0) := prob_mono hsub
        _ ≤ 6 * M / Real.sqrt (r * (d + 1)) := hlocal d (by omega)
        _ ≤ 4 * (6 * M) / Real.sqrt (n * (d + 1)) :=
            div_sqrt_le_div_sqrt (by linarith) (mul_pos hr0 (by positivity))
              (mul_pos hn0 (by positivity)) (by norm_num)
              (by nlinarith [mul_le_mul_of_nonneg_right hnr' (by positivity : (0 : ℝ) ≤ d + 1)])
        _ = 24 * M / Real.sqrt (n * (d + 1)) := by ring
        _ = 24 * (M / Real.sqrt n) * (1 / Real.sqrt (j - k + 1)) := by
            rw [hsplit ((d : ℝ) + 1) (by positivity), hd']
        _ ≤ 48 * M / Real.sqrt n * (1 / Real.sqrt (j - k + 1) + 1 / Real.sqrt (n - j + 1)) := by
            rw [mul_div_assoc]
            nlinarith [mul_nonneg hMn hX, mul_nonneg hMn hY]
    · -- the left endpoint is far: the walk sees the half-line `{i ≤ n - 1}`
      obtain ⟨d, hd⟩ : ∃ d : ℕ, d = n - 1 - j := ⟨_, rfl⟩
      have hd' : (d : ℝ) + 1 = n - j := by
        have h : d + 1 + j = n := by omega
        have h' : ((d + 1 + j : ℕ) : ℝ) = n := by exact_mod_cast h
        push_cast at h'
        linarith
      have hsub : exitsBefore (2 * (n : ℝ)) B (axisPt j) ⊆
          exitsBefore r {z | -z ∈ axisSet {i | -(d : ℤ) ≤ i}} 0 := by
        refine exitsBefore_subset_of_local (by rw [hjnorm]; exact hrn') fun z hz hzr => ?_
        simp only [axisSet, Set.mem_setOf_eq, Pi.neg_apply, neg_eq_zero, neg_le_neg_iff] at hz
        obtain ⟨hz1, hz0⟩ := hz
        obtain ⟨hl, hu⟩ := bounds_of_euclidNorm_lt hz1 hzr
        refine (hBmem _).2 ⟨?_, ?_, ?_⟩
        · simp [axisPt_apply_one, hz1]
        · simp only [Pi.add_apply, axisPt_apply_zero]
          omega
        · simp only [Pi.add_apply, axisPt_apply_zero]
          omega
      have hnj : (1 : ℝ) ≤ n - j := by linarith
      calc prob (exitsBefore (2 * (n : ℝ)) B (axisPt j))
          ≤ prob (exitsBefore r {z | -z ∈ axisSet {i | -(d : ℤ) ≤ i}} 0) := prob_mono hsub
        _ = prob (exitsBefore r (axisSet {i | -(d : ℤ) ≤ i}) 0) := prob_exitsBefore_neg _ _
        _ ≤ 6 * M / Real.sqrt (r * (d + 1)) := hlocal d (by omega)
        _ ≤ 4 * (6 * M) / Real.sqrt (n * (d + 1)) :=
            div_sqrt_le_div_sqrt (by linarith) (mul_pos hr0 (by positivity))
              (mul_pos hn0 (by positivity)) (by norm_num)
              (by nlinarith [mul_le_mul_of_nonneg_right hnr' (by positivity : (0 : ℝ) ≤ d + 1)])
        _ = 24 * M / Real.sqrt (n * (n - j)) := by rw [hd']; ring
        _ ≤ 2 * (24 * M) / Real.sqrt (n * (n - j + 1)) :=
            div_sqrt_le_div_sqrt (by linarith) (mul_pos hn0 (by linarith))
              (mul_pos hn0 (by linarith)) (by norm_num)
              (by nlinarith [mul_le_mul_of_nonneg_left hnj hn0.le])
        _ = 2 * (24 * (M / Real.sqrt n) * (1 / Real.sqrt (n - j + 1))) := by
            rw [← hsplit ((n : ℝ) - j + 1) (by linarith)]
            ring
        _ ≤ 48 * M / Real.sqrt n * (1 / Real.sqrt (j - k + 1) + 1 / Real.sqrt (n - j + 1)) := by
            rw [mul_div_assoc]
            nlinarith [mul_nonneg hMn hX, mul_nonneg hMn hY]
  -- Step 2: the maximum principle
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (n : ℝ) ^ 4 := ⟨_, rfl⟩
  rw [← hm]
  have hm5 : 5 * (n : ℝ) < m := by
    have hx3 : (5 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    have h125 : (125 : ℝ) ≤ (n : ℝ) ^ 3 := by norm_num at hx3; exact hx3
    have h1 : 125 * (n : ℝ) ≤ (n : ℝ) ^ 3 * n := mul_le_mul_of_nonneg_right h125 (by linarith)
    have h2 : (n : ℝ) ^ 4 = (n : ℝ) ^ 3 * n := by ring
    linarith
  -- reaching radius `m` or `2n` without a visit to `B`, and reaching radius `m` without entering
  -- the disk of radius `n`
  obtain ⟨e, he⟩ : ∃ e : Site 2 → ℝ, ∀ y, e y = prob (exitsAvoiding m B y) := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Site 2 → ℝ, ∀ y, g y = prob (exitsAvoiding (2 * n) B y) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Site 2 → ℝ,
      ∀ y, u y = prob (exitsAvoiding m {z | euclidNorm z < n} y) := ⟨_, fun _ => rfl⟩
  have he0 : ∀ y, 0 ≤ e y := fun y => (he y).symm ▸ prob_nonneg _
  have hg0 : ∀ y, 0 ≤ g y := fun y => (hg y).symm ▸ prob_nonneg _
  have hu0 : ∀ y, 0 ≤ u y := fun y => (hu y).symm ▸ prob_nonneg _
  have heB : ∀ y, y ∈ B → e y = 0 := fun y hy => by
    rw [he, exitsAvoiding_eq_empty hy, prob_empty]
  have hgB : ∀ y, y ∈ B → g y = 0 := fun y hy => by
    rw [hg, exitsAvoiding_eq_empty hy, prob_empty]
  have heM : ∀ y, y ∉ B → m ≤ euclidNorm y → e y = 1 := fun y hy hm' => by
    rw [he, exitsAvoiding_eq_univ hy hm', prob_univ]
  have hgM : ∀ y, y ∉ B → 2 * (n : ℝ) ≤ euclidNorm y → g y = 1 := fun y hy hm' => by
    rw [hg, exitsAvoiding_eq_univ hy hm', prob_univ]
  have heS : ∀ y, y ∉ B → euclidNorm y < m → e y = (∑ a : Dir 2, e (y + dirVec a)) / 4 :=
    fun y hy hym => by
      simp only [he]
      exact prob_exitsAvoiding_step hy hym
  have hgS : ∀ y, y ∉ B → euclidNorm y < 2 * n → g y = (∑ a : Dir 2, g (y + dirVec a)) / 4 :=
    fun y hy hym => by
      simp only [hg]
      exact prob_exitsAvoiding_step hy hym
  have huS : ∀ y, (n : ℝ) ≤ euclidNorm y → euclidNorm y < m →
      u y = (∑ a : Dir 2, u (y + dirVec a)) / 4 := fun y hy1 hym => by
    simp only [hu]
    exact prob_exitsAvoiding_step (by simpa using hy1) hym
  have huM : ∀ y, m ≤ euclidNorm y → u y = 1 := fun y hy => by
    rw [hu, exitsAvoiding_eq_univ (by simp only [Set.mem_setOf_eq, not_lt]; linarith) hy,
      prob_univ]
  -- Lemma 7 for the positive half-axis, whose part in `n / 2 ≤ |z| < n` lies in `B`
  have hshell : shellPart (axisSet {i | 0 ≤ i}) ((n : ℝ) / 2) n ⊆ B := by
    intro z hz
    obtain ⟨hzA, hz1, hz2⟩ := hz
    simp only [axisSet, Set.mem_setOf_eq] at hzA
    obtain ⟨hzA1, hzA0⟩ := hzA
    have h0 : (0 : ℝ) ≤ ((z 0 : ℤ) : ℝ) := by exact_mod_cast hzA0
    rw [euclidNorm_of_eq_zero hzA1, abs_of_nonneg h0] at hz1 hz2
    have hk2 : (k : ℝ) ≤ (n : ℝ) / 2 := by
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := 2)
      have hk' : (k : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hkn
      push_cast at this
      linarith
    refine (hBmem z).2 ⟨hzA1, ?_, ?_⟩
    · have : (k : ℝ) ≤ ((z 0 : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    · exact_mod_cast hz2
  have hhit' : ∀ y : Site 2, euclidNorm y < 3 * n / 2 →
      cs ≤ prob (hitsBefore B (2 * n) y) := by
    intro y hy
    have e1 : ((2 * n : ℕ) : ℝ) / 4 = (n : ℝ) / 2 := by push_cast; ring
    have e2 : ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) := by push_cast; ring
    have e3 : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    have h := hhit (2 * n) (by omega) _ isDense_axisSet_nonneg y (by rw [e3]; linarith)
    rw [e1, e2, e3] at h
    exact h.trans (prob_mono (hitsBefore_mono hshell _ _))
  -- leaving the disk of radius `2n` before visiting `B` has probability at most `1 - cs`
  have hgle : ∀ y : Site 2, euclidNorm y < 3 * n / 2 → g y ≤ 1 - cs := fun y hy => by
    have h1 := prob_exitsAvoiding_add_hitsBefore_le (2 * (n : ℝ)) B y
    have h2 := hhit' y hy
    rw [hg]
    linarith
  -- the maximum of `e` over the disk of radius `2n + 1`
  obtain ⟨z₀, hz₀, hmax⟩ := Finset.exists_max_image (diskFinset (2 * (n : ℝ) + 1)) e
    ⟨0, by rw [mem_diskFinset_iff', euclidNorm_zero]; linarith⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = e z₀ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := hq ▸ he0 z₀
  have hemax : ∀ y : Site 2, euclidNorm y < 2 * n + 1 → e y ≤ q := fun y hy =>
    hq ▸ hmax y (mem_diskFinset_iff'.2 hy)
  -- from a start in the disk of radius `2n`, `e` is at most `q` times `g`
  have hF4 : ∀ y : Site 2, euclidNorm y < 2 * n → e y ≤ q * g y := by
    intro y hy
    by_cases hyB : y ∈ B
    · rw [heB y hyB, hgB y hyB]
      simp
    · have key := le_of_neighbour_mean
        ((diskFinset (2 * (n : ℝ))).filter fun z => z ∉ B) (fun z => e z - q * g z) 0 ?_ ?_ y
        (Finset.mem_filter.2 ⟨mem_diskFinset_iff'.2 hy, hyB⟩)
      · linarith
      · intro z hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
        have hz1' := mem_diskFinset_iff'.1 hz1
        have h1 := heS z hz2 (by linarith)
        have h2 := hgS z hz2 hz1'
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2]
        ring
      · intro z hz a hza
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
        have hz1' := mem_diskFinset_iff'.1 hz1
        have hnorm := euclidNorm_add_dirVec_le z a
        by_cases hwB : z + dirVec a ∈ B
        · simp only [heB _ hwB, hgB _ hwB]
          simp
        · have hw2n : 2 * (n : ℝ) ≤ euclidNorm (z + dirVec a) := by
            by_contra hlt
            exact hza (Finset.mem_filter.2 ⟨mem_diskFinset_iff'.2 (not_le.1 hlt), hwB⟩)
          simp only [hgM _ hwB hw2n]
          have := hemax (z + dirVec a) (by linarith)
          linarith
  have hF5 : ∀ y : Site 2, euclidNorm y < n → e y ≤ q * (1 - cs) := fun y hy =>
    (hF4 y (by linarith)).trans (mul_le_mul_of_nonneg_left (hgle y (by linarith)) hq0)
  have hqc0 : 0 ≤ q * (1 - cs) := (he0 0).trans (hF5 0 (by rw [euclidNorm_zero]; linarith))
  -- outside the disk of radius `n`, `e` is at most `u` plus the bound inside the disk
  have hF6 : ∀ y : Site 2, euclidNorm y < m → e y ≤ u y + q * (1 - cs) := by
    intro y hy
    by_cases hyn : euclidNorm y < n
    · have := hF5 y hyn
      linarith [hu0 y]
    · rw [not_lt] at hyn
      have key := le_of_neighbour_mean ((diskFinset m).filter fun z => (n : ℝ) ≤ euclidNorm z)
        (fun z => e z - u z) (q * (1 - cs)) ?_ ?_ y
        (Finset.mem_filter.2 ⟨mem_diskFinset_iff'.2 hy, hyn⟩)
      · linarith
      · intro z hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
        have hz1' := mem_diskFinset_iff'.1 hz1
        have hzB : z ∉ B := fun h => absurd (hBsub z h) (not_lt.2 hz2)
        have h1 := heS z hzB hz1'
        have h2 := huS z hz2 hz1'
        rw [Finset.sum_sub_distrib]
        linarith
      · intro z hz a hza
        by_cases hwn : euclidNorm (z + dirVec a) < n
        · have := hF5 _ hwn
          linarith [hu0 (z + dirVec a)]
        · have hwm : m ≤ euclidNorm (z + dirVec a) := by
            by_contra hlt
            exact hza (Finset.mem_filter.2 ⟨mem_diskFinset_iff'.2 (not_le.1 hlt), not_lt.1 hwn⟩)
          have hwB : z + dirVec a ∉ B := fun h => absurd (hBsub _ h) (by linarith)
          rw [heM _ hwB hwm, huM _ hwm]
          linarith
  -- equation (29): reaching radius `m` before entering the disk of radius `n`
  have hF7 : ∀ y : Site 2, euclidNorm y < 4 * n → u y ≤ K / Real.log n := by
    intro y hy
    have h := h29 n hn2 y hy
    rw [← hm] at h
    have hset : exitsAvoiding m {z | euclidNorm z < n} y =
        {ω | ∃ t, m ≤ euclidNorm (walkPos y ω t) ∧ ∀ s ≤ t, n ≤ euclidNorm (walkPos y ω s)} := by
      ext ω
      simp only [exitsAvoiding, Set.mem_setOf_eq, not_lt]
    rw [hu, hset]
    exact h
  have hz₀n := mem_diskFinset_iff'.1 hz₀
  have hq1 : q ≤ K / Real.log n + q * (1 - cs) := by
    have h1 := hF6 z₀ (by linarith)
    have h2 := hF7 z₀ (by linarith)
    rw [← hq] at h1
    linarith
  have hq2 : q ≤ max K 0 / cs / Real.log n := by
    rw [div_right_comm, le_div_iff₀ hcs]
    have : K / Real.log n ≤ max K 0 / Real.log n :=
      div_le_div_of_nonneg_right (le_max_left _ _) hlogpos.le
    linarith
  -- Step 3: the first step from `(j, 0)`
  have hjm : euclidNorm (axisPt (j : ℤ)) < 2 * n := by rw [hjnorm]; linarith
  have hstep : prob (exitsBefore m B (axisPt j)) ≤ q * prob (exitsBefore (2 * n) B (axisPt j)) := by
    rw [prob_exitsBefore_step (by linarith), prob_exitsBefore_step hjm, mul_div_assoc',
      Finset.mul_sum]
    refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => ?_) (by norm_num)
    rw [← he, ← hg]
    exact hF4 _ (by have := euclidNorm_add_dirVec_le (axisPt (j : ℤ)) a; linarith)
  have hQ : 0 ≤ max K 0 / cs / Real.log n := div_nonneg (div_nonneg hK' hcs.le) hlogpos.le
  calc prob (exitsBefore m B (axisPt j))
      ≤ q * prob (exitsBefore (2 * n) B (axisPt j)) := hstep
    _ ≤ max K 0 / cs / Real.log n * prob (exitsBefore (2 * n) B (axisPt j)) :=
        mul_le_mul_of_nonneg_right hq2 (prob_nonneg _)
    _ ≤ max K 0 / cs / Real.log n *
          (48 * M / Real.sqrt n * (1 / Real.sqrt (j - k + 1) + 1 / Real.sqrt (n - j + 1))) :=
        mul_le_mul_of_nonneg_left hbA hQ
    _ = 48 * M * max K 0 / cs / Real.sqrt n *
          (1 / Real.sqrt (j - k + 1) + 1 / Real.sqrt (n - j + 1)) * (1 / Real.log n) := by
        ring

end FiniteAvalanches.Walk.Beurling
