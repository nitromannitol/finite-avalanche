/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/Main.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added;
`Set.mem_ofPred_eq` replaced by `Set.mem_setOf_eq` (4 times); `measurableSet_setOfPred` replaced by
`measurableSet_setOf` (once).
-/
import FiniteAvalanches.Walk.Beurling.FarEscape

/-!
# The Beurling estimate for dense sets

For the simple random walk on `ℤ²` and a dense set `A`, one that meets every annulus
`j ≤ |z| < j + 1`, the probability that the walk from the origin leaves the disk of radius `2n`
before it visits `A[k, n]`, the part of `A` in the annulus `k ≤ |z| < n`, is at most `c √(k / n)`
(Lawler and Limic, 2004, Theorem 1, for `κ = 1`). This file derives it from the bound of section 5
of the paper for large `n`: the probability of reaching the circle of radius `n⁴` before visiting
`A[k, n]` is at most of order `√k / (√n log n)` for a minimal dense set `A`.

A dense set contains a minimal one, with one point in each annulus, and removing points from `A`
only enlarges the event, so it suffices to treat minimal sets. For `k > n / 2`, or for `n` below a
fixed threshold, the bound holds with a large constant. Otherwise let `B = A[k, n]` and
`m = n⁴`. From every site at distance between `2n` and `2n + 1` from the origin, the walk reaches
the circle of radius `m` before it enters the closed disk of radius `n`, hence before it visits
`B`, with probability at least `c / log n`. This follows, as Lemma 13 (i) of the paper, from the
comparison with an affine function of the potential kernel `a`, harmonic off the origin with
`a(x) = (2/π) log |x| + κ + O(|x|⁻¹)`; here the inner radius is `n` in place of `2n`. The maximum
principle on the disk of radius `2n` with `B` removed then gives
`P(τ_m < T_B) ≥ (c / log n) P(τ_{2n} < T_B)`, and the bound for `P(τ_m < T_B)` gives the theorem.

## Main statements

* `exitsAvoiding_closedDisk_lower`: from distance between `2n` and `2n + 1`, the walk reaches the
  circle of radius `n⁴` before it enters the closed disk of radius `n` with probability at least
  of order `1 / log n`.
* `mul_prob_exitsBefore_le`: the maximum principle comparison of `P(τ_m < T_B)` with
  `P(τ_r < T_B)` for `r ≤ m`.
* `lawler_limic_beurling_of_far_escape`: Theorem 1 of Lawler and Limic (2004) for `κ = 1`, from
  the bound of section 5 for large `n`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

section Aux

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

private theorem le_euclidNorm_add_dirVec (y : Site 2) (a : Dir 2) :
    euclidNorm y ≤ euclidNorm (y + dirVec a) + 1 := by
  have h := euclidNorm_add_le' (y + dirVec a) (-dirVec a)
  rwa [add_neg_cancel_right, euclidNorm_neg', euclidNorm_dirVec] at h

private theorem measurableSet_exitsAvoiding (r : ℝ) (B : Set (Site 2)) (y : Site 2) :
    MeasurableSet (exitsAvoiding r B y) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    (measurable_walkPos_pred y (fun z => r ≤ euclidNorm z) t).and <| Measurable.forall fun s =>
      measurable_walkPos_pred y (fun z => s ≤ t → z ∉ B) s

private theorem exitsAvoiding_eq_empty {r : ℝ} {B : Set (Site 2)} {y : Site 2} (hy : y ∈ B) :
    exitsAvoiding r B y = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨t, _, hs⟩ =>
    hs 0 (Nat.zero_le t) (by simpa [walkPos] using hy)

private theorem exitsAvoiding_eq_univ {r : ℝ} {B : Set (Site 2)} {y : Site 2} (hy : y ∉ B)
    (hr : r ≤ euclidNorm y) : exitsAvoiding r B y = Set.univ := by
  ext ω
  simp only [exitsAvoiding, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  refine ⟨0, by simpa [walkPos] using hr, fun s hs => ?_⟩
  obtain rfl : s = 0 := by omega
  simpa [walkPos] using hy

private theorem exitsAvoiding_anti {B B' : Set (Site 2)} (h : B ⊆ B') (r : ℝ) (y : Site 2) :
    exitsAvoiding r B' y ⊆ exitsAvoiding r B y :=
  fun _ ⟨t, ht, hs⟩ => ⟨t, ht, fun s hst hB => hs s hst (h hB)⟩

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

private theorem potentialKernel_approx :
    ∃ c₀ κ C R : ℝ, 0 < c₀ ∧ 0 ≤ C ∧ 1 ≤ R ∧ ∀ x : Site 2, R ≤ euclidNorm x →
      |potentialKernel x - (c₀ * Real.log (euclidNorm x) + κ)| ≤ C / euclidNorm x := by
  obtain ⟨κ, C, R, hR, h⟩ := exists_abs_potentialKernel_sub_log_le
  refine ⟨2 / Real.pi, κ, max C 0, R, div_pos two_pos Real.pi_pos, le_max_right _ _, hR,
    fun x hx => ?_⟩
  have hxpos : 0 < euclidNorm x := by linarith
  refine (h x hx).trans ?_
  have h2 : euclidNorm x ^ (-2 : ℝ) ≤ 1 / euclidNorm x := by
    rw [Real.rpow_neg hxpos.le, Real.rpow_two, one_div]
    exact inv_anti₀ hxpos (by nlinarith)
  calc C * euclidNorm x ^ (-2 : ℝ) ≤ max C 0 * euclidNorm x ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 / euclidNorm x) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = max C 0 / euclidNorm x := by ring

/-- The lower bound for the potential kernel on `{r ≤ |z|}`. -/
private theorem le_potentialKernel {c₀ κ C R : ℝ} (hc₀ : 0 < c₀) (hC : 0 ≤ C)
    (hpk : ∀ x : Site 2, R ≤ euclidNorm x →
      |potentialKernel x - (c₀ * Real.log (euclidNorm x) + κ)| ≤ C / euclidNorm x)
    {r : ℝ} (hr : 0 < r) (hRr : R ≤ r) {z : Site 2} (hz : r ≤ euclidNorm z) :
    c₀ * Real.log r + κ - C / r ≤ potentialKernel z := by
  have h1 := (abs_le.1 (hpk z (hRr.trans hz))).1
  have h2 := mul_le_mul_of_nonneg_left (Real.log_le_log hr hz) hc₀.le
  have h3 : C / euclidNorm z ≤ C / r := div_le_div_of_nonneg_left hC hr hz
  linarith

/-- The upper bound for the potential kernel on `{r ≤ |z| ≤ s}`. -/
private theorem potentialKernel_le {c₀ κ C R : ℝ} (hc₀ : 0 < c₀) (hC : 0 ≤ C)
    (hpk : ∀ x : Site 2, R ≤ euclidNorm x →
      |potentialKernel x - (c₀ * Real.log (euclidNorm x) + κ)| ≤ C / euclidNorm x)
    {r s : ℝ} (hr : 0 < r) (hRr : R ≤ r) {z : Site 2} (hz : r ≤ euclidNorm z)
    (hzs : euclidNorm z ≤ s) :
    potentialKernel z ≤ c₀ * Real.log s + κ + C / r := by
  have hzpos : 0 < euclidNorm z := lt_of_lt_of_le hr hz
  have h1 := (abs_le.1 (hpk z (hRr.trans hz))).2
  have h2 := mul_le_mul_of_nonneg_left (Real.log_le_log hzpos hzs) hc₀.le
  have h3 : C / euclidNorm z ≤ C / r := div_le_div_of_nonneg_left hC hr hz
  linarith

private theorem potentialKernel_harmonic {y : Site 2} (hy : y ≠ 0) :
    (∑ a : Dir 2, potentialKernel (y + dirVec a)) / 4 = potentialKernel y := by
  have h := walkOp_potentialKernel_sub y
  have h0 : (if y = 0 then (1 : ℝ) else 0) = 0 := by simp [hy]
  rw [h0, sub_eq_zero, walkOp_eq_sum] at h
  exact h

private theorem affine_potentialKernel_harmonic {y : Site 2} (hy : y ≠ 0) (lo s : ℝ) :
    (potentialKernel y - lo) * s =
      (∑ a : Dir 2, (potentialKernel (y + dirVec a) - lo) * s) / 4 := by
  have h := potentialKernel_harmonic hy
  have hs : ∑ a : Dir 2, potentialKernel (y + dirVec a) = 4 * potentialKernel y := by linarith
  have hcard : (Finset.univ : Finset (Dir 2)).card = 4 := by simp
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, hcard, hs]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The part of the disk of radius `m` outside the closed disk of radius `ρ`. -/
private def annulus (ρ m : ℝ) : Finset (Site 2) := by
  classical exact (diskFinset m).filter fun z => ρ < euclidNorm z

private theorem mem_annulus {ρ m : ℝ} {z : Site 2} :
    z ∈ annulus ρ m ↔ ρ < euclidNorm z ∧ euclidNorm z < m := by
  classical
  unfold annulus
  rw [Finset.mem_filter, mem_diskFinset_iff']
  tauto

/-- A neighbour of a site of the annulus outside the annulus lies in the inner or the outer
boundary layer. -/
private theorem annulus_boundary {ρ m : ℝ} {z : Site 2} (hz : z ∈ annulus ρ m) (a : Dir 2)
    (hza : z + dirVec a ∉ annulus ρ m) :
    (ρ - 1 < euclidNorm (z + dirVec a) ∧ euclidNorm (z + dirVec a) ≤ ρ) ∨
      (m ≤ euclidNorm (z + dirVec a) ∧ euclidNorm (z + dirVec a) < m + 1) := by
  obtain ⟨hz1, hz2⟩ := mem_annulus.1 hz
  have h1 := le_euclidNorm_add_dirVec z a
  have h2 := euclidNorm_add_dirVec_le z a
  rw [mem_annulus] at hza
  by_cases h : ρ < euclidNorm (z + dirVec a)
  · right
    refine ⟨not_lt.1 fun h' => hza ⟨h, h'⟩, by linarith⟩
  · left
    exact ⟨by linarith, not_lt.1 h⟩

/-- Comparison from below with the potential kernel, harmonic off the origin. -/
private theorem affine_le_exitsAvoiding {ρ m lo hi : ℝ} (hρ : 0 ≤ ρ) (hlohi : lo < hi)
    (hlo : ∀ z : Site 2, ρ - 1 < euclidNorm z → euclidNorm z ≤ ρ → potentialKernel z ≤ lo)
    (hhi : ∀ z : Site 2, m ≤ euclidNorm z → euclidNorm z < m + 1 → potentialKernel z ≤ hi)
    {y : Site 2} (hyρ : ρ < euclidNorm y) (hym : euclidNorm y < m) :
    (potentialKernel y - lo) / (hi - lo) ≤ prob (exitsAvoiding m {z | euclidNorm z ≤ ρ} y) := by
  set s := (hi - lo)⁻¹ with hs
  have hspos : 0 < s := inv_pos.2 (sub_pos.2 hlohi)
  have hss : (hi - lo) * s = 1 := mul_inv_cancel₀ (sub_pos.2 hlohi).ne'
  have key := le_of_neighbour_mean (annulus ρ m)
    (fun z => (potentialKernel z - lo) * s - prob (exitsAvoiding m {z | euclidNorm z ≤ ρ} z)) 0
    ?_ ?_ y (mem_annulus.2 ⟨hyρ, hym⟩)
  · rw [div_eq_mul_inv, ← hs]
    linarith
  · intro z hz
    obtain ⟨hz1, hz2⟩ := mem_annulus.1 hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
    have hB : z ∉ {z : Site 2 | euclidNorm z ≤ ρ} := by simpa using hz1
    have hstep := prob_exitsAvoiding_step hB hz2
    have haff := affine_potentialKernel_harmonic hz0 lo s
    simp only [Finset.sum_sub_distrib]
    linarith
  · intro z hz a hza
    rcases annulus_boundary hz a hza with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hB : z + dirVec a ∈ {z : Site 2 | euclidNorm z ≤ ρ} := h2
      rw [exitsAvoiding_eq_empty hB, prob, measure_empty, ENNReal.toReal_zero]
      have := mul_nonneg (sub_nonneg.2 (hlo _ h1 h2)) hspos.le
      nlinarith
    · have hB : z + dirVec a ∉ {z : Site 2 | euclidNorm z ≤ ρ} := by
        simp only [Set.mem_setOf_eq, not_le]
        linarith
      rw [exitsAvoiding_eq_univ hB h1, prob_univ]
      have := mul_le_mul_of_nonneg_right (sub_le_sub_right (hhi _ h1 h2) lo) hspos.le
      linarith

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

end Aux

/-- From a start at distance between `2n` and `2n + 1` from the origin, the walk reaches the
circle of radius `n⁴` before it enters the closed disk of radius `n` with probability at least of
order `1 / log n`. This is the form of Lemma 13 (i) of Lawler and Limic (2004) used in section 5
of that paper. -/
theorem exitsAvoiding_closedDisk_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ y : Site 2, 2 * n ≤ euclidNorm y →
      euclidNorm y < 2 * n + 1 →
        c / Real.log n ≤ prob (exitsAvoiding ((n : ℝ) ^ 4) {z | euclidNorm z ≤ n} y) := by
  obtain ⟨c₀, κ, C, R, hc₀, hC, hR, hpk⟩ := potentialKernel_approx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = c₀ * Real.log 2 := ⟨_, rfl⟩
  have hνpos : 0 < ν := hν ▸ mul_pos hc₀ hlog2
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * R + 3 + 6 * C / ν)
  refine ⟨ν / (2 * (5 * c₀ + C)), by positivity, N, fun n hn y hy2 hy3 => ?_⟩
  have hxN : 2 * R + 3 + 6 * C / ν ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = n := ⟨_, rfl⟩
  rw [← hx] at hxN hy2 hy3 ⊢
  have hC6 : 0 ≤ 6 * C / ν := by positivity
  have hx5 : 5 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hlog2x : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos (by linarith)
  have hlox : 0 ≤ Real.log x := by linarith
  have hCx : C / x ≤ ν / 6 := by
    have h1 : 6 * C / ν ≤ x := by linarith
    rw [div_le_iff₀ hνpos] at h1
    rw [div_le_iff₀ hx0]
    linarith
  have hx3 : (5 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx5 3
  have hm : 3 * x < x ^ 4 := by
    have h125 : (125 : ℝ) ≤ x ^ 3 := by norm_num at hx3; exact hx3
    have h1 : 125 * x ≤ x ^ 3 * x := mul_le_mul_of_nonneg_right h125 hx0.le
    have h2 : x ^ 4 = x ^ 3 * x := by ring
    linarith
  have hmpos : 0 < x ^ 4 := by positivity
  have hρ'pos : 0 < x - 1 := by linarith
  have hρ'R : R ≤ x - 1 := by linarith
  have hRm : R ≤ x ^ 4 := by linarith
  have hCρ : C / (x - 1) ≤ 2 * (C / x) := by
    have h1 : C / (x - 1) ≤ C / (x / 2) :=
      div_le_div_of_nonneg_left hC (by positivity) (by linarith)
    have h2 : C / (x / 2) = 2 * (C / x) := by
      rw [div_div_eq_mul_div]
      ring
    linarith
  have hlog2' : Real.log (2 * x) = Real.log x + Real.log 2 := by
    rw [Real.log_mul two_ne_zero hx0.ne']
    ring
  have hlog4 : Real.log x + Real.log 2 ≤ Real.log (x ^ 4 + 1) := by
    rw [← hlog2']
    exact Real.log_le_log (by positivity) (by linarith)
  have hlohi : c₀ * Real.log x + κ + C / (x - 1) <
      c₀ * Real.log (x ^ 4 + 1) + κ + C / x ^ 4 := by
    have h1 : 0 ≤ C / x ^ 4 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hlog4 hc₀.le
    linarith
  have hmain := affine_le_exitsAvoiding (m := x ^ 4) (ρ := x)
    (lo := c₀ * Real.log x + κ + C / (x - 1))
    (hi := c₀ * Real.log (x ^ 4 + 1) + κ + C / x ^ 4) hx0.le hlohi
    (fun z hz1 hz2 => potentialKernel_le hc₀ hC hpk hρ'pos hρ'R (r := x - 1) (s := x)
      hz1.le hz2)
    (fun z hz1 hz2 => potentialKernel_le hc₀ hC hpk hmpos hRm (r := x ^ 4) (s := x ^ 4 + 1)
      hz1 hz2.le)
    (y := y) (by linarith) (by linarith)
  refine le_trans ?_ hmain
  have hnum : ν / 2 ≤ potentialKernel y - (c₀ * Real.log x + κ + C / (x - 1)) := by
    have h1 := le_potentialKernel hc₀ hC hpk (r := 2 * x) (by linarith) (by linarith) hy2
    have h2 : C / (2 * x) ≤ C / x := div_le_div_of_nonneg_left hC hx0 (by linarith)
    rw [hlog2'] at h1
    linarith
  have hDpos : 0 < (c₀ * Real.log (x ^ 4 + 1) + κ + C / x ^ 4) -
      (c₀ * Real.log x + κ + C / (x - 1)) := by linarith
  have hDle : (c₀ * Real.log (x ^ 4 + 1) + κ + C / x ^ 4) -
      (c₀ * Real.log x + κ + C / (x - 1)) ≤ (5 * c₀ + C) * Real.log x := by
    have h1 : Real.log (x ^ 4 + 1) ≤ Real.log 2 + 4 * Real.log x := by
      have : Real.log (2 * x ^ 4) = Real.log 2 + 4 * Real.log x := by
        rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow]
        norm_num
      rw [← this]
      exact Real.log_le_log (by positivity) (by linarith)
    have h2 : C / x ^ 4 ≤ C := div_le_self hC (by linarith)
    have h3 : 0 ≤ C / (x - 1) := div_nonneg hC hρ'pos.le
    have h4 := mul_le_mul_of_nonneg_left h1 hc₀.le
    have h5 : 0 ≤ c₀ * Real.log x := mul_nonneg hc₀.le hlox
    have h6 : C ≤ C * Real.log x := le_mul_of_one_le_right hC hlogx
    have h7 := mul_le_mul_of_nonneg_left hlog2x hc₀.le
    linarith
  calc ν / (2 * (5 * c₀ + C)) / Real.log x = ν / 2 / ((5 * c₀ + C) * Real.log x) := by
        rw [div_div, div_div]
        congr 1
        ring
    _ ≤ ν / 2 / ((c₀ * Real.log (x ^ 4 + 1) + κ + C / x ^ 4) -
        (c₀ * Real.log x + κ + C / (x - 1))) :=
        div_le_div_of_nonneg_left (by positivity) hDpos hDle
    _ ≤ _ := div_le_div_of_nonneg_right hnum hDpos.le

/-- The maximum principle comparison. Let `r ≤ m` and suppose that from every site outside `B` at
distance between `r` and `r + 1` from the origin, the walk reaches radius `m` before it visits `B`
with probability at least `q`. Then from every start inside the disk of radius `r`, the
probability of reaching radius `m` before a visit to `B` at a positive time is at least `q` times
the probability of reaching radius `r` before a visit to `B` at a positive time. -/
theorem mul_prob_exitsBefore_le {r m q : ℝ} (hrm : r ≤ m) {B : Set (Site 2)}
    (hq : ∀ y : Site 2, y ∉ B → r ≤ euclidNorm y → euclidNorm y < r + 1 →
      q ≤ prob (exitsAvoiding m B y))
    {x : Site 2} (hx : euclidNorm x < r) :
    q * prob (exitsBefore r B x) ≤ prob (exitsBefore m B x) := by
  classical
  set g : Site 2 → ℝ := fun y => q * prob (exitsAvoiding r B y) - prob (exitsAvoiding m B y)
    with hg
  have hout : ∀ y : Site 2, ¬(y ∉ B ∧ euclidNorm y < r) → euclidNorm y < r + 1 → g y ≤ 0 := by
    intro y hy hy1
    by_cases hyB : y ∈ B
    · simp [hg, exitsAvoiding_eq_empty hyB, prob]
    · have hyr : r ≤ euclidNorm y := not_lt.1 fun h => hy ⟨hyB, h⟩
      have h := hq y hyB hyr hy1
      simp only [hg, exitsAvoiding_eq_univ hyB hyr, prob_univ, mul_one]
      linarith
  set Λ : Finset (Site 2) := (diskFinset r).filter fun y => y ∉ B with hΛ
  have hmemΛ : ∀ y, y ∈ Λ ↔ y ∉ B ∧ euclidNorm y < r := fun y => by
    rw [hΛ, Finset.mem_filter, mem_diskFinset_iff']
    exact and_comm
  have hin : ∀ y ∈ Λ, g y ≤ 0 := by
    refine le_of_neighbour_mean Λ g 0 (fun y hy => ?_) (fun y hy a hya => ?_)
    · obtain ⟨hyB, hyr⟩ := (hmemΛ y).1 hy
      have h1 := prob_exitsAvoiding_step hyB hyr
      have h2 := prob_exitsAvoiding_step hyB (hyr.trans_le hrm)
      simp only [hg, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [h1, h2]
      ring
    · have h1 := euclidNorm_add_dirVec_le y a
      have h2 := ((hmemΛ y).1 hy).2
      exact hout _ (fun h => hya ((hmemΛ _).2 h)) (by linarith)
  have hall : ∀ y : Site 2, euclidNorm y < r + 1 → g y ≤ 0 := fun y hy => by
    by_cases h : y ∉ B ∧ euclidNorm y < r
    · exact hin y ((hmemΛ y).2 h)
    · exact hout y h hy
  have hsum : ∑ a : Dir 2, g (x + dirVec a) ≤ 0 := Finset.sum_nonpos fun a _ =>
    hall _ (by have := euclidNorm_add_dirVec_le x a; linarith)
  simp only [hg, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [prob_exitsBefore_step hx, prob_exitsBefore_step (hx.trans_le hrm)]
  linarith

/-- **Lawler and Limic (2004), Theorem 1, for `κ = 1`**, from the bound of section 5 for large
`n`. There is `c > 0` such that for every dense set `A` and all `0 < k < n`, the probability that
the walk from the origin leaves the disk of radius `2n` before it visits `A[k, n]` is at most
`c √(k / n)`. The hypothesis is that bound: for `n` large and `1 ≤ k ≤ n / 2`, for a minimal dense
set the probability of reaching the circle of radius `n⁴` before visiting `A[k, n]` is at most
`c √k / (√n log n)`. -/
theorem lawler_limic_beurling_of_far_escape
    (h15 : ∃ c : ℝ, ∃ N : ℕ, ∀ n k : ℕ, N ≤ n → 1 ≤ k → k ≤ n / 2 → ∀ w : ℕ → Site 2,
      (∀ j : ℕ, (j : ℝ) ≤ euclidNorm (w j) ∧ euclidNorm (w j) < j + 1) →
      prob (exitsBefore ((n : ℝ) ^ 4) (shellPart (Set.range w) k n) 0) ≤
        c * Real.sqrt k / (Real.sqrt n * Real.log n)) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Set (Site 2), IsDense A → ∀ k n : ℕ, 0 < k → k < n →
      pathLaw 2 (exitsBefore (2 * n) (shellPart A k n) 0) ≤
        ENNReal.ofReal (c * Real.sqrt ((k : ℝ) / n)) := by
  obtain ⟨c₁₅, N₁₅, hfar⟩ := h15
  obtain ⟨c₁, hc₁, N₁, hlow⟩ := exitsAvoiding_closedDisk_lower
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = max (max N₁₅ N₁) 2 := ⟨_, rfl⟩
  have hN₁₅ : N₁₅ ≤ N := hN ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hN₁ : N₁ ≤ N := hN ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hN2 : 2 ≤ N := hN ▸ le_max_right _ _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine ⟨max (c₁₅ / c₁) (Real.sqrt (2 * N)),
    lt_max_of_lt_right (Real.sqrt_pos.2 (by positivity)), fun A hA k n hk hkn => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsq : 0 ≤ Real.sqrt ((k : ℝ) / n) := Real.sqrt_nonneg _
  rw [← ENNReal.ofReal_toReal (measure_ne_top (pathLaw 2) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  change prob _ ≤ _
  by_cases hsmall : n < N ∨ n / 2 < k
  · have h2Nk : (n : ℝ) ≤ 2 * N * k := by
      rcases hsmall with h | h
      · have h' : (n : ℝ) < N := by exact_mod_cast h
        nlinarith
      · have h' : (n : ℝ) < 2 * k := by exact_mod_cast (by omega : n < 2 * k)
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
        nlinarith
    have hone : 1 ≤ Real.sqrt (2 * N) * Real.sqrt ((k : ℝ) / n) := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * N), Real.one_le_sqrt, ← mul_div_assoc,
        le_div_iff₀ hn0, one_mul]
      exact h2Nk
    calc prob _ ≤ 1 := prob_le_one _
      _ ≤ Real.sqrt (2 * N) * Real.sqrt ((k : ℝ) / n) := hone
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hsq
  · have hNn : N ≤ n := not_lt.1 fun h => hsmall (Or.inl h)
    have hk2 : k ≤ n / 2 := not_lt.1 fun h => hsmall (Or.inr h)
    obtain ⟨w, hwA, hw⟩ := hA.exists_minimal
    have hsub : shellPart (Set.range w) k n ⊆ shellPart A k n := by
      rintro z ⟨⟨j, rfl⟩, h1, h2⟩
      exact ⟨hwA j, h1, h2⟩
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
    have hq : ∀ y : Site 2, y ∉ shellPart (Set.range w) k n → 2 * (n : ℝ) ≤ euclidNorm y →
        euclidNorm y < 2 * n + 1 →
        c₁ / Real.log n ≤ prob (exitsAvoiding ((n : ℝ) ^ 4) (shellPart (Set.range w) k n) y) := by
      intro y _ hy1 hy2
      refine (hlow n (hN₁.trans hNn) y hy1 hy2).trans (prob_mono (exitsAvoiding_anti ?_ _ _))
      rintro z ⟨_, _, hz⟩
      exact hz.le
    have hrm : 2 * (n : ℝ) ≤ (n : ℝ) ^ 4 := by
      have h8 : (2 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hn2 3
      have h4 : (n : ℝ) ^ 4 = (n : ℝ) ^ 3 * n := by ring
      nlinarith
    have h0 : euclidNorm (0 : Site 2) < 2 * n := by
      have : euclidNorm (0 : Site 2) = 0 := by simp [euclidNorm]
      rw [this]
      linarith
    have h1 := (mul_prob_exitsBefore_le hrm hq h0).trans
      (hfar n k (hN₁₅.trans hNn) (by omega) hk2 w hw)
    have e1 : c₁ / Real.log n * prob (exitsBefore (2 * n) (shellPart (Set.range w) k n) 0) =
        c₁ * prob (exitsBefore (2 * n) (shellPart (Set.range w) k n) 0) / Real.log n := by ring
    have e2 : c₁₅ * Real.sqrt k / (Real.sqrt n * Real.log n) =
        c₁₅ * Real.sqrt ((k : ℝ) / n) / Real.log n := by
      rw [Real.sqrt_div (by positivity)]
      ring
    rw [e1, e2, div_le_div_iff_of_pos_right hlogpos] at h1
    have h3 : prob (exitsBefore (2 * n) (shellPart (Set.range w) k n) 0) ≤
        c₁₅ / c₁ * Real.sqrt ((k : ℝ) / n) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc₁]
      linarith
    calc prob (exitsBefore (2 * n) (shellPart A k n) 0)
        ≤ prob (exitsBefore (2 * n) (shellPart (Set.range w) k n) 0) :=
          prob_mono (exitsBefore_anti hsub _ _)
      _ ≤ c₁₅ / c₁ * Real.sqrt ((k : ℝ) / n) := h3
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hsq

end FiniteAvalanches.Walk.Beurling
