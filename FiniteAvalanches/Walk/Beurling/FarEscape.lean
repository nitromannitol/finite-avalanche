/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/FarEscape.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added;
`Set.mem_ofPred_eq` replaced by `Set.mem_setOf_eq` (9 times); `measurableSet_setOfPred` replaced by
`measurableSet_setOf` (once).
-/
import FiniteAvalanches.Walk.Beurling.HitDense
import FiniteAvalanches.Walk.Beurling.StripExit
import LatticeProb.Walk.ExteriorDirichlet

/-!
# Escape of the walk to a far circle

For the simple random walk on `ℤ²` and `m = n⁴`, the probability that the walk started at
distance between `3n` and `4n` from the origin reaches the circle of radius `m` before it enters the
disk of radius `2n` is of order `1 / log n`. Before it visits a dense set in the annulus
`n / 2 ≤ |z| < n`, the probability that it reaches the circle of radius `m` is at most of order
`1 / log n`, uniformly in the dense set (Lawler and Limic, 2004, Lemma 13 and equation (29)).

The potential kernel `a` is harmonic off the origin and satisfies
`a(x) = (2/π) log |x| + κ + O(|x|⁻²)`. For a walk started outside a closed disk and inside the
circle of radius `m`, the probability of reaching the circle before the disk is the mean of its
values at the four neighbours, by the Markov property at time one. The maximum principle compares
it with an affine function of `a`, which gives both bounds of Lemma 13 (i) and (29). For Lemma 13
(ii) let `q` be the maximum over the disk of radius `4n + 1` of the probability of reaching the
circle of radius `m` without a visit to the dense set. The maximum principle bounds this
probability from a start in the disk of radius `2n` by `q` times the probability of leaving that
disk before visiting the dense set, which is at most `1 - c` by the uniform lower bound for hitting
a dense set (Lemma 7). The maximum principle once more, together with (29), gives
`q ≤ c' / log n + (1 - c) q`.

## Main statements

* `farBefore n w`: the walk from `w` reaches the circle of radius `n⁴` before it enters the closed
  disk of radius `2n`.
* `farBefore_bounds`: Lemma 13 (i), the probability of `farBefore n w` is of order `1 / log n`.
* `exitsBefore_shellPart_far`: Lemma 13 (ii), a uniform upper bound of order `1 / log n` for
  reaching the circle of radius `n⁴` before visiting a dense set in `n / 2 ≤ |z| < n`.
* `far_before_radius`: equation (29), reaching the circle of radius `n⁴` before entering the
  open disk of radius `n` has probability at most of order `1 / log n`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

/-- The walk from `w` reaches the circle of radius `n⁴` before entering the closed disk of
radius `2n`. -/
def farBefore (n : ℕ) (w : Site 2) : Set (ℕ → Dir 2) :=
  {ω | ∃ t, ((n : ℝ) ^ 4) ≤ euclidNorm (walkPos w ω t) ∧ ∀ s ≤ t, 2 * n < euclidNorm (walkPos w ω s)}

/-- The walk from `y` reaches radius `r` at some time `t`, with no visit to `B` at any time
`s ≤ t`, time `0` included. -/
def exitsAvoiding (r : ℝ) (B : Set (Site 2)) (y : Site 2) : Set (ℕ → Dir 2) :=
  {ω | ∃ t, r ≤ euclidNorm (walkPos y ω t) ∧ ∀ s ≤ t, walkPos y ω s ∉ B}

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

/-- Comparison from above with the potential kernel, harmonic off the origin. -/
private theorem exitsAvoiding_le_affine {ρ m lo hi : ℝ} (hρ : 0 ≤ ρ) (hlohi : lo < hi)
    (hlo : ∀ z : Site 2, ρ - 1 < euclidNorm z → euclidNorm z ≤ ρ → lo ≤ potentialKernel z)
    (hhi : ∀ z : Site 2, m ≤ euclidNorm z → euclidNorm z < m + 1 → hi ≤ potentialKernel z)
    {y : Site 2} (hyρ : ρ < euclidNorm y) (hym : euclidNorm y < m) :
    prob (exitsAvoiding m {z | euclidNorm z ≤ ρ} y) ≤ (potentialKernel y - lo) / (hi - lo) := by
  set s := (hi - lo)⁻¹ with hs
  have hspos : 0 < s := inv_pos.2 (sub_pos.2 hlohi)
  have hss : (hi - lo) * s = 1 := mul_inv_cancel₀ (sub_pos.2 hlohi).ne'
  have key := le_of_neighbour_mean (annulus ρ m)
    (fun z => prob (exitsAvoiding m {z | euclidNorm z ≤ ρ} z) - (potentialKernel z - lo) * s) 0
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
      linarith
    · have hB : z + dirVec a ∉ {z : Site 2 | euclidNorm z ≤ ρ} := by
        simp only [Set.mem_setOf_eq, not_le]
        linarith
      rw [exitsAvoiding_eq_univ hB h1, prob_univ]
      have := mul_le_mul_of_nonneg_right (sub_le_sub_right (hhi _ h1 h2) lo) hspos.le
      linarith

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

/-- The probability of reaching radius `n⁴` before entering the closed disk of radius `ρ`, for
`ρ` between `n - 1/2` and `2n`, is at most of order `1 / log n` for every start at distance
less than `5n`. -/
private theorem exitsAvoiding_upper :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ρ : ℝ, (n : ℝ) - 1 / 2 ≤ ρ → ρ ≤ 2 * n →
      ∀ y : Site 2, euclidNorm y < 5 * n →
        prob (exitsAvoiding ((n : ℝ) ^ 4) {z | euclidNorm z ≤ ρ} y) ≤ K / Real.log n := by
  obtain ⟨c₀, κ, C, R, hc₀, hC, hR, hpk⟩ := potentialKernel_approx
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * R + 3)
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK₁ : 0 < c₀ * (Real.log 5 + Real.log 2) + 4 * C := by positivity
  refine ⟨(c₀ * (Real.log 5 + Real.log 2) + 4 * C) / (2 * c₀), by positivity, N,
    fun n hn ρ hρ1 hρ2 y hy => ?_⟩
  have hxN : 2 * R + 3 ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = n := ⟨_, rfl⟩
  rw [← hx] at hxN hρ1 hρ2 hy ⊢
  have hx5 : 5 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hlogpos : 0 < Real.log x := by linarith
  have hlog2x : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos (by linarith)
  have hρ'1 : x / 2 ≤ ρ - 1 := by linarith
  have hρ'R : R ≤ ρ - 1 := by linarith
  have hρ'pos : 0 < ρ - 1 := by linarith
  have hx3 : (5 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx5 3
  have hm : 5 * x < x ^ 4 := by nlinarith
  have hmpos : 0 < x ^ 4 := by positivity
  have hρ'm : ρ - 1 < x ^ 4 := by linarith
  by_cases hyρ : euclidNorm y ≤ ρ
  · rw [exitsAvoiding_eq_empty (show y ∈ {z : Site 2 | euclidNorm z ≤ ρ} from hyρ), prob,
      measure_empty, ENNReal.toReal_zero]
    exact div_nonneg (by positivity) hlogpos.le
  rw [not_le] at hyρ
  have hD : c₀ * (Real.log (x ^ 4) - Real.log (ρ - 1)) ≤
      (c₀ * Real.log (x ^ 4) + κ - C / x ^ 4) - (c₀ * Real.log (ρ - 1) + κ - C / (ρ - 1)) := by
    have h : C / x ^ 4 ≤ C / (ρ - 1) := div_le_div_of_nonneg_left hC hρ'pos hρ'm.le
    nlinarith
  have hlogm : Real.log (x ^ 4) = 4 * Real.log x := by
    rw [Real.log_pow]
    norm_num
  have hlogρ : Real.log (ρ - 1) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul two_ne_zero hx0.ne']
    exact Real.log_le_log hρ'pos (by linarith)
  have hD2 : 2 * c₀ * Real.log x ≤
      (c₀ * Real.log (x ^ 4) + κ - C / x ^ 4) - (c₀ * Real.log (ρ - 1) + κ - C / (ρ - 1)) := by
    refine le_trans ?_ hD
    rw [hlogm]
    nlinarith
  have hDpos : 0 < 2 * c₀ * Real.log x := by positivity
  have hlohi : c₀ * Real.log (ρ - 1) + κ - C / (ρ - 1) < c₀ * Real.log (x ^ 4) + κ - C / x ^ 4 := by
    linarith
  have hmain := exitsAvoiding_le_affine (m := x ^ 4) (ρ := ρ)
    (lo := c₀ * Real.log (ρ - 1) + κ - C / (ρ - 1)) (hi := c₀ * Real.log (x ^ 4) + κ - C / x ^ 4)
    (by linarith) hlohi
    (fun z hz _ => le_potentialKernel hc₀ hC hpk hρ'pos hρ'R hz.le)
    (fun z hz _ => le_potentialKernel hc₀ hC hpk hmpos (by linarith) hz) hyρ (by linarith)
  refine hmain.trans ?_
  have hnum : potentialKernel y - (c₀ * Real.log (ρ - 1) + κ - C / (ρ - 1)) ≤
      c₀ * (Real.log 5 + Real.log 2) + 4 * C := by
    have h1 := potentialKernel_le hc₀ hC hpk hρ'pos hρ'R (z := y) (by linarith) hy.le
    have h2 : Real.log (x / 2) ≤ Real.log (ρ - 1) := Real.log_le_log (by positivity) hρ'1
    have h3 : Real.log (x / 2) = Real.log x - Real.log 2 := Real.log_div hx0.ne' two_ne_zero
    have h4 : Real.log (5 * x) = Real.log 5 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
    have h5 : C / (ρ - 1) ≤ 2 * C := by
      calc C / (ρ - 1) ≤ C / (1 / 2) :=
            div_le_div_of_nonneg_left hC (by norm_num) (by linarith)
        _ = 2 * C := by ring
    have h6 := mul_le_mul_of_nonneg_left h2 hc₀.le
    nlinarith
  calc (potentialKernel y - (c₀ * Real.log (ρ - 1) + κ - C / (ρ - 1))) /
        ((c₀ * Real.log (x ^ 4) + κ - C / x ^ 4) - (c₀ * Real.log (ρ - 1) + κ - C / (ρ - 1)))
      ≤ (c₀ * (Real.log 5 + Real.log 2) + 4 * C) /
        ((c₀ * Real.log (x ^ 4) + κ - C / x ^ 4) - (c₀ * Real.log (ρ - 1) + κ - C / (ρ - 1))) :=
        div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ (c₀ * (Real.log 5 + Real.log 2) + 4 * C) / (2 * c₀ * Real.log x) :=
        div_le_div_of_nonneg_left hK₁.le hDpos hD2
    _ = (c₀ * (Real.log 5 + Real.log 2) + 4 * C) / (2 * c₀) / Real.log x := by
        rw [div_div]

/-- The probability of reaching radius `n⁴` before entering the closed disk of radius `2n`,
from a start at distance between `3n` and `4n`, is at least of order `1 / log n`. -/
private theorem exitsAvoiding_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ y : Site 2, 3 * n ≤ euclidNorm y →
      euclidNorm y < 4 * n →
        c / Real.log n ≤ prob (exitsAvoiding ((n : ℝ) ^ 4) {z | euclidNorm z ≤ 2 * n} y) := by
  obtain ⟨c₀, κ, C, R, hc₀, hC, hR, hpk⟩ := potentialKernel_approx
  have hlog32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = c₀ * Real.log (3 / 2) := ⟨_, rfl⟩
  have hνpos : 0 < ν := hν ▸ mul_pos hc₀ hlog32
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * R + 3 + 4 * C / ν)
  refine ⟨ν / (2 * (5 * c₀ + C)), by positivity, N, fun n hn y hy3 hy4 => ?_⟩
  have hxN : 2 * R + 3 + 4 * C / ν ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = n := ⟨_, rfl⟩
  rw [← hx] at hxN hy3 hy4 ⊢
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC4 : 0 ≤ 4 * C / ν := by positivity
  have hx5 : 5 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hlogpos : 0 < Real.log x := by linarith
  have hlog2x : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos (by linarith)
  have hCx : C / x ≤ ν / 4 := by
    have h1 : 4 * C / ν ≤ x := by linarith
    rw [div_le_iff₀ hνpos] at h1
    rw [div_le_iff₀ hx0]
    linarith
  have hx3 : (5 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx5 3
  have hm : 5 * x < x ^ 4 := by
    have h125 : (125 : ℝ) ≤ x ^ 3 := by norm_num at hx3; exact hx3
    have h1 : 125 * x ≤ x ^ 3 * x := mul_le_mul_of_nonneg_right h125 hx0.le
    have h2 : x ^ 4 = x ^ 3 * x := by ring
    linarith
  have hx41 : (1 : ℝ) ≤ x ^ 4 := one_le_pow₀ (by linarith)
  have hmpos : 0 < x ^ 4 := by positivity
  have hρ'pos : 0 < 2 * x - 1 := by linarith
  have hρ'R : R ≤ 2 * x - 1 := by linarith
  have hRm : R ≤ x ^ 4 := by linarith
  have hCρ : C / (2 * x - 1) ≤ C / x := div_le_div_of_nonneg_left hC hx0 (by linarith)
  have hlog3 : Real.log (3 * x) = Real.log (2 * x) + Real.log (3 / 2) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    ring
  have hlog4 : Real.log (2 * x) + Real.log (3 / 2) ≤ Real.log (x ^ 4 + 1) := by
    rw [← hlog3]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlo2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hlohi : c₀ * Real.log (2 * x) + κ + C / (2 * x - 1) <
      c₀ * Real.log (x ^ 4 + 1) + κ + C / x ^ 4 := by
    have h1 : 0 ≤ C / x ^ 4 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hlog4 hc₀.le
    linarith
  have hmain := affine_le_exitsAvoiding (m := x ^ 4) (ρ := 2 * x)
    (lo := c₀ * Real.log (2 * x) + κ + C / (2 * x - 1))
    (hi := c₀ * Real.log (x ^ 4 + 1) + κ + C / x ^ 4) (by linarith) hlohi
    (fun z hz1 hz2 => potentialKernel_le hc₀ hC hpk hρ'pos hρ'R (r := 2 * x - 1) (s := 2 * x)
      (by linarith) hz2)
    (fun z hz1 hz2 => potentialKernel_le hc₀ hC hpk hmpos hRm (r := x ^ 4) (s := x ^ 4 + 1)
      hz1 hz2.le)
    (y := y) (by linarith) (by linarith)
  refine le_trans ?_ hmain
  have hnum : ν / 2 ≤ potentialKernel y - (c₀ * Real.log (2 * x) + κ + C / (2 * x - 1)) := by
    have h1 := le_potentialKernel hc₀ hC hpk (r := 3 * x) (by linarith) (by linarith) hy3
    have h2 : C / (3 * x) ≤ C / x := div_le_div_of_nonneg_left hC hx0 (by linarith)
    rw [hlog3] at h1
    linarith
  have hDpos : 0 < (c₀ * Real.log (x ^ 4 + 1) + κ + C / x ^ 4) -
      (c₀ * Real.log (2 * x) + κ + C / (2 * x - 1)) := by
    have h1 : 0 ≤ C / x ^ 4 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hlog4 hc₀.le
    linarith
  have hDle : (c₀ * Real.log (x ^ 4 + 1) + κ + C / x ^ 4) -
      (c₀ * Real.log (2 * x) + κ + C / (2 * x - 1)) ≤ (5 * c₀ + C) * Real.log x := by
    have h1 : Real.log (x ^ 4 + 1) ≤ Real.log 2 + 4 * Real.log x := by
      have : Real.log (2 * x ^ 4) = Real.log 2 + 4 * Real.log x := by
        rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow]
        norm_num
      rw [← this]
      exact Real.log_le_log (by positivity) (by linarith)
    have h2 : C / x ^ 4 ≤ C := div_le_self hC hx41
    have h3 : 0 ≤ C / (2 * x - 1) := by positivity
    have h4 := mul_le_mul_of_nonneg_left h1 hc₀.le
    have h5 : 0 ≤ c₀ * Real.log (2 * x) := by positivity
    have h6 : C ≤ C * Real.log x := le_mul_of_one_le_right hC hlogx
    have h7 := mul_le_mul_of_nonneg_left hlog2x hc₀.le
    linarith
  calc ν / (2 * (5 * c₀ + C)) / Real.log x = ν / 2 / ((5 * c₀ + C) * Real.log x) := by
        rw [div_div, div_div]
        congr 1
        ring
    _ ≤ ν / 2 / ((c₀ * Real.log (x ^ 4 + 1) + κ + C / x ^ 4) -
        (c₀ * Real.log (2 * x) + κ + C / (2 * x - 1))) :=
        div_le_div_of_nonneg_left (by positivity) hDpos hDle
    _ ≤ _ := div_le_div_of_nonneg_right hnum hDpos.le

private theorem farBefore_eq (n : ℕ) (w : Site 2) :
    farBefore n w = exitsAvoiding ((n : ℝ) ^ 4) {z | euclidNorm z ≤ 2 * n} w := by
  ext ω
  simp only [farBefore, exitsAvoiding, Set.mem_setOf_eq, not_le]

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

end Aux

/-- **Lawler and Limic (2004), Lemma 13 (i).** For the simple random walk on `ℤ²`, started at
distance between `3n` and `4n` from the origin, the probability of reaching the circle of
radius `n⁴` before entering the closed disk of radius `2n` is of order `1 / log n`. -/
theorem farBefore_bounds : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ w : Site 2,
    3 * n ≤ euclidNorm w → euclidNorm w < 4 * n →
    c₁ / Real.log n ≤ prob (farBefore n w) ∧ prob (farBefore n w) ≤ c₂ / Real.log n := by
  obtain ⟨c₁, hc₁, N₁, h₁⟩ := exitsAvoiding_lower
  obtain ⟨K, hK, N₂, h₂⟩ := exitsAvoiding_upper
  refine ⟨c₁, K, hc₁, hK, max N₁ N₂, fun n hn w hw3 hw4 => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  rw [farBefore_eq]
  exact ⟨h₁ n (le_trans (le_max_left _ _) hn) w hw3 hw4,
    h₂ n (le_trans (le_max_right _ _) hn) (2 * n) (by linarith) le_rfl w (by linarith)⟩

/-- **Lawler and Limic (2004), equation (29).** The probability of reaching the circle of
radius `n⁴` before entering the open disk of radius `n`, from a start at distance less than
`4n`, is at most of order `1 / log n`. -/
theorem far_before_radius : ∃ c : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : Site 2,
    euclidNorm z < 4 * n →
    prob {ω | ∃ t, (n:ℝ)^4 ≤ euclidNorm (walkPos z ω t) ∧ ∀ s ≤ t, n ≤ euclidNorm (walkPos z ω s)}
      ≤ c / Real.log n := by
  obtain ⟨K, hK, N, h⟩ := exitsAvoiding_upper
  refine ⟨K, N, fun n hn z hz => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  refine le_trans (prob_mono ?_) (h n hn ((n : ℝ) - 1 / 2) le_rfl (by linarith) z (by linarith))
  rintro ω ⟨t, ht, hs⟩
  refine ⟨t, ht, fun s hst hB => ?_⟩
  have h1 := hs s hst
  have h2 : euclidNorm (walkPos z ω s) ≤ (n : ℝ) - 1 / 2 := hB
  linarith

/-- **Lawler and Limic (2004), Lemma 13 (ii).** Uniformly over the dense sets `A`, the
probability of reaching the circle of radius `n⁴` before visiting `A` in the annulus
`n / 2 ≤ |z| < n` is at most of order `1 / log n`, for every start at distance less than `4n`. -/
theorem exitsBefore_shellPart_far : ∃ c : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Set (Site 2),
    IsDense A → ∀ w : Site 2, euclidNorm w < 4 * n →
    prob (exitsBefore ((n : ℝ) ^ 4) (shellPart A (n / 2) n) w) ≤ c / Real.log n := by
  classical
  obtain ⟨cs, hcs, N₁, hhit⟩ := hit_shellPart_lower
  obtain ⟨K, hK, N₂, hup⟩ := exitsAvoiding_upper
  refine ⟨K / cs, max (max N₁ N₂) 5, fun n hn A hA w hw => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  have hhit' : ∀ y : Site 2, euclidNorm y < 3 * n / 2 →
      cs ≤ prob (hitsBefore (shellPart A (n / 2) n) (2 * n) y) := by
    intro y hy
    have e1 : ((2 * n : ℕ) : ℝ) / 4 = (n : ℝ) / 2 := by push_cast; ring
    have e2 : ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) := by push_cast; ring
    have e3 : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    have h := hhit (2 * n) (by omega) A hA y (by rw [e3]; linarith)
    rw [e1, e2, e3] at h
    exact h
  generalize hB : shellPart A (n / 2) n = B at hhit' ⊢
  have hBsub : ∀ z, z ∈ B → euclidNorm z < n := fun z hz => by rw [← hB] at hz; exact hz.2.2
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (n : ℝ) ^ 4 := ⟨_, rfl⟩
  rw [← hm]
  have hm5 : 5 * (n : ℝ) < m := by
    have hx3 : (5 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hn5 3
    have h125 : (125 : ℝ) ≤ (n : ℝ) ^ 3 := by norm_num at hx3; exact hx3
    have h1 : 125 * (n : ℝ) ≤ (n : ℝ) ^ 3 * n := mul_le_mul_of_nonneg_right h125 (by linarith)
    have h2 : (n : ℝ) ^ 4 = (n : ℝ) ^ 3 * n := by ring
    linarith
  -- reaching radius `m` or `2n` without a visit to `B`, and reaching radius `m` without entering
  -- the disk of radius `n`
  obtain ⟨e, he⟩ : ∃ e : Site 2 → ℝ, ∀ y, e y = prob (exitsAvoiding m B y) := ⟨_, fun _ => rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : Site 2 → ℝ, ∀ y, k y = prob (exitsAvoiding (2 * n) B y) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Site 2 → ℝ,
      ∀ y, r y = prob (exitsAvoiding m {z | euclidNorm z < n} y) := ⟨_, fun _ => rfl⟩
  have he0 : ∀ y, 0 ≤ e y := fun y => (he y).symm ▸ prob_nonneg _
  have hk0 : ∀ y, 0 ≤ k y := fun y => (hk y).symm ▸ prob_nonneg _
  have hr0 : ∀ y, 0 ≤ r y := fun y => (hr y).symm ▸ prob_nonneg _
  have heB : ∀ y, y ∈ B → e y = 0 := fun y hy => by
    rw [he, exitsAvoiding_eq_empty hy, prob_empty]
  have hkB : ∀ y, y ∈ B → k y = 0 := fun y hy => by
    rw [hk, exitsAvoiding_eq_empty hy, prob_empty]
  have heM : ∀ y, y ∉ B → m ≤ euclidNorm y → e y = 1 := fun y hy hm' => by
    rw [he, exitsAvoiding_eq_univ hy hm', prob_univ]
  have hkM : ∀ y, y ∉ B → 2 * (n : ℝ) ≤ euclidNorm y → k y = 1 := fun y hy hm' => by
    rw [hk, exitsAvoiding_eq_univ hy hm', prob_univ]
  have heS : ∀ y, y ∉ B → euclidNorm y < m → e y = (∑ a : Dir 2, e (y + dirVec a)) / 4 :=
    fun y hy hym => by
      simp only [he]
      exact prob_exitsAvoiding_step hy hym
  have hkS : ∀ y, y ∉ B → euclidNorm y < 2 * n → k y = (∑ a : Dir 2, k (y + dirVec a)) / 4 :=
    fun y hy hym => by
      simp only [hk]
      exact prob_exitsAvoiding_step hy hym
  have hrS : ∀ y, (n : ℝ) ≤ euclidNorm y → euclidNorm y < m →
      r y = (∑ a : Dir 2, r (y + dirVec a)) / 4 := fun y hy1 hym => by
    simp only [hr]
    exact prob_exitsAvoiding_step (by simpa using hy1) hym
  have hrM : ∀ y, m ≤ euclidNorm y → r y = 1 := fun y hy => by
    rw [hr, exitsAvoiding_eq_univ (by simp only [Set.mem_setOf_eq, not_lt]; linarith) hy,
      prob_univ]
  -- leaving the disk of radius `2n` before visiting `B` has probability at most `1 - cs`
  have hkle : ∀ y : Site 2, euclidNorm y < 3 * n / 2 → k y ≤ 1 - cs := fun y hy => by
    have h1 := prob_exitsAvoiding_add_hitsBefore_le (2 * (n : ℝ)) B y
    have h2 := hhit' y hy
    rw [hk]
    linarith
  -- the maximum of `e` over the disk of radius `4n + 1`
  obtain ⟨z₀, hz₀, hmax⟩ := Finset.exists_max_image (diskFinset (4 * (n : ℝ) + 1)) e
    ⟨0, by rw [mem_diskFinset_iff', euclidNorm_zero]; linarith⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = e z₀ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := hq ▸ he0 z₀
  have hemax : ∀ y : Site 2, euclidNorm y < 4 * n + 1 → e y ≤ q := fun y hy =>
    hq ▸ hmax y (mem_diskFinset_iff'.2 hy)
  -- from a start in the disk of radius `2n`, `e` is at most `q` times `k`
  have hF4 : ∀ y : Site 2, euclidNorm y < 2 * n → e y ≤ q * k y := by
    intro y hy
    by_cases hyB : y ∈ B
    · rw [heB y hyB, hkB y hyB]
      simp
    · have key := le_of_neighbour_mean
        ((diskFinset (2 * (n : ℝ))).filter fun z => z ∉ B) (fun z => e z - q * k z) 0 ?_ ?_ y
        (Finset.mem_filter.2 ⟨mem_diskFinset_iff'.2 hy, hyB⟩)
      · linarith
      · intro z hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
        have hz1' := mem_diskFinset_iff'.1 hz1
        have h1 := heS z hz2 (by linarith)
        have h2 := hkS z hz2 hz1'
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2]
        ring
      · intro z hz a hza
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
        have hz1' := mem_diskFinset_iff'.1 hz1
        have hnorm := euclidNorm_add_dirVec_le z a
        by_cases hwB : z + dirVec a ∈ B
        · simp only [heB _ hwB, hkB _ hwB]
          simp
        · have hw2n : 2 * (n : ℝ) ≤ euclidNorm (z + dirVec a) := by
            by_contra hlt
            exact hza (Finset.mem_filter.2 ⟨mem_diskFinset_iff'.2 (not_le.1 hlt), hwB⟩)
          simp only [hkM _ hwB hw2n]
          have := hemax (z + dirVec a) (by linarith)
          linarith
  have hF5 : ∀ y : Site 2, euclidNorm y < n → e y ≤ q * (1 - cs) := fun y hy =>
    (hF4 y (by linarith)).trans (mul_le_mul_of_nonneg_left (hkle y (by linarith)) hq0)
  have hM0 : 0 ≤ q * (1 - cs) := (he0 0).trans (hF5 0 (by rw [euclidNorm_zero]; linarith))
  -- outside the disk of radius `n`, `e` is at most `r` plus the bound inside the disk
  have hF6 : ∀ y : Site 2, euclidNorm y < m → e y ≤ r y + q * (1 - cs) := by
    intro y hy
    by_cases hyn : euclidNorm y < n
    · have := hF5 y hyn
      linarith [hr0 y]
    · rw [not_lt] at hyn
      have key := le_of_neighbour_mean ((diskFinset m).filter fun z => (n : ℝ) ≤ euclidNorm z)
        (fun z => e z - r z) (q * (1 - cs)) ?_ ?_ y
        (Finset.mem_filter.2 ⟨mem_diskFinset_iff'.2 hy, hyn⟩)
      · linarith
      · intro z hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
        have hz1' := mem_diskFinset_iff'.1 hz1
        have hzB : z ∉ B := fun h => absurd (hBsub z h) (not_lt.2 hz2)
        have h1 := heS z hzB hz1'
        have h2 := hrS z hz2 hz1'
        rw [Finset.sum_sub_distrib]
        linarith
      · intro z hz a hza
        by_cases hwn : euclidNorm (z + dirVec a) < n
        · have := hF5 _ hwn
          linarith [hr0 (z + dirVec a)]
        · have hwm : m ≤ euclidNorm (z + dirVec a) := by
            by_contra hlt
            exact hza (Finset.mem_filter.2 ⟨mem_diskFinset_iff'.2 (not_le.1 hlt), not_lt.1 hwn⟩)
          have hwB : z + dirVec a ∉ B := fun h => absurd (hBsub _ h) (by linarith)
          rw [heM _ hwB hwm, hrM _ hwm]
          linarith
  -- reaching radius `m` before entering the disk of radius `n` is of order `1 / log n`
  have hF7 : ∀ y : Site 2, euclidNorm y < 4 * n + 1 → r y ≤ K / Real.log n := by
    intro y hy
    have h := hup n hn2 ((n : ℝ) - 1 / 2) le_rfl (by linarith) y (by linarith)
    rw [← hm] at h
    rw [hr]
    refine le_trans (prob_mono (exitsAvoiding_anti (B := {z | euclidNorm z ≤ (n : ℝ) - 1 / 2})
      (B' := {z | euclidNorm z < n}) (fun z hz => ?_) _ _)) h
    simp only [Set.mem_setOf_eq] at hz ⊢
    linarith
  have hz₀m : euclidNorm z₀ < m := by
    have := mem_diskFinset_iff'.1 hz₀
    linarith
  have hq1 : q ≤ K / Real.log n + q * (1 - cs) := by
    have h1 := hF6 z₀ hz₀m
    have h2 := hF7 z₀ (mem_diskFinset_iff'.1 hz₀)
    rw [← hq] at h1
    linarith
  have hq2 : q ≤ K / cs / Real.log n := by
    rw [div_right_comm, le_div_iff₀ hcs]
    linarith
  have hcard : (Finset.univ : Finset (Dir 2)).card = 4 := by simp
  rw [prob_exitsBefore_step (by linarith)]
  refine le_trans ?_ hq2
  calc (∑ a : Dir 2, prob (exitsAvoiding m B (w + dirVec a))) / 4 ≤ (∑ _a : Dir 2, q) / 4 := by
        refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => ?_) (by norm_num)
        rw [← he]
        exact hemax _ (by have := euclidNorm_add_dirVec_le w a; linarith)
    _ = q := by
        rw [Finset.sum_const, hcard]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]
        ring

end FiniteAvalanches.Walk.Beurling
