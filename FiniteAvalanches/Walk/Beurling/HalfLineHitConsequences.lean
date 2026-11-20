/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/HalfLineHitConsequences.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added;
`Set.mem_ofPred_eq` replaced by `Set.mem_setOf_eq` (4 times); `measurableSet_setOfPred` replaced by
`measurableSet_setOf` (2 times); `private` removed from `hitAtTime`, `prob_hit_then` and
`prob_entersAt_axis_start_le`.
-/
import FiniteAvalanches.Walk.Beurling.HalfLineHit
import FiniteAvalanches.Walk.Beurling.HalfLineHitPoint

/-!
# Entering the half-axis far from the origin and leaving a disk before a half-axis

Lawler and Limic (2004), Proposition 12 (c) and (d), for the simple random walk on `ℤ²`.

* (c) The walk started at `(n, 0)` makes its first positive-time visit to the nonnegative
  half-axis `{(j, 0) : j ≥ 0}` at the origin with probability `O(n^(-3/2))`.
* (d) The walk started at the origin leaves the disk of radius `n` before its first positive-time
  visit to `{(i, 0) : i ≥ j}` with probability `O(√(j / n))`.

G. F. Lawler and V. Limic, *The Beurling estimate for a class of random walks*, Electron. J.
Probab. 9 (2004), Proposition 12.

## Main declarations

* `exitsBefore_halfLine_le`: Proposition 12 (d).
* `entersAt_halfLine_far_le`: Proposition 12 (c).

## Proof of (d)

The events `{τ_n < T_{{i ≥ l}}}` increase with `l`. The increase from `l` to `l + 1` is contained
in the event that the first positive-time visit to `{i ≥ l}` is at `l`, followed by an exit of the
disk of radius `n / 2` before the first positive-time visit to the positive half-axis. By the
Markov property at the first visit its probability is the product of the entrance estimate at the
end of a half-axis (Proposition 12 (b), after a translation), which is `O(1 / √l)`, and the exit
estimate (Proposition 12 (a)), which is `O(1 / √n)`. Summing over `l < j ≤ n / 4` gives
`O(√(j / n))`.

## Proof of (c)

A step along the axis from `(n, 0)` reaches the nonnegative half-axis away from the origin, so only
the two vertical first steps matter. From height one at horizontal distance `n + k` from the axis
point `-k`, the half-plane Green function is `O((n + k)^(-2))` (the asymptotics of the potential
kernel with error `O(|x|^(-2))`), so the walk makes its first visit to the real axis at `-k` with
probability `O((n + k)^(-2))`. A first visit at a nonnegative point other than the origin ends the
event; a first visit at `-k` is followed by the entrance estimate of Proposition 12 (b), which is
`O(1 / √k)`, by the Markov property at the first visit. The resulting series is `O(n^(-3/2))`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

private theorem prob_nonneg' (E : Set (ℕ → Dir 2)) : 0 ≤ prob E := ENNReal.toReal_nonneg

private theorem prob_mono' {E F : Set (ℕ → Dir 2)} (h : E ⊆ F) : prob E ≤ prob F :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h)

private theorem prob_le_one' (E : Set (ℕ → Dir 2)) : prob E ≤ 1 := by
  have h : pathLaw 2 E ≤ 1 := prob_le_one
  simpa [prob] using ENNReal.toReal_mono ENNReal.one_ne_top h

private theorem prob_union_le' (E F : Set (ℕ → Dir 2)) : prob (E ∪ F) ≤ prob E + prob F := by
  unfold prob
  rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
    (measure_union_le _ _)

/-! ### Restarting the walk -/

/-- The walk from `x` is the walk from `0` translated by `x`. -/
private theorem walkPos_eq_add (x : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos x ω t = x + walkPos 0 ω t := by
  simp [walkPos]

/-- The walk at time `j + t` is the walk driven by the increments after time `j`, started at its
position at time `j`. -/
private theorem walkPos_add_shiftBy (x : Site 2) (ω : ℕ → Dir 2) (j t : ℕ) :
    walkPos x ω (j + t) = walkPos (walkPos x ω j) (shiftBy j ω) t := by
  simp only [walkPos, shiftBy, Finset.sum_range_add, add_assoc]

/-- The first `j` positions of the walk are determined by the first `j` increments. -/
private theorem walkPos_congr_of_lt (x : Site 2) {ω ω' : ℕ → Dir 2} {j : ℕ}
    (h : ∀ i < j, ω i = ω' i) {t : ℕ} (ht : t ≤ j) : walkPos x ω t = walkPos x ω' t := by
  unfold walkPos
  congr 1
  exact Finset.sum_congr rfl fun i hi => by rw [h i (by have := Finset.mem_range.mp hi; omega)]

private theorem euclidNorm_add_le'' (y z : Site 2) :
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

private theorem euclidNorm_axisPt_nat (l : ℕ) : euclidNorm (axisPt (l : ℤ)) = l := by
  simp [euclidNorm, axisPt, Fin.sum_univ_two]

/-! ### The first visit to a set at a prescribed point -/

/-- The walk from `x` is at `w` at the positive time `t`, with no visit to `B` at the times
`1, …, t - 1`. -/
def hitAtTime (B : Set (Site 2)) (x w : Site 2) (t : ℕ) : Set (ℕ → Dir 2) :=
  {ω | 1 ≤ t ∧ walkPos x ω t = w ∧ ∀ s, 1 ≤ s → s < t → walkPos x ω s ∉ B}

private theorem dependsOnFirst_hitAtTime (B : Set (Site 2)) (x w : Site 2) (t : ℕ) :
    DependsOnFirst t (hitAtTime B x w t) := by
  have key : ∀ ω ω' : ℕ → Dir 2, (∀ i < t, ω i = ω' i) →
      ω ∈ hitAtTime B x w t → ω' ∈ hitAtTime B x w t := by
    intro ω ω' h ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, fun s hs1 hs2 => ?_⟩
    · rw [← walkPos_congr_of_lt x h le_rfl]
      exact h2
    · rw [← walkPos_congr_of_lt x h hs2.le]
      exact h3 s hs1 hs2
  intro ω ω' h
  exact ⟨key ω ω' h, key ω' ω fun i hi => (h i hi).symm⟩

private theorem disjoint_hitAtTime {B : Set (Site 2)} {x w : Site 2} (hw : w ∈ B) {t t' : ℕ}
    (h : t ≠ t') : Disjoint (hitAtTime B x w t) (hitAtTime B x w t') := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact h2.2.2 t h1.1 hlt (by rw [h1.2.1]; exact hw)
  · exact h1.2.2 t' h2.1 hlt (by rw [h2.2.1]; exact hw)

private theorem iUnion_hitAtTime (B : Set (Site 2)) (x w : Site 2) :
    ⋃ t, hitAtTime B x w t = entersAt B w x := by
  ext ω
  simp only [Set.mem_iUnion, hitAtTime, entersAt, Set.mem_setOf_eq]

/-- **The Markov property at the first visit to a set.**  If the walk first visits `B` at `w`
and then continues with an event `C`, the probability is the product of the two probabilities. -/
theorem prob_hit_then {B : Set (Site 2)} {x w : Site 2} (hw : w ∈ B) {C : Set (ℕ → Dir 2)}
    (hC : MeasurableSet C) :
    prob {ω | ∃ t, ω ∈ hitAtTime B x w t ∧ shiftBy t ω ∈ C} =
      prob (entersAt B w x) * prob C := by
  have hmeas : ∀ t, MeasurableSet (hitAtTime B x w t) := fun t =>
    (dependsOnFirst_hitAtTime B x w t).measurableSet
  have hset : {ω | ∃ t, ω ∈ hitAtTime B x w t ∧ shiftBy t ω ∈ C} =
      ⋃ t, (hitAtTime B x w t ∩ shiftBy t ⁻¹' C) := by
    ext ω
    simp
  have hdisj : Pairwise (Function.onFun Disjoint fun t => hitAtTime B x w t ∩ shiftBy t ⁻¹' C) :=
    fun t t' h => (disjoint_hitAtTime hw h).mono Set.inter_subset_left Set.inter_subset_left
  have h1 : pathLaw 2 {ω | ∃ t, ω ∈ hitAtTime B x w t ∧ shiftBy t ω ∈ C} =
      pathLaw 2 (entersAt B w x) * pathLaw 2 C := by
    rw [hset, measure_iUnion hdisj fun t => (hmeas t).inter (measurable_shiftBy t hC)]
    simp_rw [markov_split (dependsOnFirst_hitAtTime B x w _) hC]
    rw [ENNReal.tsum_mul_right, ← iUnion_hitAtTime, measure_iUnion
      (fun t t' h => disjoint_hitAtTime hw h) hmeas]
  unfold prob
  rw [h1, ENNReal.toReal_mul]


/-! ### Proposition 12 (d) -/

/-- The nonnegative integers at least `l`, on the real axis. -/
private def halfAxisFrom (l : ℕ) : Set (Site 2) := axisSet {i : ℤ | (l : ℤ) ≤ i}

private theorem axisPt_mem_halfAxisFrom (l : ℕ) : axisPt (l : ℤ) ∈ halfAxisFrom l := by
  simp [halfAxisFrom, axisSet, axisPt]

private theorem halfAxisFrom_one : halfAxisFrom 1 = axisSet {i : ℤ | 0 < i} := by
  ext z
  simp only [halfAxisFrom, axisSet, Set.mem_setOf_eq, Nat.cast_one]
  omega

private theorem measurableSet_exitsWeakBefore' (r : ℝ) (B : Set (Site 2)) (x : Site 2) :
    MeasurableSet (exitsWeakBefore r B x) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    (measurable_walkPos_pred x (fun z => r ≤ euclidNorm z) t).and <| Measurable.forall fun s =>
      measurable_walkPos_pred x (fun z => 1 ≤ s → s < t → z ∉ B) s

private theorem exitsBefore_subset_exitsWeakBefore (r : ℝ) (B : Set (Site 2)) (x : Site 2) :
    exitsBefore r B x ⊆ exitsWeakBefore r B x :=
  fun _ ⟨t, h1, h2⟩ => ⟨t, h1, fun s hs1 hs2 => h2 s hs1 hs2.le⟩

/-- Entering the half-axis `{i ≥ l}` at `l` from the origin is the translate of entering the
nonnegative half-axis at the origin from `-l`. -/
private theorem entersAt_halfAxisFrom (l : ℕ) :
    entersAt (halfAxisFrom l) (axisPt (l : ℤ)) 0 =
      entersAt (axisSet {j : ℤ | 0 ≤ j}) 0 (axisPt (-(l : ℤ))) := by
  have h0 : ∀ p : Site 2, axisPt (-(l : ℤ)) + p = 0 ↔ p = axisPt (l : ℤ) := by
    intro p
    constructor
    · intro h
      ext i
      fin_cases i
      · have := congrFun h 0
        simp [axisPt] at this ⊢
        omega
      · have := congrFun h 1
        simp [axisPt] at this ⊢
        omega
    · rintro rfl
      ext i
      fin_cases i <;> simp [axisPt]
  have hm : ∀ p : Site 2, axisPt (-(l : ℤ)) + p ∈ axisSet {j : ℤ | 0 ≤ j} ↔
      p ∈ halfAxisFrom l := by
    intro p
    simp only [halfAxisFrom, axisSet, Set.mem_setOf_eq, Pi.add_apply, axisPt]
    simp
  ext ω
  simp only [entersAt, Set.mem_setOf_eq, walkPos_eq_add (axisPt (-(l : ℤ))), h0, hm]

/-- A visit to `l` before the half-axis `{i ≥ l + 1}`, preceded by no visit to `{i ≥ l}` and
followed by an exit of the disk, restarts the walk at `l`. -/
private theorem diff_subset_restart {n l m : ℕ} (hml : m + l ≤ n) :
    exitsBefore n (halfAxisFrom (l + 1)) 0 \ exitsBefore n (halfAxisFrom l) 0 ⊆
      {ω | ∃ t, ω ∈ hitAtTime (halfAxisFrom l) 0 (axisPt (l : ℤ)) t ∧
        shiftBy t ω ∈ exitsWeakBefore m (axisSet {i : ℤ | 0 < i}) 0} := by
  classical
  rintro ω ⟨⟨t, ht1, ht2⟩, h2⟩
  have hex : ∃ s, 1 ≤ s ∧ walkPos 0 ω s ∈ halfAxisFrom l ∧ s ≤ t := by
    by_contra hcon
    push Not at hcon
    exact h2 ⟨t, ht1, fun s hs1 hs2 hmem => absurd (hcon s hs1 hmem) (by omega)⟩
  have hu : 1 ≤ Nat.find hex ∧ walkPos 0 ω (Nat.find hex) ∈ halfAxisFrom l ∧
      Nat.find hex ≤ t := Nat.find_spec hex
  obtain ⟨u, hu_def⟩ : ∃ u, u = Nat.find hex := ⟨_, rfl⟩
  rw [← hu_def] at hu
  have hmin : ∀ s, s < u → ¬ (1 ≤ s ∧ walkPos 0 ω s ∈ halfAxisFrom l ∧ s ≤ t) := fun s hs => by
    rw [hu_def] at hs
    exact Nat.find_min hex hs
  have hnot : walkPos 0 ω u ∉ halfAxisFrom (l + 1) := ht2 u hu.1 hu.2.2
  have hpt : walkPos 0 ω u = axisPt (l : ℤ) := by
    obtain ⟨h1, h2'⟩ := hu.2.1
    have h3 : ¬ (((l + 1 : ℕ) : ℤ) ≤ walkPos 0 ω u 0) := fun h => hnot ⟨h1, h⟩
    have h2'' : (l : ℤ) ≤ walkPos 0 ω u 0 := h2'
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, axisPt, Matrix.cons_val_zero]
      omega
    · simpa [axisPt] using h1
  have hkey : ∀ s, walkPos 0 ω (u + s) = axisPt (l : ℤ) + walkPos 0 (shiftBy u ω) s := by
    intro s
    rw [walkPos_add_shiftBy, hpt, walkPos_eq_add]
  refine ⟨u, ⟨hu.1, hpt, fun s hs1 hs2 hmem => hmin s hs2 ⟨hs1, hmem, by omega⟩⟩, t - u, ?_, ?_⟩
  · have e := hkey (t - u)
    rw [Nat.add_sub_cancel' hu.2.2] at e
    have h1 : euclidNorm (walkPos 0 ω t) ≤ (l : ℝ) +
        euclidNorm (walkPos 0 (shiftBy u ω) (t - u)) := by
      rw [e, ← euclidNorm_axisPt_nat l]
      exact euclidNorm_add_le'' _ _
    have h2 : ((m : ℕ) : ℝ) + l ≤ n := by exact_mod_cast hml
    linarith
  · intro s hs1 hs2 hmem
    refine ht2 (u + s) (by omega) (by omega) ?_
    rw [hkey s]
    obtain ⟨hm1, hm2⟩ := hmem
    refine ⟨by simpa [axisPt] using hm1, ?_⟩
    show (((l + 1 : ℕ) : ℤ)) ≤ (axisPt (l : ℤ) + walkPos 0 (shiftBy u ω) s) 0
    have : (0 : ℤ) < walkPos 0 (shiftBy u ω) s 0 := hm2
    simp only [Pi.add_apply, axisPt, Matrix.cons_val_zero]
    omega

/-- Each step of `l` in the half-axis costs at most `Cb * c`. -/
private theorem prob_diff_le {n l m : ℕ} (hml : m + l ≤ n) {Cb c : ℝ}
    (hb : prob (entersAt (axisSet {j : ℤ | 0 ≤ j}) 0 (axisPt (-(l : ℤ)))) ≤ Cb)
    (hc : prob (exitsWeakBefore m (axisSet {i : ℤ | 0 < i}) 0) ≤ c) :
    prob (exitsBefore n (halfAxisFrom (l + 1)) 0 \ exitsBefore n (halfAxisFrom l) 0) ≤ Cb * c := by
  refine (prob_mono' (diff_subset_restart hml)).trans ?_
  rw [prob_hit_then (axisPt_mem_halfAxisFrom l) (measurableSet_exitsWeakBefore' _ _ _),
    entersAt_halfAxisFrom]
  exact mul_le_mul hb hc (prob_nonneg' _) ((prob_nonneg' _).trans hb)

private theorem prob_exitsBefore_le_sum (n : ℕ) (j : ℕ) (hj : 1 ≤ j) :
    prob (exitsBefore n (halfAxisFrom j) 0) ≤ prob (exitsBefore n (halfAxisFrom 1) 0) +
      ∑ l ∈ Finset.Ico 1 j,
        prob (exitsBefore n (halfAxisFrom (l + 1)) 0 \ exitsBefore n (halfAxisFrom l) 0) := by
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [Finset.sum_Ico_succ_top hj]
    have hsub : exitsBefore n (halfAxisFrom (j + 1)) 0 ⊆ exitsBefore n (halfAxisFrom j) 0 ∪
        (exitsBefore n (halfAxisFrom (j + 1)) 0 \ exitsBefore n (halfAxisFrom j) 0) := by
      intro ω hω
      by_cases h : ω ∈ exitsBefore n (halfAxisFrom j) 0
      · exact Or.inl h
      · exact Or.inr ⟨hω, h⟩
    have := (prob_mono' hsub).trans (prob_union_le' _ _)
    linarith

private theorem sum_range_succ_inv_sqrt_le (j : ℕ) :
    ∑ l ∈ Finset.range (j + 1), 1 / Real.sqrt l ≤ 2 * Real.sqrt j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have ha : 0 < Real.sqrt ((j : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hb : Real.sqrt j ≤ Real.sqrt ((j : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hab : Real.sqrt ((j : ℝ) + 1) ^ 2 - Real.sqrt j ^ 2 = 1 := by
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      ring
    have h1 : 1 / Real.sqrt ((j : ℝ) + 1) ≤ 2 * (Real.sqrt ((j : ℝ) + 1) - Real.sqrt j) := by
      rw [div_le_iff₀ ha]
      nlinarith [sq_nonneg (Real.sqrt ((j : ℝ) + 1) - Real.sqrt j)]
    push_cast
    linarith

private theorem sum_range_inv_sqrt_le (j : ℕ) :
    ∑ l ∈ Finset.range j, 1 / Real.sqrt l ≤ 2 * Real.sqrt j := by
  rcases j with _ | j
  · simp
  · refine (sum_range_succ_inv_sqrt_le j).trans ?_
    gcongr
    linarith


/-! ### Proposition 12 (c) -/

private theorem euclidNorm_sq' (x : Site 2) :
    euclidNorm x ^ 2 = ((x 0 : ℤ) : ℝ) ^ 2 + ((x 1 : ℤ) : ℝ) ^ 2 := by
  rw [euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_two]

private theorem rpow_neg_two' {x : ℝ} (hx : 0 ≤ x) : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_two]

private theorem log_diff_le {Np Nm : ℝ} (hNm : 0 < Nm) (hle : Nm ≤ Np)
    (h : Np ^ 2 = Nm ^ 2 + 4) :
    2 / Real.pi * (Real.log Np - Real.log Nm) ≤ 2 / Nm ^ 2 := by
  have hNp : 0 < Np := hNm.trans_le hle
  have hlog : Real.log Nm ≤ Real.log Np := Real.log_le_log hNm hle
  have h2 : 2 * (Real.log Np - Real.log Nm) = Real.log (Np ^ 2 / Nm ^ 2) := by
    rw [Real.log_div (pow_pos hNp 2).ne' (pow_pos hNm 2).ne', Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h3 := Real.log_le_sub_one_of_pos
    (show 0 < Np ^ 2 / Nm ^ 2 from div_pos (pow_pos hNp 2) (pow_pos hNm 2))
  have h4 : Np ^ 2 / Nm ^ 2 - 1 = 4 / Nm ^ 2 := by
    field_simp
    linarith [h]
  rw [h4] at h3
  have hpi : 2 / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hd0 : 0 ≤ Real.log Np - Real.log Nm := sub_nonneg.2 hlog
  have h5 : Real.log Np - Real.log Nm ≤ 2 / Nm ^ 2 := by
    have : 4 / Nm ^ 2 = 2 * (2 / Nm ^ 2) := by ring
    linarith
  calc 2 / Real.pi * (Real.log Np - Real.log Nm) ≤ 1 * (Real.log Np - Real.log Nm) :=
        mul_le_mul_of_nonneg_right hpi hd0
    _ ≤ 2 / Nm ^ 2 := by linarith

private theorem kernel_diff_far {κ C₀ Np Nm Ap Am : ℝ} (hNm : 0 < Nm) (hle : Nm ≤ Np)
    (h : Np ^ 2 = Nm ^ 2 + 4)
    (hA : |Ap - (2 / Real.pi * Real.log Np + κ)| ≤ C₀ * Np ^ (-2 : ℝ))
    (hB : |Am - (2 / Real.pi * Real.log Nm + κ)| ≤ C₀ * Nm ^ (-2 : ℝ)) :
    Ap - Am ≤ (2 + 2 * max C₀ 0) / Nm ^ 2 := by
  have hNp : 0 < Np := hNm.trans_le hle
  rw [rpow_neg_two' hNp.le] at hA
  rw [rpow_neg_two' hNm.le] at hB
  have hinv : (Np ^ 2)⁻¹ ≤ (Nm ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos hNm 2) (pow_le_pow_left₀ hNm.le hle 2)
  have hC₁ : 0 ≤ max C₀ 0 := le_max_right _ _
  have hc1 : C₀ * (Np ^ 2)⁻¹ ≤ max C₀ 0 * (Nm ^ 2)⁻¹ :=
    calc C₀ * (Np ^ 2)⁻¹ ≤ max C₀ 0 * (Np ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C₀ 0 * (Nm ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hinv hC₁
  have hc2 : C₀ * (Nm ^ 2)⁻¹ ≤ max C₀ 0 * (Nm ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hd := log_diff_le hNm hle h
  have hA' := (abs_le.1 hA).2
  have hB' := (abs_le.1 hB).1
  have e : (2 + 2 * max C₀ 0) / Nm ^ 2 =
      2 / Nm ^ 2 + max C₀ 0 * (Nm ^ 2)⁻¹ + max C₀ 0 * (Nm ^ 2)⁻¹ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [e]
  linarith

/-- From height one the half-plane kernel is `O(1 / |y - w|²)`. -/
private theorem halfPlaneKernel_height_one : ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℤ) (w y : Site 2),
    (s = 1 ∨ s = -1) → w 1 = 0 → y 1 = s →
      halfPlaneKernel w s y ≤ C / euclidNorm (y - w) ^ 2 := by
  obtain ⟨κ, C₀, R₀, hR₀, hpk⟩ := exists_abs_potentialKernel_sub_log_le
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ v : Site 2, euclidNorm v ≤ R₀ + 2 →
      |potentialKernel v| ≤ M := by
    refine ⟨∑ v ∈ ballFinset 2 (R₀ + 2), |potentialKernel v|,
      Finset.sum_nonneg fun _ _ => abs_nonneg _, fun v hv => ?_⟩
    exact Finset.single_le_sum (f := fun v => |potentialKernel v|) (fun _ _ => abs_nonneg _)
      (mem_ballFinset_iff.2 hv)
  have hC₁ : 0 ≤ max C₀ 0 := le_max_right _ _
  refine ⟨max (4 + 4 * max C₀ 0) (2 * M * (R₀ + 1) ^ 2), le_max_of_le_left (by linarith), ?_⟩
  intro s w y hs hw hy
  have hs2 : ((s : ℤ) : ℝ) ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hv1 : (y - w) 1 = s := by simp [hw, hy]
  have hv0 : (((y - w) 0 : ℤ) : ℝ) = ((y 0 : ℤ) : ℝ) - ((w 0 : ℤ) : ℝ) := by simp
  set X : ℝ := ((y 0 : ℤ) : ℝ) - ((w 0 : ℤ) : ℝ) with hX
  have hR2 : euclidNorm (y - w) ^ 2 = X ^ 2 + 1 := by
    rw [euclidNorm_sq', hv1, hv0, hs2]
  have hNp2 : euclidNorm (y - (w - vUnit s)) ^ 2 = X ^ 2 + 4 := by
    rw [euclidNorm_sq']
    have a1 : (y - (w - vUnit s)) 1 = 2 * s := by
      simp only [Pi.sub_apply, vUnit_one, hw, hy]
      ring
    have a0 : (((y - (w - vUnit s)) 0 : ℤ) : ℝ) = X := by
      simp [hX, vUnit_zero]
    rw [a1, a0]
    push_cast
    rw [mul_pow, hs2]
    ring
  have hNm2 : euclidNorm (y - (w + vUnit s)) ^ 2 = X ^ 2 := by
    rw [euclidNorm_sq']
    have a1 : (y - (w + vUnit s)) 1 = 0 := by
      simp only [Pi.sub_apply, Pi.add_apply, vUnit_one, hw, hy]
      ring
    have a0 : (((y - (w + vUnit s)) 0 : ℤ) : ℝ) = X := by
      simp [hX, vUnit_zero]
    rw [a1, a0]
    simp
  have hF : halfPlaneKernel w s y =
      potentialKernel (y - (w - vUnit s)) - potentialKernel (y - (w + vUnit s)) := rfl
  have hR0 : 0 < euclidNorm (y - w) := by
    have h0 : 0 ≤ euclidNorm (y - w) := euclidNorm_nonneg _
    by_contra hneg
    have : euclidNorm (y - w) = 0 := le_antisymm (not_lt.1 hneg) h0
    rw [this] at hR2
    nlinarith [sq_nonneg X]
  have hRpos2 : 0 < euclidNorm (y - w) ^ 2 := pow_pos hR0 2
  have hNm0 : 0 ≤ euclidNorm (y - (w + vUnit s)) := euclidNorm_nonneg _
  have hNp0 : 0 ≤ euclidNorm (y - (w - vUnit s)) := euclidNorm_nonneg _
  by_cases hfar : R₀ ≤ euclidNorm (y - (w + vUnit s))
  · have hNm_pos : 0 < euclidNorm (y - (w + vUnit s)) := by linarith
    have hNp_ge : euclidNorm (y - (w + vUnit s)) ≤ euclidNorm (y - (w - vUnit s)) := by
      by_contra hlt
      push Not at hlt
      have := pow_lt_pow_left₀ hlt hNp0 two_ne_zero
      linarith
    have hkey : halfPlaneKernel w s y ≤
        (2 + 2 * max C₀ 0) / euclidNorm (y - (w + vUnit s)) ^ 2 := by
      rw [hF]
      exact kernel_diff_far hNm_pos hNp_ge (by rw [hNp2, hNm2])
        (hpk _ (hfar.trans hNp_ge)) (hpk _ hfar)
    have hNm1 : 1 ≤ euclidNorm (y - (w + vUnit s)) ^ 2 := by
      have h1 : (1 : ℝ) ≤ euclidNorm (y - (w + vUnit s)) := hR₀.trans hfar
      calc (1 : ℝ) = 1 ^ 2 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ zero_le_one h1 2
    have hRN : euclidNorm (y - w) ^ 2 ≤ 2 * euclidNorm (y - (w + vUnit s)) ^ 2 := by
      rw [hR2]
      linarith [hNm2, hNm1]
    have hle : (2 + 2 * max C₀ 0) / euclidNorm (y - (w + vUnit s)) ^ 2 ≤
        (4 + 4 * max C₀ 0) / euclidNorm (y - w) ^ 2 := by
      rw [div_le_div_iff₀ (pow_pos hNm_pos 2) hRpos2]
      have := mul_le_mul_of_nonneg_left hRN (by linarith : 0 ≤ 2 + 2 * max C₀ 0)
      linarith
    exact hkey.trans (hle.trans
      (div_le_div_of_nonneg_right (le_max_left _ _) hRpos2.le))
  · push Not at hfar
    have hNm_lt : euclidNorm (y - (w + vUnit s)) ^ 2 < R₀ ^ 2 :=
      pow_lt_pow_left₀ hfar hNm0 two_ne_zero
    have hn1 : euclidNorm (y - (w - vUnit s)) ≤ R₀ + 2 := by
      by_contra hlt
      push Not at hlt
      have h1 := pow_lt_pow_left₀ hlt (by linarith : 0 ≤ R₀ + 2) two_ne_zero
      have e : (R₀ + 2) ^ 2 = R₀ ^ 2 + 4 * R₀ + 4 := by ring
      linarith [hNp2, hNm2]
    have hn2 : euclidNorm (y - (w + vUnit s)) ≤ R₀ + 2 := by linarith
    have hnear : halfPlaneKernel w s y ≤ 2 * M := by
      have a1 := hM _ hn1
      have a2 := hM _ hn2
      rw [hF]
      linarith [le_abs_self (potentialKernel (y - (w - vUnit s))),
        neg_abs_le (potentialKernel (y - (w + vUnit s)))]
    have hRle : euclidNorm (y - w) ^ 2 ≤ (R₀ + 1) ^ 2 := by
      have e : (R₀ + 1) ^ 2 = R₀ ^ 2 + 2 * R₀ + 1 := by ring
      linarith [hR2, hNm2]
    refine hnear.trans ?_
    rw [le_div_iff₀ hRpos2]
    calc 2 * M * euclidNorm (y - w) ^ 2 ≤ 2 * M * (R₀ + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hRle (by positivity)
      _ ≤ _ := le_max_right _ _


/-- **Proposition 12 (d).** -/
theorem exitsBefore_halfLine_le :
    ∃ C : ℝ, ∀ j n : ℕ, 1 ≤ j → 1 ≤ n →
      prob (exitsBefore n (axisSet {i : ℤ | (j : ℤ) ≤ i}) 0) ≤ C * Real.sqrt ((j : ℝ) / n) := by
  obtain ⟨Cb, hCb⟩ := entersAt_halfLine_origin_le
  obtain ⟨c₁, c₂, hc₁, hc₂, N₁, hN₁⟩ := exitsWeak_halfLine_pos
  have hCb0 : 0 ≤ max Cb 0 := le_max_right _ _
  refine ⟨max (max 2 (Real.sqrt ((2 * N₁ + 2 : ℕ) : ℝ))) (c₂ + 4 * c₂ * max Cb 0),
    fun j n hj hn => ?_⟩
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 ≤ Real.sqrt ((j : ℝ) / n) := Real.sqrt_nonneg _
  by_cases h4 : n < 4 * j
  · have h14 : (1 : ℝ) / 4 ≤ (j : ℝ) / n := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      have : (n : ℝ) < 4 * j := by exact_mod_cast h4
      linarith
    have h2 : (1 : ℝ) / 2 ≤ Real.sqrt ((j : ℝ) / n) := by
      have e : (1 : ℝ) / 2 = Real.sqrt (1 / 4) := by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [e]
      exact Real.sqrt_le_sqrt h14
    calc prob (exitsBefore n (axisSet {i : ℤ | (j : ℤ) ≤ i}) 0) ≤ 1 := prob_le_one' _
      _ ≤ 2 * Real.sqrt ((j : ℝ) / n) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hsq
  · push Not at h4
    by_cases hN : n < 2 * N₁ + 2
    · have hn' : (n : ℝ) ≤ ((2 * N₁ + 2 : ℕ) : ℝ) := by exact_mod_cast hN.le
      have h1 : (1 : ℝ) ≤ ((2 * N₁ + 2 : ℕ) : ℝ) * ((j : ℝ) / n) := by
        rw [← mul_div_assoc, le_div_iff₀ (by linarith)]
        nlinarith
      have h2 : (1 : ℝ) ≤ Real.sqrt ((2 * N₁ + 2 : ℕ) : ℝ) * Real.sqrt ((j : ℝ) / n) := by
        rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Real.sqrt_one]
        exact Real.sqrt_le_sqrt h1
      calc prob (exitsBefore n (axisSet {i : ℤ | (j : ℤ) ≤ i}) 0) ≤ 1 := prob_le_one' _
        _ ≤ Real.sqrt ((2 * N₁ + 2 : ℕ) : ℝ) * Real.sqrt ((j : ℝ) / n) := h2
        _ ≤ _ := mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_left _ _)) hsq
    · push Not at hN
      have hmN : N₁ ≤ n / 2 := by omega
      have hm1 : 1 ≤ n / 2 := by omega
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
      have hsm : 0 < Real.sqrt ((n / 2 : ℕ) : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast hm1)
      have hnm : (n : ℝ) ≤ 4 * ((n / 2 : ℕ) : ℝ) := by
        have : n ≤ 4 * (n / 2) := by omega
        exact_mod_cast this
      have hsqrt : Real.sqrt n ≤ 2 * Real.sqrt ((n / 2 : ℕ) : ℝ) := by
        refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        linarith
      have hc : prob (exitsWeakBefore ((n / 2 : ℕ) : ℝ) (axisSet {i : ℤ | 0 < i}) 0) ≤
          2 * c₂ / Real.sqrt n := by
        refine (hN₁ (n / 2) hmN).2.trans ?_
        rw [div_le_div_iff₀ hsm hsn]
        nlinarith
      have hterm : ∀ l ∈ Finset.Ico 1 j,
          prob (exitsBefore n (halfAxisFrom (l + 1)) 0 \ exitsBefore n (halfAxisFrom l) 0) ≤
            (max Cb 0 / Real.sqrt l) * (2 * c₂ / Real.sqrt n) := by
        intro l hl
        obtain ⟨hl1, hlj⟩ := Finset.mem_Ico.1 hl
        refine prob_diff_le (m := n / 2) (by omega) ?_ hc
        exact (hCb l hl1).trans
          (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
      have hE1 : prob (exitsBefore n (halfAxisFrom 1) 0) ≤ c₂ / Real.sqrt n := by
        rw [halfAxisFrom_one]
        exact (prob_mono' (exitsBefore_subset_exitsWeakBefore _ _ _)).trans
          (hN₁ n (by omega)).2
      have hS : ∑ l ∈ Finset.Ico 1 j,
          prob (exitsBefore n (halfAxisFrom (l + 1)) 0 \ exitsBefore n (halfAxisFrom l) 0) ≤
          (max Cb 0 * (2 * c₂ / Real.sqrt n)) * (2 * Real.sqrt j) := by
        refine (Finset.sum_le_sum hterm).trans ?_
        have e : ∑ l ∈ Finset.Ico 1 j, (max Cb 0 / Real.sqrt l) * (2 * c₂ / Real.sqrt n) =
            (max Cb 0 * (2 * c₂ / Real.sqrt n)) * ∑ l ∈ Finset.Ico 1 j, 1 / Real.sqrt l := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (Finset.sum_le_sum_of_subset_of_nonneg
          (fun l hl => Finset.mem_range.2 (Finset.mem_Ico.1 hl).2)
          (fun _ _ _ => by positivity)).trans (sum_range_inv_sqrt_le j)
      have hsum := prob_exitsBefore_le_sum n j hj
      have hj1 : (1 : ℝ) ≤ Real.sqrt j := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hjR
      have hsqe : Real.sqrt ((j : ℝ) / n) = Real.sqrt j / Real.sqrt n :=
        Real.sqrt_div (by linarith) _
      have ht : 0 ≤ (Real.sqrt n)⁻¹ := by positivity
      have hfin : prob (exitsBefore n (halfAxisFrom j) 0) ≤
          (c₂ + 4 * c₂ * max Cb 0) * (Real.sqrt j / Real.sqrt n) := by
        have e1 : c₂ / Real.sqrt n = c₂ * (Real.sqrt n)⁻¹ := div_eq_mul_inv _ _
        have e2 : (max Cb 0 * (2 * c₂ / Real.sqrt n)) * (2 * Real.sqrt j) =
            4 * c₂ * max Cb 0 * Real.sqrt j * (Real.sqrt n)⁻¹ := by
          rw [div_eq_mul_inv]
          ring
        have e3 : (c₂ + 4 * c₂ * max Cb 0) * (Real.sqrt j / Real.sqrt n) =
            c₂ * Real.sqrt j * (Real.sqrt n)⁻¹ +
              4 * c₂ * max Cb 0 * Real.sqrt j * (Real.sqrt n)⁻¹ := by
          rw [div_eq_mul_inv]
          ring
        have h5 : c₂ * (Real.sqrt n)⁻¹ ≤ c₂ * Real.sqrt j * (Real.sqrt n)⁻¹ := by
          have := mul_le_mul_of_nonneg_left hj1 (by positivity : 0 ≤ c₂ * (Real.sqrt n)⁻¹)
          linarith
        rw [e3]
        linarith
      rw [hsqe]
      exact hfin.trans (mul_le_mul_of_nonneg_right
        (le_max_right _ _) (by positivity))


private theorem dirVec_cases (a : Dir 2) :
    (dirVec a 0 = 1 ∧ dirVec a 1 = 0) ∨ (dirVec a 0 = -1 ∧ dirVec a 1 = 0) ∨
      (dirVec a 0 = 0 ∧ dirVec a 1 = 1) ∨ (dirVec a 0 = 0 ∧ dirVec a 1 = -1) := by
  rcases a with ⟨i, b⟩
  fin_cases i <;> cases b <;> simp [dirVec]

private theorem measurableSet_entersAt (B : Set (Site 2)) (z x : Site 2) :
    MeasurableSet (entersAt B z x) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    (measurable_const (a := 1 ≤ t)).and <| (measurable_walkPos_pred x (· = z) t).and <|
      Measurable.forall fun s =>
        measurable_walkPos_pred x (fun y => 1 ≤ s → s < t → y ∉ B) s

/-- From a point of the axis at distance `n ≥ 2` from the origin, the first visit to the real axis
is a visit to `-k` with probability `O(1 / (n + k)²)`. -/
theorem prob_entersAt_axis_start_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ n k : ℕ, 2 ≤ n →
    prob (entersAt (axisSet Set.univ) (axisPt (-(k : ℤ))) (axisPt (n : ℤ))) ≤
      C / ((n : ℝ) + k) ^ 2 := by
  obtain ⟨C₂, hC₂, hh⟩ := halfPlaneKernel_height_one
  refine ⟨C₂, hC₂, fun n k hn => ?_⟩
  have hw : (axisPt (-(k : ℤ))) 1 = 0 := by simp [axisPt]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hnk : (0 : ℝ) < (n : ℝ) + k := by linarith
  have hpos : 0 < ((n : ℝ) + k) ^ 2 := pow_pos hnk 2
  have hbound0 : 0 ≤ C₂ / ((n : ℝ) + k) ^ 2 := div_nonneg hC₂ hpos.le
  have hvert : ∀ y : Site 2, y 0 = (n : ℤ) → (y 1 = 1 ∨ y 1 = -1) → ∀ t,
      prob (entersBy (axisPt (-(k : ℤ))) y t) ≤ C₂ / ((n : ℝ) + k) ^ 2 := by
    intro y hy0 hy1 t
    have h1 := prob_entersBy_le hy1 hw t y (by rcases hy1 with h | h <;> simp [h])
    have h2 := hh (y 1) (axisPt (-(k : ℤ))) y hy1 hw rfl
    have hN : ((n : ℝ) + k) ^ 2 ≤ euclidNorm (y - axisPt (-(k : ℤ))) ^ 2 := by
      rw [euclidNorm_sq']
      have e0 : (((y - axisPt (-(k : ℤ))) 0 : ℤ) : ℝ) = (n : ℝ) + k := by
        simp [hy0, axisPt]
      rw [e0]
      nlinarith [sq_nonneg ((((y - axisPt (-(k : ℤ))) 1 : ℤ)) : ℝ)]
    have h3 : C₂ / euclidNorm (y - axisPt (-(k : ℤ))) ^ 2 ≤ C₂ / ((n : ℝ) + k) ^ 2 :=
      div_le_div_of_nonneg_left hC₂ hpos hN
    have h4 : 0 ≤ C₂ / euclidNorm (y - axisPt (-(k : ℤ))) ^ 2 := div_nonneg hC₂ (sq_nonneg _)
    linarith
  have hterm : ∀ (t : ℕ) (a : Dir 2),
      (if axisPt (n : ℤ) + dirVec a = axisPt (-(k : ℤ)) then (1 : ℝ) else
        if (axisPt (n : ℤ) + dirVec a) 1 = 0 then 0 else
          prob (entersBy (axisPt (-(k : ℤ))) (axisPt (n : ℤ) + dirVec a) t)) ≤
        C₂ / ((n : ℝ) + k) ^ 2 := by
    intro t a
    have hne : axisPt (n : ℤ) + dirVec a ≠ axisPt (-(k : ℤ)) := by
      intro h
      have h0 := congrFun h 0
      simp only [Pi.add_apply, axisPt, Matrix.cons_val_zero] at h0
      have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
      rcases dirVec_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    simp only [hne, ↓reduceIte]
    by_cases h1 : (axisPt (n : ℤ) + dirVec a) 1 = 0
    · simp only [h1, ↓reduceIte]
      exact hbound0
    · simp only [h1, ↓reduceIte]
      rcases dirVec_cases a with ⟨h0', h1'⟩ | ⟨h0', h1'⟩ | ⟨h0', h1'⟩ | ⟨h0', h1'⟩
      · exact absurd (by simp [axisPt, h1']) h1
      · exact absurd (by simp [axisPt, h1']) h1
      · exact hvert _ (by simp [axisPt, h0']) (Or.inl (by simp [axisPt, h1'])) t
      · exact hvert _ (by simp [axisPt, h0']) (Or.inr (by simp [axisPt, h1'])) t
  refine prob_entersAt_le_of_forall fun t => ?_
  cases t with
  | zero =>
    have h : entersBy (axisPt (-(k : ℤ))) (axisPt (n : ℤ)) 0 = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun ω hω => by
        obtain ⟨r, hr1, hr2, -⟩ := hω
        omega
    rw [h, prob_empty]
    exact hbound0
  | succ t =>
    rw [prob_entersBy_succ hw]
    calc ∑ a : Dir 2, (1 / 4 : ℝ) *
          (if axisPt (n : ℤ) + dirVec a = axisPt (-(k : ℤ)) then 1 else
            if (axisPt (n : ℤ) + dirVec a) 1 = 0 then 0 else
              prob (entersBy (axisPt (-(k : ℤ))) (axisPt (n : ℤ) + dirVec a) t))
        ≤ ∑ a : Dir 2, (1 / 4 : ℝ) * (C₂ / ((n : ℝ) + k) ^ 2) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hterm t a) (by norm_num)
      _ = C₂ / ((n : ℝ) + k) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ]
          simp only [nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
          push_cast
          ring

/-- The first visit to the nonnegative half-axis at the origin is either a first visit to the real
axis at the origin, or a first visit to the real axis at a negative point followed by a first
visit to the nonnegative half-axis at the origin. -/
private theorem entersAt_origin_subset (x : Site 2) :
    entersAt (axisSet {j : ℤ | 0 ≤ j}) 0 x ⊆ entersAt (axisSet Set.univ) 0 x ∪
      ⋃ k : ℕ, {ω | ∃ t, ω ∈ hitAtTime (axisSet Set.univ) x (axisPt (-((k + 1 : ℕ) : ℤ))) t ∧
        shiftBy t ω ∈ entersAt (axisSet {j : ℤ | 0 ≤ j}) 0 (axisPt (-((k + 1 : ℕ) : ℤ)))} := by
  classical
  rintro ω ⟨t, ht1, ht2, ht3⟩
  have hex : ∃ u, 1 ≤ u ∧ walkPos x ω u 1 = 0 := ⟨t, ht1, by rw [ht2]; rfl⟩
  have hu : 1 ≤ Nat.find hex ∧ walkPos x ω (Nat.find hex) 1 = 0 := Nat.find_spec hex
  have hut : Nat.find hex ≤ t := Nat.find_min' hex ⟨ht1, by rw [ht2]; rfl⟩
  have hmin : ∀ s, s < Nat.find hex → ¬ (1 ≤ s ∧ walkPos x ω s 1 = 0) :=
    fun s hs => Nat.find_min hex hs
  generalize Nat.find hex = u at hu hut hmin
  have hnot : ∀ s, 1 ≤ s → s < u → walkPos x ω s ∉ axisSet Set.univ :=
    fun s hs1 hs2 hmem => hmin s hs2 ⟨hs1, hmem.1⟩
  by_cases hnn : 0 ≤ walkPos x ω u 0
  · left
    have hut' : u = t := by
      by_contra hne
      exact ht3 u hu.1 (lt_of_le_of_ne hut hne) ⟨hu.2, hnn⟩
    subst hut'
    exact ⟨u, ht1, ht2, hnot⟩
  · right
    obtain ⟨k, hk⟩ : ∃ k : ℕ, walkPos x ω u 0 = -((k + 1 : ℕ) : ℤ) :=
      ⟨(-(walkPos x ω u 0)).toNat - 1, by omega⟩
    have hpt : walkPos x ω u = axisPt (-((k + 1 : ℕ) : ℤ)) := by
      ext i
      fin_cases i
      · simpa [axisPt] using hk
      · simpa [axisPt] using hu.2
    have hut' : u < t := by
      rcases lt_or_eq_of_le hut with h | h
      · exact h
      · exfalso
        subst h
        exact hnn (by rw [ht2]; simp)
    have hkey : ∀ s, walkPos x ω (u + s) =
        walkPos (axisPt (-((k + 1 : ℕ) : ℤ))) (shiftBy u ω) s := fun s => by
      rw [walkPos_add_shiftBy, hpt]
    refine Set.mem_iUnion.2 ⟨k, u, ⟨hu.1, hpt, hnot⟩, t - u, by omega, ?_, ?_⟩
    · rw [← hkey (t - u), Nat.add_sub_cancel' hut]
      exact ht2
    · intro s hs1 hs2
      rw [← hkey s]
      exact ht3 (u + s) (by omega) (by omega)

/-- The piece of `entersAt_origin_subset` through the point `-(k + 1)`. -/
private theorem prob_hit_axis_then_le {x : Site 2} (k : ℕ) {A Bc : ℝ}
    (hA : prob (entersAt (axisSet Set.univ) (axisPt (-((k + 1 : ℕ) : ℤ))) x) ≤ A)
    (hB : prob (entersAt (axisSet {j : ℤ | 0 ≤ j}) 0 (axisPt (-((k + 1 : ℕ) : ℤ)))) ≤ Bc) :
    prob {ω | ∃ t, ω ∈ hitAtTime (axisSet Set.univ) x (axisPt (-((k + 1 : ℕ) : ℤ))) t ∧
      shiftBy t ω ∈ entersAt (axisSet {j : ℤ | 0 ≤ j}) 0
        (axisPt (-((k + 1 : ℕ) : ℤ)))} ≤ A * Bc := by
  rw [prob_hit_then (by simp [axisSet, axisPt]) (measurableSet_entersAt _ _ _)]
  exact mul_le_mul hA hB (prob_nonneg' _) ((prob_nonneg' _).trans hA)

private theorem sum_inv_sq_tail_le (n : ℕ) (hn : 1 ≤ n) (K : ℕ) :
    ∑ k ∈ Finset.range K, (if n ≤ k then 1 / ((k : ℝ) + 1) ^ 2 else 0) ≤
      1 / (n : ℝ) - 1 / ((max K n : ℕ) : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    by_cases hK : n ≤ K
    · have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hn.trans hK
      have e1 : max K n = K := max_eq_left hK
      have e2 : max (K + 1) n = K + 1 := max_eq_left (by omega)
      rw [e1] at ih
      rw [e2]
      simp only [hK, ↓reduceIte]
      push_cast
      have h1 : 1 / (K : ℝ) - 1 / ((K : ℝ) + 1) = 1 / ((K : ℝ) * ((K : ℝ) + 1)) := by
        field_simp
        ring
      have h2 : 1 / ((K : ℝ) + 1) ^ 2 ≤ 1 / ((K : ℝ) * ((K : ℝ) + 1)) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
      linarith
    · have e1 : max K n = n := max_eq_right (by omega)
      have e2 : max (K + 1) n = n := max_eq_right (by omega)
      rw [e1] at ih
      rw [e2]
      simp only [hK, ↓reduceIte, add_zero]
      exact ih

private theorem sum_inv_sqrt_succ_le (j : ℕ) :
    ∑ k ∈ Finset.range j, 1 / Real.sqrt ((k : ℝ) + 1) ≤ 2 * Real.sqrt j := by
  have h := sum_range_succ_inv_sqrt_le j
  rw [Finset.sum_range_succ'] at h
  simpa using h


private theorem series_le (n : ℕ) (hn : 1 ≤ n) (K : ℕ) :
    ∑ k ∈ Finset.range K, 1 / (((n : ℝ) + ((k : ℝ) + 1)) ^ 2 * Real.sqrt ((k : ℝ) + 1)) ≤
      3 / ((n : ℝ) * Real.sqrt n) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hn2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hterm : ∀ k : ℕ, 1 / (((n : ℝ) + ((k : ℝ) + 1)) ^ 2 * Real.sqrt ((k : ℝ) + 1)) ≤
      (if k < n then 1 / (n : ℝ) ^ 2 * (1 / Real.sqrt ((k : ℝ) + 1)) else 0) +
        (if n ≤ k then 1 / Real.sqrt n * (if n ≤ k then 1 / ((k : ℝ) + 1) ^ 2 else 0) else 0) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hsk : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
    by_cases hk : k < n
    · have hk' : ¬ n ≤ k := not_le.2 hk
      simp only [hk, hk', ↓reduceIte, add_zero]
      rw [one_div_mul_one_div]
      refine one_div_le_one_div_of_le (by positivity) ?_
      refine mul_le_mul_of_nonneg_right ?_ hsk.le
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    · have hk' : n ≤ k := not_lt.1 hk
      simp only [hk, hk', ↓reduceIte, zero_add]
      rw [one_div_mul_one_div]
      refine one_div_le_one_div_of_le (by positivity) ?_
      have h1 : Real.sqrt n ≤ Real.sqrt ((k : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by
          have : (n : ℝ) ≤ k := by exact_mod_cast hk'
          linarith)
      have h2 : ((k : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + ((k : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      calc Real.sqrt n * ((k : ℝ) + 1) ^ 2 ≤ Real.sqrt ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ Real.sqrt ((k : ℝ) + 1) * ((n : ℝ) + ((k : ℝ) + 1)) ^ 2 :=
            mul_le_mul_of_nonneg_left h2 hsk.le
        _ = ((n : ℝ) + ((k : ℝ) + 1)) ^ 2 * Real.sqrt ((k : ℝ) + 1) := by ring
  refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
  rw [Finset.sum_add_distrib]
  have hA : ∑ k ∈ Finset.range K, (if k < n then 1 / (n : ℝ) ^ 2 * (1 / Real.sqrt ((k : ℝ) + 1))
      else 0) ≤ 1 / (n : ℝ) ^ 2 * (2 * Real.sqrt n) := by
    rw [← Finset.sum_filter]
    calc ∑ k ∈ (Finset.range K).filter (fun k => k < n),
          1 / (n : ℝ) ^ 2 * (1 / Real.sqrt ((k : ℝ) + 1))
        ≤ ∑ k ∈ Finset.range n, 1 / (n : ℝ) ^ 2 * (1 / Real.sqrt ((k : ℝ) + 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun k hk => Finset.mem_range.2 (Finset.mem_filter.1 hk).2)
            (fun _ _ _ => by positivity)
      _ = 1 / (n : ℝ) ^ 2 * ∑ k ∈ Finset.range n, 1 / Real.sqrt ((k : ℝ) + 1) := by
          rw [Finset.mul_sum]
      _ ≤ 1 / (n : ℝ) ^ 2 * (2 * Real.sqrt n) :=
          mul_le_mul_of_nonneg_left (sum_inv_sqrt_succ_le n) (by positivity)
  have hB : ∑ k ∈ Finset.range K, (if n ≤ k then
      1 / Real.sqrt n * (if n ≤ k then 1 / ((k : ℝ) + 1) ^ 2 else 0) else 0) ≤
      1 / Real.sqrt n * (1 / (n : ℝ)) := by
    have e : ∀ k : ℕ, (if n ≤ k then
        1 / Real.sqrt n * (if n ≤ k then 1 / ((k : ℝ) + 1) ^ 2 else 0) else 0) =
        1 / Real.sqrt n * (if n ≤ k then 1 / ((k : ℝ) + 1) ^ 2 else 0) := by
      intro k
      by_cases hk : n ≤ k <;> simp [hk]
    simp_rw [e]
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (sum_inv_sq_tail_le n hn K).trans ?_
    have : (0 : ℝ) ≤ 1 / ((max K n : ℕ) : ℝ) := by positivity
    linarith
  refine (add_le_add hA hB).trans (le_of_eq ?_)
  have hn_eq : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  rw [hn_eq]
  have : Real.sqrt (Real.sqrt n ^ 2) = Real.sqrt n := Real.sqrt_sq hsn.le
  rw [this]
  field_simp
  ring

/-- **Proposition 12 (c).** -/
theorem entersAt_halfLine_far_le :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      prob (entersAt (axisSet {j : ℤ | 0 ≤ j}) 0 (axisPt n)) ≤ C / (n : ℝ) ^ (3 / 2 : ℝ) := by
  obtain ⟨Cb, hCb⟩ := entersAt_halfLine_origin_le
  obtain ⟨C₁, hC₁, h1⟩ := prob_entersAt_axis_start_le
  have hCb0 : 0 ≤ max Cb 0 := le_max_right _ _
  refine ⟨max 1 (C₁ + 3 * C₁ * max Cb 0), fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hpow : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hnn : 0 < (n : ℝ) * Real.sqrt n := by positivity
  rw [hpow]
  rcases Nat.lt_or_ge n 2 with hsmall | hbig
  · have : n = 1 := by omega
    subst this
    simp only [Nat.cast_one, Real.sqrt_one, mul_one, div_one]
    exact (prob_le_one' _).trans (le_max_left _ _)
  · -- the first visit to the axis is at the origin
    have hE0 : prob (entersAt (axisSet Set.univ) 0 (axisPt (n : ℤ))) ≤ C₁ / (n : ℝ) ^ 2 := by
      have h := h1 n 0 hbig
      have e : axisPt (-((0 : ℕ) : ℤ)) = (0 : Site 2) := by
        ext i
        fin_cases i <;> simp [axisPt]
      rw [e] at h
      simpa using h
    have hG : ∀ k : ℕ, pathLaw 2 {ω | ∃ t, ω ∈ hitAtTime (axisSet Set.univ) (axisPt (n : ℤ))
        (axisPt (-((k + 1 : ℕ) : ℤ))) t ∧ shiftBy t ω ∈ entersAt (axisSet {j : ℤ | 0 ≤ j}) 0
          (axisPt (-((k + 1 : ℕ) : ℤ)))} ≤
        ENNReal.ofReal
          (C₁ / ((n : ℝ) + ((k : ℝ) + 1)) ^ 2 * (max Cb 0 / Real.sqrt ((k : ℝ) + 1))) := by
      intro k
      have hA := h1 n (k + 1) hbig
      have hB := hCb (k + 1) (by omega)
      push_cast at hA hB
      have hB' : prob (entersAt (axisSet {j : ℤ | 0 ≤ j}) 0 (axisPt (-((k + 1 : ℕ) : ℤ)))) ≤
          max Cb 0 / Real.sqrt ((k : ℝ) + 1) :=
        hB.trans (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
      have hbd := prob_hit_axis_then_le (x := axisPt (n : ℤ)) k
        (A := C₁ / ((n : ℝ) + ((k : ℝ) + 1)) ^ 2) (Bc := max Cb 0 / Real.sqrt ((k : ℝ) + 1))
        (by push_cast; exact hA) hB'
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 hbd
    have hmain : pathLaw 2 (entersAt (axisSet {j : ℤ | 0 ≤ j}) 0 (axisPt (n : ℤ))) ≤
        ENNReal.ofReal (C₁ / (n : ℝ) ^ 2) +
          ENNReal.ofReal (C₁ * max Cb 0 * (3 / ((n : ℝ) * Real.sqrt n))) := by
      refine (measure_mono (entersAt_origin_subset _)).trans
        ((measure_union_le _ _).trans (add_le_add ?_ ?_))
      · exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
          (div_nonneg hC₁ (sq_nonneg _))).2 hE0
      · refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum hG).trans ?_)
        refine ENNReal.tsum_le_of_sum_range_le fun K => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ∑ k ∈ Finset.range K, C₁ / ((n : ℝ) + ((k : ℝ) + 1)) ^ 2 *
              (max Cb 0 / Real.sqrt ((k : ℝ) + 1))
            = C₁ * max Cb 0 * ∑ k ∈ Finset.range K,
                1 / (((n : ℝ) + ((k : ℝ) + 1)) ^ 2 * Real.sqrt ((k : ℝ) + 1)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [div_mul_div_comm, mul_one_div]
          _ ≤ C₁ * max Cb 0 * (3 / ((n : ℝ) * Real.sqrt n)) :=
              mul_le_mul_of_nonneg_left (series_le n hn K) (by positivity)
    rw [← ENNReal.ofReal_add (div_nonneg hC₁ (sq_nonneg _)) (by positivity)] at hmain
    have hfin := ENNReal.toReal_le_of_le_ofReal (by positivity) hmain
    refine hfin.trans ?_
    have hsq : (n : ℝ) * Real.sqrt n ≤ (n : ℝ) ^ 2 := by
      have : Real.sqrt n ≤ n := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      nlinarith
    have h2 : C₁ / (n : ℝ) ^ 2 ≤ C₁ / ((n : ℝ) * Real.sqrt n) :=
      div_le_div_of_nonneg_left hC₁ hnn hsq
    have e : C₁ * max Cb 0 * (3 / ((n : ℝ) * Real.sqrt n)) =
        3 * C₁ * max Cb 0 / ((n : ℝ) * Real.sqrt n) := by ring
    have h3 : C₁ / ((n : ℝ) * Real.sqrt n) + 3 * C₁ * max Cb 0 / ((n : ℝ) * Real.sqrt n) =
        (C₁ + 3 * C₁ * max Cb 0) / ((n : ℝ) * Real.sqrt n) := by ring
    rw [e]
    calc C₁ / (n : ℝ) ^ 2 + 3 * C₁ * max Cb 0 / ((n : ℝ) * Real.sqrt n)
        ≤ C₁ / ((n : ℝ) * Real.sqrt n) + 3 * C₁ * max Cb 0 / ((n : ℝ) * Real.sqrt n) := by linarith
      _ = (C₁ + 3 * C₁ * max Cb 0) / ((n : ℝ) * Real.sqrt n) := h3
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hnn.le

end FiniteAvalanches.Walk.Beurling
