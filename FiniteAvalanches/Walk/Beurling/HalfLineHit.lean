/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/HalfLineHit.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added;
`LatticeProb.Prob.IidBlocks` renamed to `FiniteAvalanches.Walk.IidBlocks`; `Set.mem_ofPred_eq`
replaced by `Set.mem_setOf_eq` (3 times); `Measurable.of_eval` replaced by `measurable_pi_lambda _`
(once); `ite_eq_left` replaced by `if_pos` (once); `ite_eq_right` replaced by `if_neg` (once).
-/
import FiniteAvalanches.Walk.Beurling.HalfLineEscape
import FiniteAvalanches.Walk.Beurling.HalfLine

/-!
# Hitting a half-line

For simple random walk on `ℤ²` started at the origin, the probability of leaving the disk of
radius `n` no later than the first positive-time visit to the nonnegative (or the positive) real
half-axis is comparable to `1 / √n`. The walk started at `-n` enters the nonnegative half-axis
at the origin with probability `O(1 / √n)`. This is Proposition 12 (a), (b) of G. F. Lawler and
V. Limic, *The Beurling estimate for a class of random walks*, Electron. J. Probab. 9 (2004).

The upper bound in (a) is reduced to the strip estimate of Lemma 10 by two symmetries of the
walk. Reflecting the path after its last visit to the imaginary axis shows that the walk leaves
the disk through the closed left half-plane at least as often as through the open right
half-plane. From an exit point `w` in the left half-plane, the walk leaves the disk of radius `n`
about `w` with a vertical displacement of at least `n / √2` with probability at least `1 / 2`,
by the symmetry exchanging the two coordinates, and that disk does not meet the half-axis.

For (b), reversing the path turns the entrance probability into the expected number of visits
to `-n` before the half-axis, started at the origin. This is at most the probability of reaching
`-n` before the half-axis times the expected number of visits started at `-n`. The second factor
is bounded by Lemma 11 (a). For the first factor, the walk must leave the disk of radius `n / 3`
before the half-axis, which has probability `O(1 / √n)` by (a); from there it reaches `-n` before
the half-axis with probability `O(1 / log n)`, by Lemmas 7 and 8 and the Markov property.

## Main statements

* `exitsWeak_halfLine_nonneg`, `exitsWeak_halfLine_pos`: Proposition 12 (a).
* `entersAt_halfLine_origin_le`: Proposition 12 (b).
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

/-! ### Norms and positions -/

private theorem nrm_eq (z : Site 2) :
    euclidNorm z = Real.sqrt (((z 0 : ℤ) : ℝ) ^ 2 + ((z 1 : ℤ) : ℝ) ^ 2) := by
  rw [euclidNorm, Fin.sum_univ_two]

private theorem le_nrm_iff {r : ℝ} (hr : 0 ≤ r) (z : Site 2) :
    r ≤ euclidNorm z ↔ r ^ 2 ≤ ((z 0 : ℤ) : ℝ) ^ 2 + ((z 1 : ℤ) : ℝ) ^ 2 := by
  rw [nrm_eq]
  exact Real.le_sqrt hr (by positivity)

private theorem nrm_lt_iff {r : ℝ} (hr : 0 ≤ r) (z : Site 2) :
    euclidNorm z < r ↔ ((z 0 : ℤ) : ℝ) ^ 2 + ((z 1 : ℤ) : ℝ) ^ 2 < r ^ 2 := by
  rw [← not_le, le_nrm_iff hr, not_le]

private theorem le_nrm_of_le_abs {r : ℝ} (hr : 0 ≤ r) {z : Site 2} (h : r ≤ |((z 1 : ℤ) : ℝ)|) :
    r ≤ euclidNorm z := by
  rw [le_nrm_iff hr]
  have h1 : r ^ 2 ≤ |((z 1 : ℤ) : ℝ)| ^ 2 := pow_le_pow_left₀ hr h 2
  rw [sq_abs] at h1
  nlinarith [sq_nonneg ((z 0 : ℤ) : ℝ)]

private theorem nrm_toLp (y : Site 2) :
    euclidNorm y = ‖(WithLp.toLp 2 fun i => ((y i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2))‖ := by
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, euclidNorm]

private theorem toLp_sub' (a b : Site 2) :
    (WithLp.toLp 2 fun i => (((a - b) i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2)) =
      (WithLp.toLp 2 fun i => ((a i : ℤ) : ℝ)) - (WithLp.toLp 2 fun i => ((b i : ℤ) : ℝ)) := by
  ext i
  simp

private theorem nrm_sub_le (a b : Site 2) : euclidNorm (a - b) ≤ euclidNorm a + euclidNorm b := by
  rw [nrm_toLp (a - b), nrm_toLp a, nrm_toLp b, toLp_sub']
  exact norm_sub_le _ _

private theorem nrm_sub_ge (a b : Site 2) : euclidNorm a - euclidNorm b ≤ euclidNorm (a - b) := by
  rw [nrm_toLp (a - b), nrm_toLp a, nrm_toLp b, toLp_sub']
  exact norm_sub_norm_le _ _

private theorem nrm_dirVec (a : Dir 2) : euclidNorm (dirVec a) = 1 := by
  obtain ⟨i, b⟩ := a
  fin_cases i <;> cases b <;> simp [nrm_eq, dirVec]

private theorem abs_dirVec_le (a : Dir 2) (i : Fin 2) : |dirVec a i| ≤ 1 := by
  unfold dirVec
  split_ifs <;> simp

private theorem walkPos_eq_add' (x : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos x ω t = x + walkPos 0 ω t := by
  simp [walkPos]

private theorem walkPos_succ' (x : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos x ω (t + 1) = walkPos x ω t + dirVec (ω t) := by
  simp [walkPos, Finset.sum_range_succ, add_assoc]

private theorem walkPos_shift (x : Site 2) (ω : ℕ → Dir 2) (j t : ℕ) :
    walkPos x ω (j + t) = walkPos (walkPos x ω j) (shiftBy j ω) t := by
  rw [walkPos_eq_add' x, walkPos_zero_add, walkPos_eq_add' (walkPos x ω j),
    walkPos_eq_add' x ω j, add_assoc]

private theorem nrm_step_ge (x : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    euclidNorm (walkPos x ω t) ≤ euclidNorm (walkPos x ω (t + 1)) + 1 := by
  have h := nrm_sub_le (walkPos x ω t + dirVec (ω t)) (dirVec (ω t))
  rw [add_sub_cancel_right, nrm_dirVec] at h
  rw [walkPos_succ']
  exact h

private theorem walkPos_congr' (x : Site 2) {ω ω' : ℕ → Dir 2} {j : ℕ}
    (h : ∀ i < j, ω i = ω' i) {t : ℕ} (ht : t ≤ j) : walkPos x ω t = walkPos x ω' t := by
  rw [walkPos_eq_add' x ω, walkPos_eq_add' x ω', walkPos_congr h ht]

private theorem dependsOnFirst_of (x : Site 2) {j : ℕ} {A : Set (ℕ → Dir 2)}
    (h : ∀ ω ω' : ℕ → Dir 2, (∀ s ≤ j, walkPos x ω s = walkPos x ω' s) → ω ∈ A → ω' ∈ A) :
    DependsOnFirst j A := fun ω ω' hω =>
  ⟨h ω ω' fun _ hs => walkPos_congr' x hω hs,
    h ω' ω fun _ hs => (walkPos_congr' x hω hs).symm⟩

private theorem ne_top' (E : Set (ℕ → Dir 2)) : pathLaw 2 E ≠ ⊤ := measure_ne_top _ _

/-! ### Symmetries of the step distribution -/

private theorem map_of_involutive {f : Dir 2 → Dir 2} (hf : ∀ a, f (f a) = a) :
    (stepLaw 2).map f = stepLaw 2 := by
  refine Measure.ext_of_singleton fun a => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton a)]
  have : f ⁻¹' {a} = {f a} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => by rw [← h, hf], fun h => by rw [h, hf]⟩
  rw [this, stepLaw_singleton, stepLaw_singleton]

private theorem measurePreserving_pointwise (f : ℕ → Dir 2 → Dir 2)
    (hf : ∀ i, (stepLaw 2).map (f i) = stepLaw 2) :
    MeasurePreserving (fun (ω : ℕ → Dir 2) (i : ℕ) => f i (ω i)) (pathLaw 2) (pathLaw 2) := by
  refine ⟨measurable_pi_lambda _ fun i =>
    (measurable_of_countable (f i)).comp (measurable_pi_apply i), ?_⟩
  rw [pathLaw, Measure.infinitePi_map_pi _ (fun i => measurable_of_countable (f i))]
  simp only [hf]

private theorem rev_zero' : Fin.rev (0 : Fin 2) = 1 := rfl

private theorem rev_one' : Fin.rev (1 : Fin 2) = 0 := rfl

/-- Exchange of the two coordinate directions. -/
private def swapDir (a : Dir 2) : Dir 2 := (Fin.rev a.1, a.2)

private theorem swapDir_swapDir (a : Dir 2) : swapDir (swapDir a) = a := by
  simp [swapDir]

private theorem dirVec_swapDir (a : Dir 2) (i : Fin 2) :
    dirVec (swapDir a) i = dirVec a (Fin.rev i) := by
  obtain ⟨j, b⟩ := a
  fin_cases i <;> fin_cases j <;> cases b <;> simp [dirVec, swapDir]

private theorem walkPos_swap (ω : ℕ → Dir 2) (t : ℕ) (i : Fin 2) :
    walkPos 0 (fun j => swapDir (ω j)) t i = walkPos 0 ω t (Fin.rev i) := by
  simp only [walkPos, zero_add, Finset.sum_apply, dirVec_swapDir]

private theorem nrm_swap (ω : ℕ → Dir 2) (t : ℕ) :
    euclidNorm (walkPos 0 (fun j => swapDir (ω j)) t) = euclidNorm (walkPos 0 ω t) := by
  rw [nrm_eq, nrm_eq, walkPos_swap, walkPos_swap, rev_zero', rev_one', add_comm]

/-- Reflection of a direction in the imaginary axis. -/
private def hflip (a : Dir 2) : Dir 2 := if a.1 = 0 then (a.1, !a.2) else a

private theorem hflip_hflip (a : Dir 2) : hflip (hflip a) = a := by
  obtain ⟨i, b⟩ := a
  fin_cases i <;> simp [hflip]

private theorem dirVec_hflip_zero (a : Dir 2) : dirVec (hflip a) 0 = -dirVec a 0 := by
  obtain ⟨i, b⟩ := a
  fin_cases i <;> cases b <;> simp [hflip, dirVec]

private theorem dirVec_hflip_one (a : Dir 2) : dirVec (hflip a) 1 = dirVec a 1 := by
  obtain ⟨i, b⟩ := a
  fin_cases i <;> cases b <;> simp [hflip, dirVec]

/-- Reflect the increments with index in `[a, t)` in the imaginary axis. -/
private def reflectOn (a t : ℕ) (ω : ℕ → Dir 2) : ℕ → Dir 2 :=
  fun i => if a ≤ i ∧ i < t then hflip (ω i) else ω i

private theorem measurePreserving_reflectOn (a t : ℕ) :
    MeasurePreserving (reflectOn a t) (pathLaw 2) (pathLaw 2) := by
  have he : reflectOn a t =
      fun ω i => (if a ≤ i ∧ i < t then hflip else id) (ω i) := by
    funext ω i
    unfold reflectOn
    split_ifs <;> rfl
  rw [he]
  refine measurePreserving_pointwise _ fun i => ?_
  split_ifs
  · exact map_of_involutive hflip_hflip
  · exact Measure.map_id

private theorem walkPos_reflectOn_one (a t : ℕ) (ω : ℕ → Dir 2) (s : ℕ) :
    walkPos 0 (reflectOn a t ω) s 1 = walkPos 0 ω s 1 := by
  induction s with
  | zero => simp [walkPos]
  | succ s ih =>
    rw [walkPos_zero_succ, walkPos_zero_succ, Pi.add_apply, Pi.add_apply, ih]
    congr 1
    unfold reflectOn
    split_ifs
    · exact dirVec_hflip_one _
    · rfl

private theorem walkPos_reflectOn_le {a t s : ℕ} (ω : ℕ → Dir 2) (hs : s ≤ a) :
    walkPos 0 (reflectOn a t ω) s = walkPos 0 ω s := by
  induction s with
  | zero => simp [walkPos]
  | succ s ih =>
    rw [walkPos_zero_succ, walkPos_zero_succ, ih (by omega)]
    have : ¬(a ≤ s ∧ s < t) := fun h => by omega
    rw [show reflectOn a t ω s = ω s from if_neg this]

private theorem walkPos_reflectOn_zero {a t s : ℕ} (ω : ℕ → Dir 2) (h1 : a ≤ s) (h2 : s ≤ t) :
    walkPos 0 (reflectOn a t ω) s 0 = 2 * walkPos 0 ω a 0 - walkPos 0 ω s 0 := by
  induction s, h1 using Nat.le_induction with
  | base => rw [walkPos_reflectOn_le ω le_rfl]; ring
  | succ s hs ih =>
    rw [walkPos_zero_succ, walkPos_zero_succ, Pi.add_apply, Pi.add_apply, ih (by omega)]
    have : a ≤ s ∧ s < t := ⟨hs, by omega⟩
    rw [show reflectOn a t ω s = hflip (ω s) from if_pos this, dirVec_hflip_zero]
    ring

/-! ### Leaving the disk -/

/-- The walk from the origin leaves the disk of radius `n` for the first time at time `t`, with
no visit to `B` at the times `1, ..., t - 1`. -/
private def firstOut (n : ℕ) (B : Set (Site 2)) (t : ℕ) : Set (ℕ → Dir 2) :=
  {ω | (n : ℝ) ≤ euclidNorm (walkPos 0 ω t) ∧ (∀ s < t, euclidNorm (walkPos 0 ω s) < n) ∧
    ∀ s, 1 ≤ s → s < t → walkPos 0 ω s ∉ B}

/-- First exit through the closed left half-plane. -/
private def outL (n : ℕ) (B : Set (Site 2)) (t : ℕ) : Set (ℕ → Dir 2) :=
  firstOut n B t ∩ {ω | walkPos 0 ω t 0 ≤ 0}

/-- First exit through the open right half-plane. -/
private def outR (n : ℕ) (B : Set (Site 2)) (t : ℕ) : Set (ℕ → Dir 2) :=
  firstOut n B t ∩ {ω | 0 < walkPos 0 ω t 0}

/-- The last visit to the imaginary axis up to time `t` is at time `a < t`. -/
private def lastZero (a t : ℕ) : Set (ℕ → Dir 2) :=
  {ω | walkPos 0 ω a 0 = 0 ∧ a < t ∧ ∀ s, a < s → s ≤ t → walkPos 0 ω s 0 ≠ 0}

private theorem dependsOnFirst_outL (n : ℕ) (B : Set (Site 2)) (t : ℕ) :
    DependsOnFirst t (outL n B t) := by
  refine dependsOnFirst_of 0 fun ω ω' h hω => ?_
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hω
  refine ⟨⟨?_, fun s hs => ?_, fun s hs1 hs2 => ?_⟩, ?_⟩
  · rw [← h t le_rfl]; exact h1
  · rw [← h s hs.le]; exact h2 s hs
  · rw [← h s hs2.le]; exact h3 s hs1 hs2
  · show walkPos 0 ω' t 0 ≤ 0
    rw [← h t le_rfl]; exact h4

private theorem dependsOnFirst_outL_lastZero (n : ℕ) (B : Set (Site 2)) (a t : ℕ) :
    DependsOnFirst t (outL n B t ∩ lastZero a t) := by
  have hL : DependsOnFirst t (lastZero a t) := dependsOnFirst_of 0 fun ω ω' h hω => by
    obtain ⟨h1, h2, h3⟩ := hω
    refine ⟨?_, h2, fun s hs1 hs2 => ?_⟩
    · rw [← h a h2.le]; exact h1
    · rw [← h s hs2]; exact h3 s hs1 hs2
  exact fun ω ω' h => and_congr (dependsOnFirst_outL n B t ω ω' h) (hL ω ω' h)

private theorem firstOut_disjoint (n : ℕ) (B : Set (Site 2)) {t t' : ℕ} (h : t ≠ t') :
    Disjoint (firstOut n B t) (firstOut n B t') := by
  rw [Set.disjoint_left]
  rintro ω ⟨h1, h2, -⟩ ⟨h1', h2', -⟩
  rcases lt_or_gt_of_ne h with h | h
  · exact absurd h1 (not_le.mpr (h2' t h))
  · exact absurd h1' (not_le.mpr (h2 t' h))

private theorem exitsWeakBefore_subset_out (n : ℕ) (B : Set (Site 2)) :
    exitsWeakBefore n B 0 ⊆ (⋃ t, outL n B t) ∪ ⋃ t, outR n B t := by
  classical
  rintro ω ⟨t, ht, hB⟩
  have hex : ∃ t, (n : ℝ) ≤ euclidNorm (walkPos 0 ω t) := ⟨t, ht⟩
  have hf : ω ∈ firstOut n B (Nat.find hex) :=
    ⟨Nat.find_spec hex, fun s hs => not_le.mp (Nat.find_min hex hs),
      fun s h1 h2 => hB s h1 (lt_of_lt_of_le h2 (Nat.find_min' hex ht))⟩
  rcases le_or_gt (walkPos 0 ω (Nat.find hex) 0) 0 with h | h
  · exact Or.inl (Set.mem_iUnion.mpr ⟨_, hf, h⟩)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨_, hf, h⟩)

/-! ### The exchange of coordinates -/

/-- The walk leaves the disk of radius `n` for the first time at a point whose coordinate `i`
has square at least `n² / 2`. -/
private def exitCoord (n : ℕ) (i : Fin 2) : Set (ℕ → Dir 2) :=
  ⋃ t, {ω | (n : ℝ) ≤ euclidNorm (walkPos 0 ω t) ∧ (∀ s < t, euclidNorm (walkPos 0 ω s) < n) ∧
    (n : ℝ) ^ 2 ≤ 2 * ((walkPos 0 ω t i : ℤ) : ℝ) ^ 2}

private theorem measurableSet_exitCoord (n : ℕ) (i : Fin 2) : MeasurableSet (exitCoord n i) := by
  refine MeasurableSet.iUnion fun t => DependsOnFirst.measurableSet (j := t) ?_
  refine dependsOnFirst_of 0 fun ω ω' h hω => ?_
  obtain ⟨h1, h2, h3⟩ := hω
  refine ⟨?_, fun s hs => ?_, ?_⟩
  · rw [← h t le_rfl]; exact h1
  · rw [← h s hs.le]; exact h2 s hs
  · rw [← h t le_rfl]; exact h3

private theorem pathLaw_exit_compl (n : ℕ) :
    pathLaw 2 {ω | ∃ t, (n : ℝ) ≤ euclidNorm (walkPos 0 ω t)}ᶜ = 0 := by
  refine FiniteAvalanches.Walk.IidBlocks.measure_eq_zero_of_subset_avoidsConstantBlocks (stepLaw 2)
    ((1 : Fin 2), true) (2 * n) ?_ _ ?_
  · rw [stepLaw_singleton]; simp
  · intro N ω hω k hk hblock
    obtain ⟨t, ht⟩ := exists_strip_exit_of_upBlock ω k hblock
    refine hω ⟨t, le_nrm_of_le_abs (Nat.cast_nonneg n) ?_⟩
    have : ((n : ℤ) : ℝ) ≤ ((|walkPos 0 ω t 1| : ℤ) : ℝ) := Int.cast_le.mpr ht
    simpa using this

private theorem one_le_two_mul_exitCoord (n : ℕ) : 1 ≤ 2 * pathLaw 2 (exitCoord n 1) := by
  classical
  have hsym : pathLaw 2 (exitCoord n 0) = pathLaw 2 (exitCoord n 1) := by
    have he : (fun (ω : ℕ → Dir 2) (j : ℕ) => swapDir (ω j)) ⁻¹' exitCoord n 1 =
        exitCoord n 0 := by
      ext ω
      simp only [exitCoord, Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, nrm_swap,
        walkPos_swap, rev_one']
    rw [← he, (measurePreserving_pointwise (fun _ => swapDir)
      fun _ => map_of_involutive swapDir_swapDir).measure_preimage
      (measurableSet_exitCoord n 1).nullMeasurableSet]
  have hsub : {ω | ∃ t, (n : ℝ) ≤ euclidNorm (walkPos 0 ω t)} ⊆
      exitCoord n 0 ∪ exitCoord n 1 := by
    rintro ω ⟨t, ht⟩
    have hex : ∃ t, (n : ℝ) ≤ euclidNorm (walkPos 0 ω t) := ⟨t, ht⟩
    have h1 := Nat.find_spec hex
    have h2 : ∀ s < Nat.find hex, euclidNorm (walkPos 0 ω s) < n :=
      fun s hs => not_le.mp (Nat.find_min hex hs)
    have h3 := (le_nrm_iff (Nat.cast_nonneg n) _).mp h1
    by_cases h0 : (n : ℝ) ^ 2 ≤ 2 * ((walkPos 0 ω (Nat.find hex) 0 : ℤ) : ℝ) ^ 2
    · exact Or.inl (Set.mem_iUnion.mpr ⟨_, h1, h2, h0⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨_, h1, h2, by linarith⟩)
  calc (1 : ENNReal) = pathLaw 2 Set.univ := measure_univ.symm
    _ ≤ pathLaw 2 {ω | ∃ t, (n : ℝ) ≤ euclidNorm (walkPos 0 ω t)} +
        pathLaw 2 {ω | ∃ t, (n : ℝ) ≤ euclidNorm (walkPos 0 ω t)}ᶜ := by
      rw [← Set.union_compl_self {ω : ℕ → Dir 2 | ∃ t, (n : ℝ) ≤ euclidNorm (walkPos 0 ω t)}]
      exact measure_union_le _ _
    _ ≤ pathLaw 2 (exitCoord n 0) + pathLaw 2 (exitCoord n 1) := by
      rw [pathLaw_exit_compl, add_zero]
      exact (measure_mono hsub).trans (measure_union_le _ _)
    _ = 2 * pathLaw 2 (exitCoord n 1) := by rw [hsym, two_mul]

/-! ### Exits through the left half-plane -/

private theorem outL_inter_subset {n : ℕ} (hn : 3 ≤ n) {B : Set (Site 2)}
    (hB : B ⊆ axisSet {j | 0 ≤ j}) (t : ℕ) :
    outL n B t ∩ shiftBy t ⁻¹' exitCoord n 1 ⊆ stripExitsBefore ((n / 3 : ℕ) : ℝ) B 0 := by
  rintro ω ⟨⟨⟨h1, -, h3⟩, h4⟩, hG⟩
  obtain ⟨u, hu1, hu2, hu3⟩ := Set.mem_iUnion.mp hG
  set w := walkPos 0 ω t with hw
  set m := n / 3 with hm
  have hm1 : 1 ≤ m := by omega
  have hm3 : 3 * m ≤ n := by omega
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hwn := (le_nrm_iff hnn w).mp h1
  have hw0 : ((w 0 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h4
  -- A point within distance `n` of `w` is not on the nonnegative half-axis.
  have hK : ∀ v : Site 2, euclidNorm v < n → w + v ∉ B := by
    intro v hv hvB
    obtain ⟨hv1, hv0⟩ := hB hvB
    have e1 : ((v 1 : ℤ) : ℝ) = -((w 1 : ℤ) : ℝ) := by
      have : w 1 + v 1 = 0 := hv1
      have : v 1 = -w 1 := by omega
      exact_mod_cast this
    have e0 : -((w 0 : ℤ) : ℝ) ≤ ((v 0 : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ w 0 + v 0 := hv0
      have : -w 0 ≤ v 0 := by omega
      exact_mod_cast this
    have hv' := (nrm_lt_iff hnn v).mp hv
    have hv1sq : ((v 1 : ℤ) : ℝ) ^ 2 = ((w 1 : ℤ) : ℝ) ^ 2 := by rw [e1]; ring
    have hv0sq : ((w 0 : ℤ) : ℝ) ^ 2 ≤ ((v 0 : ℤ) : ℝ) ^ 2 := by nlinarith
    linarith
  have hK0 : w ∉ B := by
    have := hK 0 (by rw [euclidNorm_zero]; exact_mod_cast (by omega : 0 < n))
    rwa [add_zero] at this
  by_cases hwm : (m : ℝ) ≤ |((w 1 : ℤ) : ℝ)|
  · refine ⟨t, hwm, fun s hs1 hs2 => ?_⟩
    rcases lt_or_eq_of_le hs2 with hs2 | rfl
    · exact h3 s hs1 hs2
    · exact hK0
  · rw [not_le] at hwm
    set v := walkPos 0 (shiftBy t ω) u with hv
    have hpos : ∀ k, walkPos 0 ω (t + k) = w + walkPos 0 (shiftBy t ω) k :=
      fun k => walkPos_zero_add ω t k
    refine ⟨t + u, ?_, fun s hs1 hs2 => ?_⟩
    · rw [hpos u, ← hv]
      have hmR : (3 : ℝ) * m ≤ n := by exact_mod_cast hm3
      have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have hsq : ((2 : ℝ) * m) ^ 2 ≤ ((v 1 : ℤ) : ℝ) ^ 2 := by nlinarith
      have habs : |(2 : ℝ) * m| ≤ |((v 1 : ℤ) : ℝ)| := sq_le_sq.mp hsq
      rw [abs_of_nonneg (by positivity)] at habs
      have htri := abs_add_le (((w 1 : ℤ) : ℝ) + ((v 1 : ℤ) : ℝ)) (-((w 1 : ℤ) : ℝ))
      rw [add_neg_cancel_comm, abs_neg] at htri
      rw [Pi.add_apply, Int.cast_add]
      linarith
    · rcases lt_trichotomy s t with hst | rfl | hst
      · exact h3 s hs1 hst
      · exact hK0
      · obtain ⟨k, rfl⟩ : ∃ k, s = t + k := ⟨s - t, by omega⟩
        rw [hpos k]
        rcases lt_or_eq_of_le hs2 with hk | hk
        · exact hK _ (hu2 k (by omega))
        · have hku : k = u := by omega
          subst hku
          intro hB'
          have h1' : (w + v) 1 = 0 := (hB hB').1
          have : (v 1 : ℤ) = -w 1 := by
            have : w 1 + v 1 = 0 := h1'
            omega
          have hmR : (3 : ℝ) * m ≤ n := by exact_mod_cast hm3
          have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
          have hc : ((v 1 : ℤ) : ℝ) = -((w 1 : ℤ) : ℝ) := by exact_mod_cast this
          have hsq : ((w 1 : ℤ) : ℝ) ^ 2 < (m : ℝ) ^ 2 := by
            have := abs_lt.mp hwm
            nlinarith
          rw [hc, neg_sq] at hu3
          nlinarith

private theorem pathLaw_outL_le {n : ℕ} (hn : 3 ≤ n) {B : Set (Site 2)}
    (hB : B ⊆ axisSet {j | 0 ≤ j}) :
    pathLaw 2 (⋃ t, outL n B t) ≤
      2 * pathLaw 2 (stripExitsBefore ((n / 3 : ℕ) : ℝ) B 0) := by
  have hdisj : Pairwise (Function.onFun Disjoint fun t => outL n B t) := fun t t' h =>
    (firstOut_disjoint n B h).mono Set.inter_subset_left Set.inter_subset_left
  have hmeas : ∀ t, MeasurableSet (outL n B t) := fun t =>
    (dependsOnFirst_outL n B t).measurableSet
  have hG := measurableSet_exitCoord n 1
  have hprod : pathLaw 2 (⋃ t, outL n B t) * pathLaw 2 (exitCoord n 1) ≤
      pathLaw 2 (stripExitsBefore ((n / 3 : ℕ) : ℝ) B 0) := by
    rw [measure_iUnion hdisj hmeas, ← ENNReal.tsum_mul_right,
      tsum_congr fun t => (markov_split (dependsOnFirst_outL n B t) hG).symm, ← measure_iUnion]
    · exact measure_mono (Set.iUnion_subset fun t => outL_inter_subset hn hB t)
    · exact fun t t' h => (hdisj h).mono Set.inter_subset_left Set.inter_subset_left
    · exact fun t => (hmeas t).inter (measurable_shiftBy t hG)
  calc pathLaw 2 (⋃ t, outL n B t) = pathLaw 2 (⋃ t, outL n B t) * 1 := (mul_one _).symm
    _ ≤ pathLaw 2 (⋃ t, outL n B t) * (2 * pathLaw 2 (exitCoord n 1)) := by
      gcongr; exact one_le_two_mul_exitCoord n
    _ = 2 * (pathLaw 2 (⋃ t, outL n B t) * pathLaw 2 (exitCoord n 1)) := by ring
    _ ≤ 2 * pathLaw 2 (stripExitsBefore ((n / 3 : ℕ) : ℝ) B 0) := by gcongr

/-! ### Exits through the right half-plane -/

private theorem pos_of_lastZero {ω : ℕ → Dir 2} {a t : ℕ}
    (h : ∀ s, a < s → s ≤ t → walkPos 0 ω s 0 ≠ 0) (ht : 0 < walkPos 0 ω t 0) :
    ∀ s, a < s → s ≤ t → 0 < walkPos 0 ω s 0 := by
  have key : ∀ d s, s + d = t → a < s → 0 < walkPos 0 ω s 0 := by
    intro d
    induction d with
    | zero => intro s hs _; rw [add_zero] at hs; rw [hs]; exact ht
    | succ d ih =>
      intro s hs has
      have h1 := ih (s + 1) (by omega) (by omega)
      have h2 := h s has (by omega)
      have h3 := abs_le.mp (abs_dirVec_le (ω s) 0)
      rw [walkPos_zero_succ, Pi.add_apply] at h1
      omega
  intro s hs1 hs2
  exact key (t - s) s (by omega) hs1

private theorem outR_subset (n : ℕ) (B : Set (Site 2)) (t : ℕ) :
    outR n B t ⊆ ⋃ a, outR n B t ∩ lastZero a t := by
  classical
  intro ω hω
  have hpos : 0 < walkPos 0 ω t 0 := hω.2
  have ha0 : walkPos 0 ω (Nat.findGreatest (fun s => walkPos 0 ω s 0 = 0) t) 0 = 0 :=
    Nat.findGreatest_spec (P := fun s => walkPos 0 ω s 0 = 0) (Nat.zero_le t) (by simp [walkPos])
  have hat := Nat.findGreatest_le (P := fun s => walkPos 0 ω s 0 = 0) t
  have hne : Nat.findGreatest (fun s => walkPos 0 ω s 0 = 0) t ≠ t := by
    intro h
    rw [h] at ha0
    omega
  exact Set.mem_iUnion.mpr ⟨_, hω, ha0, lt_of_le_of_ne hat hne,
    fun s hs1 hs2 => Nat.findGreatest_is_greatest hs1 hs2⟩

private theorem outR_lastZero_subset (n : ℕ) {B : Set (Site 2)} (hB : B ⊆ axisSet {j | 0 ≤ j})
    (a t : ℕ) :
    outR n B t ∩ lastZero a t ⊆ reflectOn a t ⁻¹' (outL n B t ∩ lastZero a t) := by
  rintro ω ⟨⟨⟨h1, h2, h3⟩, h4⟩, ha0, hat, hnz⟩
  have h4' : 0 < walkPos 0 ω t 0 := h4
  have hp := pos_of_lastZero hnz h4'
  have hz : ∀ s, a ≤ s → s ≤ t →
      walkPos 0 (reflectOn a t ω) s 0 = -walkPos 0 ω s 0 := by
    intro s hs1 hs2
    rw [walkPos_reflectOn_zero ω hs1 hs2, ha0]
    ring
  have hn : ∀ s ≤ t, euclidNorm (walkPos 0 (reflectOn a t ω) s) = euclidNorm (walkPos 0 ω s) := by
    intro s hs
    rcases le_total s a with h | h
    · rw [walkPos_reflectOn_le ω h]
    · rw [nrm_eq, nrm_eq, hz s h hs, walkPos_reflectOn_one]
      push_cast
      ring_nf
  refine ⟨⟨⟨?_, fun s hs => ?_, fun s hs1 hs2 => ?_⟩, ?_⟩, ?_, hat, fun s hs1 hs2 => ?_⟩
  · rw [hn t le_rfl]; exact h1
  · rw [hn s hs.le]; exact h2 s hs
  · rcases le_or_gt s a with h | h
    · rw [walkPos_reflectOn_le ω h]; exact h3 s hs1 hs2
    · intro hB'
      have h0 : (0 : ℤ) ≤ walkPos 0 (reflectOn a t ω) s 0 := (hB hB').2
      rw [hz s h.le hs2.le] at h0
      have := hp s h hs2.le
      omega
  · show walkPos 0 (reflectOn a t ω) t 0 ≤ 0
    rw [hz t hat.le le_rfl]
    omega
  · show walkPos 0 (reflectOn a t ω) a 0 = 0
    rw [walkPos_reflectOn_le ω le_rfl, ha0]
  · rw [hz s hs1.le hs2]
    exact neg_ne_zero.mpr (hnz s hs1 hs2)

private theorem pathLaw_outR_le (n : ℕ) {B : Set (Site 2)} (hB : B ⊆ axisSet {j | 0 ≤ j}) :
    pathLaw 2 (⋃ t, outR n B t) ≤ pathLaw 2 (⋃ t, outL n B t) := by
  let QL : ℕ × ℕ → Set (ℕ → Dir 2) := fun p => outL n B p.2 ∩ lastZero p.1 p.2
  have hmeas : ∀ p, MeasurableSet (QL p) := fun p =>
    (dependsOnFirst_outL_lastZero n B p.1 p.2).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint QL) := by
    rintro ⟨a, t⟩ ⟨a', t'⟩ hne
    by_cases htt : t = t'
    · subst htt
      have haa : a ≠ a' := fun h => hne (by rw [h])
      rw [Function.onFun, Set.disjoint_left]
      rintro ω ⟨-, h0, ht, hnz⟩ ⟨-, h0', ht', hnz'⟩
      rcases lt_or_gt_of_ne haa with h | h
      · exact hnz a' h ht'.le h0'
      · exact hnz' a h ht.le h0
    · exact (firstOut_disjoint n B htt).mono
        (fun _ h => h.1.1) (fun _ h => h.1.1)
  calc pathLaw 2 (⋃ t, outR n B t)
      ≤ pathLaw 2 (⋃ p : ℕ × ℕ, outR n B p.2 ∩ lastZero p.1 p.2) := by
        refine measure_mono (Set.iUnion_subset fun t => ?_)
        refine (outR_subset n B t).trans (Set.iUnion_subset fun a => ?_)
        exact Set.subset_iUnion (fun p : ℕ × ℕ => outR n B p.2 ∩ lastZero p.1 p.2) (a, t)
    _ ≤ ∑' p : ℕ × ℕ, pathLaw 2 (outR n B p.2 ∩ lastZero p.1 p.2) := measure_iUnion_le _
    _ ≤ ∑' p : ℕ × ℕ, pathLaw 2 (QL p) := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        calc pathLaw 2 (outR n B p.2 ∩ lastZero p.1 p.2)
            ≤ pathLaw 2 (reflectOn p.1 p.2 ⁻¹' QL p) :=
              measure_mono (outR_lastZero_subset n hB p.1 p.2)
          _ = pathLaw 2 (QL p) :=
              (measurePreserving_reflectOn p.1 p.2).measure_preimage (hmeas p).nullMeasurableSet
    _ = pathLaw 2 (⋃ p, QL p) := (measure_iUnion hdisj hmeas).symm
    _ ≤ pathLaw 2 (⋃ t, outL n B t) :=
        measure_mono (Set.iUnion_subset fun p =>
          Set.inter_subset_left.trans (Set.subset_iUnion (fun t => outL n B t) p.2))

/-! ### Proposition 12 (a) -/

private theorem exitsWeak_le_strip {n : ℕ} (hn : 3 ≤ n) {B : Set (Site 2)}
    (hB : B ⊆ axisSet {j | 0 ≤ j}) :
    prob (exitsWeakBefore n B 0) ≤ 4 * prob (stripExitsBefore ((n / 3 : ℕ) : ℝ) B 0) := by
  have h : pathLaw 2 (exitsWeakBefore n B 0) ≤
      4 * pathLaw 2 (stripExitsBefore ((n / 3 : ℕ) : ℝ) B 0) :=
    calc pathLaw 2 (exitsWeakBefore n B 0)
        ≤ pathLaw 2 (⋃ t, outL n B t) + pathLaw 2 (⋃ t, outR n B t) :=
          (measure_mono (exitsWeakBefore_subset_out n B)).trans (measure_union_le _ _)
      _ ≤ pathLaw 2 (⋃ t, outL n B t) + pathLaw 2 (⋃ t, outL n B t) :=
          add_le_add le_rfl (pathLaw_outR_le n hB)
      _ = 2 * pathLaw 2 (⋃ t, outL n B t) := (two_mul _).symm
      _ ≤ 2 * (2 * pathLaw 2 (stripExitsBefore ((n / 3 : ℕ) : ℝ) B 0)) := by
          gcongr; exact pathLaw_outL_le hn hB
      _ = 4 * pathLaw 2 (stripExitsBefore ((n / 3 : ℕ) : ℝ) B 0) := by ring
  unfold prob
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (ne_top' _)) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this

private theorem strip_subset_exitsWeak (n : ℕ) (B : Set (Site 2)) :
    stripExitsBefore n B 0 ⊆ exitsWeakBefore n B 0 := by
  rintro ω ⟨t, ht, hB⟩
  exact ⟨t, le_nrm_of_le_abs (Nat.cast_nonneg n) ht, fun s h1 h2 => hB s h1 h2.le⟩

private theorem exitsWeak_anti {B B' : Set (Site 2)} (h : B ⊆ B') (r : ℝ) (x : Site 2) :
    exitsWeakBefore r B' x ⊆ exitsWeakBefore r B x := by
  rintro ω ⟨t, ht, hB⟩
  exact ⟨t, ht, fun s h1 h2 hs => hB s h1 h2 (h hs)⟩

private theorem prob_mono' {E F : Set (ℕ → Dir 2)} (h : E ⊆ F) : prob E ≤ prob F :=
  ENNReal.toReal_mono (ne_top' _) (measure_mono h)

private theorem prob_strip_pos_eq_neg (n : ℕ) :
    prob (stripExitsBefore n (axisSet {j | 0 < j}) 0) =
      prob (stripExitsBefore n (axisSet {j | j < 0}) 0) := by
  have he : revNeg 0 ⁻¹' stripExitsBefore n (axisSet {j | 0 < j}) 0 =
      stripExitsBefore n (axisSet {j | j < 0}) 0 := by
    ext ω
    simp only [Set.mem_preimage, mem_stripExitsBefore_iff, walkPos_revNeg_zero,
      Pi.neg_apply, abs_neg, axisSet, Set.mem_setOf_eq]
    simp only [neg_eq_zero, Left.neg_pos_iff]
  unfold prob
  rw [← he, (measurePreserving_revNeg 0).measure_preimage
    (measurableSet_stripExitsBefore _ _ _).nullMeasurableSet]

/-- The upper bound of (a) from a strip bound at a third of the radius. -/
private theorem upper_of_strip {B : Set (Site 2)} (hB : B ⊆ axisSet {j | 0 ≤ j})
    {c₂ : ℝ} (hc₂ : 0 < c₂) {N₀ : ℕ}
    (hs : ∀ m : ℕ, N₀ ≤ m → prob (stripExitsBefore m B 0) ≤ c₂ / Real.sqrt m) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      prob (exitsWeakBefore n B 0) ≤ 12 * c₂ / Real.sqrt n := by
  refine ⟨3 * N₀ + 3, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := by omega
  have hm : N₀ ≤ n / 3 := by omega
  have hm1 : 1 ≤ n / 3 := by omega
  have h9 : (n : ℝ) ≤ 9 * ((n / 3 : ℕ) : ℝ) := by
    have : n ≤ 9 * (n / 3) := by omega
    exact_mod_cast this
  have hmpos : (0 : ℝ) < ((n / 3 : ℕ) : ℝ) := by exact_mod_cast hm1
  have hsq : Real.sqrt n ≤ 3 * Real.sqrt ((n / 3 : ℕ) : ℝ) := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num] at h9
    calc Real.sqrt n ≤ Real.sqrt (3 ^ 2 * ((n / 3 : ℕ) : ℝ)) := Real.sqrt_le_sqrt h9
      _ = 3 * Real.sqrt ((n / 3 : ℕ) : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hspos : 0 < Real.sqrt ((n / 3 : ℕ) : ℝ) := Real.sqrt_pos.mpr hmpos
  have hnpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  calc prob (exitsWeakBefore n B 0) ≤ 4 * prob (stripExitsBefore ((n / 3 : ℕ) : ℝ) B 0) :=
        exitsWeak_le_strip hn3 hB
    _ ≤ 4 * (c₂ / Real.sqrt ((n / 3 : ℕ) : ℝ)) := by gcongr; exact hs _ hm
    _ ≤ 12 * c₂ / Real.sqrt n := by
        rw [mul_div_assoc', div_le_div_iff₀ hspos hnpos]
        nlinarith

/-- **Proposition 12 (a)**, nonnegative half-axis: the probability of leaving the disk of
radius `n` no later than the first positive-time visit to `{(j, 0) : j ≥ 0}` is comparable
to `1 / √n`. -/
theorem exitsWeak_halfLine_nonneg :
    Asymp (fun n => exitsWeakBefore n (axisSet {j | 0 ≤ j}) 0) (fun n => Real.sqrt n) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, N₀, hN₀⟩ := strip_halfLine_nonneg
  obtain ⟨N₁, hN₁⟩ := upper_of_strip (B := axisSet {j | 0 ≤ j}) subset_rfl
    hc₂ (N₀ := N₀) fun m hm => (hN₀ m hm).2
  refine ⟨c₁, 12 * c₂, hc₁, by positivity, max N₀ N₁,
    fun n hn => ⟨?_, hN₁ n (le_of_max_le_right hn)⟩⟩
  exact (hN₀ n (le_of_max_le_left hn)).1.trans (prob_mono' (strip_subset_exitsWeak n _))

/-- **Proposition 12 (a)**, positive half-axis: the probability of leaving the disk of radius
`n` no later than the first positive-time visit to `{(j, 0) : j > 0}` is comparable to
`1 / √n`. -/
theorem exitsWeak_halfLine_pos :
    Asymp (fun n => exitsWeakBefore n (axisSet {j | 0 < j}) 0) (fun n => Real.sqrt n) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, N₀, hN₀⟩ := strip_halfLine_nonneg
  obtain ⟨d₁, d₂, hd₁, hd₂, M₀, hM₀⟩ := strip_halfLine_neg
  have hsub : axisSet {j : ℤ | 0 < j} ⊆ axisSet {j | 0 ≤ j} :=
    fun z hz => ⟨hz.1, show (0 : ℤ) ≤ z 0 from le_of_lt hz.2⟩
  obtain ⟨N₁, hN₁⟩ := upper_of_strip (B := axisSet {j | 0 < j}) hsub
    hd₂ (N₀ := M₀) fun m hm => by rw [prob_strip_pos_eq_neg]; exact (hM₀ m hm).2
  refine ⟨c₁, 12 * d₂, hc₁, by positivity, max N₀ N₁,
    fun n hn => ⟨?_, hN₁ n (le_of_max_le_right hn)⟩⟩
  exact (hN₀ n (le_of_max_le_left hn)).1.trans
    (prob_mono' ((strip_subset_exitsWeak n _).trans (exitsWeak_anti hsub _ _)))

/-! ### Probabilities -/

private theorem prob_nonneg' {E : Set (ℕ → Dir 2)} : 0 ≤ prob E := ENNReal.toReal_nonneg

private theorem prob_le_one' {E : Set (ℕ → Dir 2)} : prob E ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

private theorem prob_union' {E F : Set (ℕ → Dir 2)} (h : Disjoint E F) (hF : MeasurableSet F) :
    prob (E ∪ F) = prob E + prob F := by
  unfold prob
  rw [measure_union h hF, ENNReal.toReal_add (ne_top' _) (ne_top' _)]

private theorem nrm_sub_comm (y z : Site 2) : euclidNorm (y - z) = euclidNorm (z - y) := by
  rw [nrm_eq, nrm_eq]
  simp only [Pi.sub_apply, Int.cast_sub]
  ring_nf

/-- The Markov property at a family of disjoint stopping events: if the walk is restarted at
time `t` on the event `S t` from a point of `Y`, and every continuation event `C w`, `w ∈ Y`, has
probability at most `M`, then the probability of the continued event is at most `M` times the
probability of stopping. -/
private theorem markov_sup (x : Site 2) {S : ℕ → Set (ℕ → Dir 2)}
    (hS : ∀ t, DependsOnFirst t (S t)) (hdisj : Pairwise (Function.onFun Disjoint S))
    (C : Site 2 → Set (ℕ → Dir 2)) (hC : ∀ w, MeasurableSet (C w)) {Y : Set (Site 2)}
    {M : ENNReal} (hY : ∀ t, ∀ ω ∈ S t, walkPos x ω t ∈ Y) (hM : ∀ w ∈ Y, pathLaw 2 (C w) ≤ M) :
    pathLaw 2 (⋃ t, S t ∩ {ω | shiftBy t ω ∈ C (walkPos x ω t)}) ≤
      M * pathLaw 2 (⋃ t, S t) := by
  have hSm : ∀ t, MeasurableSet (S t) := fun t => (hS t).measurableSet
  have hpiece : ∀ t (w : Site 2), DependsOnFirst t (S t ∩ {ω | walkPos x ω t = w}) :=
    fun t w ω ω' h => and_congr (hS t ω ω' h)
      (by simp only [Set.mem_setOf_eq, walkPos_congr' x h le_rfl])
  have hsub : ⋃ t, S t ∩ {ω | shiftBy t ω ∈ C (walkPos x ω t)} ⊆
      ⋃ t, ⋃ w : Site 2, (S t ∩ {ω | walkPos x ω t = w}) ∩ shiftBy t ⁻¹' C w := by
    intro ω hω
    obtain ⟨t, h1, h2⟩ := Set.mem_iUnion.mp hω
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨walkPos x ω t, ⟨h1, rfl⟩, h2⟩⟩
  have hterm : ∀ t w, pathLaw 2 ((S t ∩ {ω | walkPos x ω t = w}) ∩ shiftBy t ⁻¹' C w) ≤
      pathLaw 2 (S t ∩ {ω | walkPos x ω t = w}) * M := by
    intro t w
    rw [markov_split (hpiece t w) (hC w)]
    by_cases hw : w ∈ Y
    · gcongr
      exact hM w hw
    · have : S t ∩ {ω | walkPos x ω t = w} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun ω hω => hw ?_
        rw [← hω.2]
        exact hY t ω hω.1
      simp [this]
  have hrow : ∀ t, ∑' w : Site 2, pathLaw 2 (S t ∩ {ω | walkPos x ω t = w}) = pathLaw 2 (S t) := by
    intro t
    rw [← measure_iUnion]
    · congr 1
      ext ω
      simp
    · intro w w' h
      exact Set.disjoint_left.mpr fun ω h1 h2 => h (h1.2.symm.trans h2.2)
    · intro w
      exact (hpiece t w).measurableSet
  calc pathLaw 2 (⋃ t, S t ∩ {ω | shiftBy t ω ∈ C (walkPos x ω t)})
      ≤ ∑' t, ∑' w, pathLaw 2 ((S t ∩ {ω | walkPos x ω t = w}) ∩ shiftBy t ⁻¹' C w) :=
        (measure_mono hsub).trans ((measure_iUnion_le _).trans
          (ENNReal.tsum_le_tsum fun t => measure_iUnion_le _))
    _ ≤ ∑' t, ∑' w, pathLaw 2 (S t ∩ {ω | walkPos x ω t = w}) * M :=
        ENNReal.tsum_le_tsum fun t => ENNReal.tsum_le_tsum fun w => hterm t w
    _ = M * pathLaw 2 (⋃ t, S t) := by
        simp_rw [ENNReal.tsum_mul_right, hrow]
        rw [measure_iUnion hdisj hSm, mul_comm]

/-! ### Visits to a point before a set -/

section Visits

variable (N : Set (Site 2)) (a : Site 2)

/-- The walk from `x` is at `a` at time `t`, with no visit to `N` at the times `1, ..., t`. -/
private def visit (x : Site 2) (t : ℕ) : Set (ℕ → Dir 2) :=
  {ω | walkPos x ω t = a ∧ ∀ s, 1 ≤ s → s ≤ t → walkPos x ω s ∉ N}

/-- The first visit to `a` at a positive time is at time `u`, with no earlier visit to `N`. -/
private def firstVisit (x : Site 2) (u : ℕ) : Set (ℕ → Dir 2) :=
  {ω | 1 ≤ u ∧ walkPos x ω u = a ∧
    ∀ s, 1 ≤ s → s < u → walkPos x ω s ∉ N ∧ walkPos x ω s ≠ a}

/-- The walk from `x` visits `a` with no visit to `N` at the positive times up to then. -/
private def hitA (x : Site 2) : Set (ℕ → Dir 2) := ⋃ t, visit N a x t

private theorem dependsOnFirst_visit (x : Site 2) (t : ℕ) : DependsOnFirst t (visit N a x t) :=
  dependsOnFirst_of x fun ω ω' h hω =>
    ⟨by rw [← h t le_rfl]; exact hω.1, fun s hs1 hs2 => by rw [← h s hs2]; exact hω.2 s hs1 hs2⟩

private theorem dependsOnFirst_firstVisit (x : Site 2) (u : ℕ) :
    DependsOnFirst u (firstVisit N a x u) :=
  dependsOnFirst_of x fun ω ω' h hω =>
    ⟨hω.1, by rw [← h u le_rfl]; exact hω.2.1,
      fun s hs1 hs2 => by rw [← h s hs2.le]; exact hω.2.2 s hs1 hs2⟩

private theorem measurableSet_hitA (x : Site 2) : MeasurableSet (hitA N a x) :=
  MeasurableSet.iUnion fun t => (dependsOnFirst_visit N a x t).measurableSet

private theorem firstVisit_disjoint (x : Site 2) {u u' : ℕ} (h : u ≠ u') :
    Disjoint (firstVisit N a x u) (firstVisit N a x u') := by
  rw [Set.disjoint_left]
  rintro ω ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
  rcases lt_or_gt_of_ne h with h | h
  · exact (h3' u h1 h).2 h2
  · exact (h3 u' h1' h).2 h2'

private theorem shift_mem_hitA {x : Site 2} {ω : ℕ → Dir 2} {t t₁ : ℕ} (htt : t ≤ t₁)
    (h1 : walkPos x ω t₁ = a) (h2 : ∀ s, 1 ≤ s → s ≤ t₁ → walkPos x ω s ∉ N) :
    shiftBy t ω ∈ hitA N a (walkPos x ω t) := by
  refine Set.mem_iUnion.mpr ⟨t₁ - t, ?_, fun s hs1 hs2 => ?_⟩
  · rw [← walkPos_shift, Nat.add_sub_cancel' htt]
    exact h1
  · rw [← walkPos_shift]
    exact h2 (t + s) (by omega) (by omega)

private theorem visit_subset (x : Site 2) {t : ℕ} (ht : 1 ≤ t) :
    visit N a x t ⊆
      ⋃ u ∈ Finset.Icc 1 t, firstVisit N a x u ∩ shiftBy u ⁻¹' visit N a a (t - u) := by
  classical
  rintro ω ⟨h1, h2⟩
  have hex : ∃ u, 1 ≤ u ∧ walkPos x ω u = a := ⟨t, ht, h1⟩
  have hu := Nat.find_spec hex
  have hut : Nat.find hex ≤ t := Nat.find_min' hex ⟨ht, h1⟩
  have e : ∀ k, walkPos a (shiftBy (Nat.find hex) ω) k = walkPos x ω (Nat.find hex + k) := by
    intro k
    rw [walkPos_shift, hu.2]
  refine Set.mem_iUnion₂.mpr ⟨Nat.find hex, Finset.mem_Icc.mpr ⟨hu.1, hut⟩,
    ⟨hu.1, hu.2, fun s hs1 hs2 =>
      ⟨h2 s hs1 (by omega), fun hs => Nat.find_min hex hs2 ⟨hs1, hs⟩⟩⟩, ?_, fun s hs1 hs2 => ?_⟩
  · show walkPos a (shiftBy (Nat.find hex) ω) (t - Nat.find hex) = a
    rw [e, Nat.add_sub_cancel' hut]
    exact h1
  · show walkPos a (shiftBy (Nat.find hex) ω) s ∉ N
    rw [e]
    exact h2 _ (by omega) (by omega)

private theorem prob_visit_le (x : Site 2) {t : ℕ} (ht : 1 ≤ t) :
    prob (visit N a x t) ≤
      ∑ u ∈ Finset.Icc 1 t, prob (firstVisit N a x u) * prob (visit N a a (t - u)) := by
  have h1 : pathLaw 2 (visit N a x t) ≤ ∑ u ∈ Finset.Icc 1 t,
      pathLaw 2 (firstVisit N a x u) * pathLaw 2 (visit N a a (t - u)) :=
    calc pathLaw 2 (visit N a x t)
        ≤ pathLaw 2 (⋃ u ∈ Finset.Icc 1 t,
            firstVisit N a x u ∩ shiftBy u ⁻¹' visit N a a (t - u)) :=
          measure_mono (visit_subset N a x ht)
      _ ≤ ∑ u ∈ Finset.Icc 1 t,
            pathLaw 2 (firstVisit N a x u ∩ shiftBy u ⁻¹' visit N a a (t - u)) :=
          measure_biUnion_finset_le _ _
      _ = _ := Finset.sum_congr rfl fun u _ =>
          markov_split (dependsOnFirst_firstVisit N a x u)
            (dependsOnFirst_visit N a a (t - u)).measurableSet
  have hne : ∀ u ∈ Finset.Icc 1 t,
      pathLaw 2 (firstVisit N a x u) * pathLaw 2 (visit N a a (t - u)) ≠ ⊤ :=
    fun u _ => ENNReal.mul_ne_top (ne_top' _) (ne_top' _)
  have h2 := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hne) h1
  rw [ENNReal.toReal_sum hne] at h2
  unfold prob
  simpa only [ENNReal.toReal_mul] using h2

private theorem sum_prob_firstVisit_le (x : Site 2) (T : ℕ) {E : Set (ℕ → Dir 2)}
    (hE : ∀ u, firstVisit N a x u ⊆ E) :
    ∑ u ∈ Finset.Icc 1 T, prob (firstVisit N a x u) ≤ prob E := by
  have h1 := measure_biUnion_finset (μ := pathLaw 2) (s := Finset.Icc 1 T) (f := firstVisit N a x)
    (fun u _ u' _ h => firstVisit_disjoint N a x h)
    fun u _ => (dependsOnFirst_firstVisit N a x u).measurableSet
  unfold prob
  rw [← ENNReal.toReal_sum fun u _ => ne_top' _, ← h1]
  exact ENNReal.toReal_mono (ne_top' _) (measure_mono (Set.iUnion₂_subset fun u _ => hE u))

end Visits

private theorem sum_range_succ_Icc (f : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), f t = f 0 + ∑ t ∈ Finset.Icc 1 T, f t := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos T)]
  congr 1

private theorem sum_conv_le (F G : ℕ → ℝ) (hF : ∀ u, 0 ≤ F u) (hG : ∀ v, 0 ≤ G v) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, ∑ u ∈ Finset.Icc 1 t, F u * G (t - u) ≤
      (∑ u ∈ Finset.Icc 1 T, F u) * ∑ v ∈ Finset.range (T + 1), G v := by
  calc ∑ t ∈ Finset.Icc 1 T, ∑ u ∈ Finset.Icc 1 t, F u * G (t - u)
      = ∑ u ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc u T, F u * G (t - u) := by
        refine Finset.sum_comm' fun t u => ?_
        simp only [Finset.mem_Icc]
        omega
    _ ≤ ∑ u ∈ Finset.Icc 1 T, F u * ∑ v ∈ Finset.range (T + 1), G v := by
        refine Finset.sum_le_sum fun u _ => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (hF u)
        rw [← Finset.sum_image (g := fun t => t - u) (f := G) fun t ht t' ht' h => ?_]
        · refine Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => ?_) fun v _ _ => hG v
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
          simp only [Finset.mem_Icc] at ht
          simp only [Finset.mem_range]
          omega
        · simp only [Finset.mem_coe, Finset.mem_Icc] at ht ht'
          simp only at h
          omega
    _ = (∑ u ∈ Finset.Icc 1 T, F u) * ∑ v ∈ Finset.range (T + 1), G v :=
        (Finset.sum_mul _ _ _).symm

section Renewal

variable {N : Set (Site 2)} {a : Site 2}

/-- The expected number of visits to `a` from `a` before `N` is at most `1 / (1 - q)`, where
`q` bounds the probability of returning to `a` before `N`. -/
private theorem sum_visit_self_le {q : ℝ} (hq : prob (entersAt ({a} ∪ N) a a) ≤ q)
    (hq1 : q < 1) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), prob (visit N a a t) ≤ 1 / (1 - q) := by
  have hf : ∑ u ∈ Finset.Icc 1 T, prob (firstVisit N a a u) ≤ q := by
    refine (sum_prob_firstVisit_le N a a T fun u ω hω => ?_).trans hq
    refine ⟨u, hω.1, hω.2.1, fun s hs1 hs2 hs => ?_⟩
    rcases hs with hs | hs
    · exact (hω.2.2 s hs1 hs2).2 hs
    · exact (hω.2.2 s hs1 hs2).1 hs
  have e1 := sum_range_succ_Icc (fun t => prob (visit N a a t)) T
  have h0 : prob (visit N a a 0) ≤ 1 := prob_le_one'
  have hstep : ∑ t ∈ Finset.Icc 1 T, prob (visit N a a t) ≤
      ∑ t ∈ Finset.Icc 1 T, ∑ u ∈ Finset.Icc 1 t,
        prob (firstVisit N a a u) * prob (visit N a a (t - u)) :=
    Finset.sum_le_sum fun t ht => prob_visit_le N a a (Finset.mem_Icc.mp ht).1
  have hconv := sum_conv_le (fun u => prob (firstVisit N a a u)) (fun v => prob (visit N a a v))
    (fun _ => prob_nonneg') (fun _ => prob_nonneg') T
  have hA0 : 0 ≤ ∑ t ∈ Finset.range (T + 1), prob (visit N a a t) :=
    Finset.sum_nonneg fun _ _ => prob_nonneg'
  have hfA := mul_le_mul_of_nonneg_right hf hA0
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- The expected number of visits to `a` from `x ≠ a` before `N` is at most the probability of
visiting `a` before `N` times `1 / (1 - q)`. -/
private theorem sum_visit_le (ha : a ∉ N) {x : Site 2} (hx : x ≠ a) {q : ℝ}
    (hq : prob (entersAt ({a} ∪ N) a a) ≤ q) (hq1 : q < 1) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), prob (visit N a x t) ≤ prob (hitA N a x) * (1 / (1 - q)) := by
  have he : ∑ u ∈ Finset.Icc 1 T, prob (firstVisit N a x u) ≤ prob (hitA N a x) := by
    refine sum_prob_firstVisit_le N a x T fun u ω hω => Set.mem_iUnion.mpr ⟨u, hω.2.1, ?_⟩
    intro s hs1 hs2
    rcases lt_or_eq_of_le hs2 with h | rfl
    · exact (hω.2.2 s hs1 h).1
    · rw [hω.2.1]; exact ha
  have e1 := sum_range_succ_Icc (fun t => prob (visit N a x t)) T
  have h0 : visit N a x 0 = ∅ :=
    Set.eq_empty_of_forall_notMem fun ω hω => hx (by simpa [walkPos] using hω.1)
  have hstep : ∑ t ∈ Finset.Icc 1 T, prob (visit N a x t) ≤
      ∑ t ∈ Finset.Icc 1 T, ∑ u ∈ Finset.Icc 1 t,
        prob (firstVisit N a x u) * prob (visit N a a (t - u)) :=
    Finset.sum_le_sum fun t ht => prob_visit_le N a x (Finset.mem_Icc.mp ht).1
  have hconv := sum_conv_le (fun u => prob (firstVisit N a x u)) (fun v => prob (visit N a a v))
    (fun _ => prob_nonneg') (fun _ => prob_nonneg') T
  have hA := sum_visit_self_le hq hq1 T
  have hA0 : 0 ≤ ∑ t ∈ Finset.range (T + 1), prob (visit N a a t) :=
    Finset.sum_nonneg fun _ _ => prob_nonneg'
  have hprod := mul_le_mul he hA hA0 prob_nonneg'
  rw [h0, prob, measure_empty, ENNReal.toReal_zero] at e1
  linarith

/-- Path reversal: the walk from `a` entering `N` at the origin is the reversal of a walk from
the origin to `a` that avoids `N` at the times `1, ..., t`. -/
private theorem prob_entersAt_le (ha : a ∉ N) (h0 : (0 : Site 2) ∈ N) {B : ℝ} (hB : 0 ≤ B)
    (hsum : ∀ T, ∑ t ∈ Finset.range (T + 1), prob (visit N a 0 t) ≤ B) :
    prob (entersAt N 0 a) ≤ B := by
  let F : ℕ → Set (ℕ → Dir 2) := fun t =>
    {ω | 1 ≤ t ∧ walkPos a ω t = 0 ∧ ∀ s, 1 ≤ s → s < t → walkPos a ω s ∉ N}
  have he : entersAt N 0 a = ⋃ t, F t := by
    ext ω
    simp only [Set.mem_iUnion]
    exact Iff.rfl
  have hFm : ∀ t, MeasurableSet (F t) := fun t => DependsOnFirst.measurableSet (j := t)
    (dependsOnFirst_of a fun ω ω' h hω => ⟨hω.1, by rw [← h t le_rfl]; exact hω.2.1,
      fun s hs1 hs2 => by rw [← h s hs2.le]; exact hω.2.2 s hs1 hs2⟩)
  have hFd : Pairwise (Function.onFun Disjoint F) := by
    intro t t' htt
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    rcases lt_or_gt_of_ne htt with h | h
    · exact h3' t h1 h (h2 ▸ h0)
    · exact h3 t' h1' h (h2' ▸ h0)
  have hrev : ∀ t, F t ⊆ revNeg t ⁻¹' visit N a 0 t := by
    rintro t ω ⟨ht, h1, h2⟩
    have hWt : walkPos 0 ω t = -a := by
      rw [walkPos_eq_add'] at h1
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h1
    have hk : ∀ k ≤ t, walkPos 0 (revNeg t ω) k = walkPos a ω (t - k) := by
      intro k hk
      rw [walkPos_revNeg ω t hk, hWt, walkPos_eq_add' a]
      abel
    refine ⟨?_, fun s hs1 hs2 => ?_⟩
    · rw [hk t le_rfl, Nat.sub_self]
      simp [walkPos]
    · rw [hk s hs2]
      rcases Nat.eq_zero_or_pos (t - s) with h | h
      · rw [h]
        simpa [walkPos] using ha
      · exact h2 (t - s) h (by omega)
  have hle : ∀ t, pathLaw 2 (F t) ≤ pathLaw 2 (visit N a 0 t) := fun t =>
    (measure_mono (hrev t)).trans_eq ((measurePreserving_revNeg t).measure_preimage
      (dependsOnFirst_visit N a 0 t).measurableSet.nullMeasurableSet)
  have htsum : ∑' t, pathLaw 2 (F t) ≤ ENNReal.ofReal B := by
    refine ENNReal.tsum_le_of_sum_range_le fun T => ?_
    calc ∑ t ∈ Finset.range T, pathLaw 2 (F t)
        ≤ ∑ t ∈ Finset.range (T + 1), pathLaw 2 (visit N a 0 t) :=
          (Finset.sum_le_sum fun t _ => hle t).trans
            (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ T)))
      _ = ENNReal.ofReal (∑ t ∈ Finset.range (T + 1), prob (visit N a 0 t)) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => prob_nonneg']
          exact Finset.sum_congr rfl fun t _ => (ENNReal.ofReal_toReal (ne_top' _)).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hsum T)
  rw [he]
  unfold prob
  rw [measure_iUnion hFd hFm]
  exact ENNReal.toReal_le_of_le_ofReal hB htsum

end Renewal

/-! ### Proposition 12 (b) -/

private theorem axisPt_neg_notMem {n : ℕ} (hn : 1 ≤ n) :
    axisPt (-(n : ℤ)) ∉ axisSet {j | 0 ≤ j} := by
  rintro ⟨-, h⟩
  have h' : (0 : ℤ) ≤ -(n : ℤ) := by simpa [axisPt] using h
  omega

private theorem nrm_axisPt_neg (n : ℕ) : euclidNorm (axisPt (-(n : ℤ))) = n := by
  rw [nrm_eq]
  simp [axisPt]

private theorem zero_mem_halfAxis : (0 : Site 2) ∈ axisSet {j | 0 ≤ j} := ⟨rfl, by simp⟩

private theorem isDense_halfAxis : IsDense (axisSet {j | 0 ≤ j}) := by
  intro j
  refine ⟨axisPt j, ⟨by simp [axisPt], by simp [axisPt]⟩, ?_⟩
  have h : euclidNorm (axisPt j) = j := by
    rw [nrm_eq]
    simp [axisPt]
  rw [h]
  exact ⟨le_rfl, by linarith⟩

/-- The circle of radius `n / 3` and the inner side of the circle of radius `2 n`, off the
nonnegative half-axis. -/
private def restart (n : ℕ) : Set (Site 2) :=
  {y | y ∉ axisSet {j | 0 ≤ j} ∧
    ((((n / 3 : ℕ) : ℝ) ≤ euclidNorm y ∧ euclidNorm y < ((n / 3 : ℕ) : ℝ) + 1) ∨
      (2 * (n : ℝ) - 1 ≤ euclidNorm y ∧ euclidNorm y < 2 * n))}

/-- The walk from `y` is in the disk of radius `2 n` at time `t`, after having left the disk of
radius `4 n`. -/
private def back (n : ℕ) (y : Site 2) (ω : ℕ → Dir 2) (t : ℕ) : Prop :=
  euclidNorm (walkPos y ω t) < 2 * n ∧ ∃ r < t, 4 * (n : ℝ) ≤ euclidNorm (walkPos y ω r)

/-- The first return of the walk from `y` to the disk of radius `2 n` after leaving the disk of
radius `4 n` is at time `t`, with no visit to the half-axis at the times `1, ..., t`. -/
private def reentry (n : ℕ) (y : Site 2) (t : ℕ) : Set (ℕ → Dir 2) :=
  {ω | back n y ω t ∧ (∀ t' < t, ¬back n y ω t') ∧
    ∀ s, 1 ≤ s → s ≤ t → walkPos y ω s ∉ axisSet {j | 0 ≤ j}}

private theorem back_congr {n : ℕ} {y : Site 2} {ω ω' : ℕ → Dir 2} {t : ℕ}
    (h : ∀ s ≤ t, walkPos y ω s = walkPos y ω' s) {t' : ℕ} (ht : t' ≤ t) :
    back n y ω t' ↔ back n y ω' t' := by
  unfold back
  rw [h t' ht]
  constructor
  · rintro ⟨h1, r, hr, h2⟩
    exact ⟨h1, r, hr, by rw [← h r (by omega)]; exact h2⟩
  · rintro ⟨h1, r, hr, h2⟩
    exact ⟨h1, r, hr, by rw [h r (by omega)]; exact h2⟩

private theorem dependsOnFirst_reentry (n : ℕ) (y : Site 2) (t : ℕ) :
    DependsOnFirst t (reentry n y t) :=
  dependsOnFirst_of y fun ω ω' h hω =>
    ⟨(back_congr h le_rfl).mp hω.1,
      fun t' ht' hb => hω.2.1 t' ht' ((back_congr h ht'.le).mpr hb),
      fun s hs1 hs2 => by rw [← h s hs2]; exact hω.2.2 s hs1 hs2⟩

private theorem reentry_disjoint (n : ℕ) (y : Site 2) :
    Pairwise (Function.onFun Disjoint (reentry n y)) := by
  intro t t' h
  rw [Function.onFun, Set.disjoint_left]
  rintro ω ⟨h1, h2, -⟩ ⟨h1', h2', -⟩
  rcases lt_or_gt_of_ne h with h | h
  · exact h2' t h h1
  · exact h2 t' h h1'

private theorem reentry_mem (n : ℕ) (y : Site 2) (t : ℕ) (ω : ℕ → Dir 2)
    (hω : ω ∈ reentry n y t) : walkPos y ω t ∈ restart n := by
  obtain ⟨⟨h1, r, hr, h2⟩, h3, h4⟩ := hω
  have ht : 1 ≤ t := by omega
  refine ⟨h4 t ht le_rfl, Or.inr ⟨?_, h1⟩⟩
  have hprev : 2 * (n : ℝ) ≤ euclidNorm (walkPos y ω (t - 1)) := by
    rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt hr) with he | hlt
    · rw [← he]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · by_contra hc
      exact h3 (t - 1) (by omega) ⟨not_le.mp hc, r, hlt, h2⟩
  have := nrm_step_ge y ω (t - 1)
  rw [Nat.sub_add_cancel ht] at this
  linarith

private theorem reentry_subset (n : ℕ) (y : Site 2) (t : ℕ) :
    reentry n y t ⊆ exitsBefore ((4 * n : ℕ) : ℝ) (axisSet {j | 0 ≤ j}) y := by
  rintro ω ⟨⟨-, r, hr, h2⟩, -, h4⟩
  exact ⟨r, by push_cast; exact h2, fun s hs1 hs2 => h4 s hs1 (by omega)⟩

private theorem walkPos_sub' (y z : Site 2) (ω : ℕ → Dir 2) (s : ℕ) :
    walkPos (y - z) ω s = walkPos y ω s - z := by
  rw [walkPos_eq_add', walkPos_eq_add' y]
  abel

private theorem hitA_subset_restart {n : ℕ} (hn : 1 ≤ n) (y : Site 2) :
    hitA (axisSet {j | 0 ≤ j}) (axisPt (-(n : ℤ))) y ⊆
      hitsBefore {0} ((5 * n : ℕ) : ℝ) (y - axisPt (-(n : ℤ))) ∪
        ⋃ t, reentry n y t ∩
          {ω | shiftBy t ω ∈ hitA (axisSet {j | 0 ≤ j}) (axisPt (-(n : ℤ))) (walkPos y ω t)} := by
  classical
  intro ω hω
  obtain ⟨t₁, h1, h2⟩ := Set.mem_iUnion.mp hω
  have hna := nrm_axisPt_neg n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hfar : ∃ r ≤ t₁, 4 * (n : ℝ) ≤ euclidNorm (walkPos y ω r)
  · right
    obtain ⟨r, hr, hr2⟩ := hfar
    have hrt : r < t₁ := by
      rcases lt_or_eq_of_le hr with h | h
      · exact h
      · rw [h, h1, hna] at hr2
        linarith
    have hbt : back n y ω t₁ := ⟨by rw [h1, hna]; linarith, r, hrt, hr2⟩
    have hb : ∃ t, back n y ω t := ⟨t₁, hbt⟩
    obtain ⟨t₀, ht₀, hmin, ht⟩ : ∃ t₀, back n y ω t₀ ∧ (∀ t' < t₀, ¬back n y ω t') ∧ t₀ ≤ t₁ :=
      ⟨Nat.find hb, Nat.find_spec hb, fun t' ht' => Nat.find_min hb ht', Nat.find_min' hb hbt⟩
    have hm : ω ∈ reentry n y t₀ := ⟨ht₀, hmin, fun s hs1 hs2 => h2 s hs1 (hs2.trans ht)⟩
    have hs : shiftBy t₀ ω ∈ hitA (axisSet {j | 0 ≤ j}) (axisPt (-(n : ℤ))) (walkPos y ω t₀) :=
      shift_mem_hitA _ _ ht h1 h2
    exact Set.mem_iUnion.mpr ⟨t₀, hm, hs⟩
  · left
    replace hfar : ∀ r ≤ t₁, euclidNorm (walkPos y ω r) < 4 * n :=
      fun r hr => not_le.mp fun h => hfar ⟨r, hr, h⟩
    refine ⟨t₁, ?_, fun s hs => ?_⟩
    · show walkPos (y - axisPt (-(n : ℤ))) ω t₁ ∈ ({0} : Set (Site 2))
      rw [walkPos_sub', h1, sub_self]
      rfl
    · rw [walkPos_sub']
      have h3 := nrm_sub_le (walkPos y ω s) (axisPt (-(n : ℤ)))
      have h4 := hfar s hs
      rw [hna] at h3
      push_cast
      linarith

private theorem toReal_iSup_restart_le {n : ℕ} (hn : 6 ≤ n) {c7 c8 : ℝ} (hc7 : 0 < c7)
    (hc8 : 0 < c8)
    (h7 : ∀ y : Site 2, euclidNorm y < 2 * n → c7 ≤ prob (hitsBefore
      (shellPart (axisSet {j | 0 ≤ j}) (((4 * n : ℕ) : ℝ) / 4) (((4 * n : ℕ) : ℝ) / 2))
      ((4 * n : ℕ) : ℝ) y))
    (h8 : ∀ z : Site 2, ((5 * n : ℕ) : ℝ) / 10 ≤ euclidNorm z →
      euclidNorm z < 9 * ((5 * n : ℕ) : ℝ) / 10 →
      prob (hitsBefore {0} ((5 * n : ℕ) : ℝ) z) ≤ c8 / Real.log ((5 * n : ℕ) : ℝ)) :
    (⨆ y ∈ restart n, pathLaw 2 (hitA (axisSet {j | 0 ≤ j}) (axisPt (-(n : ℤ))) y)).toReal ≤
      c8 / Real.log ((5 * n : ℕ) : ℝ) / c7 := by
  set N0 : Set (Site 2) := axisSet {j | 0 ≤ j} with hN0
  set a : Site 2 := axisPt (-(n : ℤ)) with ha
  set M := ⨆ y ∈ restart n, pathLaw 2 (hitA N0 a y) with hM
  set L := Real.log ((5 * n : ℕ) : ℝ) with hL
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hLpos : 0 < L := Real.log_pos (by push_cast; linarith)
  have hε : 0 ≤ c8 / L := (div_pos hc8 hLpos).le
  have hc71 : c7 ≤ 1 := (h7 0 (by rw [euclidNorm_zero]; linarith)).trans prob_le_one'
  have hM1 : M ≤ 1 := iSup₂_le fun y _ => prob_le_one
  have hMtop : M ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hM1
  have hM0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  have hle : ∀ y ∈ restart n, pathLaw 2 (hitA N0 a y) ≤ M := fun y hy =>
    le_iSup₂ (f := fun y _ => pathLaw 2 (hitA N0 a y)) y hy
  have hna := nrm_axisPt_neg n
  have hstep : ∀ y ∈ restart n, prob (hitA N0 a y) ≤ c8 / L + M.toReal * (1 - c7) := by
    intro y hy
    obtain ⟨hyN, hyr⟩ := hy
    have hk : ((n / 3 : ℕ) : ℝ) ≤ n / 3 := Nat.cast_div_le
    have hy2 : euclidNorm y < 2 * n := by
      rcases hyr with h | h
      · linarith [h.2]
      · exact h.2
    have hyl : (n : ℝ) / 2 ≤ euclidNorm (y - a) := by
      rcases hyr with h | h
      · have := nrm_sub_ge a y
        rw [nrm_sub_comm a y, hna] at this
        linarith [h.2]
      · have := nrm_sub_ge y a
        rw [hna] at this
        linarith [h.1]
    have hyu : euclidNorm (y - a) < 3 * n := by
      have := nrm_sub_le y a
      rw [hna] at this
      linarith
    have h1 : pathLaw 2 (hitA N0 a y) ≤ pathLaw 2 (hitsBefore {0} ((5 * n : ℕ) : ℝ) (y - a)) +
        M * pathLaw 2 (exitsBefore ((4 * n : ℕ) : ℝ) N0 y) :=
      (measure_mono (hitA_subset_restart (by omega) y)).trans ((measure_union_le _ _).trans
        (add_le_add le_rfl ((markov_sup y (dependsOnFirst_reentry n y) (reentry_disjoint n y)
          (hitA N0 a) (measurableSet_hitA N0 a) (fun t ω hω => reentry_mem n y t ω hω) hle).trans
          (mul_le_mul_of_nonneg_left
            (measure_mono (Set.iUnion_subset fun t => reentry_subset n y t)) zero_le))))
    have h8' : prob (hitsBefore {0} ((5 * n : ℕ) : ℝ) (y - a)) ≤ c8 / L :=
      h8 _ (by push_cast; linarith) (by push_cast; linarith)
    have h7' : prob (exitsBefore ((4 * n : ℕ) : ℝ) N0 y) ≤ 1 - c7 := by
      have hd : Disjoint (exitsBefore ((4 * n : ℕ) : ℝ) N0 y) (hitsBefore
          (shellPart N0 (((4 * n : ℕ) : ℝ) / 4) (((4 * n : ℕ) : ℝ) / 2)) ((4 * n : ℕ) : ℝ) y) := by
        rw [Set.disjoint_left]
        rintro ω ⟨r, hr, hr2⟩ ⟨t', ht', ht'2⟩
        have htr : t' < r := by
          by_contra hc
          exact absurd (ht'2 r (not_lt.mp hc)) (not_lt.mpr hr)
        rcases Nat.eq_zero_or_pos t' with h0 | hpos
        · subst h0
          exact hyN (by simpa [walkPos] using ht'.1)
        · exact hr2 t' hpos htr.le ht'.1
      have hu := prob_union' hd (measurableSet_hitsBefore _ _ _)
      have h7y := h7 y hy2
      have h1 := prob_le_one' (E := exitsBefore ((4 * n : ℕ) : ℝ) N0 y ∪ hitsBefore
          (shellPart N0 (((4 * n : ℕ) : ℝ) / 4) (((4 * n : ℕ) : ℝ) / 2)) ((4 * n : ℕ) : ℝ) y)
      linarith
    have h1r := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨ne_top' _, ENNReal.mul_ne_top hMtop (ne_top' _)⟩) h1
    rw [ENNReal.toReal_add (ne_top' _) (ENNReal.mul_ne_top hMtop (ne_top' _)),
      ENNReal.toReal_mul] at h1r
    change prob _ ≤ prob _ + M.toReal * prob _ at h1r
    nlinarith [mul_le_mul_of_nonneg_left h7' hM0]
  have hnn : 0 ≤ c8 / L + M.toReal * (1 - c7) := add_nonneg hε (mul_nonneg hM0 (by linarith))
  have hMle : M ≤ ENNReal.ofReal (c8 / L + M.toReal * (1 - c7)) :=
    iSup₂_le fun y hy => (ENNReal.le_ofReal_iff_toReal_le (ne_top' _) hnn).mpr (hstep y hy)
  have hMr := ENNReal.toReal_le_of_le_ofReal hnn hMle
  rw [le_div_iff₀ hc7]
  nlinarith

/-- First exit from the disk of radius `k` at time `t`, with no visit to the half-axis at the
times `1, ..., t`. -/
private def exitAt (k t : ℕ) : Set (ℕ → Dir 2) :=
  {ω | (k : ℝ) ≤ euclidNorm (walkPos 0 ω t) ∧ (∀ s < t, euclidNorm (walkPos 0 ω s) < k) ∧
    ∀ s, 1 ≤ s → s ≤ t → walkPos 0 ω s ∉ axisSet {j | 0 ≤ j}}

private theorem pathLaw_hitA_zero_le {n : ℕ} (hn : 6 ≤ n) :
    pathLaw 2 (hitA (axisSet {j | 0 ≤ j}) (axisPt (-(n : ℤ))) 0) ≤
      (⨆ y ∈ restart n, pathLaw 2 (hitA (axisSet {j | 0 ≤ j}) (axisPt (-(n : ℤ))) y)) *
        pathLaw 2 (exitsWeakBefore ((n / 3 : ℕ) : ℝ) (axisSet {j | 0 ≤ j}) 0) := by
  classical
  set k := n / 3 with hk
  have hk2 : 2 ≤ k := by omega
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n 3
  have hdep : ∀ t, DependsOnFirst t (exitAt k t) := fun t =>
    dependsOnFirst_of 0 fun ω ω' h hω => ⟨by rw [← h t le_rfl]; exact hω.1,
      fun s hs => by rw [← h s hs.le]; exact hω.2.1 s hs,
      fun s hs1 hs2 => by rw [← h s hs2]; exact hω.2.2 s hs1 hs2⟩
  have hdisj : Pairwise (Function.onFun Disjoint (exitAt k)) := by
    intro t t' h
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, h2, -⟩ ⟨h1', h2', -⟩
    rcases lt_or_gt_of_ne h with h | h
    · exact absurd h1 (not_le.mpr (h2' t h))
    · exact absurd h1' (not_le.mpr (h2 t' h))
  have hsub : hitA (axisSet {j | 0 ≤ j}) (axisPt (-(n : ℤ))) 0 ⊆ ⋃ t, exitAt k t ∩
      {ω | shiftBy t ω ∈ hitA (axisSet {j | 0 ≤ j}) (axisPt (-(n : ℤ))) (walkPos 0 ω t)} := by
    intro ω hω
    obtain ⟨t₁, h1, h2⟩ := Set.mem_iUnion.mp hω
    have hkt : (k : ℝ) ≤ euclidNorm (walkPos 0 ω t₁) := by rw [h1, nrm_axisPt_neg]; exact hkR
    have hex : ∃ t, (k : ℝ) ≤ euclidNorm (walkPos 0 ω t) := ⟨t₁, hkt⟩
    obtain ⟨t₀, ht₀, hmin, ht⟩ : ∃ t₀, (k : ℝ) ≤ euclidNorm (walkPos 0 ω t₀) ∧
        (∀ s < t₀, euclidNorm (walkPos 0 ω s) < k) ∧ t₀ ≤ t₁ :=
      ⟨Nat.find hex, Nat.find_spec hex, fun s hs => not_le.mp (Nat.find_min hex hs),
        Nat.find_min' hex hkt⟩
    have hm : ω ∈ exitAt k t₀ := ⟨ht₀, hmin, fun s hs1 hs2 => h2 s hs1 (hs2.trans ht)⟩
    have hs : shiftBy t₀ ω ∈ hitA (axisSet {j | 0 ≤ j}) (axisPt (-(n : ℤ))) (walkPos 0 ω t₀) :=
      shift_mem_hitA _ _ ht h1 h2
    exact Set.mem_iUnion.mpr ⟨t₀, hm, hs⟩
  have hmem : ∀ t, ∀ ω ∈ exitAt k t, walkPos 0 ω t ∈ restart n := by
    rintro t ω ⟨h1, h2, h3⟩
    have ht : 1 ≤ t := by
      by_contra h0
      have ht0 : t = 0 := by omega
      rw [ht0, show walkPos 0 ω 0 = 0 by simp [walkPos], euclidNorm_zero] at h1
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      linarith
    refine ⟨h3 t ht le_rfl, Or.inl ⟨h1, ?_⟩⟩
    have := euclidNorm_walkPos_succ_le 0 ω (t - 1)
    rw [Nat.sub_add_cancel ht] at this
    linarith [h2 (t - 1) (by omega)]
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := markov_sup 0 hdep hdisj _ (measurableSet_hitA _ _) hmem fun y hy =>
        le_iSup₂ (f := fun y _ => pathLaw 2 (hitA (axisSet {j | 0 ≤ j}) (axisPt (-(n : ℤ))) y))
          y hy
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (measure_mono (Set.iUnion_subset fun t ω hω => ?_)) zero_le
        exact ⟨t, hω.1, fun s hs1 hs2 => hω.2.2 s hs1 hs2.le⟩

/-- **Proposition 12 (b)**: the walk started at `-n` enters the nonnegative half-axis at the
origin with probability `O(1 / √n)`. -/
theorem entersAt_halfLine_origin_le :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      prob (entersAt (axisSet {j | 0 ≤ j}) 0 (axisPt (-n))) ≤ C / Real.sqrt n := by
  obtain ⟨cA₁, cA, hcA₁, hcA, NA, hNA⟩ := exitsWeak_halfLine_nonneg
  obtain ⟨c11, hc11, N11, hN11⟩ := return_before_halfLine
  obtain ⟨c7, hc7, N7, hN7⟩ := hit_shellPart_lower
  obtain ⟨c8₁, c8, hc8₁, hc8, N8, hN8⟩ := hit_origin_annulus
  refine ⟨max (3 * cA * c8 / (c7 * c11)) (Real.sqrt (6 + 3 * NA + N11 + N7 + N8 : ℕ)),
    fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  rcases lt_or_ge n (6 + 3 * NA + N11 + N7 + N8) with hsmall | hbig
  · have h1 : 1 ≤ Real.sqrt (6 + 3 * NA + N11 + N7 + N8 : ℕ) / Real.sqrt n := by
      rw [le_div_iff₀ hsn, one_mul]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hsmall.le)
    calc prob _ ≤ 1 := prob_le_one'
      _ ≤ Real.sqrt (6 + 3 * NA + N11 + N7 + N8 : ℕ) / Real.sqrt n := h1
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hsn.le
  have hn6 : 6 ≤ n := by omega
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn6
  set N0 : Set (Site 2) := axisSet {j | 0 ≤ j} with hN0
  set a : Site 2 := axisPt (-(n : ℤ)) with ha_def
  have ha : a ∉ N0 := axisPt_neg_notMem hn
  have h0N : (0 : Site 2) ∈ N0 := zero_mem_halfAxis
  have hx : (0 : Site 2) ≠ a := fun h => ha (h ▸ h0N)
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  set q := 1 - c11 / Real.log n with hq_def
  have hq : prob (entersAt ({a} ∪ N0) a a) ≤ q := hN11 n (by omega)
  have hq1 : q < 1 := by
    have := div_pos hc11 hlogn
    linarith
  have hinv : 1 / (1 - q) = Real.log n / c11 := by rw [hq_def, sub_sub_cancel, one_div_div]
  have hmain := prob_entersAt_le ha h0N
    (mul_nonneg prob_nonneg' (by rw [hinv]; positivity)) (sum_visit_le ha hx hq hq1)
  rw [hinv] at hmain
  set k := n / 3 with hk
  have hkA : NA ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkpos
  have h7 : ∀ y : Site 2, euclidNorm y < 2 * n → c7 ≤ prob (hitsBefore
      (shellPart N0 (((4 * n : ℕ) : ℝ) / 4) (((4 * n : ℕ) : ℝ) / 2)) ((4 * n : ℕ) : ℝ) y) :=
    fun y hy => hN7 (4 * n) (by omega) N0 isDense_halfAxis y (by push_cast; linarith)
  have h8 : ∀ z : Site 2, ((5 * n : ℕ) : ℝ) / 10 ≤ euclidNorm z →
      euclidNorm z < 9 * ((5 * n : ℕ) : ℝ) / 10 →
      prob (hitsBefore {0} ((5 * n : ℕ) : ℝ) z) ≤ c8 / Real.log ((5 * n : ℕ) : ℝ) :=
    fun z h1 h2 => (hN8 (5 * n) (by omega) z h1 h2).2
  have hMr := toReal_iSup_restart_le hn6 hc7 hc8 h7 h8
  set M := ⨆ y ∈ restart n, pathLaw 2 (hitA N0 a y) with hM
  have hMtop : M ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup₂_le fun _ _ => prob_le_one)
  have he : prob (hitA N0 a 0) ≤ M.toReal * prob (exitsWeakBefore (k : ℝ) N0 0) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hMtop (ne_top' _)) (pathLaw_hitA_zero_le hn6)
    rwa [ENNReal.toReal_mul] at this
  have hpk : prob (exitsWeakBefore (k : ℝ) N0 0) ≤ 3 * cA / Real.sqrt n := by
    have h1 := (hNA k hkA).2
    have h9 : (n : ℝ) ≤ 9 * k := by exact_mod_cast (show n ≤ 9 * k by omega)
    have hsq : Real.sqrt n ≤ 3 * Real.sqrt k := by
      calc Real.sqrt n ≤ Real.sqrt (3 ^ 2 * k) := Real.sqrt_le_sqrt (by linarith)
        _ = 3 * Real.sqrt k := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    refine h1.trans ?_
    rw [div_le_div_iff₀ hsk hsn]
    nlinarith
  have hL5 : Real.log n ≤ Real.log ((5 * n : ℕ) : ℝ) :=
    Real.log_le_log hnpos (by push_cast; linarith)
  have hL5pos : 0 < Real.log ((5 * n : ℕ) : ℝ) := hlogn.trans_le hL5
  have hMlog : M.toReal * Real.log n ≤ c8 / c7 := by
    calc M.toReal * Real.log n
        ≤ (c8 / Real.log ((5 * n : ℕ) : ℝ) / c7) * Real.log ((5 * n : ℕ) : ℝ) :=
          mul_le_mul hMr hL5 hlogn.le (by positivity)
      _ = c8 / c7 := by field_simp
  calc prob (entersAt N0 0 a) ≤ prob (hitA N0 a 0) * (Real.log n / c11) := hmain
    _ ≤ M.toReal * prob (exitsWeakBefore (k : ℝ) N0 0) * (Real.log n / c11) :=
        mul_le_mul_of_nonneg_right he (by positivity)
    _ = (M.toReal * Real.log n) * prob (exitsWeakBefore (k : ℝ) N0 0) / c11 := by ring
    _ ≤ (c8 / c7) * (3 * cA / Real.sqrt n) / c11 :=
        div_le_div_of_nonneg_right (mul_le_mul hMlog hpk prob_nonneg' (by positivity)) hc11.le
    _ = 3 * cA * c8 / (c7 * c11) / Real.sqrt n := by
        field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) hsn.le

end FiniteAvalanches.Walk.Beurling
