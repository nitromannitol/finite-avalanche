import FiniteAvalanches.Walk.Beurling.HalfLineHitConsequences
import FiniteAvalanches.Walk.Beurling.Segment

/-!
# Leaving a disk before a shifted half-axis

Lawler and Limic (2004), Proposition 12 (e), for the simple random walk on `ℤ²` and `1 ≤ j ≤ n`:
the walk started at the origin leaves the disk of radius `n` before its first positive-time visit
to the half-axis `{(i, 0) : i ≥ -j}` with probability `O(1 / √(j n))`.

## Main statements

* `exitsBefore_shiftedHalfLine_le`: Proposition 12 (e) for `1 ≤ j ≤ n`.

## Proof

Decompose at the first positive-time visit to the real axis `ℤ`. If the walk leaves the disk
before that visit, the event `{τ_n < T_ℤ}` occurs; by Lemma 6 its probability is `O(1 / n)`, which
is `O(1 / √(j n))` because `j ≤ n`. Otherwise the first visit is at a point `-k` with `k > j`. By
the half-plane kernel from height one this happens with probability `O(1 / k²)`, and the walk
then restarts at `-k` (Markov property at the first visit). For `2 k ≤ n`, the translation by `k`
turns the remaining event into leaving the disk of radius `n - k ≥ n / 2` before the half-axis
`{i ≥ k - j}`, whose probability is `O(√((k - j) / n)) = O(√k / √n)` by Proposition 12 (d). For
`2 k > n` the trivial bound `1` is also `O(√k / √n)`. Hence the term of `k` is
`O(k^(-3/2) / √n)`, and `∑_{k > j} k^(-3/2) ≤ 2 / √j`.

G. F. Lawler and V. Limic, *The Beurling estimate for a class of random walks*, Electron. J.
Probab. 9 (2004), Lemma 6 and Proposition 12.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb MeasureTheory

private theorem prob_nonneg' (E : Set (ℕ → Dir 2)) : 0 ≤ prob E := ENNReal.toReal_nonneg

private theorem prob_mono' {E F : Set (ℕ → Dir 2)} (h : E ⊆ F) : prob E ≤ prob F :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h)

private theorem prob_le_one' (E : Set (ℕ → Dir 2)) : prob E ≤ 1 := by
  have h : pathLaw 2 E ≤ 1 := prob_le_one
  simpa [prob] using ENNReal.toReal_mono ENNReal.one_ne_top h

private theorem walkPos_eq_add' (x : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos x ω t = x + walkPos 0 ω t := by
  simp [walkPos]

private theorem walkPos_add_shiftBy' (x : Site 2) (ω : ℕ → Dir 2) (j t : ℕ) :
    walkPos x ω (j + t) = walkPos (walkPos x ω j) (shiftBy j ω) t := by
  simp only [walkPos, shiftBy, Finset.sum_range_add, add_assoc]

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

private theorem axisPt_apply_zero (a : ℤ) : axisPt a 0 = a := by simp [axisPt]

private theorem axisPt_apply_one (a : ℤ) : axisPt a 1 = 0 := by simp [axisPt]

private theorem euclidNorm_axisPt_neg (k : ℕ) : euclidNorm (axisPt (-(k : ℤ))) = k := by
  simp [euclidNorm, axisPt, Fin.sum_univ_two]

private theorem site_two_ext_iff (u v : Site 2) : u = v ↔ u 0 = v 0 ∧ u 1 = v 1 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i
    · exact h0
    · exact h1

/-! ### The first visit to the real axis from the origin -/

/-- Entering the real axis at `-(k + 2)` from the origin is the translate of entering it at `-k`
from `(2, 0)`. -/
private theorem entersAt_axis_origin_eq (k : ℕ) :
    entersAt (axisSet Set.univ) (axisPt (-((k + 2 : ℕ) : ℤ))) 0 =
      entersAt (axisSet Set.univ) (axisPt (-(k : ℤ))) (axisPt ((2 : ℕ) : ℤ)) := by
  have hpt : ∀ p : Site 2, axisPt ((2 : ℕ) : ℤ) + p = axisPt (-(k : ℤ)) ↔
      p = axisPt (-((k + 2 : ℕ) : ℤ)) := by
    intro p
    rw [site_two_ext_iff, site_two_ext_iff]
    simp only [Pi.add_apply, axisPt_apply_zero, axisPt_apply_one]
    push_cast
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨h0, h1⟩
      exact ⟨by omega, by omega⟩
  have hmem : ∀ p : Site 2, axisPt ((2 : ℕ) : ℤ) + p ∈ axisSet Set.univ ↔
      p ∈ axisSet Set.univ := by
    intro p
    simp only [axisSet, Set.mem_setOf_eq, Set.mem_univ, and_true, Pi.add_apply, axisPt_apply_one,
      zero_add]
  ext ω
  simp only [entersAt, Set.mem_setOf_eq, walkPos_eq_add' (axisPt ((2 : ℕ) : ℤ)), hpt, hmem]

/-- From the origin, the first positive-time visit to the real axis is a visit to `-k` with
probability `O(1 / k²)`. -/
private theorem prob_entersAt_axis_origin_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 2 ≤ k →
    prob (entersAt (axisSet Set.univ) (axisPt (-(k : ℤ))) 0) ≤ C / (k : ℝ) ^ 2 := by
  obtain ⟨C, hC, h⟩ := prob_entersAt_axis_start_le
  refine ⟨C, hC, fun k hk => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 2 := ⟨k - 2, by omega⟩
  rw [entersAt_axis_origin_eq l]
  have := h 2 l le_rfl
  convert this using 3
  push_cast
  ring

/-! ### The decomposition at the first visit to the real axis -/

/-- Leaving the disk before the half-axis `{i ≥ -j}` either avoids the real axis until the exit,
or first visits the real axis at a point `-(m + j + 1)` and then leaves the disk before the
half-axis. -/
private theorem exitsBefore_shifted_subset (n j : ℕ) :
    exitsBefore n (axisSet {i : ℤ | -(j : ℤ) ≤ i}) 0 ⊆
      exitsBefore n (axisSet Set.univ) 0 ∪
        ⋃ m : ℕ, {ω | ∃ t, ω ∈ hitAtTime (axisSet Set.univ) 0
          (axisPt (-((m + j + 1 : ℕ) : ℤ))) t ∧ shiftBy t ω ∈
            exitsBefore n (axisSet {i : ℤ | -(j : ℤ) ≤ i}) (axisPt (-((m + j + 1 : ℕ) : ℤ)))} := by
  classical
  rintro ω ⟨t, ht1, ht2⟩
  by_cases hZ : ∃ s, 1 ≤ s ∧ s ≤ t ∧ walkPos 0 ω s ∈ axisSet Set.univ
  · right
    have hu := Nat.find_spec hZ
    have hmin : ∀ s, s < Nat.find hZ → ¬ (1 ≤ s ∧ s ≤ t ∧ walkPos 0 ω s ∈ axisSet Set.univ) :=
      fun s hs => Nat.find_min hZ hs
    generalize Nat.find hZ = u at hu hmin
    obtain ⟨hu1, hut, huZ⟩ := hu
    have huH : walkPos 0 ω u ∉ axisSet {i : ℤ | -(j : ℤ) ≤ i} := ht2 u hu1 hut
    have hy1 : walkPos 0 ω u 1 = 0 := huZ.1
    have hy0 : walkPos 0 ω u 0 < -(j : ℤ) := by
      by_contra h
      exact huH ⟨hy1, not_lt.1 h⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, walkPos 0 ω u 0 = -((m + j + 1 : ℕ) : ℤ) :=
      ⟨(-(walkPos 0 ω u 0) - j - 1).toNat, by omega⟩
    have hpt : walkPos 0 ω u = axisPt (-((m + j + 1 : ℕ) : ℤ)) := by
      rw [site_two_ext_iff, axisPt_apply_zero, axisPt_apply_one]
      exact ⟨hm, hy1⟩
    have hkey : ∀ s, walkPos 0 ω (u + s) =
        walkPos (axisPt (-((m + j + 1 : ℕ) : ℤ))) (shiftBy u ω) s := fun s => by
      rw [walkPos_add_shiftBy', hpt]
    refine Set.mem_iUnion.2 ⟨m, u, ⟨hu1, hpt, fun s hs1 hs2 hsZ =>
      hmin s hs2 ⟨hs1, by omega, hsZ⟩⟩, t - u, ?_, ?_⟩
    · rw [← hkey, Nat.add_sub_cancel' hut]
      exact ht1
    · intro s hs1 hs2
      rw [← hkey]
      exact ht2 (u + s) (by omega) (by omega)
  · left
    push Not at hZ
    exact ⟨t, ht1, fun s hs1 hs2 => hZ s hs1 hs2⟩

/-- From `-k` with `j < k ≤ n`, leaving the disk of radius `n` before the half-axis `{i ≥ -j}` is
contained, after the translation by `k`, in leaving the disk of radius `n - k` before the half-axis
`{i ≥ k - j}`. -/
private theorem exitsBefore_from_axis_subset {n j k : ℕ} (hjk : j < k) (hkn : k ≤ n) :
    exitsBefore n (axisSet {i : ℤ | -(j : ℤ) ≤ i}) (axisPt (-(k : ℤ))) ⊆
      exitsBefore ((n - k : ℕ) : ℝ) (axisSet {i : ℤ | ((k - j : ℕ) : ℤ) ≤ i}) 0 := by
  rintro ω ⟨t, ht1, ht2⟩
  refine ⟨t, ?_, fun s hs1 hs2 hmem => ht2 s hs1 hs2 ?_⟩
  · have h := euclidNorm_add_le' (axisPt (-(k : ℤ))) (walkPos 0 ω t)
    rw [← walkPos_eq_add', euclidNorm_axisPt_neg] at h
    rw [Nat.cast_sub hkn]
    linarith
  · obtain ⟨h1, h2⟩ := hmem
    have h2' : ((k - j : ℕ) : ℤ) ≤ walkPos 0 ω s 0 := h2
    rw [walkPos_eq_add']
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, axisPt_apply_one, h1, add_zero]
    · show -(j : ℤ) ≤ (axisPt (-(k : ℤ)) + walkPos 0 ω s) 0
      simp only [Pi.add_apply, axisPt_apply_zero]
      omega

/-! ### Summation -/

/-- One step of the comparison of `∑ k^(-3/2)` with `2 / √j`. -/
private theorem inv_mul_sqrt_succ_le {a : ℝ} (ha : 1 ≤ a) :
    1 / ((a + 1) * Real.sqrt (a + 1)) ≤ 2 / Real.sqrt a - 2 / Real.sqrt (a + 1) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 (by linarith)
  have ht : 0 < Real.sqrt (a + 1) := Real.sqrt_pos.2 (by linarith)
  have hs2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
  have ht2 : Real.sqrt (a + 1) ^ 2 = a + 1 := Real.sq_sqrt (by linarith)
  have hst : Real.sqrt a ≤ Real.sqrt (a + 1) := Real.sqrt_le_sqrt (by linarith)
  set s := Real.sqrt a
  set t := Real.sqrt (a + 1)
  have hz : t ^ 2 - s ^ 2 - 1 = 0 := by rw [hs2, ht2]; ring
  have key : (2 * t - 2 * s) * (t ^ 2 * t) - s * t =
      (t - s) ^ 2 * t * (2 * t + s) + s * t * (t ^ 2 - s ^ 2 - 1) := by ring
  rw [hz, mul_zero, add_zero] at key
  have hpos : 0 ≤ (t - s) ^ 2 * t * (2 * t + s) := by positivity
  rw [← ht2, div_sub_div _ _ hs.ne' ht.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [key, hpos]

/-- `∑_{k > j} k^(-3/2) ≤ 2 / √j`. -/
private theorem sum_inv_mul_sqrt_le (j : ℕ) (hj : 1 ≤ j) (M : ℕ) :
    ∑ m ∈ Finset.range M, 1 / (((m + j + 1 : ℕ) : ℝ) * Real.sqrt ((m + j + 1 : ℕ) : ℝ)) ≤
      2 / Real.sqrt j := by
  have key : ∀ M : ℕ, ∑ m ∈ Finset.range M,
      1 / (((m + j + 1 : ℕ) : ℝ) * Real.sqrt ((m + j + 1 : ℕ) : ℝ)) ≤
        2 / Real.sqrt j - 2 / Real.sqrt ((M + j : ℕ) : ℝ) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have ha : (1 : ℝ) ≤ ((M + j : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ M + j)
      have e1 : ((M + j + 1 : ℕ) : ℝ) = ((M + j : ℕ) : ℝ) + 1 := by push_cast; ring
      have e2 : ((M + 1 + j : ℕ) : ℝ) = ((M + j : ℕ) : ℝ) + 1 := by push_cast; ring
      have hstep := inv_mul_sqrt_succ_le ha
      rw [← e1] at hstep
      rw [e2, ← e1]
      linarith
  refine (key M).trans ?_
  have : 0 ≤ 2 / Real.sqrt ((M + j : ℕ) : ℝ) := by positivity
  linarith

/-- The bound for one term of the decomposition. -/
private theorem term_le {C₁ M A B : ℝ} {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hM : 1 ≤ M)
    (hA0 : 0 ≤ A) (hA : A ≤ C₁ / (k : ℝ) ^ 2) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hB : 2 * k ≤ n → B ≤ M * Real.sqrt 2 * Real.sqrt k / Real.sqrt n) :
    A * B ≤ C₁ * Real.sqrt 2 * M / Real.sqrt n * (1 / ((k : ℝ) * Real.sqrt k)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.2 (by linarith)
  have hr : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hA' : 0 ≤ C₁ / (k : ℝ) ^ 2 := hA0.trans hA
  have hks : (k : ℝ) = Real.sqrt k ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hR : C₁ * Real.sqrt 2 * M / Real.sqrt n * (1 / ((k : ℝ) * Real.sqrt k)) =
      C₁ / (k : ℝ) ^ 2 * (M * Real.sqrt 2 * Real.sqrt k / Real.sqrt n) := by
    have hs' : Real.sqrt k ≠ 0 := hs.ne'
    have hr' : Real.sqrt n ≠ 0 := hr.ne'
    set s := Real.sqrt k
    rw [hks]
    field_simp
  rw [hR]
  rcases le_or_gt (2 * k) n with h2k | h2k
  · exact mul_le_mul hA (hB h2k) hB0 hA'
  · have h1 : 1 ≤ M * Real.sqrt 2 * Real.sqrt k / Real.sqrt n := by
      rw [le_div_iff₀ hr, one_mul]
      have hlt : (n : ℝ) ≤ 2 * k := by
        have : (n : ℝ) < 2 * k := by exact_mod_cast h2k
        linarith
      have hsq : Real.sqrt n ≤ Real.sqrt 2 * Real.sqrt k := by
        rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) (k : ℝ)]
        exact Real.sqrt_le_sqrt hlt
      nlinarith [mul_nonneg (sub_nonneg.2 hM) (mul_pos h2 hs).le]
    calc A * B ≤ A := mul_le_of_le_one_right hA0 hB1
      _ ≤ C₁ / (k : ℝ) ^ 2 := hA
      _ = C₁ / (k : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hA'

/-! ### Proposition 12 (e) -/

/-- **Lawler and Limic (2004), Proposition 12 (e), for `j ≤ n`.** For `1 ≤ j ≤ n`, the walk
started at the origin leaves the disk of radius `n` before its first positive-time visit to the
half-axis `{(i, 0) : i ≥ -j}` with probability at most `C / √(j n)`. -/
theorem exitsBefore_shiftedHalfLine_le :
    ∃ C : ℝ, ∀ j n : ℕ, 1 ≤ j → 1 ≤ n → j ≤ n →
      prob (exitsBefore n (axisSet {i | -(j : ℤ) ≤ i}) 0) ≤ C / Real.sqrt (j * n) := by
  obtain ⟨_, c₂, _, hc₂, N, hN⟩ := segment_escape
  obtain ⟨C₁, hC₁, hK⟩ := prob_entersAt_axis_origin_le
  obtain ⟨Cd, hCd⟩ := exitsBefore_halfLine_le
  set M : ℝ := max Cd 1 with hMdef
  have hM : 1 ≤ M := le_max_right _ _
  set K₀ : ℝ := C₁ * Real.sqrt 2 * M with hK₀def
  have hK₀ : 0 ≤ K₀ := mul_nonneg (mul_nonneg hC₁ (Real.sqrt_nonneg 2)) (by linarith)
  refine ⟨max ((N : ℝ) + 1) (c₂ + 2 * K₀), fun j n hj hn hjn => ?_⟩
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hjnR : (j : ℝ) ≤ n := by exact_mod_cast hjn
  have hsq : 0 < Real.sqrt (j * n) := Real.sqrt_pos.2 (by positivity)
  have hsqn : Real.sqrt (j * n) ≤ n := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  rcases lt_or_ge n N with hsmall | hbig
  · have hnN : (n : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hsmall
    calc prob (exitsBefore n (axisSet {i | -(j : ℤ) ≤ i}) 0) ≤ 1 := prob_le_one' _
      _ ≤ ((N : ℝ) + 1) / Real.sqrt (j * n) := by
          rw [le_div_iff₀ hsq]
          linarith
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) hsq.le
  · have hA : prob (exitsBefore n (axisSet Set.univ) 0) ≤ c₂ / n := by
      have h : prob (exitsBefore n (axisSet (Set.Ico (-(n : ℤ)) n)) 0) ≤ c₂ / n := (hN n hbig).2
      exact (prob_mono' (exitsBefore_anti (B := axisSet (Set.Ico (-(n : ℤ)) n))
        (B' := axisSet Set.univ) (fun z hz => ⟨hz.1, Set.mem_univ _⟩) n 0)).trans h
    have hterm : ∀ m : ℕ, pathLaw 2 {ω | ∃ t, ω ∈ hitAtTime (axisSet Set.univ) 0
        (axisPt (-((m + j + 1 : ℕ) : ℤ))) t ∧ shiftBy t ω ∈
          exitsBefore n (axisSet {i : ℤ | -(j : ℤ) ≤ i}) (axisPt (-((m + j + 1 : ℕ) : ℤ)))} ≤
        ENNReal.ofReal (K₀ / Real.sqrt n *
          (1 / (((m + j + 1 : ℕ) : ℝ) * Real.sqrt ((m + j + 1 : ℕ) : ℝ)))) := by
      intro m
      refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 ?_
      change prob _ ≤ _
      rw [prob_hit_then (B := axisSet Set.univ) (x := 0) (w := axisPt (-((m + j + 1 : ℕ) : ℤ)))
        (C := exitsBefore n (axisSet {i : ℤ | -(j : ℤ) ≤ i}) (axisPt (-((m + j + 1 : ℕ) : ℤ))))
        (by simp [axisSet, axisPt]) (measurableSet_exitsBefore _ _ _)]
      have hk2 : 2 ≤ m + j + 1 := by omega
      refine term_le hn (by omega) hM (prob_nonneg' _) (hK _ hk2) (prob_nonneg' _)
        (prob_le_one' _) fun h2k => ?_
      have hsub := exitsBefore_from_axis_subset (n := n) (j := j) (k := m + j + 1) (by omega)
        (by omega)
      have hd := hCd (m + j + 1 - j) (n - (m + j + 1)) (by omega) (by omega)
      refine (prob_mono' hsub).trans (hd.trans ?_)
      have hkR : (1 : ℝ) ≤ ((m + j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + j + 1)
      have hkj : ((m + j + 1 - j : ℕ) : ℝ) ≤ ((m + j + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le _ _
      have h2kR : 2 * ((m + j + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h2k
      have hnk : (n : ℝ) / 2 ≤ ((n - (m + j + 1) : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        linarith
      have hnk0 : 0 < ((n - (m + j + 1) : ℕ) : ℝ) := by linarith
      have hfrac : ((m + j + 1 - j : ℕ) : ℝ) / ((n - (m + j + 1) : ℕ) : ℝ) ≤
          2 * ((m + j + 1 : ℕ) : ℝ) / n := by
        rw [div_le_div_iff₀ hnk0 (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_right hkj (by linarith : (0 : ℝ) ≤ n),
          mul_le_mul_of_nonneg_left hnk (by linarith : (0 : ℝ) ≤ ((m + j + 1 : ℕ) : ℝ))]
      have hsqrt : Real.sqrt (((m + j + 1 - j : ℕ) : ℝ) / ((n - (m + j + 1) : ℕ) : ℝ)) ≤
          Real.sqrt 2 * Real.sqrt ((m + j + 1 : ℕ) : ℝ) / Real.sqrt n := by
        rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) ((m + j + 1 : ℕ) : ℝ),
          ← Real.sqrt_div (show (0 : ℝ) ≤ 2 * ((m + j + 1 : ℕ) : ℝ) by positivity) (n : ℝ)]
        exact Real.sqrt_le_sqrt hfrac
      calc Cd * Real.sqrt (((m + j + 1 - j : ℕ) : ℝ) / ((n - (m + j + 1) : ℕ) : ℝ))
          ≤ M * Real.sqrt (((m + j + 1 - j : ℕ) : ℝ) / ((n - (m + j + 1) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
        _ ≤ M * (Real.sqrt 2 * Real.sqrt ((m + j + 1 : ℕ) : ℝ) / Real.sqrt n) :=
            mul_le_mul_of_nonneg_left hsqrt (by linarith)
        _ = M * Real.sqrt 2 * Real.sqrt ((m + j + 1 : ℕ) : ℝ) / Real.sqrt n := by ring
    have hmain : pathLaw 2 (exitsBefore n (axisSet {i : ℤ | -(j : ℤ) ≤ i}) 0) ≤
        ENNReal.ofReal (c₂ / n) + ENNReal.ofReal (K₀ / Real.sqrt n * (2 / Real.sqrt j)) := by
      refine (measure_mono (exitsBefore_shifted_subset n j)).trans
        ((measure_union_le _ _).trans (add_le_add ?_ ?_))
      · exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 hA
      · refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum hterm).trans ?_)
        refine ENNReal.tsum_le_of_sum_range_le fun L => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_inv_mul_sqrt_le j hj L) (by positivity)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hmain
    have hfin := ENNReal.toReal_le_of_le_ofReal (by positivity) hmain
    refine hfin.trans ?_
    have hsjn : Real.sqrt (j * n) = Real.sqrt j * Real.sqrt n := Real.sqrt_mul (by positivity) _
    have hsj : 0 < Real.sqrt j := Real.sqrt_pos.2 (by linarith)
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
    have h1 : c₂ / n ≤ c₂ / Real.sqrt (j * n) := div_le_div_of_nonneg_left hc₂.le hsq hsqn
    have h2 : K₀ / Real.sqrt n * (2 / Real.sqrt j) = 2 * K₀ / Real.sqrt (j * n) := by
      rw [hsjn, div_mul_div_comm, mul_comm K₀ 2, mul_comm (Real.sqrt n) (Real.sqrt j)]
    calc c₂ / n + K₀ / Real.sqrt n * (2 / Real.sqrt j)
        ≤ c₂ / Real.sqrt (j * n) + 2 * K₀ / Real.sqrt (j * n) := by rw [h2]; linarith
      _ = (c₂ + 2 * K₀) / Real.sqrt (j * n) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hsq.le

end FiniteAvalanches.Walk.Beurling
