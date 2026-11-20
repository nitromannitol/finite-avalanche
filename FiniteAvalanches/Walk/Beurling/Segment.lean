import FiniteAvalanches.Walk.Beurling.LastExit
import FiniteAvalanches.Walk.Beurling.DiskGreenLower
import FiniteAvalanches.Walk.Beurling.StripExit

/-!
# Escape from a segment of the real axis

Estimates for the probability that planar simple random walk exits a disk before returning to
an interval on the real axis, following Lawler and Limic (2004), Lemma 6.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

/-- Leaving a horizontal strip before visiting the axis entails leaving the disk before visiting
any subset of the axis. -/
theorem stripExitsBefore_axis_subset_exitsBefore (r : ℝ) (S : Set ℤ) (x : Site 2) :
    stripExitsBefore r (axisSet Set.univ) x ⊆ exitsBefore r (axisSet S) x := by
  intro ω hω
  obtain ⟨t, ht, hs⟩ := hω
  refine ⟨t, ht.trans (abs_coord_le_euclidNorm (walkPos x ω t) 1), ?_⟩
  intro s hs1 hst hmem
  exact hs s hs1 hst ⟨hmem.1, Set.mem_univ _⟩

/-- The strip gambler's ruin bound yields the lower bound for segment escape. -/
theorem segment_escape_lower (n : ℕ) (hn : 1 ≤ n) :
    1 / (2 * (n : ℝ)) ≤
      prob (exitsBefore n (axisSet (Set.Ico (-(n : ℤ)) n)) 0) := by
  rw [← strip_exit_axis_eq n hn]
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (stripExitsBefore_axis_subset_exitsBefore _ _ _))

private def positiveAxisSegment (m : ℕ) : Finset (Site 2) :=
  (Finset.range m).image fun j : ℕ => axisPt (j : ℤ)

private theorem axisPt_injective : Function.Injective axisPt := by
  intro j k h
  have h0 := congrFun h 0
  simpa [axisPt] using h0

private theorem axisPt_nat_injective : Function.Injective (fun j : ℕ => axisPt (j : ℤ)) := by
  intro j k h
  exact_mod_cast axisPt_injective h

private theorem euclidNorm_axisPt (j : ℤ) : euclidNorm (axisPt j) = |(j : ℝ)| := by
  simp [euclidNorm, axisPt, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]

private theorem positiveAxisSegment_card (m : ℕ) : (positiveAxisSegment m).card = m := by
  simp [positiveAxisSegment, Finset.card_image_of_injective, axisPt_nat_injective]

private theorem euclidNorm_add_le (y z : Site 2) :
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

private theorem segment_event_subset (n m k : ℕ) (hm : 0 < m) (hk : k < m)
    (hn : 8 * m ≤ n) :
    exitsBefore n (axisSet (Set.Ico (-(n : ℤ)) n)) 0 ⊆
      exitsBefore (4 * (m : ℝ)) (positiveAxisSegment m) (axisPt k) := by
  intro ω hω
  obtain ⟨t, ht, hs⟩ := hω
  have hpos (s : ℕ) : walkPos (axisPt k) ω s = axisPt k + walkPos 0 ω s := by
    simp [walkPos]
  have hneg (x : Site 2) : euclidNorm (-x) = euclidNorm x := by
    simp [euclidNorm]
  have hnorm : euclidNorm (walkPos 0 ω t) ≤
      euclidNorm (walkPos (axisPt k) ω t) + euclidNorm (axisPt k) := by
    have h := euclidNorm_add_le (walkPos (axisPt k) ω t) (-(axisPt k))
    rw [hneg] at h
    have heq : walkPos (axisPt k) ω t + -(axisPt k) = walkPos 0 ω t := by
      rw [hpos]
      abel
    rwa [heq] at h
  have hkreal : (k : ℝ) < m := by exact_mod_cast hk
  have hnreal : (8 : ℝ) * m ≤ n := by exact_mod_cast hn
  have haxis : euclidNorm (axisPt k) = (k : ℝ) := by
    rw [euclidNorm_axisPt]
    simp
  have hcross : 4 * (m : ℝ) ≤ euclidNorm (walkPos (axisPt k) ω t) := by
    rw [haxis] at hnorm
    linarith
  refine ⟨t, hcross, ?_⟩
  intro s hs1 hst hmem
  obtain ⟨j, hj, hsite⟩ := Finset.mem_image.mp hmem
  have hjm : j < m := Finset.mem_range.mp hj
  have heq := hpos s
  rw [← hsite] at heq
  have heq0 := congrFun heq 0
  have heq1 := congrFun heq 1
  simp [axisPt] at heq0 heq1
  have hnint : (8 : ℤ) * m ≤ n := by exact_mod_cast hn
  have hjint : (j : ℤ) < m := by exact_mod_cast hjm
  have hkint : (k : ℤ) < m := by exact_mod_cast hk
  apply hs s hs1 hst
  constructor
  · exact heq1.symm
  · constructor <;> omega

private theorem segment_escape_upper : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    prob (exitsBefore n (axisSet (Set.Ico (-(n : ℤ)) n)) 0) ≤ C / n := by
  classical
  obtain ⟨c, hc, N₀, hgreen⟩ := green_lower (1 / 2) (by norm_num) (by norm_num)
  refine ⟨16 / c, by positivity, max 16 (8 * N₀ + 8), ?_⟩
  intro n hn
  have hn16 : 16 ≤ n := le_of_max_le_left hn
  have hnN : 8 * N₀ + 8 ≤ n := le_of_max_le_right hn
  let m := n / 8
  have hm : 0 < m := by dsimp [m]; omega
  have hmn : 8 * m ≤ n := by dsimp [m]; omega
  have hnm : n ≤ 16 * m := by dsimp [m]; omega
  have hN : N₀ ≤ 4 * m := by dsimp [m]; omega
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnmreal : (n : ℝ) ≤ 16 * m := by exact_mod_cast hnm
  let B := positiveAxisSegment m
  have hB : ∀ x ∈ B, euclidNorm x < (4 * m : ℕ) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjm : (j : ℝ) < m := by exact_mod_cast (Finset.mem_range.mp hj)
    rw [euclidNorm_axisPt]
    simp only [Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ j by positivity)]
    linarith
  have h0B : (0 : Site 2) ∈ B := by
    change (0 : Site 2) ∈ (Finset.range m).image (fun j : ℕ => axisPt (j : ℤ))
    refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hm, ?_⟩
    ext i
    fin_cases i <;> simp [axisPt]
  have hhit : prob (hitsBefore B (4 * m : ℕ) 0) = 1 := by
    have h : hitsBefore B (4 * m : ℕ) 0 = Set.univ := by
      ext ω
      simp only [Set.mem_univ, iff_true]
      refine ⟨0, ?_, ?_⟩
      · simpa [walkPos] using h0B
      · intro s hs
        have : s = 0 := by omega
        subst s
        simp [walkPos, euclidNorm_zero, hm]
    rw [h, prob, measure_univ, ENNReal.toReal_one]
  let q := prob (exitsBefore n (axisSet (Set.Ico (-(n : ℤ)) n)) 0)
  have hq : 0 ≤ q := ENNReal.toReal_nonneg
  have hbound : ∀ x ∈ B, c * q ≤ green (4 * m : ℕ) 0 x *
      prob (exitsBefore (4 * m : ℕ) B x) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjm : j < m := Finset.mem_range.mp hj
    have hjreal : (j : ℝ) < m := by exact_mod_cast hjm
    have hlower : c ≤ green (4 * m : ℕ) 0 (axisPt j) := by
      apply hgreen (4 * m) hN 0 (axisPt j)
      · simp only [euclidNorm_zero, Nat.cast_mul, Nat.cast_ofNat]
        linarith
      · rw [euclidNorm_axisPt]
        simp only [Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat]
        rw [abs_of_nonneg (show (0 : ℝ) ≤ j by positivity)]
        linarith
    have hcompare : q ≤ prob (exitsBefore (4 * m : ℕ) B (axisPt j)) := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      simpa [B] using segment_event_subset n m j hm hjm hmn
    exact mul_le_mul hlower hcompare hq (hc.le.trans hlower)
  have hsum : (m : ℝ) * (c * q) ≤ 1 := by
    calc
      (m : ℝ) * (c * q) = ∑ _x ∈ B, c * q := by
        simp [B, positiveAxisSegment_card]
      _ ≤ ∑ x ∈ B, green (4 * m : ℕ) 0 x *
          prob (exitsBefore (4 * m : ℕ) B x) := Finset.sum_le_sum hbound
      _ = prob (hitsBefore B (4 * m : ℕ) 0) :=
        (hitsBefore_eq_sum_green_mul _ B hB 0).symm
      _ = 1 := hhit
  have hscaled := mul_le_mul_of_nonneg_right hnmreal hq
  have hmain : c * ((n : ℝ) * q) ≤ 16 := by nlinarith [hsum, hscaled]
  dsimp [q] at hmain ⊢
  apply (le_div_iff₀ hnreal).2
  have hcne : c ≠ 0 := ne_of_gt hc
  apply (le_div_iff₀ hc).2
  nlinarith [hmain]

/-- **Lawler–Limic (2004), Lemma 6.** The probability of leaving a disk before returning to
its diameter on the real axis is comparable to the reciprocal of its radius. -/
theorem segment_escape :
    Asymp (fun n => exitsBefore n (axisSet (Set.Ico (-(n : ℤ)) n)) 0)
      (fun n => (n : ℝ)) := by
  obtain ⟨C, hC, N, hupper⟩ := segment_escape_upper
  refine ⟨1 / 2, C, by norm_num, hC, max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnN : N ≤ n := le_of_max_le_right hn
  constructor
  · convert segment_escape_lower n hn1 using 1; ring
  · exact hupper n hnN

end FiniteAvalanches.Walk.Beurling
