import FiniteAvalanches.Walk.Beurling.StripExit

/-!
# Escape from a half-line

For simple random walk on `ℤ²`, the probability of leaving a horizontal strip before
visiting either half of the real axis is comparable to the reciprocal square root of the
strip width. See Lawler and Limic, *The Beurling estimate for a class of random walks*,
Lemma 10.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

/-- Negating every increment negates the position of the walk. -/
theorem walkPos_revNeg_zero (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos 0 (revNeg 0 ω) t = -walkPos 0 ω t := by
  simp [walkPos, revNeg, revIdx, dirVec_negDir, Finset.sum_neg_distrib]

/-- The probability for the nonnegative half-axis equals that for the nonpositive half-axis. -/
theorem prob_strip_nonneg_eq_nonpos (n : ℕ) :
    prob (stripExitsBefore n (axisSet {j | 0 ≤ j}) 0) =
      prob (stripExitsBefore n (axisSet {j | j ≤ 0}) 0) := by
  have he : revNeg 0 ⁻¹' stripExitsBefore n (axisSet {j | 0 ≤ j}) 0 =
      stripExitsBefore n (axisSet {j | j ≤ 0}) 0 := by
    ext ω
    simp only [Set.mem_preimage, mem_stripExitsBefore_iff, walkPos_revNeg_zero,
      Pi.neg_apply, abs_neg, axisSet, Set.mem_setOf_eq]
    simp only [neg_eq_zero, neg_nonneg]
  unfold prob
  rw [← he, (measurePreserving_revNeg 0).measure_preimage
    (measurableSet_stripExitsBefore _ _ _).nullMeasurableSet]

/-- A first step to the right turns an escape from the negative half-axis into an escape
from the nonpositive half-axis. -/
theorem firstStep_escape_subset (n : ℕ) :
    {ω : ℕ → Dir 2 | ω 0 = (0, true)} ∩
        shiftBy 1 ⁻¹' stripExitsBefore n (axisSet {j | j < 0}) 0 ⊆
      stripExitsBefore n (axisSet {j | j ≤ 0}) 0 := by
  intro ω hω
  obtain ⟨ha, ht⟩ := hω
  rw [Set.mem_preimage, mem_stripExitsBefore_iff] at ht
  obtain ⟨t, ht, hs⟩ := ht
  rw [mem_stripExitsBefore_iff]
  refine ⟨1 + t, ?_, ?_⟩
  · rw [walkPos_add_apply, walkPos_one, ha]
    simpa [dirVec] using ht
  · intro s hs1 hst hmem
    obtain ⟨u, rfl⟩ : ∃ u, s = 1 + u := ⟨s - 1, by omega⟩
    have hu : u ≤ t := by omega
    have h0 : walkPos 0 ω (1 + u) 0 = 1 + walkPos 0 (shiftBy 1 ω) u 0 := by
      rw [walkPos_add_apply, walkPos_one, ha]
      simp [dirVec]
    have h1 : walkPos 0 ω (1 + u) 1 = walkPos 0 (shiftBy 1 ω) u 1 := by
      rw [walkPos_add_apply, walkPos_one, ha]
      simp [dirVec]
    simp only [axisSet, Set.mem_setOf_eq] at hmem
    rw [h0, h1] at hmem
    by_cases hu0 : u = 0
    · subst u
      simp [walkPos] at hmem
    · have : walkPos 0 (shiftBy 1 ω) u ∈ axisSet {j | j < 0} := by
        simp only [axisSet, Set.mem_setOf_eq]
        exact ⟨hmem.1, by omega⟩
      exact hs u (by omega) hu this

/-- The two half-axis escape probabilities differ by at most a factor of four. -/
theorem prob_strip_neg_le_four_mul_nonpos (n : ℕ) :
    prob (stripExitsBefore n (axisSet {j | j < 0}) 0) ≤
      4 * prob (stripExitsBefore n (axisSet {j | j ≤ 0}) 0) := by
  let A : Set (ℕ → Dir 2) := {ω | ω 0 = (0, true)}
  let B := stripExitsBefore n (axisSet {j | j < 0}) 0
  have hA : DependsOnFirst 1 A := by
    intro ω ω' h
    simpa [A] using congrArg (fun a => a = (0, true)) (h 0 (by omega))
  have hm := measureReal_mono (μ := pathLaw 2) (firstStep_escape_subset n)
  have he : prob (A ∩ shiftBy 1 ⁻¹' B) = (1 / 4 : ℝ) * prob B := by
    change (pathLaw 2 (A ∩ shiftBy 1 ⁻¹' B)).toReal = (1 / 4 : ℝ) * (pathLaw 2 B).toReal
    have hsplit : pathLaw 2 (A ∩ shiftBy 1 ⁻¹' B) = pathLaw 2 A * pathLaw 2 B :=
      markov_split hA (show MeasurableSet B from measurableSet_stripExitsBefore _ _ _)
    rw [hsplit, show pathLaw 2 A = (4 : ENNReal)⁻¹ from pathLaw_firstStep _,
      ENNReal.toReal_mul]
    norm_num
  change prob (A ∩ shiftBy 1 ⁻¹' B) ≤
    prob (stripExitsBefore n (axisSet {j | j ≤ 0}) 0) at hm
  rw [he] at hm
  dsimp [B] at hm
  linarith

/-- The negative and nonpositive half-axis probabilities bound one another. -/
theorem prob_strip_nonpos_le_neg (n : ℕ) :
    prob (stripExitsBefore n (axisSet {j | j ≤ 0}) 0) ≤
      prob (stripExitsBefore n (axisSet {j | j < 0}) 0) := by
  apply measureReal_mono ?_ (by finiteness)
  apply stripExitsBefore_anti
  intro z hz
  change z 1 = 0 ∧ z 0 < 0 at hz
  change z 1 = 0 ∧ z 0 ≤ 0
  exact ⟨hz.1, le_of_lt hz.2⟩

/-- Multiplicative comparison and a product identity give reciprocal square-root bounds. -/
theorem halfLine_bounds {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s)
    (hba : b ≤ a) (hab : a ≤ 4 * b) (hp : (a * s) * (b * s) = 1 / 2) :
    1 / 2 / s ≤ a ∧ a ≤ 2 / s ∧ 1 / 8 / s ≤ b ∧ b ≤ 2 / s := by
  have hx : 0 ≤ a * s := mul_nonneg ha hs.le
  have hy : 0 ≤ b * s := mul_nonneg hb hs.le
  have hyx : b * s ≤ a * s := mul_le_mul_of_nonneg_right hba hs.le
  have hxy : a * s ≤ 4 * (b * s) := by nlinarith [mul_le_mul_of_nonneg_right hab hs.le]
  have hsqlo : (1 / 2 : ℝ) ≤ (a * s) ^ 2 := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hyx)]
  have hsqhi : (a * s) ^ 2 ≤ 2 := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hxy)]
  have hxlo : (1 / 2 : ℝ) ≤ a * s := by nlinarith
  have hxhi : a * s ≤ 2 := by nlinarith
  have hylo : (1 / 8 : ℝ) ≤ b * s := by linarith
  have hyhi : b * s ≤ 2 := by linarith
  exact ⟨(div_le_iff₀ hs).2 (by linarith), (le_div_iff₀ hs).2 (by linarith),
    (div_le_iff₀ hs).2 (by linarith), (le_div_iff₀ hs).2 (by linarith)⟩

/-- The two half-axis escape probabilities are bounded above and below by constant multiples of
`1 / √n`. -/
theorem strip_halfLine_bounds (n : ℕ) (hn : 1 ≤ n) :
    let a := prob (stripExitsBefore n (axisSet {j | j < 0}) 0)
    let b := prob (stripExitsBefore n (axisSet {j | j ≤ 0}) 0)
    1 / 2 / Real.sqrt n ≤ a ∧ a ≤ 2 / Real.sqrt n ∧
      1 / 8 / Real.sqrt n ≤ b ∧ b ≤ 2 / Real.sqrt n := by
  dsimp only
  let a := prob (stripExitsBefore n (axisSet {j | j < 0}) 0)
  let b := prob (stripExitsBefore n (axisSet {j | j ≤ 0}) 0)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hs2 : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  have hp : a * b = 1 / (2 * (n : ℝ)) := by
    exact (strip_axis_product n).symm.trans (strip_exit_axis_eq n hn)
  have hp' : (a * Real.sqrt n) * (b * Real.sqrt n) = 1 / 2 := by
    calc
      (a * Real.sqrt n) * (b * Real.sqrt n) = (a * b) * (Real.sqrt n * Real.sqrt n) := by ring
      _ = 1 / 2 := by rw [hp, hs2]; field_simp
  exact halfLine_bounds (measureReal_nonneg) (measureReal_nonneg) hs
    (prob_strip_nonpos_le_neg n) (prob_strip_neg_le_four_mul_nonpos n) hp'

/-- Escape from the strictly negative half-axis has probability comparable to `1 / √n`. -/
theorem strip_halfLine_neg :
    Asymp (fun n => stripExitsBefore n (axisSet {j | j < 0}) 0) (fun n => Real.sqrt n) := by
  refine ⟨1 / 2, 2, by norm_num, by norm_num, 1, ?_⟩
  intro n hn
  obtain ⟨h1, h2, _, _⟩ := strip_halfLine_bounds n hn
  exact ⟨by simpa using h1, h2⟩

/-- Escape from the nonnegative half-axis has probability comparable to `1 / √n`. -/
theorem strip_halfLine_nonneg :
    Asymp (fun n => stripExitsBefore n (axisSet {j | 0 ≤ j}) 0) (fun n => Real.sqrt n) := by
  refine ⟨1 / 8, 2, by norm_num, by norm_num, 1, ?_⟩
  intro n hn
  obtain ⟨_, _, h1, h2⟩ := strip_halfLine_bounds n hn
  rw [prob_strip_nonneg_eq_nonpos]
  exact ⟨by simpa using h1, h2⟩

end FiniteAvalanches.Walk.Beurling
