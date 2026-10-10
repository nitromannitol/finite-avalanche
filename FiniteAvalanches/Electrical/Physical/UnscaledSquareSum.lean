import FiniteAvalanches.Electrical.Physical.UnscaledStripIntegral
import FiniteAvalanches.Electrical.Physical.UnscaledSquareOscillation

/-! The sharp unscaled angular square sum, using open carriers throughout. -/

open Set MeasureTheory
open scoped BigOperators
open FiniteAvalanches.Electrical.Geometry

namespace FiniteAvalanches.Electrical.Physical.Unscaled

/-- A point square has zero actual angular oscillation on its triple dilation. -/
theorem square_angularOsc_eq_zero_of_side_eq_zero (Q : Square) (epsilon y0 : ℝ)
    (he : 0 < epsilon) (hs : Q.side = 0) :
    Q.angularOsc epsilon y0 3 (by norm_num) he = 0 := by
  have hz : (Q.x, Q.y) ∈ Q.carrier :=
    ⟨⟨le_rfl, by linarith only [Q.side_nonneg]⟩,
      ⟨le_rfl, by linarith only [Q.side_nonneg]⟩⟩
  have hb := square_angularOsc_le_six Q epsilon y0 he (Q.x, Q.y) hz
  rw [hs, mul_zero, zero_div] at hb
  exact le_antisymm hb (Q.angularOsc_bounds epsilon y0 3 he (by norm_num)).1

/-- Integrate the squared six-side estimate on the open carrier and cancel its positive area.
The point-square branch occurs before area cancellation. -/
theorem square_angularOsc_sq_le_integral (Q : Square) (epsilon y0 : ℝ)
    (he : 0 < epsilon)
    (hQ : Q.carrier ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :
    (Q.angularOsc epsilon y0 3 (by norm_num) he) ^ 2 ≤
      36 * (∫ z : ℝ × ℝ in Q.openCarrier,
        1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2 ∂volume) := by
  by_cases hs : Q.side = 0
  · rw [square_angularOsc_eq_zero_of_side_eq_zero Q epsilon y0 he hs, zero_pow (by decide)]
    exact mul_nonneg (by norm_num)
      (setIntegral_nonneg Q.measurableSet_openCarrier (fun _ _ => by positivity))
  · have hspos : 0 < Q.side := lt_of_le_of_ne Q.side_nonneg (Ne.symm hs)
    have harea : 0 < Q.side ^ 2 := sq_pos_of_pos hspos
    have hK := (integrableOn_strip_kernel epsilon y0 he).mono_set
      (Q.openCarrier_subset_carrier.trans hQ)
    have hconst : IntegrableOn (fun _z : ℝ × ℝ =>
        (Q.angularOsc epsilon y0 3 (by norm_num) he) ^ 2) Q.openCarrier volume :=
      integrableOn_const (by rw [Q.volume_openCarrier]; exact ENNReal.ofReal_ne_top)
    have hb0 := (Q.angularOsc_bounds epsilon y0 3 he (by norm_num)).1
    have hpoint : ∀ z ∈ Q.openCarrier,
        (Q.angularOsc epsilon y0 3 (by norm_num) he) ^ 2 ≤
          (36 * Q.side ^ 2) * (1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2) := by
      intro z hz
      have hb := square_angularOsc_le_six Q epsilon y0 he z
        (Q.openCarrier_subset_carrier hz)
      calc
        _ ≤ (6 * Q.side / max epsilon (radialDistance y0 z)) ^ 2 := by
          simpa only [pow_two] using mul_self_le_mul_self hb0 hb
        _ = _ := by unfold radialDistance; ring
    have hint := setIntegral_mono_on hconst (hK.const_mul (36 * Q.side ^ 2))
      Q.measurableSet_openCarrier hpoint
    rw [setIntegral_const, smul_eq_mul, Q.area_openCarrier, integral_const_mul] at hint
    apply (mul_le_mul_iff_right₀ harea).mp
    calc
      _ = Q.side ^ 2 * (Q.angularOsc epsilon y0 3 (by norm_num) he) ^ 2 := by ring
      _ ≤ (36 * Q.side ^ 2) * (∫ z : ℝ × ℝ in Q.openCarrier,
          1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2 ∂volume) := hint
      _ = _ := by ring

/-- Sharp 144 for any finite family of original squares in the unit strip, including point squares.
Only disjoint open interiors and closed-carrier containment are assumed. -/
theorem angular_square_sum_le_144 {I : Type*} (s : Finset I) (Q : I → Square)
    (hd : Set.PairwiseDisjoint (↑s) (fun i => (Q i).openCarrier))
    (epsilon y0 : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hQ : ∀ i ∈ s, (Q i).carrier ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :
    (∑ i ∈ s, ((Q i).angularOsc epsilon y0 3 (by norm_num) he) ^ 2) ≤
      144 * (1 + Real.log (1 / epsilon)) := by
  have hstrip := integrableOn_strip_kernel epsilon y0 he
  have hK : ∀ i ∈ s, IntegrableOn
      (fun z : ℝ × ℝ => 1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2)
      (Q i).openCarrier volume :=
    fun i hi => hstrip.mono_set ((Q i).openCarrier_subset_carrier.trans (hQ i hi))
  have hU : (⋃ i ∈ s, (Q i).openCarrier) ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    intro z hz
    obtain ⟨i, hi, hz⟩ := Set.mem_iUnion₂.mp hz
    exact hQ i hi ((Q i).openCarrier_subset_carrier hz)
  have hmono := setIntegral_mono_set hstrip
    (Filter.Eventually.of_forall (fun _z => by positivity))
    (Filter.Eventually.of_forall hU)
  calc
    _ ≤ ∑ i ∈ s, 36 * (∫ z : ℝ × ℝ in (Q i).openCarrier,
        1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2 ∂volume) :=
      Finset.sum_le_sum (fun i hi => square_angularOsc_sq_le_integral (Q i) epsilon y0 he (hQ i hi))
    _ = 36 * (∫ z : ℝ × ℝ in ⋃ i ∈ s, (Q i).openCarrier,
        1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2 ∂volume) := by
      rw [integral_biUnion_finset s (fun i _ => (Q i).measurableSet_openCarrier) hd hK,
        Finset.mul_sum]
    _ ≤ 36 * (∫ z : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ),
        1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2 ∂volume) :=
      mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = 144 * (1 + Real.log (1 / epsilon)) := by
      rw [integral_strip_kernel epsilon y0 he he1]
      ring

/-- The physical cutoff is literally p/2 and yields log(2/p), for each supplied positive current. -/
theorem angular_square_sum_cutoff_le_144 {I : Type*} (s : Finset I) (Q : I → Square)
    (hd : Set.PairwiseDisjoint (↑s) (fun i => (Q i).openCarrier))
    (p y0 : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hQ : ∀ i ∈ s, (Q i).carrier ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :
    (∑ i ∈ s, ((Q i).angularOsc (p / 2) y0 3 (by norm_num) (by positivity)) ^ 2) ≤
      144 * (1 + Real.log (2 / p)) := by
  have he : 0 < p / 2 := by positivity
  have he1 : p / 2 ≤ 1 := by linarith only [hp1]
  have hrecip : 1 / (p / 2) = 2 / p := by ring
  simpa only [hrecip] using angular_square_sum_le_144 s Q hd (p / 2) y0 he he1 hQ

end FiniteAvalanches.Electrical.Physical.Unscaled
