import FiniteAvalanches.Electrical.Physical.UnscaledVerticalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp

/-! Exact integration of the unscaled angular kernel on the horizontal unit strip. -/

open Set MeasureTheory

namespace FiniteAvalanches.Electrical.Physical.Unscaled

private theorem continuous_horizontal_max (epsilon : ℝ) (he : 0 < epsilon) :
    Continuous (fun x : ℝ => 1 / max epsilon x) := by
  apply continuous_const.div (continuous_const.max continuous_id)
  intro x
  exact ne_of_gt (he.trans_le (le_max_left epsilon x))

/-- The truncated horizontal reciprocal is integrable on the closed unit interval. -/
theorem integrableOn_horizontal_max (epsilon : ℝ) (he : 0 < epsilon) :
    IntegrableOn (fun x : ℝ => 1 / max epsilon x) (Icc 0 1) volume :=
  (continuous_horizontal_max epsilon he).continuousOn.integrableOn_Icc

/-- Exact horizontal integration for every cutoff in the unit interval. -/
theorem integral_horizontal_max (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    (∫ x : ℝ in Icc 0 1, 1 / max epsilon x ∂volume) = 1 + Real.log (1 / epsilon) := by
  have hc := continuous_horizontal_max epsilon he
  have hleft : (∫ x : ℝ in 0..epsilon, 1 / max epsilon x) = 1 := by
    calc
      _ = ∫ _x : ℝ in 0..epsilon, 1 / epsilon := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le he.le] at hx
        dsimp only
        rw [max_eq_left hx.2]
      _ = 1 := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
        field_simp
  have hright : (∫ x : ℝ in epsilon..1, 1 / max epsilon x) =
      Real.log (1 / epsilon) := by
    calc
      _ = ∫ x : ℝ in epsilon..1, 1 / x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le he1] at hx
        dsimp only
        rw [max_eq_right hx.1]
      _ = Real.log (1 / epsilon) := integral_one_div_of_pos he (by norm_num)
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 epsilon) (hc.intervalIntegrable epsilon 1),
    hleft, hright]

private theorem continuous_strip_kernel (epsilon y0 : ℝ) (he : 0 < epsilon) :
    Continuous (fun z : ℝ × ℝ => 1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2) := by
  apply continuous_const.div
    ((continuous_const.max (continuous_fst.abs.max
      (continuous_snd.sub continuous_const).abs)).pow 2)
  intro z
  exact pow_ne_zero 2 (ne_of_gt (he.trans_le (le_max_left _ _)))

private theorem vertical_slice_eq (epsilon y0 x : ℝ) (hx : 0 ≤ x) :
    (fun y : ℝ => 1 / (max epsilon (max |x| |y - y0|)) ^ 2) =
      (fun y : ℝ => 1 / (max (max epsilon x) |y - y0|) ^ 2) := by
  funext y
  rw [abs_of_nonneg hx, max_assoc]

/-- Product-measure integrability is derived from the exact integrable vertical slices. -/
theorem integrable_strip_kernel_prod (epsilon y0 : ℝ) (he : 0 < epsilon) :
    Integrable (fun z : ℝ × ℝ => 1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
  apply (integrable_prod_iff
    (continuous_strip_kernel epsilon y0 he).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [vertical_slice_eq epsilon y0 x hx.1]
    exact integrable_vertical_max_sub (max epsilon x) y0
      (he.trans_le (le_max_left _ _))
  · apply ((integrableOn_horizontal_max epsilon he).const_mul 4).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hnonneg : ∀ y : ℝ,
        0 ≤ 1 / (max epsilon (max |x| |y - y0|)) ^ 2 := by
      intro y
      positivity
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
    rw [vertical_slice_eq epsilon y0 x hx.1,
      integral_vertical_max_sub (max epsilon x) y0 (he.trans_le (le_max_left _ _))]
    ring

/-- Integrability on the closed unit strip, with the ordinary product Lebesgue volume. -/
theorem integrableOn_strip_kernel (epsilon y0 : ℝ) (he : 0 < epsilon) :
    IntegrableOn (fun z : ℝ × ℝ => 1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2)
      (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) volume := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  exact integrable_strip_kernel_prod epsilon y0 he

/-- The exact strip integral has vertical factor four and no rescaling. -/
theorem integral_strip_kernel (epsilon y0 : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    (∫ z : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ),
      1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2 ∂volume) =
      4 * (1 + Real.log (1 / epsilon)) := by
  rw [Measure.volume_eq_prod,
    setIntegral_prod _ (by
      rw [← Measure.volume_eq_prod]
      exact integrableOn_strip_kernel epsilon y0 he)]
  simp only [setIntegral_univ]
  calc
    _ = ∫ x : ℝ in Icc 0 1, 4 * (1 / max epsilon x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      dsimp only
      rw [vertical_slice_eq epsilon y0 x hx.1,
        integral_vertical_max_sub (max epsilon x) y0 (he.trans_le (le_max_left _ _))]
      ring
    _ = 4 * (∫ x : ℝ in Icc 0 1, 1 / max epsilon x) := integral_const_mul _ _
    _ = 4 * (1 + Real.log (1 / epsilon)) := by
      rw [integral_horizontal_max epsilon he he1]

end FiniteAvalanches.Electrical.Physical.Unscaled
