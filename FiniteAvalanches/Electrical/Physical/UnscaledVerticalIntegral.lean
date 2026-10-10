import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set MeasureTheory

namespace FiniteAvalanches.Electrical.Physical.Unscaled

private theorem vertical_max_positive_half (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => 1 / (max a |y|) ^ 2) (Ioi 0) ∧
      (∫ y : ℝ in Ioi 0, 1 / (max a |y|) ^ 2) = 2 / a := by
  have hcenter_eq : EqOn (fun y : ℝ => 1 / (max a |y|) ^ 2)
      (fun _ : ℝ => 1 / a ^ 2) (Ioc 0 a) := by
    intro y hy
    dsimp only
    rw [abs_of_pos hy.1, max_eq_left hy.2]
  have htail_eq : EqOn (fun y : ℝ => 1 / (max a |y|) ^ 2)
      (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi a) := by
    intro y hy
    have hypos : 0 < y := ha.trans hy
    dsimp only
    rw [abs_of_pos hypos, max_eq_right hy.le,
      show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg hypos.le, Real.rpow_two]
    simp only [one_div]
  have hconst : IntegrableOn (fun _ : ℝ => 1 / a ^ 2) (Ioc 0 a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp intervalIntegrable_const
  have hcenter : IntegrableOn (fun y : ℝ => 1 / (max a |y|) ^ 2) (Ioc 0 a) :=
    hconst.congr_fun hcenter_eq.symm measurableSet_Ioc
  have hpower : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha
  have htail : IntegrableOn (fun y : ℝ => 1 / (max a |y|) ^ 2) (Ioi a) :=
    hpower.congr_fun htail_eq.symm measurableSet_Ioi
  have hcenter_value : (∫ y : ℝ in Ioc 0 a, 1 / (max a |y|) ^ 2) = 1 / a := by
    calc
      _ = ∫ _ : ℝ in Ioc 0 a, 1 / a ^ 2 :=
        setIntegral_congr_fun measurableSet_Ioc hcenter_eq
      _ = ∫ _ : ℝ in (0 : ℝ)..a, 1 / a ^ 2 :=
        (intervalIntegral.integral_of_le ha.le).symm
      _ = 1 / a := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        field_simp [ha.ne']
  have htail_value : (∫ y : ℝ in Ioi a, 1 / (max a |y|) ^ 2) = 1 / a := by
    calc
      _ = ∫ y : ℝ in Ioi a, y ^ (-2 : ℝ) :=
        setIntegral_congr_fun measurableSet_Ioi htail_eq
      _ = -a ^ ((-2 : ℝ) + 1) / ((-2 : ℝ) + 1) :=
        integral_Ioi_rpow_of_lt (by norm_num) ha
      _ = 1 / a := by norm_num [Real.rpow_neg_one, one_div]
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hcenter htail
  rw [Ioc_union_Ioi_eq_Ioi ha.le] at hsplit
  constructor
  · simpa only [Ioc_union_Ioi_eq_Ioi ha.le] using hcenter.union htail
  · rw [hsplit, hcenter_value, htail_value]
    ring

/-- The unscaled vertical kernel is integrable for every positive cutoff. -/
theorem integrable_vertical_max (a : ℝ) (ha : 0 < a) :
    Integrable (fun y : ℝ => 1 / (max a |y|) ^ 2) := by
  have hpos := (vertical_max_positive_half a ha).1
  have hpos' : IntegrableOn (fun y : ℝ => 1 / (max a |y|) ^ 2)
      (Ioi (-(0 : ℝ))) := by
    simpa only [neg_zero] using hpos
  have hneg_open : IntegrableOn (fun y : ℝ => 1 / (max a |y|) ^ 2)
      (Iio (0 : ℝ)) := by
    simpa only [abs_neg] using hpos'.comp_neg_Iio (c := (0 : ℝ))
  have hneg : IntegrableOn (fun y : ℝ => 1 / (max a |y|) ^ 2) (Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio
      (f := fun y : ℝ => 1 / (max a |y|) ^ 2) (b := (0 : ℝ)) (μ := volume)).mpr hneg_open
  apply integrableOn_univ.mp
  simpa only [Iic_union_Ioi] using hneg.union hpos

/-- The exact unscaled vertical integral, including both tails. -/
theorem integral_vertical_max (a : ℝ) (ha : 0 < a) :
    (∫ y : ℝ, 1 / (max a |y|) ^ 2) = 4 / a := by
  have hhalf : (∫ y : ℝ in Ioi 0, 1 / (max a y) ^ 2) = 2 / a := by
    calc
      _ = ∫ y : ℝ in Ioi 0, 1 / (max a |y|) ^ 2 := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro y hy
        dsimp only
        rw [abs_of_pos hy]
      _ = 2 / a := (vertical_max_positive_half a ha).2
  calc
    _ = 2 * (∫ y : ℝ in Ioi 0, 1 / (max a y) ^ 2) :=
      integral_comp_abs (f := fun y : ℝ => 1 / (max a y) ^ 2)
    _ = 4 / a := by rw [hhalf]; ring

/-- Translation preserves integrability of the vertical kernel. -/
theorem integrable_vertical_max_sub (a y₀ : ℝ) (ha : 0 < a) :
    Integrable (fun y : ℝ => 1 / (max a |y - y₀|) ^ 2) := by
  exact (integrable_vertical_max a ha).comp_sub_right y₀

/-- The same sharp integral holds around an arbitrary vertical center. -/
theorem integral_vertical_max_sub (a y₀ : ℝ) (ha : 0 < a) :
    (∫ y : ℝ, 1 / (max a |y - y₀|) ^ 2) = 4 / a := by
  calc
    _ = ∫ y : ℝ, 1 / (max a |y|) ^ 2 :=
      integral_sub_right_eq_self (fun y : ℝ => 1 / (max a |y|) ^ 2) y₀
    _ = 4 / a := integral_vertical_max a ha

end FiniteAvalanches.Electrical.Physical.Unscaled
