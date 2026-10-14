import FiniteAvalanches.Needle.Direct.Ratio
import FiniteAvalanches.Needle.Geometry

/-! A lattice test function for a box joined to a boundary vertex. -/

namespace FiniteAvalanches.Needle
open LatticeProb

/-- A clipped quotient of the depth in the box and distance from the boundary vertex. -/
noncomputable def needleTestFunction (h : ℕ) (w x : Point) : ℝ :=
  min 1 (3 * max 0 (2 * (h : ℝ) + 1 - (radius x : ℝ)) /
    (1 + (linf x w : ℝ)))

theorem needle_test_function_nonneg (h : ℕ) (w x : Point) :
    0 ≤ needleTestFunction h w x := by
  apply le_min (by norm_num)
  exact div_nonneg (mul_nonneg (by norm_num) (le_max_left _ _))
    (by have := radius_nonneg (x - w); dsimp only [linf]; positivity)

theorem needle_test_function_le_one (h : ℕ) (w x : Point) :
    needleTestFunction h w x ≤ 1 := min_le_left _ _

theorem needle_test_function_eq_zero_of_outside (h : ℕ) (w x : Point)
    (hx : x ∉ box 2 (2 * h)) : needleTestFunction h w x = 0 := by
  have hr : (2 * h : ℤ) + 1 ≤ radius x := by
    rw [mem_box_iff] at hx
    push_cast at hx ⊢
    omega
  have hr' : 2 * (h : ℝ) + 1 ≤ (radius x : ℝ) := by exact_mod_cast hr
  simp only [needleTestFunction, max_eq_left (by linarith :
    2 * (h : ℝ) + 1 - (radius x : ℝ) ≤ 0), mul_zero, zero_div,
    min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem needle_test_function_eq_one_on_box (h : ℕ) (w x : Point)
    (hw : radius w = 2 * h) (hx : x ∈ box 2 h) :
    needleTestFunction h w x = 1 := by
  have hr : (radius x : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast (mem_box_iff x h).mp hx
  have hd : (linf x w : ℝ) ≤ 3 * (h : ℝ) := by
    have hh := radius_sub_le x w
    rw [hw] at hh
    dsimp only [linf]
    exact_mod_cast (by have := (mem_box_iff x h).mp hx; omega :
      radius (x - w) ≤ 3 * (h : ℤ))
  have hn : 0 ≤ (linf x w : ℝ) := by exact_mod_cast radius_nonneg (x - w)
  apply min_eq_left
  apply (le_div_iff₀ (by linarith : 0 < 1 + (linf x w : ℝ))).mpr
  have hm := le_max_right (0 : ℝ) (2 * (h : ℝ) + 1 - (radius x : ℝ))
  nlinarith

theorem needle_test_function_eq_one_of_distance_le (h : ℕ) (w x : Point)
    (hx : linf x w ≤ 2 * (2 * h - radius x) + 1) :
    needleTestFunction h w x = 1 := by
  have hd : (linf x w : ℝ) ≤ 2 * (2 * (h : ℝ) - (radius x : ℝ)) + 1 := by
    exact_mod_cast hx
  have hn : 0 ≤ (linf x w : ℝ) := by exact_mod_cast radius_nonneg (x - w)
  apply min_eq_left
  apply (le_div_iff₀ (by linarith : 0 < 1 + (linf x w : ℝ))).mpr
  have hm := le_max_right (0 : ℝ) (2 * (h : ℝ) + 1 - (radius x : ℝ))
  nlinarith

theorem needle_test_numerator_le_denominator (h : ℕ) (w x : Point)
    (hw : radius w = 2 * h) :
    3 * max 0 (2 * (h : ℝ) + 1 - (radius x : ℝ)) ≤
      3 * (1 + (linf x w : ℝ)) := by
  have hh := radius_le_radius_add w x
  rw [hw] at hh
  have he : radius (w - x) = radius (x - w) := by
    simp only [radius, Pi.sub_apply, abs_sub_comm]
  rw [he] at hh
  have hh' : 2 * (h : ℝ) ≤ (linf x w : ℝ) + (radius x : ℝ) := by
    exact_mod_cast hh
  have hn : 0 ≤ (linf x w : ℝ) := by exact_mod_cast radius_nonneg (x - w)
  have hm : max 0 (2 * (h : ℝ) + 1 - (radius x : ℝ)) ≤
      1 + (linf x w : ℝ) := max_le (by linarith) (by linarith)
  linarith

end FiniteAvalanches.Needle
