import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Elementary quotient bounds for a clipped test function. -/

namespace FiniteAvalanches.Needle

private theorem abs_div_sub_div_le_of_le
    (a b u v : ℝ) (ha : 0 ≤ a) (hu : 0 < u) (hv : 0 < v)
    (hau : a ≤ 3 * u) (huv : u ≤ v)
    (hab : |a - b| ≤ 3) (hden : |u - v| ≤ 1) :
    |a / u - b / v| ≤ 6 / v := by
  obtain ⟨hablo, habhi⟩ := abs_le.mp hab
  obtain ⟨hdenlo, _⟩ := abs_le.mp hden
  have hupper : a * v - b * u ≤ 6 * u := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 3 * u - a)
      (by linarith : 0 ≤ v - u)]
  have hlower : -(6 * u) ≤ a * v - b * u := by
    nlinarith [mul_nonneg ha (by linarith : 0 ≤ v - u)]
  have he : a / u - b / v = (a * v - b * u) / (u * v) := by
    field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hu hv)]
  apply (div_le_iff₀ (mul_pos hu hv)).mpr
  have he' : (6 / v) * (u * v) = 6 * u := by
    field_simp
  rw [he']
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- A clipped quotient changes by at most six divided by the larger denominator. -/
theorem abs_min_one_div_sub_min_one_div_le
    (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < u) (hv : 0 < v)
    (hau : a ≤ 3 * u) (hbv : b ≤ 3 * v)
    (hab : |a - b| ≤ 3) (hden : |u - v| ≤ 1) :
    |min 1 (a / u) - min 1 (b / v)| ≤ 6 / max u v := by
  have hclip : |min 1 (a / u) - min 1 (b / v)| ≤ |a / u - b / v| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (a / u - b / v))] using
      abs_min_sub_min_le_max (1 : ℝ) (a / u) 1 (b / v)
  apply hclip.trans
  rcases le_total u v with huv | hvu
  · rw [max_eq_right huv]
    exact abs_div_sub_div_le_of_le a b u v ha hu hv hau huv hab hden
  · rw [max_eq_left hvu, abs_sub_comm]
    exact abs_div_sub_div_le_of_le b a v u hb hv hu hbv hvu
      (by simpa only [abs_sub_comm] using hab)
      (by simpa only [abs_sub_comm] using hden)

end FiniteAvalanches.Needle
