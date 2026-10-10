module

public import FiniteAvalanches.Electrical.Geometry.DyadicSum

/-! Explicit transport from epsilon = s/10 to the source logarithm. -/
@[expose] public section

namespace FiniteAvalanches.Electrical.Geometry

 theorem log_bound_tenth (theta s : ℝ) (hs : 0 < s) (hst : s ≤ theta) :
    3 + Real.log (theta/(s/10))/Real.log 2 ≤
      (3 + Real.log 10/Real.log 2 + 1/Real.log 2)*(1+Real.log (theta/s)) := by
  have hr : 1 ≤ theta/s := (le_div_iff₀ hs).mpr (by simpa using hst)
  have hp : 0 < theta/s := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hr
  have hL : 0 ≤ Real.log (theta/s) := Real.log_nonneg hr
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h10 : 0 ≤ Real.log 10/Real.log 2 :=
    div_nonneg (Real.log_nonneg (by norm_num)) h2.le
  have hb : 0 ≤ 1/Real.log 2 := by positivity
  have heq : theta/(s/10) = 10*(theta/s) := by ring
  rw [heq, Real.log_mul (by norm_num : (10:ℝ) ≠ 0) hp.ne']
  have ha : 3+Real.log 10/Real.log 2 ≤ 3+Real.log 10/Real.log 2+1/Real.log 2 := by linarith only [hb]
  have hc : 1/Real.log 2 ≤ 3+Real.log 10/Real.log 2+1/Real.log 2 := by linarith only [h10]
  have hm := mul_le_mul_of_nonneg_right hc hL
  calc
    _ = (3+Real.log 10/Real.log 2) + (1/Real.log 2)*Real.log (theta/s) := by ring
    _ ≤ (3+Real.log 10/Real.log 2+1/Real.log 2) +
        (3+Real.log 10/Real.log 2+1/Real.log 2)*Real.log (theta/s) := add_le_add ha hm
    _ = _ := by ring

end FiniteAvalanches.Electrical.Geometry
