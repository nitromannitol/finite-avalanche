import FiniteAvalanches.Electrical.Geometry.Oscillation

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Physical.Unscaled
open Geometry

private theorem pointDist_le_two_side (Q : Square) (z u : ℝ × ℝ)
    (hz : z ∈ Q.carrier) (hu : u ∈ (Q.dilate 3 (by norm_num)).carrier) :
    pointDist z u ≤ 2 * Q.side := by
  have hs := Q.side_nonneg
  change (Q.x - (3 - 1) * Q.side / 2 ≤ u.1 ∧
      u.1 ≤ Q.x - (3 - 1) * Q.side / 2 + 3 * Q.side) ∧
    (Q.y - (3 - 1) * Q.side / 2 ≤ u.2 ∧
      u.2 ≤ Q.y - (3 - 1) * Q.side / 2 + 3 * Q.side) at hu
  apply max_le
  · exact abs_le.mpr ⟨by linarith [hz.1.1, hu.1.2], by linarith [hz.1.2, hu.1.1]⟩
  · exact abs_le.mpr ⟨by linarith [hz.2.1, hu.2.2], by linarith [hz.2.2, hu.2.1]⟩

/-- The literal six-side pointwise oscillation bound, including point squares. -/
theorem square_angularOsc_le_six (Q : Square) (epsilon y0 : ℝ) (he : 0 < epsilon)
    (z : ℝ × ℝ) (hz : z ∈ Q.carrier) :
    Q.angularOsc epsilon y0 3 (by norm_num) he ≤
      6 * Q.side / max epsilon (radialDistance y0 z) := by
  let r := max epsilon (radialDistance y0 z)
  have hr : 0 < r := lt_of_lt_of_le he (le_max_left _ _)
  have hs := Q.side_nonneg
  apply oscillation_le
  intro u hu v hv
  by_cases hsmall : r ≤ 6 * Q.side
  · exact (angular_sub_le_one epsilon y0 he u v).trans
      ((le_div_iff₀ hr).mpr (by simpa only [one_mul] using hsmall))
  · let Du := max epsilon (radialDistance y0 u)
    have hDu : 0 < Du := lt_of_lt_of_le he (le_max_left _ _)
    have hrDu : r ≤ 2 * Du := by
      by_cases hz1 : radialDistance y0 z ≤ epsilon
      · have hre : r = epsilon := max_eq_left hz1
        have hu1 : epsilon ≤ Du := le_max_left _ _
        rw [hre]
        linarith only [hu1, he]
      · have hre : r = radialDistance y0 z := max_eq_right (le_of_not_ge hz1)
        have hdist := (radialDistance_sub_le y0 z u).trans (pointDist_le_two_side Q z u hz hu)
        have huD : radialDistance y0 u ≤ Du := le_max_right _ _
        have hcorner : r ≤ Du + 2 * Q.side := by
          rw [hre]
          linarith only [(abs_le.mp hdist).2, huD]
        have hlarge : 6 * Q.side < r := lt_of_not_ge hsmall
        linarith only [hcorner, hlarge, hs]
    have hdiam := pointDist_le_of_mem_square (Q.dilate 3 (by norm_num)) u v hu hv
    change pointDist u v ≤ 3 * Q.side at hdiam
    calc
      |angular epsilon y0 u - angular epsilon y0 v| ≤ pointDist u v / Du :=
        angular_sub_le epsilon y0 he u v
      _ ≤ 3 * Q.side / Du := div_le_div_of_nonneg_right hdiam hDu.le
      _ ≤ 6 * Q.side / r := (div_le_div_iff₀ hDu hr).mpr (by
        calc
          3 * Q.side * r ≤ 3 * Q.side * (2 * Du) :=
            mul_le_mul_of_nonneg_left hrDu (mul_nonneg (by norm_num) hs)
          _ = 6 * Q.side * Du := by ring)

end FiniteAvalanches.Electrical.Physical.Unscaled
