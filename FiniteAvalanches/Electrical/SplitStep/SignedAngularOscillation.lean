import FiniteAvalanches.Electrical.SplitStep.SignedTerminalMidpoints

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep

/-- Both numerical orientations have identical pointwise oscillations on the same coordinates. -/
theorem signed_angular_abs_sub (sigma epsilon y0 : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) (z w : ℝ × ℝ) :
    |signedAngular sigma epsilon y0 z - signedAngular sigma epsilon y0 w| =
      |Geometry.angular epsilon y0 z - Geometry.angular epsilon y0 w| := by
  rcases hsigma with rfl | rfl
  · rw [signed_angular_eq_angular, signed_angular_eq_angular]
  · rw [signed_angular_neg_eq_one_sub, signed_angular_neg_eq_one_sub]
    have h : (1 - Geometry.angular epsilon y0 z) - (1 - Geometry.angular epsilon y0 w) =
        Geometry.angular epsilon y0 w - Geometry.angular epsilon y0 z := by ring
    rw [h, abs_sub_comm]

end FiniteAvalanches.Electrical.SplitStep
