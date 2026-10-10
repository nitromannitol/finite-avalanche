import FiniteAvalanches.Electrical.SplitStep.OriginalStreamIncrements
import FiniteAvalanches.Electrical.Geometry.BoundaryMidpoints
import Mathlib.Order.Fin.Basic

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open scoped Classical
noncomputable section

/-- Each of the two adjacent exceptional copies gives the same signed half-current separation. -/
theorem signed_terminal_midpoint_bounds {m : ℕ} (y : Fin (m + 1) → ℝ)
    (p : Fin m → ℝ) (hp : ∀ k, 0 ≤ p k) (sigma : ℝ)
    (hstep : ∀ k, sigma * (y k.succ - y k.castSucc) = p k)
    (i : Fin (m + 1)) (j : Fin m) (hj : j.val + 1 = i.val ∨ j.val = i.val) :
    let w := fun k : Fin m => (y k.castSucc + y k.succ) / 2
    ∀ k : Fin m, k ≠ j →
      (k.val < i.val → sigma * (w k - w j) ≤ -(p j / 2)) ∧
      (i.val ≤ k.val → p j / 2 ≤ sigma * (w k - w j)) := by
  intro w
  let h := fun k : Fin (m + 1) => sigma * y k
  have hs (k : Fin m) : h k.succ - h k.castSucc = p k := by
    simpa only [h, mul_sub] using hstep k
  have hmono : Monotone h := Fin.monotone_iff_le_succ.mpr (fun k => by
    have hh := hs k
    linarith only [hh, hp k])
  intro k hkj
  have hne : k.val ≠ j.val := fun he => hkj (Fin.ext he)
  have hw : sigma * (w k - w j) =
      (h k.castSucc + h k.succ - h j.castSucc - h j.succ) / 2 := by
    dsimp only [w, h]
    ring
  have hk := hmono (Fin.castSucc_le_succ k)
  have hjstep := hs j
  constructor
  · intro hki
    have hij : k.succ ≤ j.castSucc := by
      change k.val + 1 ≤ j.val
      rcases hj with hj | hj <;> omega
    have hh := hmono hij
    rw [hw]
    linarith only [hh, hk, hjstep]
  · intro hik
    have hij : j.succ ≤ k.castSucc := by
      change j.val + 1 ≤ k.val
      rcases hj with hj | hj <;> omega
    have hh := hmono hij
    rw [hw]
    linarith only [hh, hk, hjstep]

/-- Numerical sign choice leaves the angular oscillation comparisons unchanged. -/
def signedAngular (sigma epsilon y0 : ℝ) (z : ℝ × ℝ) : ℝ :=
  1 / 2 + sigma * (z.2 - y0) /
    (2 * max epsilon (max |z.1| |z.2 - y0|))

theorem signed_angular_eq_angular (epsilon y0 : ℝ) (z : ℝ × ℝ) :
    signedAngular 1 epsilon y0 z = Geometry.angular epsilon y0 z := by
  simp only [signedAngular, one_mul, Geometry.angular, Geometry.radialDistance]

theorem signed_angular_neg_eq_one_sub (epsilon y0 : ℝ) (z : ℝ × ℝ) :
    signedAngular (-1) epsilon y0 z = 1 - Geometry.angular epsilon y0 z := by
  unfold signedAngular Geometry.angular Geometry.radialDistance
  ring

/-- Signed midpoint separation fixes the actual zero/one alpha values without reflecting a drawing. -/
theorem signed_angular_axis_values (sigma epsilon y0 y : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) (he : 0 < epsilon) :
    (sigma * (y - y0) ≤ -epsilon → signedAngular sigma epsilon y0 (0, y) = 0) ∧
    (epsilon ≤ sigma * (y - y0) → signedAngular sigma epsilon y0 (0, y) = 1) := by
  rcases hsigma with rfl | rfl
  · rw [signed_angular_eq_angular]
    constructor
    · intro hy
      apply Geometry.angular_axis_eq_zero _ _ _ he
      linarith only [hy]
    · intro hy
      apply Geometry.angular_axis_eq_one _ _ _ he
      linarith only [hy]
  · rw [signed_angular_neg_eq_one_sub]
    constructor
    · intro hy
      have h := Geometry.angular_axis_eq_one epsilon y0 y he (by linarith only [hy])
      rw [h, sub_self]
    · intro hy
      have h := Geometry.angular_axis_eq_zero epsilon y0 y he (by linarith only [hy])
      rw [h, sub_zero]

end
end FiniteAvalanches.Electrical.SplitStep
