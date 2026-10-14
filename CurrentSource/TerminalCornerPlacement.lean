import Mathlib.Order.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Half-current separation of both actual boundary-square corners. -/

namespace FiniteAvalanches.Electrical.SplitStep

/-- Both corners of every other boundary square are separated from the exceptional
square's center by half its current, for either adjacent choice of the exception. -/
theorem signed_terminal_corner_bounds {m : ℕ} (y : Fin (m + 1) → ℝ)
    (p : Fin m → ℝ) (hp : ∀ k, 0 ≤ p k) (sigma : ℝ)
    (hstep : ∀ k, sigma * (y k.succ - y k.castSucc) = p k)
    (i : Fin (m + 1)) (j : Fin m) (hj : j.val + 1 = i.val ∨ j.val = i.val) :
    let y0 := (y j.castSucc + y j.succ) / 2
    ∀ k : Fin m, k ≠ j →
      (k.val < i.val →
        sigma * (y k.castSucc - y0) ≤ -(p j / 2) ∧
          sigma * (y k.succ - y0) ≤ -(p j / 2)) ∧
      (i.val ≤ k.val →
        p j / 2 ≤ sigma * (y k.castSucc - y0) ∧
          p j / 2 ≤ sigma * (y k.succ - y0)) := by
  intro y0
  let h := fun k : Fin (m + 1) => sigma * y k
  have hs (k : Fin m) : h k.succ - h k.castSucc = p k := by
    simpa only [h, mul_sub] using hstep k
  have hmono : Monotone h := Fin.monotone_iff_le_succ.mpr (fun k => by
    linarith only [hs k, hp k])
  have hcenter (z : Fin (m + 1)) : sigma * (y z - y0) =
      h z - (h j.castSucc + h j.succ) / 2 := by
    dsimp only [y0, h]
    ring
  intro k hkj
  have hne : k.val ≠ j.val := fun he => hkj (Fin.ext he)
  have hjstep := hs j
  have hkstep := hmono (Fin.castSucc_le_succ k)
  constructor
  · intro hki
    have hidx : k.succ ≤ j.castSucc := by
      change k.val + 1 ≤ j.val
      rcases hj with hj | hj <;> omega
    have hk := hmono hidx
    rw [hcenter, hcenter]
    constructor <;> linarith only [hk, hkstep, hjstep]
  · intro hik
    have hidx : j.succ ≤ k.castSucc := by
      change j.val + 1 ≤ k.val
      rcases hj with hj | hj <;> omega
    have hk := hmono hidx
    rw [hcenter, hcenter]
    constructor <;> linarith only [hk, hkstep, hjstep]

end FiniteAvalanches.Electrical.SplitStep
