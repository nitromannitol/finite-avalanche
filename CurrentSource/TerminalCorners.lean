import FiniteAvalanches.Electrical.SplitStep.SignedTerminalMidpoints

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.Source.CurrentTerminalHeight
open scoped Classical

/-- The two endpoint heights, rather than their average, stay on the required side of
the exceptional square at either split adjacent to it. -/
theorem terminal_corner_bounds {m : ℕ} (y : Fin (m + 1) → ℝ) (p : Fin m → ℝ)
    (hp : ∀ k, 0 ≤ p k)
    (hstep : ∀ k, y k.succ - y k.castSucc = p k)
    (i : Fin (m + 1)) (j : Fin m) (hj : j.val + 1 = i.val ∨ j.val = i.val) :
    let y0 := (y j.castSucc + y j.succ) / 2
    ∀ k : Fin m, k ≠ j →
      (k.val < i.val → y k.castSucc - y0 ≤ -(p j / 2) ∧
        y k.succ - y0 ≤ -(p j / 2)) ∧
      (i.val ≤ k.val → p j / 2 ≤ y k.castSucc - y0 ∧
        p j / 2 ≤ y k.succ - y0) := by
  intro y0
  have hmono : Monotone y := Fin.monotone_iff_le_succ.mpr (by
    intro k
    linarith only [hstep k, hp k])
  intro k hkj
  have hneq : k.val ≠ j.val := fun h => hkj (Fin.ext h)
  constructor
  · intro hki
    have hle : k.succ ≤ j.castSucc := by
      change k.val + 1 ≤ j.val
      omega
    have h1 := hmono hle
    have h2 := hmono (Fin.castSucc_le_succ k)
    dsimp only [y0]
    constructor <;> linarith only [h1, h2, hstep j]
  · intro hik
    have hle : j.succ ≤ k.castSucc := by
      change j.val + 1 ≤ k.val
      omega
    have h1 := hmono hle
    have h2 := hmono (Fin.castSucc_le_succ k)
    dsimp only [y0]
    constructor <;> linarith only [h1, h2, hstep j]

/-- Both actual axis corners take the alpha terminal value. The exceptional original
copy is deliberately excluded, and no midpoint conclusion is used. -/
theorem terminal_corner_angular {m : ℕ} (y : Fin (m + 1) → ℝ) (p : Fin m → ℝ)
    (hp : ∀ k, 0 < p k) (hstep : ∀ k, y k.succ - y k.castSucc = p k)
    (i : Fin (m + 1)) (j : Fin m) (hj : j.val + 1 = i.val ∨ j.val = i.val) :
    let y0 := (y j.castSucc + y j.succ) / 2
    ∀ k : Fin m, k ≠ j →
      Geometry.angular (p j / 2) y0 (0, y k.castSucc) = (if k.val < i.val then 0 else 1) ∧
      Geometry.angular (p j / 2) y0 (0, y k.succ) = (if k.val < i.val then 0 else 1) := by
  intro y0 k hkj
  have hb := terminal_corner_bounds y p (fun r => (hp r).le) hstep i j hj k hkj
  have he : 0 < p j / 2 := half_pos (hp j)
  have haxis (r : Fin (m + 1)) :=
    SplitStep.signed_angular_axis_values 1 (p j / 2) y0 (y r) (Or.inl rfl) he
  simp only [one_mul] at haxis
  rw [← SplitStep.signed_angular_eq_angular, ← SplitStep.signed_angular_eq_angular]
  split_ifs with hki
  · exact ⟨(haxis _).1 (hb.1 hki).1, (haxis _).1 (hb.1 hki).2⟩
  · exact ⟨(haxis _).2 (hb.2 (by omega)).1, (haxis _).2 (hb.2 (by omega)).2⟩

end FiniteAvalanches.Electrical.Source.CurrentTerminalHeight
