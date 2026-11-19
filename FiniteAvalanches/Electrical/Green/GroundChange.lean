import FiniteAvalanches.Electrical.Green.Current

/-! Voltage differences are independent of the chosen ground. -/

set_option autoImplicit false

namespace FiniteAvalanches.Electrical

open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The full Laplacian of a grounded Green column injects at its source and
extracts at the ground, including coincident source and ground. -/
theorem groundedGreen_laplacian_full (a b : E → V) (g : V)
    (hc : (supportGraph a b).Preconnected) (u x : V) :
    laplacian a b (groundedGreen a b g hc u) x =
      (if x = u then (1 : ℝ) else 0) - (if x = g then 1 else 0) := by
  by_cases hx : x = g
  · subst x
    by_cases hu : u = g
    · subst u
      rw [groundedGreen_ground_source]
      simp only [ite_true, sub_self]
      exact laplacian_const a b 0 g
    · rw [groundedGreen_laplacian_ground a b g hc u hu]
      simp [Ne.symm hu]
  · rw [groundedGreen_laplacian a b g hc u x hx]
    simp [hx]

/-- The voltage between two vertices due to a unit source and sink is independent
of the vertex used to ground the Green kernel. -/
theorem groundedGreen_double_difference_ground_independent (a b : E → V)
    (g h : V) (hc : (supportGraph a b).Preconnected) (u v x y : V) :
    groundedGreen a b g hc u x - groundedGreen a b g hc v x -
        groundedGreen a b g hc u y + groundedGreen a b g hc v y =
      groundedGreen a b h hc u x - groundedGreen a b h hc v x -
        groundedGreen a b h hc u y + groundedGreen a b h hc v y := by
  let r : V → ℝ := fun z => (if z = u then 1 else 0) - (if z = v then 1 else 0)
  let p : V → ℝ := fun z => groundedGreen a b g hc u z - groundedGreen a b g hc v z -
    (groundedGreen a b g hc u h - groundedGreen a b g hc v h)
  let q : V → ℝ := fun z => groundedGreen a b h hc u z - groundedGreen a b h hc v z
  have hp : p h = 0 ∧ ∀ z, z ≠ h → laplacian a b p z = r z := by
    constructor
    · simp [p]
    · intro z _
      change laplacian a b ((groundedGreen a b g hc u - groundedGreen a b g hc v) -
        fun _ => groundedGreen a b g hc u h - groundedGreen a b g hc v h) z = _
      rw [laplacian_sub, laplacian_sub, laplacian_const,
        groundedGreen_laplacian_full, groundedGreen_laplacian_full]
      dsimp [r]
      ring
  have hq : q h = 0 ∧ ∀ z, z ≠ h → laplacian a b q z = r z := by
    constructor
    · simp [q, groundedGreen_ground]
    · intro z _
      change laplacian a b (groundedGreen a b h hc u - groundedGreen a b h hc v) z = _
      rw [laplacian_sub, groundedGreen_laplacian_full, groundedGreen_laplacian_full]
      dsimp [r]
      ring
  have he : p = q := (groundedPoisson_eq a b h hc r p hp).trans
    (groundedPoisson_eq a b h hc r q hq).symm
  have hx := congrFun he x
  have hy := congrFun he y
  dsimp [p, q] at hx hy
  linarith

end FiniteAvalanches.Electrical
