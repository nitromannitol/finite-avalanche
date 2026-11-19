import FiniteAvalanches.Electrical.Trees.ResistanceMinor
import FiniteAvalanches.Electrical.Green.GroundChange

/-! The resistance determinant's linear coefficient is independent of the ground. -/

set_option autoImplicit false

namespace FiniteAvalanches.Electrical

open Polynomial

/-- The linear resistance-determinant coefficient does not depend on the
choice of ground, even when terminal vertices coincide with a ground. -/
theorem resistanceDet_coeff_one_ground_independent {V E : Type} [Fintype V] [Fintype E]
    (l r : E → V) (g h : V) (hc : (supportGraph l r).Preconnected)
    {n : ℕ} (a b : Fin (n + 1) → V) :
    ((Matrix.of fun i j : Fin (n + 1) =>
      (X : Polynomial ℝ) - C ((groundedGreen l r g hc (a i) (a i) +
        groundedGreen l r g hc (b j) (b j) - 2 * groundedGreen l r g hc (a i) (b j)) / 2)).det).coeff 1 =
    ((Matrix.of fun i j : Fin (n + 1) =>
      (X : Polynomial ℝ) - C ((groundedGreen l r h hc (a i) (a i) +
        groundedGreen l r h hc (b j) (b j) - 2 * groundedGreen l r h hc (a i) (b j)) / 2)).det).coeff 1 := by
  rw [resistanceDet_coeff_one, resistanceDet_coeff_one]
  congr 1
  ext i j
  exact groundedGreen_double_difference_ground_independent l r g h hc (a i.succ) (a 0)
    (b j.succ) (b 0)

end FiniteAvalanches.Electrical
