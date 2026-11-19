import LatticeProb.LinearAlgebra.DeterminantCoefficient
import Mathlib.Data.Real.Basic

/-! The linear coefficient of the resistance determinant is a Green-function minor. -/

set_option autoImplicit false

namespace FiniteAvalanches.Electrical

open Polynomial

/-- Row and column terms cancel when the resistance determinant is reduced to its
linear coefficient. This applies in particular to a grounded Green function. -/
theorem resistanceDet_coeff_one {V : Type*} {n : ℕ} (G : V → V → ℝ)
    (a b : Fin (n + 1) → V) :
    ((Matrix.of fun i j : Fin (n + 1) =>
      (X : Polynomial ℝ) - C ((G (a i) (a i) + G (b j) (b j) - 2 * G (a i) (b j)) / 2)).det).coeff 1 =
      (Matrix.of fun i j : Fin n =>
        G (a i.succ) (b j.succ) - G (a 0) (b j.succ) -
          G (a i.succ) (b 0) + G (a 0) (b 0)).det := by
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
    -((G (a i) (a i) + G (b j) (b j) - 2 * G (a i) (b j)) / 2)
  have h := LatticeProb.LinearAlgebra.det_X_add_C_coeff_one M
  have hmat : (Matrix.of fun i j : Fin n =>
      M i.succ j.succ - M 0 j.succ - M i.succ 0 + M 0 0) =
      (Matrix.of fun i j : Fin n =>
        G (a i.succ) (b j.succ) - G (a 0) (b j.succ) -
          G (a i.succ) (b 0) + G (a 0) (b 0)) := by
    ext i j
    dsimp [M]
    ring
  rw [hmat] at h
  simpa only [M, map_neg, sub_eq_add_neg] using h

end FiniteAvalanches.Electrical
