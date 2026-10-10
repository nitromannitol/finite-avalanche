import FiniteAvalanches.Electrical.PairContact.Combinatorics
import FiniteAvalanches.Electrical.Green.PairDeterminants
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The actual three-by-three resistance minors in grounded Green coordinates. -/
namespace FiniteAvalanches.Electrical.PairFormula
open FiniteAvalanches.Electrical.StatementGeometry
open Polynomial

def pairResistance {V : Type} (G : V → V → ℝ) (i j : V) := G i i + G j j - 2*G i j

private theorem coeff_triple (a b c : ℝ) :
    ((X-C a)*(X-C b)*(X-C c)).coeff 1 = a*b+a*c+b*c := by
  have h : (X-C a)*(X-C b)*(X-C c) =
      X^3-C (a+b+c)*X^2+C (a*b+a*c+b*c)*X-C (a*b*c) := by
    simp only [map_add,map_mul]
    ring
  rw [h]
  simp only [coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow,coeff_C]
  norm_num

/-- The coefficient is a double-difference determinant; row/column-only terms cancel. -/
theorem resistanceMinor_coeff {V : Type} (G : V → V → ℝ) (U W : Fin 3 → V)
    (hg : ∀ y, G (U 0) y = 0) :
    ((Matrix.of fun r s : Fin 3 => (X : Polynomial ℝ)-C
      ((G (U r) (U r)+G (W s) (W s)-2*G (U r) (W s))/2)).det).coeff 1 =
    (G (U 1) (W 0)-G (U 1) (W 2))*(G (U 2) (W 1)-G (U 2) (W 2)) -
    (G (U 1) (W 1)-G (U 1) (W 2))*(G (U 2) (W 0)-G (U 2) (W 2)) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply,coeff_add,coeff_sub,coeff_triple,hg]
  ring

/-- The two actual source row orders subtract to the eight Green terms. -/
theorem resistanceMinors_sub (G : Fin 6 → Fin 6 → ℝ)
    (hg : ∀ y, G 0 y = 0) (hs : G 3 2 = G 2 3) :
    ((Matrix.of fun r s : Fin 3 => (X : Polynomial ℝ)-C
      (pairResistance G (triple124 r) (triple356 s)/2)).det).coeff 1 -
    ((Matrix.of fun r s : Fin 3 => (X : Polynomial ℝ)-C
      (pairResistance G (triple123 r) (triple456 s)/2)).det).coeff 1 =
    G 1 2*(G 3 4-G 3 5)-G 1 3*(G 2 4-G 2 5)-
      G 1 4*(G 2 5-G 3 5)+G 1 5*(G 2 4-G 3 4) := by
  rw [show ((Matrix.of fun r s : Fin 3 => (X : Polynomial ℝ)-C
      (pairResistance G (triple124 r) (triple356 s)/2)).det).coeff 1 = _ from
    resistanceMinor_coeff G triple124 triple356 hg]
  rw [show ((Matrix.of fun r s : Fin 3 => (X : Polynomial ℝ)-C
      (pairResistance G (triple123 r) (triple456 s)/2)).det).coeff 1 = _ from
    resistanceMinor_coeff G triple123 triple456 hg]
  change (G 1 2-G 1 5)*(G 3 4-G 3 5)-(G 1 4-G 1 5)*(G 3 2-G 3 5) -
    ((G 1 3-G 1 5)*(G 2 4-G 2 5)-(G 1 4-G 1 5)*(G 2 3-G 2 5)) = _
  rw [hs]
  ring

/-- Specialization to the actual positive copied-Laplacian Green kernel, not a free scalar. -/
theorem groundedGreen_resistanceMinors_sub {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (hc : (supportGraph J.left J.right).Preconnected)
    (x : Fin 6 → V) :
    let G := fun i j => groundedGreen J.left J.right (x 0) hc (x i) (x j)
    ((Matrix.of fun r s : Fin 3 => (X : Polynomial ℝ)-C
      (pairResistance G (triple124 r) (triple356 s)/2)).det).coeff 1 -
    ((Matrix.of fun r s : Fin 3 => (X : Polynomial ℝ)-C
      (pairResistance G (triple123 r) (triple456 s)/2)).det).coeff 1 =
    G 1 2*(G 3 4-G 3 5)-G 1 3*(G 2 4-G 2 5)-
      G 1 4*(G 2 5-G 3 5)+G 1 5*(G 2 4-G 3 4) := by
  apply resistanceMinors_sub
  · intro y
    rw [groundedGreen_ground_source]
    rfl
  · exact groundedGreen_symm J.left J.right (x 0) hc (x 3) (x 2)
end FiniteAvalanches.Electrical.PairFormula
