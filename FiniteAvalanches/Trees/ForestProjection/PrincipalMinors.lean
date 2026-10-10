import FiniteAvalanches.Trees.ForestProjection.Incidence
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.ForestProjectionAlgebra

/-- Inclusion–exclusion for a principal determinant, on the original copied-edge subsets. -/
theorem det_principal_eq_sum_complementary {I : Type} [Fintype I]
    (M : Matrix I I ℝ) (A : Finset I) :
    (M.submatrix (Subtype.val : A → I) Subtype.val).det =
      ∑ s ∈ A.powerset, (-1 : ℝ) ^ s.card *
        (((1 : Matrix I I ℝ) - M).submatrix (Subtype.val : s → I) Subtype.val).det := by
  let D := (Matrix.detRowAlternating : (I → ℝ) [⋀^I]→ₗ[ℝ] ℝ)
  let N := (1 : Matrix I I ℝ) - M
  have hM : (Matrix.row (-N) + Matrix.row (1 : Matrix I I ℝ)) = Matrix.row M := by
    funext i j
    simp only [Pi.add_apply, Matrix.row_apply, Matrix.neg_apply, N, Matrix.sub_apply]
    ring
  have h := D.map_piecewise_add (Matrix.row (-N)) (Matrix.row (1 : Matrix I I ℝ)) A
  rw [hM] at h
  change (Matrix.of (A.piecewise M.row (1 : Matrix I I ℝ).row)).det =
    ∑ s ∈ A.powerset, (Matrix.of (s.piecewise (-N).row (1 : Matrix I I ℝ).row)).det at h
  rw [Matrix.det_piecewise_one_eq_submatrix_det] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.det_piecewise_one_eq_submatrix_det]
  simp only [Matrix.submatrix_neg, Pi.neg_apply]
  rw [Matrix.det_neg, Fintype.card_coe]

end FiniteAvalanches.ForestProjectionAlgebra
