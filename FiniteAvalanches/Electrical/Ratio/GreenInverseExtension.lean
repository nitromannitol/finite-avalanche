import FiniteAvalanches.Electrical.Ratio.Green
import LatticeProb.LinearAlgebra.ZeroSumBorderInverse

/-! The extended inverse of the grounded Laplacian is the Green kernel. -/

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.Ratio

open FiniteAvalanches.Electrical.StatementGeometry FiniteAvalanches.Electrical.ChordSplit
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E]

/-- Extending the inverse grounded block by zero gives the Green kernel, with
its source and evaluation indices in the corresponding order. -/
theorem groundInverseExtension_eq_groundedGreen (J : CopiedGraph V E) (g : V)
    (hc : (supportGraph J.left J.right).Preconnected) (x y : V) :
    LatticeProb.LinearAlgebra.groundInverseExtension (copiedLaplacian J) g x y =
      groundedGreen J.left J.right g hc y x := by
  by_cases hx : x = g
  · subst x
    rw [LatticeProb.LinearAlgebra.groundInverseExtension_ground_row, groundedGreen_ground]
  by_cases hy : y = g
  · subst y
    rw [LatticeProb.LinearAlgebra.groundInverseExtension_ground_column, groundedGreen_ground_source]
    rfl
  let e : {z : V // z ≠ g} ≃ {z : V // z ∉ ({g} : Finset V)} :=
    { toFun := fun z => ⟨z.val, by simpa only [Finset.mem_singleton] using z.property⟩
      invFun := fun z => ⟨z.val, by simpa only [Finset.mem_singleton] using z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hm : (copiedLaplacian J).submatrix
      (fun z : {z : V // z ≠ g} => z.val) Subtype.val =
      (groundMatrix J g).submatrix e e := by rfl
  rw [LatticeProb.LinearAlgebra.groundInverseExtension_apply (copiedLaplacian J) g
    ⟨x, hx⟩ ⟨y, hy⟩, hm, Matrix.inv_submatrix_equiv]
  change (groundMatrix J g)⁻¹ (e ⟨x, hx⟩) (e ⟨y, hy⟩) = _
  exact (groundedGreen_eq_inverse J g hc (e ⟨y, hy⟩) (e ⟨x, hx⟩)).symm

end
end FiniteAvalanches.Electrical.Ratio
