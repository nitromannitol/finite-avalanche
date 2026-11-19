import FiniteAvalanches.Electrical.Trees.ResistanceGround
import FiniteAvalanches.Electrical.Ratio.GreenInverseExtension
import LatticeProb.LinearAlgebra.ZeroSumComplementaryMinor

/-! Complementary Laplacian minors give resistance-determinant coefficients. -/

set_option autoImplicit false

namespace FiniteAvalanches.Electrical

open StatementGeometry ChordSplit Ratio Polynomial
open scoped Classical BigOperators

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E]

/-- Every row of the copied Laplacian sums to zero, including loop copies. -/
theorem copiedLaplacian_sum_row (J : CopiedGraph V E) (x : V) :
    ∑ y, copiedLaplacian J x y = 0 := by
  simp only [copiedLaplacian, Finset.sum_comm, ← Finset.mul_sum]
  simp [eq_comm]

/-- A resistance-determinant coefficient, multiplied by the full tree count,
is the signed Laplacian minor indexed by the complementary vertex lists. -/
theorem resistanceDet_coeff_mul_tree_count (J : CopiedGraph V E)
    (hc : (supportGraph J.left J.right).Preconnected) (g : V)
    {m : Type} [Fintype m] [DecidableEq m] {n : ℕ}
    (e f : (m ⊕ Fin (n + 1)) ≃ V) :
    let a := fun i : Fin (n + 1) => e (Sum.inr i)
    let b := fun i : Fin (n + 1) => f (Sum.inr i)
    ((Matrix.of fun i j : Fin (n + 1) =>
      (X : Polynomial ℝ) - C ((groundedGreen J.left J.right g hc (a i) (a i) +
        groundedGreen J.left J.right g hc (b j) (b j) -
          2 * groundedGreen J.left J.right g hc (a i) (b j)) / 2)).det).coeff 1 *
        (Nat.card J.SpanningTree : ℝ) =
      ((Equiv.Perm.sign (f.trans e.symm) : ℤ) : ℝ) *
        ((copiedLaplacian J).submatrix (fun i : m => e (Sum.inl i))
          (fun i : m => f (Sum.inl i))).det := by
  dsimp only
  let root : V := e (Sum.inr 0)
  let a : Fin (n + 1) → V := fun i => e (Sum.inr i)
  let b : Fin (n + 1) → V := fun i => f (Sum.inr i)
  let eqv : {z : V // z ≠ root} ≃ {z : V // z ∉ ({root} : Finset V)} :=
    { toFun := fun z => ⟨z.val, by simpa only [Finset.mem_singleton] using z.property⟩
      invFun := fun z => ⟨z.val, by simpa only [Finset.mem_singleton] using z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmatrix : (copiedLaplacian J).submatrix
      (fun z : {z : V // z ≠ root} => z.val) Subtype.val =
      (groundMatrix J root).submatrix eqv eqv := by rfl
  have hdet : ((copiedLaplacian J).submatrix
      (fun z : {z : V // z ≠ root} => z.val) Subtype.val).det =
      (Nat.card J.SpanningTree : ℝ) := by
    rw [hmatrix, Matrix.det_submatrix_equiv_self]
    exact J.copiedLaplacian_det_eq_tree_count root
  have hu : IsUnit (((copiedLaplacian J).submatrix
      (fun z : {z : V // z ≠ root} => z.val) Subtype.val).det) := by
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (copied_tree_count_pos J root hc))
  have h := LatticeProb.LinearAlgebra.det_groundInverseExtension_differences_mul_det
    (copiedLaplacian J) (copiedLaplacian_sum_row J) e f hu
  rw [hdet] at h
  have hminor : (Matrix.of fun i j : Fin n =>
      LatticeProb.LinearAlgebra.groundInverseExtension (copiedLaplacian J) root
        (b j.succ) (a i.succ) -
      LatticeProb.LinearAlgebra.groundInverseExtension (copiedLaplacian J) root
        (b 0) (a i.succ)) =
      (Matrix.of fun i j : Fin n =>
        groundedGreen J.left J.right root hc (a i.succ) (b j.succ) -
        groundedGreen J.left J.right root hc (a 0) (b j.succ) -
        groundedGreen J.left J.right root hc (a i.succ) (b 0) +
        groundedGreen J.left J.right root hc (a 0) (b 0)) := by
    ext i j
    simp only [Matrix.of_apply]
    rw [groundInverseExtension_eq_groundedGreen J root hc,
      groundInverseExtension_eq_groundedGreen J root hc]
    change _ = _ - groundedGreen J.left J.right root hc root _ - _ +
      groundedGreen J.left J.right root hc root _
    rw [groundedGreen_ground_source]
    simp
  change (Matrix.of fun i j : Fin n =>
      LatticeProb.LinearAlgebra.groundInverseExtension (copiedLaplacian J) root
        (b j.succ) (a i.succ) -
      LatticeProb.LinearAlgebra.groundInverseExtension (copiedLaplacian J) root
        (b 0) (a i.succ)).det * _ = _ at h
  rw [hminor] at h
  have hchange := resistanceDet_coeff_one_ground_independent J.left J.right g root hc a b
  have hfinal : ((Matrix.of fun i j : Fin (n + 1) =>
      (X : Polynomial ℝ) - C ((groundedGreen J.left J.right g hc (a i) (a i) +
        groundedGreen J.left J.right g hc (b j) (b j) -
          2 * groundedGreen J.left J.right g hc (a i) (b j)) / 2)).det).coeff 1 *
        (Nat.card J.SpanningTree : ℝ) =
      ((Equiv.Perm.sign (f.trans e.symm) : ℤ) : ℝ) *
        ((copiedLaplacian J).submatrix (fun i : m => e (Sum.inl i))
          (fun i : m => f (Sum.inl i))).det := by
    rw [hchange, resistanceDet_coeff_one]
    exact h
  exact hfinal

end
end FiniteAvalanches.Electrical
