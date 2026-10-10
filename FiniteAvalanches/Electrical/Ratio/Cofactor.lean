import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic

/-! Diagonal inverse entries expressed by principal minors on the actual index carrier. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Ratio
open scoped Classical Matrix
noncomputable section
variable {N : Type} [Fintype N] [DecidableEq N]

/-- The diagonal cofactor deletes exactly its own index, including a one-by-one matrix. -/
theorem adjugate_diagonal_eq_deleted_det (A : Matrix N N ℝ) (i : N) :
    A.adjugate i i = (A.submatrix
      (fun x : {x : N // x ≠ i} => x.val)
      (fun x : {x : N // x ≠ i} => x.val)).det := by
  letI : Nonempty N := ⟨i⟩
  have hpos : 0 < Fintype.card N := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  let e : Fin (k + 1) ≃ N := (Fintype.equivFinOfCardEq hk).symm
  let j : Fin (k + 1) := e.symm i
  let d : Fin k ≃ {x : N // x ≠ i} := (finSuccAboveEquiv j).trans
    (e.subtypeEquiv (fun x => by
      change x ≠ e.symm i ↔ e x ≠ i
      exact not_congr e.apply_eq_iff_eq_symm_apply.symm))
  have h := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ => M j j)
    (Matrix.adjugate_submatrix_equiv_self e A)
  change (A.submatrix e e).adjugate j j = A.adjugate (e j) (e j) at h
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at h
  have hsign : (-1 : ℝ) ^ (j.val + j.val) = 1 := by
    rw [show j.val + j.val = 2 * j.val by omega, pow_mul, neg_one_sq, one_pow]
  rw [hsign, one_mul] at h
  have hm : (A.submatrix e e).submatrix j.succAbove j.succAbove =
      (A.submatrix (fun x : {x : N // x ≠ i} => x.val)
        (fun x : {x : N // x ≠ i} => x.val)).submatrix d d := rfl
  rw [hm, Matrix.det_submatrix_equiv_self] at h
  simpa only [j, Equiv.apply_symm_apply] using h.symm

/-- Ordinary inverse/cofactor formula; no count ratio is assumed. -/
theorem inverse_diagonal_eq_deleted_det_div (A : Matrix N N ℝ) (i : N) :
    A⁻¹ i i = (A.submatrix
      (fun x : {x : N // x ≠ i} => x.val)
      (fun x : {x : N // x ≠ i} => x.val)).det / A.det := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    adjugate_diagonal_eq_deleted_det, div_eq_mul_inv, mul_comm]

end
end FiniteAvalanches.Electrical.Ratio
