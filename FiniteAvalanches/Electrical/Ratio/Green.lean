import FiniteAvalanches.Electrical.Ratio.Cofactor
import FiniteAvalanches.Electrical.Trees.CopiedAllMinors
import FiniteAvalanches.Electrical.LoopDeletion
import FiniteAvalanches.Electrical.Green.Grounded

/-! Count ratios for the actual grounded Green function on finite copied networks. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Ratio
open StatementGeometry ChordSplit
open scoped Classical BigOperators Matrix
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- The entire one-root principal block of the copied Laplacian. -/
def groundMatrix (J : CopiedGraph V E) (v : V) :
    Matrix {x : V // x ∉ ({v} : Finset V)} {x : V // x ∉ ({v} : Finset V)} ℝ :=
  (copiedLaplacian J).submatrix Subtype.val Subtype.val

/-- Genuine connectedness makes every nonempty rooted principal minor positive. -/
theorem copied_principal_det_pos (J : CopiedGraph V E) (R : Finset V)
    (hR : R.Nonempty) (hc : (supportGraph J.left J.right).Preconnected) :
    0 < ((copiedLaplacian J).submatrix
      (fun x : {x : V // x ∉ R} => x.val)
      (fun x : {x : V // x ∉ R} => x.val)).det := by
  rw [J.copiedLaplacian_rootGram]
  exact J.nonloopGraph.rootGram_det_pos R hR (deleteLoops_preconnected J hc)

/-- The copied single-root block acts by the original positive electrical Laplacian. -/
theorem groundMatrix_mulVec (J : CopiedGraph V E) (v : V)
    (u : {x : V // x ∉ ({v} : Finset V)} → ℝ)
    (x : {x : V // x ∉ ({v} : Finset V)}) :
    (groundMatrix J v *ᵥ u) x = laplacian J.left J.right (zeroExtend {v} u) x.val := by
  unfold groundMatrix
  rw [J.copiedLaplacian_rootGram, J.nonloopGraph.rootGram_eq_dirichletMatrix,
    LinearMap.toMatrix'_mulVec]
  change laplacian (deleteLoops J).left (deleteLoops J).right _ _ = _
  exact deleteLoops_laplacian J _ _

/-- Restricting the characterized Green solve gives the corresponding inverse column. -/
theorem groundedGreen_eq_inverse (J : CopiedGraph V E) (v : V)
    (hc : (supportGraph J.left J.right).Preconnected)
    (x y : {x : V // x ∉ ({v} : Finset V)}) :
    groundedGreen J.left J.right v hc x.val y.val = (groundMatrix J v)⁻¹ y x := by
  let u : {x : V // x ∉ ({v} : Finset V)} → ℝ :=
    fun z => groundedGreen J.left J.right v hc x.val z.val
  have hu : zeroExtend {v} u = groundedGreen J.left J.right v hc x.val := by
    funext z
    by_cases hz : z ∈ ({v} : Finset V)
    · have hzv : z = v := Finset.mem_singleton.mp hz
      rw [zeroExtend, dif_pos hz, hzv, groundedGreen_ground]
    · rw [zeroExtend, dif_neg hz]
  have hmul : groundMatrix J v *ᵥ u = Pi.single x 1 := by
    funext z
    rw [groundMatrix_mulVec, hu, groundedGreen_laplacian J.left J.right v hc x.val z.val
      (by simpa only [Finset.mem_singleton] using z.property)]
    simp only [Pi.single_apply, Subtype.ext_iff]
  have hdet : IsUnit (groundMatrix J v).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (copied_principal_det_pos J {v}
      (Finset.singleton_nonempty v) hc))
  have hs := congrArg (fun f => (groundMatrix J v)⁻¹ *ᵥ f) hmul
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] at hs
  have hy := congrFun hs y
  simpa [u, Matrix.mulVec, dotProduct, Pi.single_apply] using hy

/-- Deleting a non-ground index from the grounded carrier deletes exactly the two roots. -/
def deletedGroundEquiv (v : V) (x : {x : V // x ∉ ({v} : Finset V)}) :
    {y : {y : V // y ∉ ({v} : Finset V)} // y ≠ x} ≃
      {y : V // y ∉ ({x.val, v} : Finset V)} where
  toFun y := ⟨y.val.val, by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => y.property (Subtype.ext h),
      by simpa only [Finset.mem_singleton] using y.val.property⟩⟩
  invFun y := ⟨⟨y.val, fun h => y.property (Finset.mem_insert_of_mem h)⟩, by
    intro h
    have he : y.val = x.val := congrArg Subtype.val h
    apply y.property
    rw [he]
    exact Finset.mem_insert_self _ _⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual copied tree denominator is positive, derived from connectedness. -/
theorem copied_tree_count_pos (J : CopiedGraph V E) (v : V)
    (hc : (supportGraph J.left J.right).Preconnected) :
    0 < (Nat.card J.SpanningTree : ℝ) := by
  rw [← J.copiedLaplacian_det_eq_tree_count v]
  exact copied_principal_det_pos J {v} (Finset.singleton_nonempty v) hc

/-- The actual two-root denominator is positive, derived from connectedness. -/
theorem copied_twoRootForest_count_pos (J : CopiedGraph V E) (u v : V)
    (hc : (supportGraph J.left J.right).Preconnected) :
    0 < (Nat.card (J.TwoRootForest u v) : ℝ) := by
  rw [← J.copiedLaplacian_det_eq_twoRootForest_count u v]
  exact copied_principal_det_pos J {u, v} ⟨u, Finset.mem_insert_self _ _⟩ hc

/-- Green's diagonal is the whole separating two-forest count divided by the whole tree count. -/
theorem groundedGreen_diagonal_eq_count_ratio (J : CopiedGraph V E) (v u : V)
    (hc : (supportGraph J.left J.right).Preconnected) (huv : u ≠ v) :
    groundedGreen J.left J.right v hc u u =
      (Nat.card (J.TwoRootForest u v) : ℝ) / (Nat.card J.SpanningTree : ℝ) := by
  let x : {x : V // x ∉ ({v} : Finset V)} := ⟨u, by simpa only [Finset.mem_singleton] using huv⟩
  rw [show u = x.val from rfl, groundedGreen_eq_inverse J v hc x x,
    inverse_diagonal_eq_deleted_det_div (groundMatrix J v) x]
  have hm : (groundMatrix J v).submatrix
      (fun y : {y : {y : V // y ∉ ({v} : Finset V)} // y ≠ x} => y.val)
      (fun y : {y : {y : V // y ∉ ({v} : Finset V)} // y ≠ x} => y.val) =
    ((copiedLaplacian J).submatrix
      (fun y : {y : V // y ∉ ({x.val, v} : Finset V)} => y.val)
      (fun y : {y : V // y ∉ ({x.val, v} : Finset V)} => y.val)).submatrix
        (deletedGroundEquiv v x) (deletedGroundEquiv v x) := rfl
  rw [hm, Matrix.det_submatrix_equiv_self, J.copiedLaplacian_det_eq_twoRootForest_count]
  unfold groundMatrix
  rw [J.copiedLaplacian_det_eq_tree_count]

end
end FiniteAvalanches.Electrical.Ratio
