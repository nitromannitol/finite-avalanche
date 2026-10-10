import FiniteAvalanches.Electrical.SplitStep.OriginalAlphaBoundary

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical BigOperators
noncomputable section

/-- At each internal original path face, the complete indicator boundary has exactly two terms. -/
theorem original_star_internal_residual (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) {m : ℕ}
    (vertices : Fin (m + 1) → Face Q) (hinj : Function.Injective vertices)
    (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (hends : ∀ k : Fin m,
      ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
      ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ))
    (hmarked :
      ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
        (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
      ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m)))
    (k : Fin m) (hk : k.val + 1 < m) :
    let J := sourceDualGraph D P Q charts
    let K := LatticeDrawing.primalGraph D P
    let g := Plane.copyGradient K.left K.right (fun x => if x = alpha D P then (1 : ℝ) else 0)
    let a := fun j : Fin m => (sourceDeletedDualGraph D P marked Q charts).left (copies j).val
    let c := fun j : Fin m => g (retainedPrimal D P marked (copies j).val)
    Plane.copyBoundary J.left J.right g (vertices k.succ) =
      pathFlowCoefficient a vertices c ⟨k.val + 1, hk⟩ - pathFlowCoefficient a vertices c k := by
  intro J K g a c
  have hn0 : vertices 0 ≠ vertices k.succ := by
    intro he
    have hv := congrArg Fin.val (hinj he)
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  have hnm : vertices (Fin.last m) ≠ vertices k.succ := by
    intro he
    have hv := congrArg Fin.val (hinj he)
    simp only [Fin.val_last, Fin.val_succ] at hv
    omega
  have hzero :
      ((if J.left (markedPrimal D P marked) = vertices k.succ then
        g (markedPrimal D P marked) else 0) -
       (if J.right (markedPrimal D P marked) = vertices k.succ then
        g (markedPrimal D P marked) else 0)) = 0 := by
    rcases hmarked with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · simp only [J, ha, hb, if_neg hn0, if_neg hnm, sub_self]
    · simp only [J, ha, hb, if_neg hn0, if_neg hnm, sub_self]
  have hs := original_alpha_boundary_sum D P marked Q charts copies (vertices k.succ)
  change Plane.copyBoundary J.left J.right g (vertices k.succ) = _ at hs
  rw [hs, hzero, add_zero]
  exact path_boundary_internal a
    (fun j => (sourceDeletedDualGraph D P marked Q charts).right (copies j).val)
    vertices hinj hends c k hk

/-- Every listed original star flow coefficient is literally plus or minus one. -/
theorem original_star_coefficient_sign (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) {m : ℕ}
    (vertices : Fin (m + 1) → Face Q)
    (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (k : Fin m) :
    let K := LatticeDrawing.primalGraph D P
    let g := Plane.copyGradient K.left K.right (fun x => if x = alpha D P then (1 : ℝ) else 0)
    let a := fun j : Fin m => (sourceDeletedDualGraph D P marked Q charts).left (copies j).val
    let c := fun j : Fin m => g (retainedPrimal D P marked (copies j).val)
    pathFlowCoefficient a vertices c k = 1 ∨ pathFlowCoefficient a vertices c k = -1 := by
  intro K g a c
  have hg := alpha_indicator_gradient K (primal_loopless D P) (alpha D P)
    (retainedPrimal D P marked (copies k).val)
  have hc : c k = 1 ∨ c k = -1 := by
    rcases (copies k).property with ha | hb
    · exact Or.inl (hg.1 ha)
    · exact Or.inr (hg.2.1 hb)
  unfold pathFlowCoefficient
  split
  · exact hc
  · rcases hc with hc | hc
    · right; rw [hc]
    · left; rw [hc]; norm_num

end
end FiniteAvalanches.Electrical.SplitStep
