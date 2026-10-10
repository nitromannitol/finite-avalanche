import FiniteAvalanches.Electrical.SplitStep.OriginalStarResidual

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

/-- Indicator face balance forces one orientation on the entire supplied star, before any split. -/
theorem original_star_orientation_of_face_balance (D : Finset (Site 2)) (P : OneSet D)
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
    (hm : 0 < m)
    (hbalance : ∀ F : Face Q,
      Plane.copyBoundary (sourceDualGraph D P Q charts).left
        (sourceDualGraph D P Q charts).right
        (Plane.copyGradient (LatticeDrawing.primalGraph D P).left
          (LatticeDrawing.primalGraph D P).right (fun x => if x = alpha D P then (1 : ℝ) else 0)) F = 0) :
    let K := LatticeDrawing.primalGraph D P
    let g := Plane.copyGradient K.left K.right (fun x => if x = alpha D P then (1 : ℝ) else 0)
    let a := fun j : Fin m => (sourceDeletedDualGraph D P marked Q charts).left (copies j).val
    let c := fun j : Fin m => g (retainedPrimal D P marked (copies j).val)
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      ∀ k : Fin m, pathFlowCoefficient a vertices c k = -sigma := by
  intro K g a c
  let d := pathFlowCoefficient a vertices c
  have hnext (k : Fin m) (hk : k.val + 1 < m) : d ⟨k.val + 1, hk⟩ = d k := by
    have hr := original_star_internal_residual D P marked Q charts vertices hinj copies hends hmarked k hk
    change Plane.copyBoundary (sourceDualGraph D P Q charts).left
      (sourceDualGraph D P Q charts).right g (vertices k.succ) =
      d ⟨k.val + 1, hk⟩ - d k at hr
    rw [hbalance] at hr
    exact sub_eq_zero.mp hr.symm
  have hall (n : ℕ) : ∀ hn : n < m, d ⟨n, hn⟩ = d ⟨0, hm⟩ := by
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      exact (hnext ⟨n, by omega⟩ hn).trans (ih (by omega))
  refine ⟨-d ⟨0, hm⟩, ?_, ?_⟩
  · have hs := original_star_coefficient_sign D P marked Q charts vertices copies ⟨0, hm⟩
    change d ⟨0, hm⟩ = 1 ∨ d ⟨0, hm⟩ = -1 at hs
    rcases hs with hs | hs
    · right; rw [hs]
    · left; rw [hs]; norm_num
  · intro k
    rw [neg_neg]
    exact hall k.val k.isLt

end
end FiniteAvalanches.Electrical.SplitStep
