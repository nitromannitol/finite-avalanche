import FiniteAvalanches.Electrical.SplitStep.OriginalStarOrientation

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

/-- Original face balance and signed stream increments derive one physical height orientation. -/
theorem original_boundary_increments_of_stream_and_balance (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
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
          (LatticeDrawing.primalGraph D P).right (fun x => if x = alpha D P then (1 : ℝ) else 0)) F = 0)
    (psi : Face Q → ℝ)
    (hpsi : ∀ e : Copy D P marked,
      psi ((sourceDeletedDualGraph D P marked Q charts).right e) -
        psi ((sourceDeletedDualGraph D P marked Q charts).left e) =
      Repair8.voltage D P hD marked (copyA D P marked e) -
        Repair8.voltage D P hD marked (copyB D P marked e)) :
    let phi := Repair8.voltage D P hD marked
    let p := fun k : Fin m => phi
      (if copyA D P marked (copies k).val = alpha D P
        then copyB D P marked (copies k).val else copyA D P marked (copies k).val)
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      ∀ k : Fin m, sigma * (psi (vertices k.succ) - psi (vertices k.castSucc)) = p k := by
  intro phi p
  let K := LatticeDrawing.primalGraph D P
  let g := Plane.copyGradient K.left K.right (fun x => if x = alpha D P then (1 : ℝ) else 0)
  let a := fun j : Fin m => (sourceDeletedDualGraph D P marked Q charts).left (copies j).val
  let c := fun j : Fin m => g (retainedPrimal D P marked (copies j).val)
  obtain ⟨sigma, hsigma, hc⟩ := original_star_orientation_of_face_balance
    D P marked Q charts vertices hinj copies hends hmarked hm hbalance
  refine ⟨sigma, hsigma, ?_⟩
  have hsquare : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> norm_num
  intro k
  have hp0 : phi (alpha D P) = 0 := (Repair8.voltage_spec D P hD marked).1
  have hg : phi (copyA D P marked (copies k).val) - phi (copyB D P marked (copies k).val) =
      -p k * c k := by
    by_cases ha : copyA D P marked (copies k).val = alpha D P
    · have hb : copyB D P marked (copies k).val ≠ alpha D P :=
        fun hb => copy_loopless D P marked (copies k).val (ha.trans hb.symm)
      simp only [p, c, g, K, Plane.copyGradient]
      change phi (copyA D P marked (copies k).val) - phi (copyB D P marked (copies k).val) =
        -phi (if copyA D P marked (copies k).val = alpha D P then
          copyB D P marked (copies k).val else copyA D P marked (copies k).val) *
        ((if copyA D P marked (copies k).val = alpha D P then 1 else 0) -
          (if copyB D P marked (copies k).val = alpha D P then 1 else 0))
      rw [if_pos ha, if_pos ha, if_neg hb, ha, hp0]
      ring
    · have hb := (copies k).property.resolve_left ha
      simp only [p, c, g, K, Plane.copyGradient]
      change phi (copyA D P marked (copies k).val) - phi (copyB D P marked (copies k).val) =
        -phi (if copyA D P marked (copies k).val = alpha D P then
          copyB D P marked (copies k).val else copyA D P marked (copies k).val) *
        ((if copyA D P marked (copies k).val = alpha D P then 1 else 0) -
          (if copyB D P marked (copies k).val = alpha D P then 1 else 0))
      rw [if_neg ha, if_neg ha, if_pos hb, hb, hp0]
      ring
  have hdelta : psi (vertices k.succ) - psi (vertices k.castSucc) =
      -p k * pathFlowCoefficient a vertices c k := by
    have hstream := (hpsi (copies k).val).trans hg
    have hne : vertices k.succ ≠ vertices k.castSucc := by
      intro he
      have hv := congrArg Fin.val (hinj he)
      simp only [Fin.val_succ, Fin.val_castSucc] at hv
      omega
    rcases hends k with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · rw [ha, hb] at hstream
      simpa only [pathFlowCoefficient, a, ha, ↓reduceIte] using hstream
    · rw [ha, hb] at hstream
      have hc' : pathFlowCoefficient a vertices c k = -c k := by
        simp only [pathFlowCoefficient, a, ha, if_neg hne]
      rw [hc']
      linarith only [hstream]
  rw [hc k] at hdelta
  calc
    sigma * (psi (vertices k.succ) - psi (vertices k.castSucc)) =
        p k * (sigma * sigma) := by rw [hdelta]; ring
    _ = p k := by rw [hsquare, mul_one]

end
end FiniteAvalanches.Electrical.SplitStep
