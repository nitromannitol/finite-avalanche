import FiniteAvalanches.Electrical.SplitStep.OriginalTrialFromSides

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing PhysicalCharging
open scoped Classical BigOperators
noncomputable section

/-- The signed trial supplies the original response bound with the actual Green correction.
The geometric side equations remain explicit; the diagonal dictionary is separate. -/
theorem original_response_bound_of_side_equations
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) [finiteFaces : Fintype (Face Q)] {m : ℕ}
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
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (faces : Face Q ≃ A.embedding.Face)
    (hfaces : ∀ e : Copy D P marked,
      faces ((sourceDeletedDualGraph D P marked Q charts).left e) = A.embedding.rightFace (.inl e) ∧
      faces ((sourceDeletedDualGraph D P marked Q charts).right e) = A.embedding.leftFace (.inl e))
    (hmarkedSides : if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P then
      faces ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) = A.embedding.rightFace (.inr ()) ∧
      faces ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = A.embedding.leftFace (.inr ())
    else
      faces ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) = A.embedding.leftFace (.inr ()) ∧
      faces ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = A.embedding.rightFace (.inr ())) :
    let J := sourceDeletedDualGraph D P marked Q charts
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      FiniteAvalanches.External.finite_plane_dual_connected FiniteAvalanches.External.finite_plane_dual_bond_cycle
    let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
    ∀ (i : Fin (m + 1)), 0 < i.val → i.val < m →
      ∀ (j : Fin m), (j.val + 1 = i.val ∨ j.val = i.val) →
        let p := G (vertices 0) (vertices j.castSucc) - G (vertices 0) (vertices j.succ)
        totalResponse D P hD marked copies i.val - G (vertices 0) (vertices i) ≤
          1 + 3888 * (1 + Real.log (2 / p)) := by
  intro J hc G
  obtain ⟨psi, _, sigma, _, htrial⟩ := original_physical_trial_of_side_equations
    D P hD hDc hP marked Q charts vertices hinj copies hends hmarked B A faces hfaces hmarkedSides
  intro i hi him j hj p
  let y0 := (psi (faces (vertices j.castSucc)) + psi (faces (vertices j.succ))) / 2
  let f := signedSplitMidpointTrial (originalGraph D P marked) B (alpha D P) (beta D P) A
    (Repair8.voltage D P hD marked) psi sigma (p / 2) y0
  have ht := htrial i hi him j hj
  change f (.inr false) = 0 ∧ f (.inr true) = 1 ∧
    f (.inl ⟨beta D P, by intro he; cases he⟩) = 0 ∧ (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧
    weightedEnergy (actualSplit D P marked copies i.val).left
      (actualSplit D P marked copies i.val).right (fun v => 1 - splitVoltage D P hD marked v) f ≤
      1 + 3888 * (1 + Real.log (2 / p)) at ht
  have hs := actual_split_response_sub_original_green_bound D P hD hDc hP marked Q charts
    vertices hinj copies hends hmarked i f ht.1 ht.2.1
  exact hs.trans ht.2.2.2.2

end
end FiniteAvalanches.Electrical.SplitStep
