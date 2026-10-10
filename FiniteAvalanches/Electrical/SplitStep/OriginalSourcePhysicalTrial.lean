import FiniteAvalanches.Electrical.SplitStep.OriginalSourceStreamBalance
import FiniteAvalanches.Electrical.SplitStep.OriginalFaceSignedTrial

/-! One original physical stream and one sign for every proper split and adjacent copy. -/
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing PhysicalCharging
open scoped Classical BigOperators
noncomputable section

/-- The original full-face stream and balance supply the exact 3888 trial, uniformly in i and j. -/
theorem original_source_full_physical_trial
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
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) :
    let J := sourceDeletedDualGraph D P marked Q charts
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      FiniteAvalanches.External.finite_plane_dual_connected FiniteAvalanches.External.finite_plane_dual_bond_cycle
    let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
    ∃ B : PlaneEmbedding (originalGraph D P marked),
    ∃ A : OuterArc B (alpha D P) (beta D P),
    ∃ faces : Face Q ≃ A.embedding.Face,
      (∀ e : Copy D P marked,
      faces ((sourceDeletedDualGraph D P marked Q charts).left e) = A.embedding.rightFace (.inl e) ∧
      faces ((sourceDeletedDualGraph D P marked Q charts).right e) = A.embedding.leftFace (.inl e)) ∧
      (if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P then
      faces ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) = A.embedding.rightFace (.inr ()) ∧
      faces ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = A.embedding.leftFace (.inr ())
    else
      faces ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) = A.embedding.leftFace (.inr ()) ∧
      faces ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = A.embedding.rightFace (.inr ())) ∧
    ∃ psi : A.embedding.Face → ℝ,
      Source.stream_spec B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi ∧
      (∀ e : Copy D P marked,
        (psi ∘ faces) ((sourceDeletedDualGraph D P marked Q charts).right e) -
          (psi ∘ faces) ((sourceDeletedDualGraph D P marked Q charts).left e) =
        Repair8.voltage D P hD marked (copyA D P marked e) -
          Repair8.voltage D P hD marked (copyB D P marked e)) ∧
    (if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P then
      (psi ∘ faces) ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) = 0 ∧
      (psi ∘ faces) ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) =
        Source.mass (originalGraph D P marked) (Repair8.voltage D P hD marked)
    else
      (psi ∘ faces) ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) =
        Source.mass (originalGraph D P marked) (Repair8.voltage D P hD marked) ∧
      (psi ∘ faces) ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = 0) ∧
      (∀ (q : Vertex D P → ℝ) (F : Face Q),
        Plane.copyBoundary (sourceDualGraph D P Q charts).left (sourceDualGraph D P Q charts).right
          (Plane.copyGradient (LatticeDrawing.primalGraph D P).left (LatticeDrawing.primalGraph D P).right q) F = 0) ∧
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      ∀ (i : Fin (m + 1)), 0 < i.val → i.val < m →
        ∀ (j : Fin m), (j.val + 1 = i.val ∨ j.val = i.val) →
          let p := G (vertices 0) (vertices j.castSucc) - G (vertices 0) (vertices j.succ)
          let y0 := (psi (faces (vertices j.castSucc)) + psi (faces (vertices j.succ))) / 2
          let f := signedSplitMidpointTrial (originalGraph D P marked) B (alpha D P) (beta D P) A
            (Repair8.voltage D P hD marked) psi sigma (p / 2) y0
          f (.inr false) = 0 ∧ f (.inr true) = 1 ∧
            f (.inl ⟨beta D P, by intro h; cases h⟩) = 0 ∧ (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧
            weightedEnergy (actualSplit D P marked copies i.val).left
              (actualSplit D P marked copies i.val).right
              (fun v => 1 - splitVoltage D P hD marked v) f ≤
                1 + 3888 * (1 + Real.log (2 / p)) := by
  intro J hc G
  obtain ⟨B, A, faces, hfaces, hmarkedSides, psi, hpsi, hstream, hgauge, hbalance⟩ :=
    original_source_full_stream_balance D P hD marked Q charts
  refine ⟨B, A, faces, hfaces, hmarkedSides, psi, hpsi, hstream, hgauge, hbalance, ?_⟩
  exact original_physical_trial_of_face_transport_and_balance
    D P hD hDc hP marked Q charts vertices hinj copies hends hmarked B A faces hfaces
    psi hpsi (hbalance (fun x => if x = alpha D P then (1 : ℝ) else 0))

end
end FiniteAvalanches.Electrical.SplitStep
