import CurrentSource.PhysicalTerminalHeight

/-! Definitional graph-name transport for the complete same-stream physical height provider. -/

namespace FiniteAvalanches.Electrical.Source.CurrentTerminalHeight
open LatticeProb StatementGeometry BSST Plane.SourceLattice LatticeDrawing SplitStep
open Plane.SourceLattice.CurrentRegularPhysical
open scoped Classical BigOperators
noncomputable section

/-- Both graph names are the literal original copy endpoints. This bridge preserves every field,
carrier, sign, gauge and uniform terminal conclusion. -/
theorem source_height_terminal_canonical
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
    ∃ B : PlaneEmbedding (sourceGraph D P marked),
    ∃ A : OuterArc B (alpha D P) (beta D P),
    ∃ faces : Face Q ≃ A.embedding.Face,
      (∀ e : Copy D P marked,
        faces ((sourceDeletedDualGraph D P marked Q charts).left e) = A.embedding.rightFace (.inl e) ∧
        faces ((sourceDeletedDualGraph D P marked Q charts).right e) = A.embedding.leftFace (.inl e)) ∧
    ∃ psi : A.embedding.Face → ℝ,
      Source.stream_spec B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi ∧
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      let H := fun F => sigma * (psi F - psi (faces (vertices (Fin.last m))))
      let J := sourceDeletedDualGraph D P marked Q charts
      let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
        FiniteAvalanches.External.finite_plane_dual_connected
        FiniteAvalanches.External.finite_plane_dual_bond_cycle
      let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
      (∀ F : Face Q, H (faces F) = -G (vertices 0) F) ∧
      ∀ (i : Fin (m + 1)) (j : Fin m), (j.val + 1 = i.val ∨ j.val = i.val) →
        let p := G (vertices 0) (vertices j.castSucc) - G (vertices 0) (vertices j.succ)
        let y0 := (H (faces (vertices j.castSucc)) + H (faces (vertices j.succ))) / 2
        0 < p / 2 ∧ p / 2 ≤ 1 / 2 ∧
        H (faces (vertices j.castSucc)) - y0 = -(p / 2) ∧
        H (faces (vertices j.succ)) - y0 = p / 2 ∧
        retainedPrimal D P marked (copies j).val ≠ markedPrimal D P marked ∧
        (∀ z : ℝ × ℝ, Geometry.angular (p / 2) y0 z =
          1 / 2 + ((2 / p) * (z.2 - y0)) /
            (2 * max 1 (max |(2 / p) * z.1| |(2 / p) * (z.2 - y0)|))) ∧
        ∀ k : Fin m, k ≠ j →
          (if copyA D P marked (copies k).val = alpha D P then
            (actualSplit D P marked copies i.val).left (copies k).val else
            (actualSplit D P marked copies i.val).right (copies k).val) =
              .inr (decide (i.val ≤ k.val)) ∧
          ∀ F : A.embedding.Face,
            (F = A.embedding.leftFace (.inl (copies k).val) ∨
              F = A.embedding.rightFace (.inl (copies k).val)) →
            (0, H F) ∈ Source.edgeSquare B (alpha D P) (beta D P) A
              (Repair8.voltage D P hD marked) H (copies k).val ∧
            (k.val < i.val → H F - y0 ≤ -(p / 2)) ∧
            (i.val ≤ k.val → p / 2 ≤ H F - y0) ∧
            Geometry.angular (p / 2) y0 (0, H F) = if k.val < i.val then 0 else 1 := by
  exact original_source_height_terminal D P hD hDc hP marked Q charts vertices hinj copies hends hmarked

end
end FiniteAvalanches.Electrical.Source.CurrentTerminalHeight
