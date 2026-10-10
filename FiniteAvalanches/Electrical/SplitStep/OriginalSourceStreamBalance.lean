import FiniteAvalanches.Electrical.SplitStep.OriginalPhysicalGeometry
import FiniteAvalanches.Electrical.SplitStep.OriginalFullStreamWitness
import FiniteAvalanches.External.PlanePuncturedChartFaceTransport

/-! Original source stream and full-face balance from the supplied drawing. -/
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing PhysicalCharging
open scoped Classical BigOperators
noncomputable section

/-- A single physical stream on all original faces, including both marked storage orientations. -/
theorem original_source_full_stream_balance
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) :
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
      ∀ (q : Vertex D P → ℝ) (F : Face Q),
        Plane.copyBoundary (sourceDualGraph D P Q charts).left (sourceDualGraph D P Q charts).right
          (Plane.copyGradient (LatticeDrawing.primalGraph D P).left (LatticeDrawing.primalGraph D P).right q) F = 0 := by
  obtain ⟨B, A, faces, hfaces, hmarked⟩ := original_marked_physical_geometry D P marked Q charts
  refine ⟨B, A, faces, hfaces, hmarked, ?_⟩
  exact original_full_stream_balance_of_side_equations D P hD marked Q charts B A faces hfaces hmarked

end
end FiniteAvalanches.Electrical.SplitStep
