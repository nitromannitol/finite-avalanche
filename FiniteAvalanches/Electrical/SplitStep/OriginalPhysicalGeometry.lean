import FiniteAvalanches.Electrical.SplitStep.OriginalPhysicalCarrier
import FiniteAvalanches.External.PlanePuncturedChartFaceTransport

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

/-- The full original face carrier and its supplied oriented sides have a physical
marked outer arc, with the marked sides following their actual storage orientation. -/
theorem original_marked_physical_geometry (D : Finset (Site 2)) (P : OneSet D)
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
        faces ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = A.embedding.rightFace (.inr ())) := by
  obtain ⟨p, hp, c, hformula, Q', _hpoint, hcurve, inversionFaces, hregion,
    B, A, hdraw, _hbase, _physical, _hphysical, _hphysicalRegion, _hphysicalClosure,
    _hphysicalIncidence, _hphysicalPoints, _hparameters, _hinverseParameters⟩ :=
    original_marked_physical_carrier D P marked Q charts
  have hretained := original_physical_retained_sides_of_side_equations
    D P marked Q Q' charts B A hdraw inversionFaces (fun e =>
      External.plane_punctured_chart_face_transport (LatticeDrawing.primalGraph D P)
        Q p hp c hformula Q' hcurve inversionFaces hregion
        (retainedPrimal D P marked e) (charts _) (physicalRetainedChart D P marked Q' B A hdraw e))
  have hmarked := original_physical_marked_sides_of_side_equations
    D P marked Q Q' charts B A hdraw inversionFaces
      (External.plane_punctured_chart_face_transport (LatticeDrawing.primalGraph D P)
        Q p hp c hformula Q' hcurve inversionFaces hregion
        (markedPrimal D P marked) (charts _) (physicalMarkedChart D P marked Q' B A hdraw))
  refine ⟨B, A, inversionFaces.trans (originalPhysicalFaceEquiv D P marked Q' B A hdraw),
    hretained, ?_⟩
  by_cases ha : (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P
  · simp only [if_pos ha] at hmarked ⊢
    exact hmarked
  · simp only [if_neg ha] at hmarked ⊢
    exact hmarked

end
end FiniteAvalanches.Electrical.SplitStep
