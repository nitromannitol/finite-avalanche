import FiniteAvalanches.Electrical.SplitStep.OriginalMarkedCopy

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

/-- The same marked inversion gives a physical carrier for every full original face,
with whole region, closure, incidence, and original-copy parameter transport. -/
theorem original_marked_physical_carrier (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) :
    ∃ p : Plane, ∃ hp : p ∉ drawingTrace Q,
    ∃ c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)},
      (∀ z : {z : Plane // z ≠ p},
        (c z).val = ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
          -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2))) ∧
    ∃ Q' : Drawing (LatticeDrawing.primalGraph D P),
      (∀ v, Q'.point v = (c ⟨Q.point v, by
        intro heq; apply hp
        exact heq ▸ (Or.inl (Set.mem_range_self v) : Q.point v ∈ drawingTrace Q)⟩).val) ∧
      (∀ e t, Q'.curve e t = (c ⟨Q.curve e t, by
        intro heq; apply hp
        exact heq ▸ (Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_range_self t⟩) :
          Q.curve e t ∈ drawingTrace Q)⟩).val) ∧
    ∃ inversionFaces : Face Q ≃ Face Q',
      (∀ F : Face Q, ∀ z : {z : Plane // z ≠ p},
        z.val ∈ faceRegion Q F ↔ (c z).val ∈ faceRegion Q' (inversionFaces F)) ∧
    ∃ B : PlaneEmbedding (originalGraph D P marked),
    ∃ A : OuterArc B (alpha D P) (beta D P),
    ∃ hdraw : A.embedding.drawing = originalAugmentedDrawing D P marked Q',
      B.drawing = deleteMarkedDrawing D P marked Q' ∧
    ∃ physical : Face Q ≃ A.embedding.Face,
      physical = inversionFaces.trans (originalPhysicalFaceEquiv D P marked Q' B A hdraw) ∧
      (∀ F : Face Q, ∀ z : {z : Plane // z ≠ p},
        z.val ∈ faceRegion Q F ↔ (c z).val ∈ faceRegion A.embedding.drawing (physical F)) ∧
      (∀ F : Face Q, ∀ z : {z : Plane // z ≠ p},
        z.val ∈ closure (faceRegion Q F) ↔
          (c z).val ∈ closure (faceRegion A.embedding.drawing (physical F))) ∧
      (∀ F : Face Q, ∀ v : Vertex D P,
        incident Q v F ↔ A.embedding.incident v (physical F)) ∧
      A.embedding.drawing.point = Q'.point ∧
      (∀ e t, A.embedding.drawing.curve e t =
        Q'.curve (augmentedOriginalCopyEquiv D P marked e) (originalCopyParameter D P marked e t)) ∧
      (∀ e t, A.embedding.drawing.curve ((augmentedOriginalCopyEquiv D P marked).symm e)
        ((originalCopyParameter D P marked ((augmentedOriginalCopyEquiv D P marked).symm e)).symm t) =
        Q'.curve e t) := by
  obtain ⟨_F, _aux, _haux, _hsubset, p, hp, _hpB, _hpF, c, hformula,
    Q', hpoint, hcurve, inversionFaces, hregion, hclosure, hincidence, _hcurveclosure, _hu,
    _F', _aux', _haux', _hu', _hsubset', baseCharts, A, _hAF, hdraw, hpoints, _hretained, _hmarked⟩ :=
    original_marked_outer_inversion D P marked Q (charts _)
  let B : PlaneEmbedding (originalGraph D P marked) := ChartExistence.planeEmbeddingOfCharts (deleteMarkedDrawing D P marked Q') (copy_loopless D P marked) baseCharts
  change OuterArc B (alpha D P) (beta D P) at A
  let physical : Face Q ≃ A.embedding.Face := inversionFaces.trans (originalPhysicalFaceEquiv D P marked Q' B A hdraw)
  have hr (F : Face Q) : faceRegion Q' (inversionFaces F) =
      faceRegion A.embedding.drawing (physical F) :=
    trace_face_region Q' A.embedding.drawing (original_physical_trace D P marked Q' B A hdraw) _
  have hparams := original_physical_copy_parameters D P marked Q' B A hdraw
  refine ⟨p, hp, c, hformula, Q', hpoint, hcurve, inversionFaces, hregion, B, A, hdraw,
    rfl, physical, rfl, ?_, ?_, ?_, hpoints, hparams.1, hparams.2⟩
  · intro F z
    rw [← hr F]
    exact hregion F z
  · intro F z
    rw [← hr F]
    exact hclosure F z
  · intro F v
    change Q.point v ∈ closure (faceRegion Q F) ↔
      A.embedding.drawing.point v ∈ closure (faceRegion A.embedding.drawing (physical F))
    rw [hpoints, ← hr F]
    exact hincidence F v

end
end FiniteAvalanches.Electrical.SplitStep
