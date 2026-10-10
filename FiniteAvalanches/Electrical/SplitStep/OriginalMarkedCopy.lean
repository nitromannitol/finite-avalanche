import FiniteAvalanches.Electrical.SplitStep.ReversedChart

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

/-- The inverse relabelling keeps every retained ID and singles out exactly the marked ID. -/
theorem original_copy_inverse (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    (∀ e, (augmentedOriginalCopyEquiv D P marked).symm (retainedPrimal D P marked e) = .inl e) ∧
    (augmentedOriginalCopyEquiv D P marked).symm (markedPrimal D P marked) = .inr () := by
  constructor
  · intro e
    apply (augmentedOriginalCopyEquiv D P marked).injective
    rw [Equiv.apply_symm_apply]
    rfl
  · apply (augmentedOriginalCopyEquiv D P marked).injective
    rw [Equiv.apply_symm_apply]
    rfl

/-- Retained parameters are unchanged; only the marked parameter may be reversed. -/
def originalCopyParameter (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    Copy D P marked ⊕ Unit → ArcParameter ≃ₜ ArcParameter :=
  Sum.elim (fun _ => Homeomorph.refl _) (fun _ => markedParameter D P marked)

/-- The physical marked drawing and its inverse copy map retain the whole original curves. -/
theorem original_physical_copy_parameters (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (hdraw : A.embedding.drawing = originalAugmentedDrawing D P marked Q) :
    (∀ e t, A.embedding.drawing.curve e t =
      Q.curve (augmentedOriginalCopyEquiv D P marked e) (originalCopyParameter D P marked e t)) ∧
    (∀ e t, A.embedding.drawing.curve ((augmentedOriginalCopyEquiv D P marked).symm e)
      ((originalCopyParameter D P marked ((augmentedOriginalCopyEquiv D P marked).symm e)).symm t) =
      Q.curve e t) := by
  have h : ∀ e t, A.embedding.drawing.curve e t =
      Q.curve (augmentedOriginalCopyEquiv D P marked e) (originalCopyParameter D P marked e t) := by
    intro e t
    rw [hdraw]
    cases e <;> rfl
  refine ⟨h, ?_⟩
  intro e t
  rw [h, Homeomorph.apply_symm_apply, Equiv.apply_symm_apply]

/-- Pull the physical marked chart back along the actual stored marked parameter. -/
def physicalMarkedChart (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (hdraw : A.embedding.drawing = originalAugmentedDrawing D P marked Q) :
    EdgeChart Q (markedPrimal D P marked) :=
  if ha : (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P then
    copyEdgeChart Q A.embedding.drawing (original_physical_trace D P marked Q B A hdraw)
      (markedPrimal D P marked) (.inr ()) (by
        rw [(original_physical_curves D P marked Q B A hdraw).2.2]
        simp only [markedParameter, if_pos ha, Homeomorph.refl_apply, Function.comp_def]
        rfl)
      (A.embedding.edgeChart (.inr ()))
  else
    reverseEdgeChart Q A.embedding.drawing (original_physical_trace D P marked Q B A hdraw)
      (markedPrimal D P marked) (.inr ()) (by
        intro t
        rw [(original_physical_curves D P marked Q B A hdraw).2.2]
        change Q.curve _ t = Q.curve _ (markedParameter D P marked (unitInterval.symm t))
        simp only [markedParameter, if_neg ha]
        change Q.curve _ t = Q.curve _ (unitInterval.symm (unitInterval.symm t))
        rw [unitInterval.symm_symm])
      (A.embedding.edgeChart (.inr ()))

/-- Both marked chart sides follow storage orientation, swapping exactly when its parameter is reversed. -/
theorem physical_marked_chart_faces (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (hdraw : A.embedding.drawing = originalAugmentedDrawing D P marked Q) :
    originalPhysicalFaceEquiv D P marked Q B A hdraw
      (negativeChartFace Q (markedPrimal D P marked) (physicalMarkedChart D P marked Q B A hdraw)) =
      (if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P
        then A.embedding.rightFace (.inr ()) else A.embedding.leftFace (.inr ())) ∧
    originalPhysicalFaceEquiv D P marked Q B A hdraw
      (positiveChartFace Q (markedPrimal D P marked) (physicalMarkedChart D P marked Q B A hdraw)) =
      (if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P
        then A.embedding.leftFace (.inr ()) else A.embedding.rightFace (.inr ())) := by
  by_cases ha : (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P
  · simp only [physicalMarkedChart, dif_pos ha, if_pos ha, originalPhysicalFaceEquiv]
    exact copy_edge_chart_faces Q A.embedding.drawing
      (original_physical_trace D P marked Q B A hdraw) _ _ _ _
  · simp only [physicalMarkedChart, dif_neg ha, if_neg ha, originalPhysicalFaceEquiv]
    exact reverse_edge_chart_faces Q A.embedding.drawing
      (original_physical_trace D P marked Q B A hdraw) _ _ _ _

/-- A full-face inversion carries both supplied marked sides through the actual storage reversal. -/
theorem original_physical_marked_sides_of_side_equations (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q Q' : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (hdraw : A.embedding.drawing = originalAugmentedDrawing D P marked Q')
    (faces : Face Q ≃ Face Q')
    (hside :
      faces (negativeChartFace Q (markedPrimal D P marked) (charts _)) =
        negativeChartFace Q' (markedPrimal D P marked) (physicalMarkedChart D P marked Q' B A hdraw) ∧
      faces (positiveChartFace Q (markedPrimal D P marked) (charts _)) =
        positiveChartFace Q' (markedPrimal D P marked) (physicalMarkedChart D P marked Q' B A hdraw)) :
    let physical := faces.trans (originalPhysicalFaceEquiv D P marked Q' B A hdraw)
    physical ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) =
      (if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P
        then A.embedding.rightFace (.inr ()) else A.embedding.leftFace (.inr ())) ∧
    physical ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) =
      (if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P
        then A.embedding.leftFace (.inr ()) else A.embedding.rightFace (.inr ())) := by
  intro physical
  have hc := physical_marked_chart_faces D P marked Q' B A hdraw
  exact ⟨(congrArg (originalPhysicalFaceEquiv D P marked Q' B A hdraw) hside.1).trans hc.1,
    (congrArg (originalPhysicalFaceEquiv D P marked Q' B A hdraw) hside.2).trans hc.2⟩

end
end FiniteAvalanches.Electrical.SplitStep
