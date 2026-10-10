import FiniteAvalanches.Electrical.SplitStep.OriginalMarkedInversion
import FiniteAvalanches.Electrical.SplitStep.OriginalMarkedCharts

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

private theorem component_cast_point (S T : Set Plane) (h : S = T)
    (z : Plane) (hs : z ∉ S) (ht : z ∉ T) :
    Equiv.cast (congrArg (fun U : Set Plane => ConnectedComponents {w : Plane // w ∉ U}) h)
      (ConnectedComponents.mk (⟨z, hs⟩ : {w : Plane // w ∉ S})) =
    ConnectedComponents.mk (⟨z, ht⟩ : {w : Plane // w ∉ T}) := by
  cases h
  rfl

/-- Copy a supplied oriented chart across identical traces and identical parametrized curves. -/
def copyEdgeChart {V E W I : Type} [Fintype V] [Fintype E] [Fintype W] [Fintype I]
    {J : CopiedGraph V E} {K : CopiedGraph W I}
    (R : Drawing J) (S : Drawing K) (htrace : drawingTrace R = drawingTrace S)
    (e : E) (f : I) (hcurve : R.curve e = S.curve f) (c : EdgeChart S f) : EdgeChart R e where
  chart := c.chart
  radius := c.radius
  radius_pos := c.radius_pos
  radius_small := c.radius_small
  straight := by intro t ht; rw [hcurve]; exact c.straight t ht
  trace_box := by intro z hx hy; rw [htrace]; exact c.trace_box z hx hy

/-- The full complement-component cast carries both literal side points of a copied chart. -/
theorem copy_edge_chart_faces {V E W I : Type} [Fintype V] [Fintype E] [Fintype W] [Fintype I]
    {J : CopiedGraph V E} {K : CopiedGraph W I}
    (R : Drawing J) (S : Drawing K) (htrace : drawingTrace R = drawingTrace S)
    (e : E) (f : I) (hcurve : R.curve e = S.curve f) (c : EdgeChart S f) :
    traceFaceEquiv R S htrace (negativeChartFace R e (copyEdgeChart R S htrace e f hcurve c)) =
      negativeChartFace S f c ∧
    traceFaceEquiv R S htrace (positiveChartFace R e (copyEdgeChart R S htrace e f hcurve c)) =
      positiveChartFace S f c := by
  constructor
  · exact component_cast_point _ _ htrace _ _ _
  · exact component_cast_point _ _ htrace _ _ _

/-- Relabelling the full original drawing as the supplied marked outer arc changes no trace. -/
theorem original_physical_trace (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (hdraw : A.embedding.drawing = originalAugmentedDrawing D P marked Q) :
    drawingTrace Q = drawingTrace A.embedding.drawing :=
  (original_augmented_trace D P marked Q).trans (congrArg drawingTrace hdraw.symm)

/-- Every original face is retained, including faces adjacent to the marked copy. -/
def originalPhysicalFaceEquiv (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (hdraw : A.embedding.drawing = originalAugmentedDrawing D P marked Q) : Face Q ≃ A.embedding.Face :=
  traceFaceEquiv Q A.embedding.drawing (original_physical_trace D P marked Q B A hdraw)

/-- The physical marked drawing retains each original point, retained curve, and marked parameter. -/
theorem original_physical_curves (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (hdraw : A.embedding.drawing = originalAugmentedDrawing D P marked Q) :
    A.embedding.drawing.point = Q.point ∧
      (∀ e, A.embedding.drawing.curve (.inl e) = Q.curve (retainedPrimal D P marked e)) ∧
      A.embedding.drawing.curve (.inr ()) = Q.curve (markedPrimal D P marked) ∘ markedParameter D P marked := by
  rw [hdraw]
  exact ⟨rfl, fun _ => rfl, rfl⟩

/-- Pull a physical retained chart back to its literal original copy without changing orientation. -/
def physicalRetainedChart (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (hdraw : A.embedding.drawing = originalAugmentedDrawing D P marked Q) (e : Copy D P marked) :
    EdgeChart Q (retainedPrimal D P marked e) :=
  copyEdgeChart Q A.embedding.drawing (original_physical_trace D P marked Q B A hdraw)
    (retainedPrimal D P marked e) (.inl e)
    ((original_physical_curves D P marked Q B A hdraw).2.1 e).symm (A.embedding.edgeChart (.inl e))

/-- The retained copy cast maps negative to physical right and positive to physical left. -/
theorem physical_retained_chart_faces (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (hdraw : A.embedding.drawing = originalAugmentedDrawing D P marked Q) (e : Copy D P marked) :
    originalPhysicalFaceEquiv D P marked Q B A hdraw
      (negativeChartFace Q (retainedPrimal D P marked e) (physicalRetainedChart D P marked Q B A hdraw e)) =
      A.embedding.rightFace (.inl e) ∧
    originalPhysicalFaceEquiv D P marked Q B A hdraw
      (positiveChartFace Q (retainedPrimal D P marked e) (physicalRetainedChart D P marked Q B A hdraw e)) =
      A.embedding.leftFace (.inl e) :=
  copy_edge_chart_faces Q A.embedding.drawing (original_physical_trace D P marked Q B A hdraw)
    (retainedPrimal D P marked e) (.inl e)
    ((original_physical_curves D P marked Q B A hdraw).2.1 e).symm (A.embedding.edgeChart (.inl e))

/-- Inversion followed by the literal drawing-copy cast retains both original supplied sides. -/
theorem original_physical_retained_sides_of_side_equations (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q Q' : Drawing (primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (hdraw : A.embedding.drawing = originalAugmentedDrawing D P marked Q')
    (faces : Face Q ≃ Face Q')
    (hside : ∀ e : Copy D P marked,
      faces (negativeChartFace Q (retainedPrimal D P marked e) (charts _)) =
        negativeChartFace Q' (retainedPrimal D P marked e) (physicalRetainedChart D P marked Q' B A hdraw e) ∧
      faces (positiveChartFace Q (retainedPrimal D P marked e) (charts _)) =
        positiveChartFace Q' (retainedPrimal D P marked e) (physicalRetainedChart D P marked Q' B A hdraw e)) :
    let physical := faces.trans (originalPhysicalFaceEquiv D P marked Q' B A hdraw)
    ∀ e : Copy D P marked,
      physical ((sourceDeletedDualGraph D P marked Q charts).left e) = A.embedding.rightFace (.inl e) ∧
      physical ((sourceDeletedDualGraph D P marked Q charts).right e) = A.embedding.leftFace (.inl e) := by
  intro physical e
  have hc := physical_retained_chart_faces D P marked Q' B A hdraw e
  exact ⟨(congrArg (originalPhysicalFaceEquiv D P marked Q' B A hdraw) (hside e).1).trans hc.1,
    (congrArg (originalPhysicalFaceEquiv D P marked Q' B A hdraw) (hside e).2).trans hc.2⟩

end
end FiniteAvalanches.Electrical.SplitStep
