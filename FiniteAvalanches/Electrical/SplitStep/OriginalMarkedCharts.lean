import FiniteAvalanches.Electrical.SplitStep.OriginalMarkedAuxiliary

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

private theorem component_cast_mk (S T : Set Plane) (h : S = T)
    (z : Plane) (hz : z ∉ S) (ht : z ∉ T) :
    Equiv.cast (congrArg (fun U : Set Plane => ConnectedComponents {w : Plane // w ∉ U}) h)
      (ConnectedComponents.mk (⟨z, hz⟩ : {w : Plane // w ∉ S})) =
    ConnectedComponents.mk (⟨z, ht⟩ : {w : Plane // w ∉ T}) := by
  cases h
  rfl

/-- Every retained supplied chart still straightens the identical original curve. -/
def originalRetainedChart (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (e : Copy D P marked) :
    EdgeChart (originalAugmentedDrawing D P marked Q) (.inl e) where
  chart := (charts (retainedPrimal D P marked e)).chart
  radius := (charts (retainedPrimal D P marked e)).radius
  radius_pos := (charts (retainedPrimal D P marked e)).radius_pos
  radius_small := (charts (retainedPrimal D P marked e)).radius_small
  straight := (charts (retainedPrimal D P marked e)).straight
  trace_box := by
    intro z hx hy
    rw [← original_augmented_trace D P marked Q]
    exact (charts (retainedPrimal D P marked e)).trace_box z hx hy

/-- The complete original full-H face cast preserves both supplied retained chart sides. -/
theorem original_retained_chart_faces (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (e : Copy D P marked) :
    let A := originalAugmentedDrawing D P marked Q
    let faces := traceFaceEquiv Q A (original_augmented_trace D P marked Q)
    faces ((sourceDeletedDualGraph D P marked Q charts).left e) =
      negativeChartFace A (.inl e) (originalRetainedChart D P marked Q charts e) ∧
    faces ((sourceDeletedDualGraph D P marked Q charts).right e) =
      positiveChartFace A (.inl e) (originalRetainedChart D P marked Q charts e) := by
  intro A faces
  constructor
  · exact component_cast_mk _ _ (original_augmented_trace D P marked Q) _ _ _
  · exact component_cast_mk _ _ (original_augmented_trace D P marked Q) _ _ _

/-- Any signed stream equation on this exact auxiliary drawing pulls back to all original faces. -/
theorem original_stream_equation_pullback (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (phi : Vertex D P → ℝ)
    (psi : Face (originalAugmentedDrawing D P marked Q) → ℝ)
    (hpsi : ∀ e,
      psi (positiveChartFace _ (.inl e) (originalRetainedChart D P marked Q charts e)) -
        psi (negativeChartFace _ (.inl e) (originalRetainedChart D P marked Q charts e)) =
      phi (copyA D P marked e) - phi (copyB D P marked e)) :
    let faces := traceFaceEquiv Q (originalAugmentedDrawing D P marked Q)
      (original_augmented_trace D P marked Q)
    ∀ e, (psi ∘ faces) ((sourceDeletedDualGraph D P marked Q charts).right e) -
      (psi ∘ faces) ((sourceDeletedDualGraph D P marked Q charts).left e) =
      phi (copyA D P marked e) - phi (copyB D P marked e) := by
  intro faces e
  have hf := original_retained_chart_faces D P marked Q charts e
  change psi (faces _) - psi (faces _) = _
  rw [hf.1, hf.2]
  exact hpsi e

end
end FiniteAvalanches.Electrical.SplitStep
