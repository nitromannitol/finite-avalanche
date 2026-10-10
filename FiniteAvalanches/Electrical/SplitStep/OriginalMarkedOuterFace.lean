import FiniteAvalanches.Electrical.SplitStep.OriginalMarkedAuxiliary
import FiniteAvalanches.Electrical.Geometry.MarkedFaceInclusion
import FiniteAvalanches.External.PlaneEdgeChartIncidence

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open ComplementFaces PunctureTransport
open scoped Classical
noncomputable section

/-- Endpoint reversal fixes the original marked midpoint. -/
theorem marked_parameter_midpoint (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) :
    markedParameter D P marked ⟨1/2, by constructor <;> norm_num⟩ =
      ⟨1/2, by constructor <;> norm_num⟩ := by
  unfold markedParameter
  split
  · rfl
  · apply Subtype.ext
    change 1 - (1/2 : ℝ) = 1/2
    norm_num

/-- The retained drawing has a literal subset of the full original trace. -/
theorem original_deleted_trace_subset (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P)) :
    drawingTrace (deleteMarkedDrawing D P marked Q) ⊆ drawingTrace Q := by
  rintro z (⟨v, hv⟩ | hz)
  · exact Or.inl ⟨v, hv⟩
  · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp hz
    exact Or.inr (Set.mem_iUnion.mpr ⟨retainedPrimal D P marked e, t, ht⟩)

/-- An original marked auxiliary arc contains the original midpoint in its face. -/
theorem original_marked_midpoint_in_face (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (F : Face (deleteMarkedDrawing D P marked Q))
    (A : AuxiliaryArc (deleteMarkedDrawing D P marked Q) F (alpha D P) (beta D P))
    (hA : A.drawing = originalAugmentedDrawing D P marked Q) :
    Q.curve (markedPrimal D P marked) ⟨1/2, by constructor <;> norm_num⟩ ∈
      faceRegion (deleteMarkedDrawing D P marked Q) F := by
  have h := A.interior_in_face ⟨1/2, by constructor <;> norm_num⟩
    (by norm_num) (by norm_num)
  rw [hA] at h
  change Q.curve _ (markedParameter D P marked _) ∈ _ at h
  rw [marked_parameter_midpoint] at h
  exact h

/-- The full positive-side marked face lies in the actual marked H0 common face. -/
theorem original_marked_adjacent_face_subset (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (chart : EdgeChart Q (markedPrimal D P marked))
    (F : Face (deleteMarkedDrawing D P marked Q))
    (A : AuxiliaryArc (deleteMarkedDrawing D P marked Q) F (alpha D P) (beta D P))
    (hA : A.drawing = originalAugmentedDrawing D P marked Q) :
    faceRegion Q (positiveChartFace Q (markedPrimal D P marked) chart) ⊆
      faceRegion (deleteMarkedDrawing D P marked Q) F := by
  have hclosure := (External.plane_edge_chart_incidence
    (LatticeDrawing.primalGraph D P) Q (markedPrimal D P marked) chart
    (primal_loopless D P _)).1
  exact faceRegion_subset_of_closure_point Q (deleteMarkedDrawing D P marked Q)
    (original_deleted_trace_subset D P marked Q) _ F _
    (hclosure (Set.mem_range_self ⟨1/2, by constructor <;> norm_num⟩))
    (original_marked_midpoint_in_face D P marked Q F A hA)

end
end FiniteAvalanches.Electrical.SplitStep
