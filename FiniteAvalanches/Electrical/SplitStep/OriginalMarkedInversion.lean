import FiniteAvalanches.Electrical.SplitStep.OriginalMarkedOuterFace
import FiniteAvalanches.Electrical.Geometry.PrescribedOuterArc

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open ComplementFaces PunctureTransport ChartExistence
open scoped Classical
noncomputable section

/-- Invert the supplied full drawing next to its actual marked curve, retaining every
full face and original copy. The same marked auxiliary curve bounds an unbounded H0 face. -/
theorem original_marked_outer_inversion (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (chart : EdgeChart Q (markedPrimal D P marked)) :
    ∃ F : Face (deleteMarkedDrawing D P marked Q),
    ∃ A : AuxiliaryArc (deleteMarkedDrawing D P marked Q) F (alpha D P) (beta D P),
      A.drawing = originalAugmentedDrawing D P marked Q ∧
    let B := positiveChartFace Q (markedPrimal D P marked) chart
    faceRegion Q B ⊆ faceRegion (deleteMarkedDrawing D P marked Q) F ∧
  ∃ p : Plane, ∃ hp : p ∉ drawingTrace Q,
    p ∈ faceRegion Q B ∧
    p ∈ faceRegion (deleteMarkedDrawing D P marked Q) F ∧
    ∃ c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)},
      (∀ z : {z : Plane // z ≠ p},
        (c z).val =
          ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
           -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2))) ∧
      ∃ Q' : Drawing (LatticeDrawing.primalGraph D P),
        (∀ v, Q'.point v = (c ⟨Q.point v, by
          intro heq
          apply hp
          exact heq ▸ (Or.inl (Set.mem_range_self v) : Q.point v ∈ drawingTrace Q)⟩).val) ∧
        (∀ e t, Q'.curve e t = (c ⟨Q.curve e t, by
          intro heq
          apply hp
          exact heq ▸ (Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_range_self t⟩) :
            Q.curve e t ∈ drawingTrace Q)⟩).val) ∧
        ∃ faces : Face Q ≃ Face Q',
          (∀ G : Face Q, ∀ z : {z : Plane // z ≠ p},
            z.val ∈ faceRegion Q G ↔ (c z).val ∈ faceRegion Q' (faces G)) ∧
          (∀ G : Face Q, ∀ z : {z : Plane // z ≠ p},
            z.val ∈ closure (faceRegion Q G) ↔
              (c z).val ∈ closure (faceRegion Q' (faces G))) ∧
          (∀ G : Face Q, ∀ v : Vertex D P, incident Q v G ↔ incident Q' v (faces G)) ∧
          (∀ e : LatticeDrawing.PrimalCopy D P, ∀ S : Set ArcParameter, ∀ t : ArcParameter,
            Q.curve e t ∈ closure (Q.curve e '' S) ↔
              Q'.curve e t ∈ closure (Q'.curve e '' S)) ∧
          ¬Bornology.IsBounded (faceRegion Q' (faces B)) ∧
          ∃ F' : Face (deleteMarkedDrawing D P marked Q'),
          ∃ A' : AuxiliaryArc (deleteMarkedDrawing D P marked Q') F' (alpha D P) (beta D P),
            A'.drawing = originalAugmentedDrawing D P marked Q' ∧
            ¬Bornology.IsBounded (faceRegion (deleteMarkedDrawing D P marked Q') F') ∧
            faceRegion Q' (faces B) ⊆ faceRegion (deleteMarkedDrawing D P marked Q') F' ∧
          ∃ baseCharts : ∀ e, EdgeChart (deleteMarkedDrawing D P marked Q') e,
          ∃ O : OuterArc (planeEmbeddingOfCharts (deleteMarkedDrawing D P marked Q')
            (copy_loopless D P marked) baseCharts) (alpha D P) (beta D P),
            O.face = F' ∧ O.embedding.drawing = originalAugmentedDrawing D P marked Q' ∧
            O.embedding.drawing.point = Q'.point ∧
            (∀ e, O.embedding.drawing.curve (.inl e) = Q'.curve (retainedPrimal D P marked e)) ∧
            O.embedding.drawing.curve (.inr ()) =
              Q'.curve (markedPrimal D P marked) ∘ markedParameter D P marked := by
  obtain ⟨F, A, hA, _⟩ := original_marked_auxiliary_dictionary D P marked Q
  let B := positiveChartFace Q (markedPrimal D P marked) chart
  have hsubset : faceRegion Q B ⊆ faceRegion (deleteMarkedDrawing D P marked Q) F :=
    original_marked_adjacent_face_subset D P marked Q chart F A hA
  obtain ⟨p, hpole, hpB, c, hformula, Q', hpoint, hcurve,
    faces, hregions, hclosures, hincidences, hcurveclosures, hunbounded⟩ :=
    full_face_inversion_transport Q B
  obtain ⟨F', A', hA', _⟩ := original_marked_auxiliary_dictionary D P marked Q'
  let mid : ArcParameter := ⟨1/2, by constructor <;> norm_num⟩
  have hoff : Q.curve (markedPrimal D P marked) mid ≠ p := by
    intro heq
    apply hpole
    exact heq ▸ (Or.inr (Set.mem_iUnion.mpr
      ⟨markedPrimal D P marked, Set.mem_range_self mid⟩))
  have hcl : Q.curve (markedPrimal D P marked) mid ∈ closure (faceRegion Q B) :=
    (External.plane_edge_chart_incidence (LatticeDrawing.primalGraph D P) Q
      (markedPrimal D P marked) chart (primal_loopless D P _)).1 (Set.mem_range_self mid)
  have hcl' : Q'.curve (markedPrimal D P marked) mid ∈ closure (faceRegion Q' (faces B)) := by
    rw [hcurve]
    exact (hclosures B ⟨_, hoff⟩).mp hcl
  have hsubset' : faceRegion Q' (faces B) ⊆ faceRegion (deleteMarkedDrawing D P marked Q') F' :=
    faceRegion_subset_of_closure_point Q' (deleteMarkedDrawing D P marked Q')
      (original_deleted_trace_subset D P marked Q') (faces B) F' _ hcl'
      (original_marked_midpoint_in_face D P marked Q' F' A' hA')
  have hu' : ¬Bornology.IsBounded (faceRegion (deleteMarkedDrawing D P marked Q') F') :=
    fun hb => hunbounded (hb.subset hsubset')
  have hne : alpha D P ≠ beta D P := by intro he; cases he
  obtain ⟨augCharts⟩ := consume_auxiliary_straightening
    External.parametrized_plane_arc_straightening (deleteMarkedDrawing D P marked Q')
    (copy_loopless D P marked) (alpha D P) (beta D P) hne F' A'
  obtain ⟨baseCharts, O, hOF, hOA, _⟩ := outerArc_of_prescribed_auxiliary
    (deleteMarkedDrawing D P marked Q') (copy_loopless D P marked)
    (alpha D P) (beta D P) hne F' A' hu' augCharts
  have hO : O.embedding.drawing = originalAugmentedDrawing D P marked Q' := hOA.trans hA'
  refine ⟨F, A, hA, hsubset, p, hpole, hpB, hsubset hpB, c, hformula,
    Q', hpoint, hcurve, faces, hregions, hclosures, hincidences, hcurveclosures, hunbounded,
    F', A', hA', hu', hsubset', baseCharts, O, hOF, hO, ?_, ?_, ?_⟩
  · rw [hO]; rfl
  · intro e; rw [hO]; rfl
  · rw [hO]; rfl

end
end FiniteAvalanches.Electrical.SplitStep
