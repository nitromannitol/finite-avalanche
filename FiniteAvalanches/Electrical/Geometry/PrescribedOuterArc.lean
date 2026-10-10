import FiniteAvalanches.Electrical.Geometry.EdgeCharts
import FiniteAvalanches.Electrical.Geometry.DeletedArcFace
import FiniteAvalanches.External.ArcStraightening

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.ChartExistence
open StatementGeometry Source BSST
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- Endpoints of the supplied auxiliary curve are incident to its actual face. -/
theorem prescribed_auxiliary_endpoints (D : Drawing J) (F : Face D)
    (alpha beta : V) (A : AuxiliaryArc D F alpha beta) :
    BSST.incident D alpha F ∧ BSST.incident D beta F := by
  obtain ⟨G, _, hclosure, hunique⟩ := DeletedArc.common_face D
    (A.drawing.curve (.inr ())) (A.drawing.continuous _)
    (fun t ht0 ht1 => (A.interior_in_face t ht0 ht1).1)
  have hF : F = G := hunique F A.interior_in_face
  rw [← hF] at hclosure
  constructor
  · have h := hclosure ⟨⟨0, by constructor <;> norm_num⟩, A.drawing.start (.inr ())⟩
    change A.drawing.point alpha ∈ closure (faceRegion D F) at h
    change D.point alpha ∈ closure (faceRegion D F)
    simpa only [A.point_eq] using h
  · have h := hclosure ⟨⟨1, by constructor <;> norm_num⟩, A.drawing.finish (.inr ())⟩
    change A.drawing.point beta ∈ closure (faceRegion D F) at h
    change D.point beta ∈ closure (faceRegion D F)
    simpa only [A.point_eq] using h

/-- Package the supplied auxiliary drawing and supplied augmented charts as an OuterArc.
Unboundedness is an explicit internal premise of this packaging lemma. -/
theorem outerArc_of_prescribed_auxiliary (D : Drawing J)
    (hloop : ∀ e, J.left e ≠ J.right e) (alpha beta : V) (hne : alpha ≠ beta)
    (F : Face D) (A : AuxiliaryArc D F alpha beta)
    (hu : ¬Bornology.IsBounded (faceRegion D F))
    (augCharts : ∀ e, EdgeChart A.drawing e) :
    ∃ charts : ∀ e, EdgeChart D e,
    ∃ O : OuterArc (planeEmbeddingOfCharts D hloop charts) alpha beta,
      O.face = F ∧ O.embedding.drawing = A.drawing ∧
      (∀ e, HEq (O.embedding.edgeChart e) (augCharts e)) := by
  obtain ⟨charts⟩ := consume_arc_straightening
    External.parametrized_plane_arc_straightening D hloop
  have hends := prescribed_auxiliary_endpoints D F alpha beta A
  let O : OuterArc (planeEmbeddingOfCharts D hloop charts) alpha beta := {
    face := F
    alpha_incident := hends.1
    beta_incident := hends.2
    unbounded := hu
    embedding := planeEmbeddingOfCharts A.drawing (by
      intro e
      cases e with
      | inl e => exact hloop e
      | inr _ => exact hne) augCharts
    point_eq := A.point_eq
    curve_eq := A.curve_eq
    interior_in_face := A.interior_in_face }
  exact ⟨charts, O, rfl, rfl, fun _ => HEq.rfl⟩

end
end FiniteAvalanches.Electrical.ChartExistence
