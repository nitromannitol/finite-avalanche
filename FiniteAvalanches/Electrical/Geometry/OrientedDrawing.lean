import FiniteAvalanches.Electrical.Geometry.DiskDrawing
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

/-! Proper plane drawings, actual complement faces, and oriented local edge charts. -/
namespace FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical
noncomputable section
abbrev Plane := ℝ × ℝ

/-- An orientation-preserving plane chart, with its orientation witnessed by an isotopy. -/
structure OrientedChart where
  map : Plane ≃ₜ Plane
  isotopy : ArcParameter → Plane ≃ₜ Plane
  continuous : Continuous (fun p : ArcParameter × Plane => isotopy p.1 p.2)
  inverse_continuous : Continuous (fun p : ArcParameter × Plane => (isotopy p.1).symm p.2)
  start : isotopy ⟨0,by norm_num⟩ = Homeomorph.refl Plane
  finish : isotopy ⟨1,by norm_num⟩ = map

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- The whole embedded graph, retaining every original copied arc. -/
def drawingTrace (D : Drawing J) : Set Plane :=
  Set.range D.point ∪ ⋃ e, Set.range (D.curve e)

/-- A regular oriented neighborhood of an interior point of the actual edge arc. -/
structure EdgeChart (D : Drawing J) (e : E) where
  chart : OrientedChart
  radius : ℝ
  radius_pos : 0 < radius
  radius_small : radius < 1/4
  straight : ∀ t : ArcParameter, |t.val-1/2| < radius →
    chart.map (D.curve e t) = (t.val,0)
  trace_box : ∀ z : Plane, |z.1-1/2| < radius → |z.2| < radius →
    (chart.map.symm z ∈ drawingTrace D ↔ z.2 = 0)

/-- A finite proper plane embedding by simple arcs, with oriented regular edge charts.
All geometry concerns the actual curves; no rotation, face count or Euler identity is supplied. -/
structure PlaneEmbedding (J : CopiedGraph V E) where
  drawing : Drawing J
  edge_injective : ∀ e, Function.Injective (drawing.curve e)
  edgeChart : ∀ e, EdgeChart drawing e

namespace PlaneEmbedding
variable (D : PlaneEmbedding J)

/-- Faces are actual connected components of the complement of the embedded graph. -/
abbrev Face := ConnectedComponents {z : Plane // z ∉ drawingTrace D.drawing}

def faceRegion (F : D.Face) : Set Plane :=
  {z | ∃ hz : z ∉ drawingTrace D.drawing,
    ConnectedComponents.mk (⟨z,hz⟩ : {w // w ∉ drawingTrace D.drawing}) = F}

private theorem side_off_trace (e : E) (positive : Bool) :
    (D.edgeChart e).chart.map.symm
      (1/2,if positive then (D.edgeChart e).radius/2 else -((D.edgeChart e).radius/2)) ∉
        drawingTrace D.drawing := by
  let c := D.edgeChart e
  have hr := c.radius_pos
  have h0 : |(1/2 : ℝ)-1/2| < c.radius := by simpa using hr
  have hp : |c.radius/2| < c.radius := by rw [abs_of_pos (by linarith)]; linarith
  have hn : |-(c.radius/2)| < c.radius := by rw [abs_neg]; exact hp
  cases positive
  · simp only [Bool.false_eq_true,if_false]
    change c.chart.map.symm (1/2,-(c.radius/2)) ∉ drawingTrace D.drawing
    exact fun h => (by linarith : -(c.radius/2) ≠ 0)
      ((c.trace_box _ h0 hn).mp h)
  · change c.chart.map.symm (1/2,c.radius/2) ∉ drawingTrace D.drawing
    exact fun h => (by linarith : c.radius/2 ≠ 0)
      ((c.trace_box _ h0 hp).mp h)

/-- The actual face immediately to the left of the original oriented edge copy. -/
def leftFace (e : E) : D.Face := ConnectedComponents.mk
  ⟨(D.edgeChart e).chart.map.symm (1/2,(D.edgeChart e).radius/2),D.side_off_trace e true⟩

/-- The actual face immediately to the right; bridges may have the same face on both sides. -/
def rightFace (e : E) : D.Face := ConnectedComponents.mk
  ⟨(D.edgeChart e).chart.map.symm (1/2,-((D.edgeChart e).radius/2)),D.side_off_trace e false⟩

/-- Literal geometric incidence, including repeated visits of a face at a vertex. -/
def incident (x : V) (F : D.Face) : Prop := D.drawing.point x ∈ closure (D.faceRegion F)
end PlaneEmbedding

/-- The auxiliary alpha-to-beta arc retains every original edge copy. -/
def augmentedGraph (J : CopiedGraph V E) (alpha beta : V) : CopiedGraph V (E ⊕ Unit) :=
  ⟨Sum.elim J.left (fun _ => alpha),Sum.elim J.right (fun _ => beta)⟩

/-- An actual arc in the chosen common outer face, not a combinatorial face assumption. -/
structure OuterArc (D : PlaneEmbedding J) (alpha beta : V) where
  face : D.Face
  alpha_incident : D.incident alpha face
  beta_incident : D.incident beta face
  unbounded : ¬Bornology.IsBounded (D.faceRegion face)
  embedding : PlaneEmbedding (augmentedGraph J alpha beta)
  point_eq : embedding.drawing.point = D.drawing.point
  curve_eq : ∀ e, embedding.drawing.curve (.inl e) = D.drawing.curve e
  interior_in_face : ∀ t : ArcParameter, 0 < t.val → t.val < 1 →
    embedding.drawing.curve (.inr ()) t ∈ D.faceRegion face

end
end FiniteAvalanches.Electrical.Source
