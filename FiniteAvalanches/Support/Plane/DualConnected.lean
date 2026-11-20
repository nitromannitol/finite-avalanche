import FiniteAvalanches.Electrical.Geometry.BSST
import FiniteAvalanches.Support.Plane.FinitePointComplement
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Connected components of plane graph duals

A connectedness criterion for the chart-face dual in terms of locally constant
extensions across edge interiors.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open scoped Classical
open FiniteAvalanches.Electrical
open Source BSST

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
variable {J : CopiedGraph V E}

/-- The supporting graph of the dual defined by the two sides of each edge chart. -/
def chartDualGraph (D : Drawing J) (charts : ∀ e, EdgeChart D e) : SimpleGraph (Face D) :=
  supportGraph (fun e => negativeChartFace D e (charts e))
    (fun e => positiveChartFace D e (charts e))

/-- The complement of the embedded vertex set. -/
abbrev vertexComplement (D : Drawing J) := {z : Plane // z ∉ Set.range D.point}

/-- A point off the drawing trace also lies outside the vertex set. -/
def offTraceToVertexComplement (D : Drawing J) (z : {z : Plane // z ∉ drawingTrace D}) :
    vertexComplement D :=
  ⟨z, fun hz => z.property (Or.inl hz)⟩

/-- The dual is preconnected exactly when its face-component labels extend locally constantly
across edge interiors, after removing the vertex points. -/
theorem chartDualGraph_preconnected_iff_locallyConstant_extension
    (D : Drawing J) (charts : ∀ e, EdgeChart D e) :
    (chartDualGraph D charts).Preconnected ↔
      ∃ f : vertexComplement D → (chartDualGraph D charts).ConnectedComponent,
        IsLocallyConstant f ∧
        ∀ z : {z : Plane // z ∉ drawingTrace D},
          f (offTraceToVertexComplement D z) =
            (chartDualGraph D charts).connectedComponentMk (ConnectedComponents.mk z) := by
  constructor
  · intro h
    let e : E := Classical.choice ‹Nonempty E›
    let c := (chartDualGraph D charts).connectedComponentMk
      (negativeChartFace D e (charts e))
    refine ⟨fun _ => c, IsLocallyConstant.const c, ?_⟩
    intro z
    exact SimpleGraph.ConnectedComponent.sound (h _ _)
  · rintro ⟨f, hf, hface⟩ F H
    let : PreconnectedSpace (vertexComplement D) :=
      Subtype.preconnectedSpace (LatticeProb.PlaneTopology.isPathConnected_compl_range D.point).isConnected.isPreconnected
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe F
    obtain ⟨w, rfl⟩ := ConnectedComponents.surjective_coe H
    apply SimpleGraph.ConnectedComponent.exact
    rw [← hface z, ← hface w]
    exact hf.apply_eq_of_preconnectedSpace _ _

end
end FiniteAvalanches.Electrical.StatementGeometry
