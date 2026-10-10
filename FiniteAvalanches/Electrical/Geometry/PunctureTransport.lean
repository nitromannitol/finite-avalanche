import FiniteAvalanches.Electrical.Geometry.SourceRetainedPathBoundary
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Maps.Proper.Basic

/-! Ordinary boundary transport on actual plane complement components. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.PunctureTransport
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST

variable {V E W A : Type} [Fintype V] [Fintype E] [Fintype W] [Fintype A]
  {J : CopiedGraph V E} {K : CopiedGraph W A}

/-- Point and whole-curve identities determine a Drawing, including its proof fields. -/
theorem drawing_eq_of_points_curves (R S : Drawing J)
    (hp : ∀ v, R.point v = S.point v)
    (hc : ∀ e t, R.curve e t = S.curve e t) : R = S := by
  have hp' : R.point = S.point := funext hp
  have hc' : R.curve = S.curve := funext (fun e => funext (hc e))
  cases R
  cases S
  cases hp'
  cases hc'
  rfl

/-- A literal complement face is an open planar connected component. -/
theorem faceRegion_isOpen (R : Drawing J) (F : Face R) : IsOpen (faceRegion R F) := by
  obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe F
  have heq : faceRegion R (ConnectedComponents.mk a) =
      connectedComponentIn (drawingTrace R)ᶜ a.val := by
    rw [connectedComponentIn_eq_image a.property]
    ext z
    constructor
    · rintro ⟨hz, he⟩
      exact ⟨⟨z, hz⟩, ConnectedComponents.coe_eq_coe'.mp he, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.property, ConnectedComponents.coe_eq_coe'.mpr hb⟩
  rw [heq]
  exact (drawingTrace_isClosed R).isOpen_compl.connectedComponentIn

/-- For actual complement faces, region and closure equivalences transport the frontier. -/
theorem frontier_transport (R : Drawing J) (S : Drawing K)
    (F : Face R) (G : Face S) (x y : Plane)
    (hregion : x ∈ faceRegion R F ↔ y ∈ faceRegion S G)
    (hclosure : x ∈ closure (faceRegion R F) ↔ y ∈ closure (faceRegion S G)) :
    x ∈ frontier (faceRegion R F) ↔ y ∈ frontier (faceRegion S G) := by
  rw [frontier, frontier, (faceRegion_isOpen R F).interior_eq,
    (faceRegion_isOpen S G).interior_eq]
  exact and_congr hclosure (not_congr hregion)

end FiniteAvalanches.Electrical.PunctureTransport
