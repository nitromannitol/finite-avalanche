import FiniteAvalanches.Electrical.Geometry.FullFaceInversion

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.ComplementFaces
open StatementGeometry Source BSST PunctureTransport
variable {V E W I : Type} [Fintype V] [Fintype E] [Fintype W] [Fintype I]
  {J : CopiedGraph V E} {K : CopiedGraph W I}

/-- A shared complement point identifies which larger region contains a full face. -/
theorem faceRegion_subset_of_shared_point (Q : Drawing J) (R : Drawing K)
    (htrace : drawingTrace R ⊆ drawingTrace Q) (F : Face Q) (G : Face R)
    (x : Plane) (hxF : x ∈ faceRegion Q F) (hxG : x ∈ faceRegion R G) :
    faceRegion Q F ⊆ faceRegion R G := by
  have hF := face_eq_of_mem Q F (faceAt Q x hxF.1) x hxF (mem_faceAt Q x hxF.1)
  have hG := face_eq_of_mem R G (faceAt R x (fun h => hxF.1 (htrace h))) x hxG
    (mem_faceAt R x (fun h => hxF.1 (htrace h)))
  rw [hF, hG]
  exact faceRegion_subset_of_trace_subset Q R htrace x hxF.1

/-- A full face approaching a point inside a deleted face lies in that deleted face. -/
theorem faceRegion_subset_of_closure_point (Q : Drawing J) (R : Drawing K)
    (htrace : drawingTrace R ⊆ drawingTrace Q) (F : Face Q) (G : Face R)
    (x : Plane) (hxF : x ∈ closure (faceRegion Q F)) (hxG : x ∈ faceRegion R G) :
    faceRegion Q F ⊆ faceRegion R G := by
  obtain ⟨y, hyG, hyF⟩ := mem_closure_iff.mp hxF (faceRegion R G)
    (faceRegion_isOpen R G) hxG
  exact faceRegion_subset_of_shared_point Q R htrace F G y hyF hyG

end FiniteAvalanches.Electrical.ComplementFaces
