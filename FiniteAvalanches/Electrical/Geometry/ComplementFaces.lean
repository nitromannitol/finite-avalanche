import FiniteAvalanches.Electrical.Geometry.DeletedArcFace

/-! Complement components under deletion, on the literal drawn plane regions. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.ComplementFaces
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open scoped Classical
noncomputable section

variable {V E W F : Type} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
  {J : CopiedGraph V E} {K : CopiedGraph W F}

/-- The face at a point is its actual complement component. -/
def faceAt (D : Drawing J) (z : Plane) (hz : z ∉ drawingTrace D) : Face D :=
  ConnectedComponents.mk ⟨z, hz⟩

/-- A point belongs to its actual face. -/
theorem mem_faceAt (D : Drawing J) (z : Plane) (hz : z ∉ drawingTrace D) :
    z ∈ faceRegion D (faceAt D z hz) := ⟨hz, rfl⟩

/-- A complement point determines its face uniquely. -/
theorem face_eq_of_mem (D : Drawing J) (A B : Face D) (z : Plane)
    (ha : z ∈ faceRegion D A) (hb : z ∈ faceRegion D B) : A = B :=
  ha.2.symm.trans hb.2

/-- Deleting trace cannot separate two points of an original complement component. -/
theorem faceRegion_subset_of_trace_subset (D : Drawing J) (R : Drawing K)
    (htrace : drawingTrace R ⊆ drawingTrace D) (z : Plane)
    (hz : z ∉ drawingTrace D) :
    faceRegion D (faceAt D z hz) ⊆
      faceRegion R (faceAt R z (fun h => hz (htrace h))) := by
  let f : {x : Plane // x ∉ drawingTrace D} → {x : Plane // x ∉ drawingTrace R} :=
    fun x => ⟨x.val, fun h => x.property (htrace h)⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  rintro x ⟨hx, he⟩
  refine ⟨fun h => hx (htrace h), ?_⟩
  apply ConnectedComponents.coe_eq_coe'.mpr
  exact hf.mapsTo_connectedComponent ⟨z, hz⟩ (ConnectedComponents.coe_eq_coe'.mp he)

/-- A whole continuous curve avoiding the trace stays in the face of its initial point. -/
theorem range_subset_faceAt (D : Drawing J) (gamma : ArcParameter → Plane)
    (hc : Continuous gamma) (hoff : ∀ t, gamma t ∉ drawingTrace D) :
    Set.range gamma ⊆ faceRegion D
      (faceAt D (gamma ⟨0, by constructor <;> norm_num⟩) (hoff _)) := by
  let f : ArcParameter → {z : Plane // z ∉ drawingTrace D} :=
    fun t => ⟨gamma t, hoff t⟩
  have hf : Continuous f := hc.subtype_mk _
  have hconn : IsPreconnected (Set.range f) := isPreconnected_range hf
  rintro z ⟨t, rfl⟩
  refine ⟨hoff t, ?_⟩
  apply ConnectedComponents.coe_eq_coe'.mpr
  exact hconn.subset_connectedComponent
    (Set.mem_range_self ⟨0, by constructor <;> norm_num⟩) (Set.mem_range_self t)

end
end FiniteAvalanches.Electrical.ComplementFaces
