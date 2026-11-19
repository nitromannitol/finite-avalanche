import FiniteAvalanches.Support.Plane.GeometricDual
import FiniteAvalanches.Support.Plane.HalfOpenLocalStraightening
import FiniteAvalanches.Electrical.Geometry.ComplementFaces
import FiniteAvalanches.Electrical.Geometry.ConnectedDrawingQuotient

/-!
# Faces after deleting an edge

When the midpoint of an edge is absent from a subdrawing, both chart-side faces
of the original drawing lie in one face of that subdrawing.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST ComplementFaces DrawingContraction Set
open scoped Classical

variable {V E W F : Type} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
variable {J : CopiedGraph V E} {K : CopiedGraph W F}

/-- A face of the original drawing lies in the subdrawing face containing any
one of its points. -/
theorem faceRegion_subset_of_mem_of_trace_subset (D : Drawing J) (R : Drawing K)
    (htrace : drawingTrace R ⊆ drawingTrace D) (A : Face D) (B : Face R)
    {z : Plane} (hzA : z ∈ faceRegion D A) (hzB : z ∈ faceRegion R B) :
    faceRegion D A ⊆ faceRegion R B := by
  have hzR : z ∉ drawingTrace R := fun h => hzA.1 (htrace h)
  have hA : faceAt D z hzA.1 = A := hzA.2
  have hB : faceAt R z hzR = B := hzB.2
  simpa only [hA, hB] using faceRegion_subset_of_trace_subset D R htrace z hzA.1

/-- If a subdrawing omits an edge midpoint, both of the edge's chart faces are
contained in one subdrawing face. -/
theorem chart_faces_merge_of_midpoint_off_trace (D : Drawing J) (R : Drawing K)
    (htrace : drawingTrace R ⊆ drawingTrace D) (e : E) (c : EdgeChart D e)
    (hoff : D.curve e ⟨1 / 2, by constructor <;> norm_num⟩ ∉ drawingTrace R) :
    ∃ B : Face R,
      faceRegion D (positiveChartFace D e c) ⊆ faceRegion R B ∧
      faceRegion D (negativeChartFace D e c) ⊆ faceRegion R B := by
  let m : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
  let B : Face R := faceAt R (D.curve e m) hoff
  have hmB : D.curve e m ∈ faceRegion R B := mem_faceAt R _ hoff
  have hBopen : IsOpen (faceRegion R B) := punctured_faceRegion_isOpen R B
  have hmpos : D.curve e m ∈ closure (faceRegion D (positiveChartFace D e c)) :=
    (mem_closure_faceRegion_iff_chart_face D e c _ m
      (by simpa [m] using c.radius_pos)).mpr (Or.inl rfl)
  have hmneg : D.curve e m ∈ closure (faceRegion D (negativeChartFace D e c)) :=
    (mem_closure_faceRegion_iff_chart_face D e c _ m
      (by simpa [m] using c.radius_pos)).mpr (Or.inr rfl)
  obtain ⟨x, hxB, hxpos⟩ := mem_closure_iff.mp hmpos _ hBopen hmB
  obtain ⟨y, hyB, hyneg⟩ := mem_closure_iff.mp hmneg _ hBopen hmB
  exact ⟨B, faceRegion_subset_of_mem_of_trace_subset D R htrace _ _ hxpos hxB,
    faceRegion_subset_of_mem_of_trace_subset D R htrace _ _ hyneg hyB⟩

/-- The midpoint of an edge omitted by an injective edge restriction does not
belong to the restricted drawing trace. -/
theorem midpoint_off_restrictDrawing {V E F : Type} [Fintype V] [Fintype E] [Fintype F]
    {J : CopiedGraph V E} {K : CopiedGraph V F} (D : Drawing J)
    (i : F → E) (hi : Function.Injective i)
    (hl : ∀ f, J.left (i f) = K.left f) (hr : ∀ f, J.right (i f) = K.right f)
    (e : E) (he : e ∉ range i) :
    D.curve e ⟨1 / 2, by constructor <;> norm_num⟩ ∉
      drawingTrace (restrictDrawing D i hi hl hr) := by
  let m : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
  rintro (⟨v, hv⟩ | h)
  · exact D.avoids e m (by norm_num [m]) (by norm_num [m]) v hv.symm
  · obtain ⟨f, t, ht⟩ := mem_iUnion.mp h
    have hef : e ≠ i f := fun h => he ⟨f, h.symm⟩
    have hends := (D.intersects e (i f) hef m t ht.symm).1
    rcases hends with h0 | h1 <;> norm_num [m] at *

/-- Deleting an edge merges its two original chart-side faces into one face of
the restricted drawing. -/
theorem chart_faces_merge_of_omitted_edge {V E F : Type}
    [Fintype V] [Fintype E] [Fintype F]
    {J : CopiedGraph V E} {K : CopiedGraph V F} (D : Drawing J)
    (i : F → E) (hi : Function.Injective i)
    (hl : ∀ f, J.left (i f) = K.left f) (hr : ∀ f, J.right (i f) = K.right f)
    (e : E) (he : e ∉ range i) (c : EdgeChart D e) :
    ∃ B : Face (restrictDrawing D i hi hl hr),
      faceRegion D (positiveChartFace D e c) ⊆ faceRegion (restrictDrawing D i hi hl hr) B ∧
      faceRegion D (negativeChartFace D e c) ⊆ faceRegion (restrictDrawing D i hi hl hr) B :=
  chart_faces_merge_of_midpoint_off_trace D (restrictDrawing D i hi hl hr)
    (drawingTrace_restrictDrawing_subset D i hi hl hr) e c
    (midpoint_off_restrictDrawing D i hi hl hr e he)

/-- An interior edge point is incident exactly to the two faces named by its
midpoint chart, allowing the two faces to coincide. -/
theorem mem_closure_faceRegion_iff_chart_face_of_interior
    (D : Drawing J) (e : E) (c : EdgeChart D e) (A : Face D)
    (t : ArcParameter) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
    D.curve e t ∈ closure (faceRegion D A) ↔
      A = positiveChartFace D e c ∨ A = negativeChartFace D e c := by
  have hcharts : ∀ (s : ArcParameter), 0 < s.val → s.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (r : ℝ), 0 < r ∧
        (∀ z ∈ LatticeProb.PlaneTopology.axisBox s.val r,
          h.symm z ∈ drawingTrace D ↔ z.2 = 0) ∧
        (∀ u : ArcParameter, |u.val - s.val| < r → h (D.curve e u) = (u.val, 0)) := by
    intro s hs0 hs1
    obtain ⟨h, δ, hδ, hs⟩ := D.exists_interior_straightening e s hs0 hs1
    obtain ⟨r, hr, htrace, hparam⟩ :=
      exists_trace_box_of_straightened_subarc D e s hs0 hs1 h δ hδ hs
    exact ⟨h, r, hr, htrace, hparam⟩
  let m : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
  exact (closure_incidence_of_local_charts D e A hcharts t m ht0 ht1
    (by norm_num [m]) (by norm_num [m])).trans
      (mem_closure_faceRegion_iff_chart_face D e c A m (by simpa [m] using c.radius_pos))

/-- The map on faces induced by inclusion of drawing complements. -/
def faceProjection (D : Drawing J) (R : Drawing K)
    (htrace : drawingTrace R ⊆ drawingTrace D) : Face D → Face R :=
  (continuous_subtype_val.subtype_mk
    (fun z : {z : Plane // z ∉ drawingTrace D} => fun h => z.property (htrace h)))
      |>.connectedComponentsMap

/-- The original face region is contained in the region of its projected face. -/
theorem faceRegion_subset_faceProjection (D : Drawing J) (R : Drawing K)
    (htrace : drawingTrace R ⊆ drawingTrace D) (A : Face D) :
    faceRegion D A ⊆ faceRegion R (faceProjection D R htrace A) := by
  obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe A
  exact faceRegion_subset_of_trace_subset D R htrace z z.property

/-- A deleted edge has the same projected face on both chart sides. -/
theorem faceProjection_chart_faces_eq_of_midpoint_off_trace
    (D : Drawing J) (R : Drawing K) (htrace : drawingTrace R ⊆ drawingTrace D)
    (e : E) (c : EdgeChart D e)
    (hoff : D.curve e ⟨1 / 2, by constructor <;> norm_num⟩ ∉ drawingTrace R) :
    faceProjection D R htrace (positiveChartFace D e c) =
      faceProjection D R htrace (negativeChartFace D e c) := by
  obtain ⟨B, hpos, hneg⟩ := chart_faces_merge_of_midpoint_off_trace D R htrace e c hoff
  obtain ⟨x, hx⟩ := (faceRegion_isConnected D (positiveChartFace D e c)).nonempty
  obtain ⟨y, hy⟩ := (faceRegion_isConnected D (negativeChartFace D e c)).nonempty
  have hx' : faceProjection D R htrace (positiveChartFace D e c) = B :=
    face_eq_of_mem R _ _ x (faceRegion_subset_faceProjection D R htrace _ hx) (hpos hx)
  have hy' : faceProjection D R htrace (negativeChartFace D e c) = B :=
    face_eq_of_mem R _ _ y (faceRegion_subset_faceProjection D R htrace _ hy) (hneg hy)
  exact hx'.trans hy'.symm

/-- A dual walk crossing only omitted edges stays in one subdrawing face. -/
theorem faceProjection_eq_of_dual_reaches
    (D : Drawing J) (R : Drawing K) (htrace : drawingTrace R ⊆ drawingTrace D)
    (charts : ∀ e, EdgeChart D e) (S : Finset E)
    (hoff : ∀ e ∈ S, D.curve e ⟨1 / 2, by constructor <;> norm_num⟩ ∉ drawingTrace R)
    {A B : Face D}
    (h : (⟨fun e => negativeChartFace D e (charts e),
      fun e => positiveChartFace D e (charts e)⟩ : CopiedGraph (Face D) E).reaches S A B) :
    faceProjection D R htrace A = faceProjection D R htrace B := by
  induction h with
  | refl => rfl
  | @tail u v _ hedge ih =>
    obtain ⟨e, he, hends⟩ := hedge
    have hside := faceProjection_chart_faces_eq_of_midpoint_off_trace D R htrace e (charts e)
      (hoff e he)
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ih.trans hside.symm
    · exact ih.trans hside

end FiniteAvalanches.Electrical.StatementGeometry
