import FiniteAvalanches.Support.Plane.ArcComponentPreservation
import FiniteAvalanches.Support.Plane.EdgeComponentIncidence
import FiniteAvalanches.Support.Plane.EdgePathDualityReduction

/-!
# Faces of an edge joining distinct components

An edge joining different components does not separate the two sides of its
interior in the drawing consisting of that edge and the selected subgraph.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST ComplementFaces DrawingContraction Set
open scoped Classical

/-- The trace of the edge-restricted drawing agrees with the selected trace. -/
theorem drawingTrace_edgeSetDrawing {V E : Type} [Fintype V] [Fintype E]
    {G : CopiedGraph V E} (D : Drawing G) (A : Finset E) :
    drawingTrace (edgeSetDrawing D A) = D.trace Set.univ A := by
  ext z
  constructor
  · rintro (⟨v, hv⟩ | h)
    · exact Or.inl ⟨v, mem_univ v, hv⟩
    · obtain ⟨f, t, ht⟩ := mem_iUnion.mp h
      exact Or.inr ⟨f.val, f.property, t, ht⟩
  · rintro (⟨v, _, hv⟩ | ⟨f, hf, t, ht⟩)
    · exact Or.inl ⟨v, hv⟩
    · exact Or.inr (mem_iUnion.mpr ⟨⟨f, hf⟩, t, ht⟩)

/-- The sides of an added edge belong to one face when its endpoints are not
connected by the selected edges. -/
theorem chart_faces_eq_of_not_reaches {V E : Type} [Fintype V] [Fintype E]
    {G : CopiedGraph V E} (D : Drawing G) (A : Finset E) (e : E)
    (c : EdgeChart D e) (he : e ∉ A)
    (hnot : ¬ G.reaches A (G.left e) (G.right e)) :
    let R := edgeSetDrawing D (insert e A)
    let htrace := edgeSetDrawing_trace_subset D (insert e A)
    faceProjection D R htrace (negativeChartFace D e c) =
      faceProjection D R htrace (positiveChartFace D e c) := by
  let C := reachableVertices G A (G.left e)
  let S := reachableEdges G A (G.left e)
  let K := D.trace C S
  let L := D.trace Cᶜ (A \ S)
  let p : Path (D.point (G.left e)) (D.point (G.right e)) :=
    ⟨⟨D.curve e, D.continuous e⟩, D.start e, D.finish e⟩
  have hne : G.left e ≠ G.right e := by
    intro h
    apply hnot
    rw [← h]
    exact Relation.ReflTransGen.refl
  have hp : Function.Injective p := D.nonloop_curve_injective e hne
  have hdisj : Disjoint K L := D.disjoint_reachable_traces A (G.left e)
  have hinter := D.edge_inter_reachable_traces A e he hnot
  have hPK : IsPreconnected (range p ∩ K) :=
    (Set.subsingleton_singleton.anti hinter.1).isPreconnected
  have hPKL : IsPreconnected ((range p ∪ K) ∩ L) := by
    have hsub : (range p ∪ K) ∩ L ⊆ {D.point (G.right e)} := by
      rintro z ⟨hz | hz, hl⟩
      · exact hinter.2 ⟨hz, hl⟩
      · exact (Set.disjoint_left.mp hdisj hz hl).elim
    exact (Set.subsingleton_singleton.anti hsub).isPreconnected
  have htraceA : drawingTrace (edgeSetDrawing D A) = K ∪ L := by
    rw [drawingTrace_edgeSetDrawing, D.trace_reachable_partition]
  have htraceAe : drawingTrace (edgeSetDrawing D (insert e A)) = (range p ∪ K) ∪ L := by
    rw [drawingTrace_edgeSetDrawing]
    rw [union_assoc, ← htraceA, drawingTrace_edgeSetDrawing]
    ext z
    simp only [Drawing.trace, mem_union, mem_image, mem_univ, true_and, mem_setOf_eq,
      Finset.mem_insert, mem_range]
    constructor
    · rintro (h | ⟨f, hf | hf, t, ht⟩)
      · exact Or.inr (Or.inl h)
      · subst f
        exact Or.inl ⟨t, ht⟩
      · exact Or.inr (Or.inr ⟨f, hf, t, ht⟩)
    · rintro (⟨t, ht⟩ | h | ⟨f, hf, t, ht⟩)
      · exact Or.inr ⟨e, Or.inl rfl, t, ht⟩
      · exact Or.inl h
      · exact Or.inr ⟨f, Or.inr hf, t, ht⟩
  obtain ⟨x, hx⟩ := (faceRegion_isConnected D (positiveChartFace D e c)).nonempty
  obtain ⟨y, hy⟩ := (faceRegion_isConnected D (negativeChartFace D e c)).nonempty
  have hoff : D.curve e ⟨1 / 2, by constructor <;> norm_num⟩ ∉
      drawingTrace (edgeSetDrawing D A) := by
    apply midpoint_off_restrictDrawing D Subtype.val Subtype.val_injective
      (fun _ => rfl) (fun _ => rfl) e
    simpa only [Subtype.range_val_subtype, mem_setOf_eq] using he
  obtain ⟨B, hpos, hneg⟩ := chart_faces_merge_of_midpoint_off_trace D
    (edgeSetDrawing D A) (edgeSetDrawing_trace_subset D A) e c hoff
  have hxB := hpos hx
  have hyB := hneg hy
  have hxy : y ∈ connectedComponentIn (K ∪ L)ᶜ x := by
    rw [← htraceA]
    exact (faceRegion_isConnected (edgeSetDrawing D A) B).isPreconnected.subset_connectedComponentIn
      hxB (fun _ hz => hz.1) hyB
  have hxall : x ∉ (range p ∪ K) ∪ L := by
    rw [← htraceAe]
    exact fun h => hx.1 (edgeSetDrawing_trace_subset D (insert e A) h)
  have hyall : y ∉ (range p ∪ K) ∪ L := by
    rw [← htraceAe]
    exact fun h => hy.1 (edgeSetDrawing_trace_subset D (insert e A) h)
  have hxy' := connectedComponentIn_compl_union_path_two
    (D.trace_isCompact C S) (D.trace_isCompact Cᶜ (A \ S)) p hp hPK hPKL hxall hyall hxy
  have hxoff : x ∉ drawingTrace (edgeSetDrawing D (insert e A)) := by
    rw [htraceAe]
    exact hxall
  have hxy'' : y ∈ faceRegion (edgeSetDrawing D (insert e A))
      (faceAt (edgeSetDrawing D (insert e A)) x hxoff) := by
    rw [faceAt, faceRegion_mk]
    change y ∈ connectedComponentIn (drawingTrace (edgeSetDrawing D (insert e A)))ᶜ x
    rw [htraceAe]
    exact hxy'
  have hx' := faceRegion_subset_faceProjection D (edgeSetDrawing D (insert e A))
    (edgeSetDrawing_trace_subset D (insert e A)) _ hx
  have hy' := faceRegion_subset_faceProjection D (edgeSetDrawing D (insert e A))
    (edgeSetDrawing_trace_subset D (insert e A)) _ hy
  have hx'' : x ∈ faceRegion (edgeSetDrawing D (insert e A))
      (faceAt (edgeSetDrawing D (insert e A)) x hxoff) := mem_faceAt _ _ _
  exact (face_eq_of_mem _ _ _ y hy' hxy'').trans
    (face_eq_of_mem _ _ _ x hx' hx'').symm

end FiniteAvalanches.Electrical.StatementGeometry
