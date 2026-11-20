import FiniteAvalanches.Support.Plane.FiniteFaceFrontier
import FiniteAvalanches.Support.Plane.LoopEdgeJordan
import FiniteAvalanches.Support.Plane.EdgePathDualityReduction

/-!
# Drawing faces at a Jordan curve

Both complementary regions of a Jordan curve contained in a finite drawing
have incident drawing faces at each point of the curve.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST ComplementFaces Set
open scoped Classical

/-- A Jordan curve contained in the drawing trace has distinct incident faces
on its two sides at every point. -/
theorem exists_distinct_faces_at_jordan {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    {G : CopiedGraph V E} (D : Drawing G) (charts : ∀ e, EdgeChart D e)
    (C : Set Schoenflies.Plane) (hC : Schoenflies.IsSeparating C)
    (hCtrace : C ⊆ euclideanPlaneHomeomorph '' drawingTrace D) {z : Plane}
    (hz : euclideanPlaneHomeomorph z ∈ C) :
    ∃ F G : Face D, F ≠ G ∧ z ∈ closure (faceRegion D F) ∧
      z ∈ closure (faceRegion D G) ∧
      (euclideanPlaneHomeomorph '' faceRegion D F ∩ Schoenflies.inside C).Nonempty ∧
      (euclideanPlaneHomeomorph '' faceRegion D G ∩ Schoenflies.outside C).Nonempty := by
  let H := euclideanPlaneHomeomorph
  let T := H '' drawingTrace D
  let U : Face D → Set Schoenflies.Plane := fun F => H '' faceRegion D F
  letI : Finite (Face D) := (finite_faces_and_card_le D charts).1
  have hdense0 : Dense (drawingTrace D)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp (drawingTrace_interior_eq_empty D)
  have hdense : Dense Tᶜ := by
    rw [← image_compl_eq H.bijective]
    exact H.surjective.denseRange.dense_image H.continuous hdense0
  have hsub : ∀ F, U F ⊆ Tᶜ := by
    intro F w hw hT
    obtain ⟨x, hx, rfl⟩ := hw
    obtain ⟨y, hy, heq⟩ := hT
    exact hx.1 (H.injective heq ▸ hy)
  have hcover : Tᶜ ⊆ ⋃ F, U F := by
    intro w hw
    let x := H.symm w
    have hx : x ∉ drawingTrace D := by
      intro ht
      exact hw ⟨x, ht, H.apply_symm_apply w⟩
    refine mem_iUnion.mpr ⟨faceAt D x hx, ?_⟩
    exact ⟨x, mem_faceAt D x hx, H.apply_symm_apply w⟩
  have hconn : ∀ F, IsPreconnected (U F) := by
    intro F
    exact (faceRegion_isConnected D F).isPreconnected.image H H.continuous.continuousOn
  obtain ⟨F, K, hne, hF, hK, hin, hout⟩ :=
    exists_distinct_cover_members_at_jordan T C U hdense hcover hsub hconn hCtrace hC hz
  have hF' : z ∈ closure (faceRegion D F) := by
    rw [← H.image_closure] at hF
    obtain ⟨x, hx, he⟩ := hF
    exact H.injective he ▸ hx
  have hK' : z ∈ closure (faceRegion D K) := by
    rw [← H.image_closure] at hK
    obtain ⟨x, hx, he⟩ := hK
    exact H.injective he ▸ hx
  exact ⟨F, K, hne, hF', hK', hin, hout⟩

/-- A Jordan curve retained by a subdrawing and passing through an edge's
midpoint separates the projected chart faces of that edge. -/
theorem projected_chart_faces_ne_of_jordan {V E W F : Type}
    [Fintype V] [Fintype E] [Nonempty E] [Fintype W] [Fintype F]
    {G : CopiedGraph V E} {K : CopiedGraph W F} (D : Drawing G) (R : Drawing K)
    (htrace : drawingTrace R ⊆ drawingTrace D) (charts : ∀ e, EdgeChart D e)
    (e : E) (C : Set Schoenflies.Plane) (hC : Schoenflies.IsSeparating C)
    (hCR : C ⊆ euclideanPlaneHomeomorph '' drawingTrace R)
    (hmC : euclideanPlaneHomeomorph (D.curve e ⟨1 / 2, by constructor <;> norm_num⟩) ∈ C) :
    faceProjection D R htrace (negativeChartFace D e (charts e)) ≠
      faceProjection D R htrace (positiveChartFace D e (charts e)) := by
  let H := euclideanPlaneHomeomorph
  let m : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
  have hCD : C ⊆ H '' drawingTrace D := hCR.trans (image_mono htrace)
  obtain ⟨A, B, hAB, hAm, hBm, hin, hout⟩ :=
    exists_distinct_faces_at_jordan D charts C hC hCD hmC
  have hA := (mem_closure_faceRegion_iff_chart_face D e (charts e) A m
    (by simpa [m] using (charts e).radius_pos)).mp hAm
  have hB := (mem_closure_faceRegion_iff_chart_face D e (charts e) B m
    (by simpa [m] using (charts e).radius_pos)).mp hBm
  have hproj : faceProjection D R htrace A ≠ faceProjection D R htrace B := by
    intro heq
    obtain ⟨x, ⟨x', hx', rfl⟩, hxi⟩ := hin
    obtain ⟨y, ⟨y', hy', rfl⟩, hyo⟩ := hout
    let S := H '' faceRegion R (faceProjection D R htrace A)
    have hxS : H x' ∈ S := ⟨x', faceRegion_subset_faceProjection D R htrace A hx', rfl⟩
    have hyS : H y' ∈ S := ⟨y', heq ▸ faceRegion_subset_faceProjection D R htrace B hy', rfl⟩
    have hS : IsPreconnected S :=
      (faceRegion_isConnected R _).isPreconnected.image H H.continuous.continuousOn
    have hSC : S ⊆ Cᶜ := by
      rintro _ ⟨w, hw, rfl⟩ hwC
      obtain ⟨u, hu, heu⟩ := hCR hwC
      exact hw.1 (H.injective heu ▸ hu)
    have hycomp : H y' ∈ connectedComponentIn Cᶜ (H x') :=
      hS.subset_connectedComponentIn hxS hSC hyS
    exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
      (Schoenflies.connectedComponentIn_subset_inside hxi hycomp) hyo
  intro heq
  apply hproj
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · rw [hA, hB]
  · rw [hA, hB]; exact heq.symm
  · rw [hA, hB]; exact heq
  · rw [hA, hB]

/-- The chart sides of a loop remain distinct in every subdrawing that retains
the whole loop. -/
theorem loop_projected_chart_faces_ne {V E W F : Type}
    [Fintype V] [Fintype E] [Nonempty E] [Fintype W] [Fintype F]
    {G : CopiedGraph V E} {K : CopiedGraph W F} (D : Drawing G) (R : Drawing K)
    (htrace : drawingTrace R ⊆ drawingTrace D) (charts : ∀ e, EdgeChart D e)
    (e : E) (hloop : G.left e = G.right e)
    (hretain : ∀ t, D.curve e t ∈ drawingTrace R) :
    faceProjection D R htrace (negativeChartFace D e (charts e)) ≠
      faceProjection D R htrace (positiveChartFace D e (charts e)) := by
  apply projected_chart_faces_ne_of_jordan D R htrace charts e
    (euclideanPlaneHomeomorph '' range (D.curve e)) (D.loop_isSeparating e hloop)
  · rintro _ ⟨x, ⟨t, rfl⟩, rfl⟩
    exact ⟨D.curve e t, hretain t, rfl⟩
  · exact ⟨_, ⟨⟨1 / 2, by constructor <;> norm_num⟩, rfl⟩, rfl⟩

/-- Edge-path duality holds for a loop edge. -/
theorem edge_path_duality_of_loop {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    {G : CopiedGraph V E} (D : Drawing G) (charts : ∀ e, EdgeChart D e)
    (A : Finset E) (e : E) (hloop : G.left e = G.right e) :
    (G.reaches A (G.left e) (G.right e) ↔
      ¬ (⟨fun e => negativeChartFace D e (charts e),
        fun e => positiveChartFace D e (charts e)⟩ : CopiedGraph (Face D) E).reaches
        (Aᶜ.erase e) (negativeChartFace D e (charts e)) (positiveChartFace D e (charts e))) := by
  have hprimal : G.reaches A (G.left e) (G.right e) := hloop ▸ Relation.ReflTransGen.refl
  refine iff_of_true hprimal ?_
  intro hdual
  apply loop_projected_chart_faces_ne D (edgeSetDrawing D (insert e A))
    (edgeSetDrawing_trace_subset D (insert e A)) charts e hloop ?_
      ((edge_dual_reaches_iff_projected_faces_eq D charts A e).mp hdual)
  intro t
  exact Or.inr (mem_iUnion.mpr ⟨⟨e, Finset.mem_insert_self e A⟩, t, rfl⟩)

end FiniteAvalanches.Electrical.StatementGeometry
