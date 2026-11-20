import FiniteAvalanches.Support.Plane.VertexFaceIncidence

/-!
# Connectivity of the face star of a vertex

Closures of face regions cover a punctured vertex neighborhood. Their
intersections outside the vertices join faces across an incident edge, so
connectedness of the punctured neighborhood connects the face star.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- Two distinct faces are adjacent at a vertex when they share an incident edge. -/
def vertexFaceGraph (D : Drawing J) (v : V) : SimpleGraph (Face D) where
  Adj F G := F ≠ G ∧ ∃ e : E, (J.left e = v ∨ J.right e = v) ∧
    F ∈ edgeFaces D e ∧ G ∈ edgeFaces D e
  symm := ⟨by
    rintro F G ⟨hne, e, he, hF, hG⟩
    exact ⟨hne.symm, e, he, hG, hF⟩⟩
  loopless := ⟨by
    intro F h
    exact h.1 rfl⟩

/-- Every vertex has a ball meeting only edges incident to that vertex. -/
theorem exists_ball_meeting_only_incident_edges (D : Drawing J) (v : V) :
    ∃ r : ℝ, 0 < r ∧ ∀ (e : E) (t : ArcParameter),
      D.curve e t ∈ Metric.ball (D.point v) r → J.left e = v ∨ J.right e = v := by
  classical
  let K : Set Plane := ⋃ e : {e : E // ¬ (J.left e = v ∨ J.right e = v)}, range (D.curve e.val)
  have hKclosed : IsClosed K := isClosed_iUnion_of_finite (fun e =>
    (isCompact_range (D.continuous e.val)).isClosed)
  have hxK : D.point v ∉ K := by
    intro hx
    obtain ⟨e, t, ht⟩ := mem_iUnion.mp hx
    have h := (D.curve_vertex_iff e.val t v).mp ht
    exact e.property (h.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
  obtain ⟨r, hr, hrK⟩ := (Metric.isOpen_iff.mp hKclosed.isOpen_compl) _ hxK
  refine ⟨r, hr, ?_⟩
  intro e t ht
  by_contra he
  exact (hrK ht) (mem_iUnion.mpr ⟨⟨e, he⟩, t, rfl⟩)

/-- All faces incident to a vertex lie in one component of its edge-face graph. -/
theorem vertexFaceGraph_reachable (D : Drawing J) [Nonempty E] (v : V)
    (F G : Face D) (hF : incident D v F) (hG : incident D v G) :
    (vertexFaceGraph D v).Reachable F G := by
  classical
  letI : Finite (Face D) := finite_faces_of_drawing D
  obtain ⟨r, hr, hrinc⟩ := exists_ball_meeting_only_incident_edges D v
  let U : Set Plane := Metric.ball (D.point v) r
  let S : Set Plane := U \ range D.point
  have hS : IsPreconnected S :=
    isPreconnected_sdiff_finite Metric.isOpen_ball (convex_ball _ _).isPreconnected
      (finite_range D.point)
  let H := vertexFaceGraph D v
  let label := H.connectedComponentMk
  have hmeet : ∀ {z : Plane}, z ∈ S → ∀ A B : Face D,
      z ∈ closure (faceRegion D A) → z ∈ closure (faceRegion D B) → label A = label B := by
    intro z hz A B hA hB
    by_cases ht : z ∈ drawingTrace D
    · rcases ht with hzv | hze
      · exact (hz.2 hzv).elim
      · obtain ⟨e, t, ht⟩ := mem_iUnion.mp hze
        have ht0 : 0 < t.val := by
          by_contra h
          have heq : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt h) t.property.1)
          apply hz.2
          exact ⟨J.left e, by rw [← ht, heq]; exact (D.start e).symm⟩
        have ht1 : t.val < 1 := by
          by_contra h
          have heq : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt h))
          apply hz.2
          exact ⟨J.right e, by rw [← ht, heq]; exact (D.finish e).symm⟩
        have he : J.left e = v ∨ J.right e = v := hrinc e t (ht ▸ hz.1)
        have ha : A ∈ edgeFaces D e :=
          range_curve_subset_closure_of_interior_incidence D e A t ht0 ht1 (ht ▸ hA)
        have hb : B ∈ edgeFaces D e :=
          range_curve_subset_closure_of_interior_incidence D e B t ht0 ht1 (ht ▸ hB)
        by_cases hab : A = B
        · rw [hab]
        · apply SimpleGraph.ConnectedComponent.sound
          exact (show H.Adj A B from ⟨hab, e, he, ha, hb⟩).reachable
    · have hA' := mem_faceRegion_of_mem_closure D A ht hA
      have hB' := mem_faceRegion_of_mem_closure D B ht hB
      have heq : A = B := hA'.2.symm.trans hB'.2
      rw [heq]
  apply SimpleGraph.ConnectedComponent.exact
  by_contra hFG
  let A : Set Plane := ⋃ F' : {T : Face D // label T = label F}, closure (faceRegion D F'.val)
  let B : Set Plane := ⋃ F' : {T : Face D // label T ≠ label F}, closure (faceRegion D F'.val)
  have hA : IsClosed A := isClosed_iUnion_of_finite (fun _ => isClosed_closure)
  have hB : IsClosed B := isClosed_iUnion_of_finite (fun _ => isClosed_closure)
  have hAB : ∀ z ∈ S, ¬ (z ∈ A ∧ z ∈ B) := by
    intro z hz ⟨ha, hb⟩
    obtain ⟨a, ha⟩ := mem_iUnion.mp ha
    obtain ⟨b, hb⟩ := mem_iUnion.mp hb
    exact b.property ((hmeet hz a.val b.val ha hb).symm.trans a.property)
  have hSA : S ⊆ Bᶜ ∪ Aᶜ := by
    intro z hz
    by_cases h : z ∈ B
    · exact Or.inr (fun ha => hAB z hz ⟨ha, h⟩)
    · exact Or.inl h
  obtain ⟨x, hxU, hxF⟩ := mem_closure_iff.mp hF U Metric.isOpen_ball (Metric.mem_ball_self hr)
  obtain ⟨y, hyU, hyG⟩ := mem_closure_iff.mp hG U Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hxS : x ∈ S := ⟨hxU, fun hv => hxF.1 (Or.inl hv)⟩
  have hyS : y ∈ S := ⟨hyU, fun hv => hyG.1 (Or.inl hv)⟩
  have hxA : x ∈ A := mem_iUnion.mpr ⟨⟨F, rfl⟩, subset_closure hxF⟩
  have hyB : y ∈ B := mem_iUnion.mpr ⟨⟨G, Ne.symm hFG⟩, subset_closure hyG⟩
  obtain ⟨z, hz, hzB, hzA⟩ := hS Bᶜ Aᶜ hB.isOpen_compl hA.isOpen_compl hSA
    ⟨x, hxS, fun hb => hAB x hxS ⟨hxA, hb⟩⟩
    ⟨y, hyS, fun ha => hAB y hyS ⟨ha, hyB⟩⟩
  obtain ⟨T, hT⟩ := exists_face_closure_of_drawing D z
  by_cases hT' : label T = label F
  · exact hzA (mem_iUnion.mpr ⟨⟨T, hT'⟩, hT⟩)
  · exact hzB (mem_iUnion.mpr ⟨⟨T, hT'⟩, hT⟩)

/-- Incident faces are connected by a finite chain of incident edges. -/
theorem vertex_face_star_connected (D : Drawing J) [Nonempty E] (v : V)
    (F G : Face D) (hF : incident D v F) (hG : incident D v G) :
    Relation.ReflTransGen (fun A B : Face D => ∃ e : E,
      (J.left e = v ∨ J.right e = v) ∧ A ∈ edgeFaces D e ∧ B ∈ edgeFaces D e) F G := by
  have h := vertexFaceGraph_reachable D v F G hF hG
  rw [SimpleGraph.reachable_eq_reflTransGen] at h
  clear hF hG
  induction h with
  | refl => exact .refl
  | tail _ hadj ih => exact ih.tail hadj.2

end FiniteAvalanches.Electrical.StatementGeometry
