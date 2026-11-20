import FiniteAvalanches.Support.Plane.LocalVertexIncidence

/-!
# Vertex and edge face incidence

In a sufficiently small vertex neighborhood, every edge encountered is
incident to that vertex. Local frontier incidence then identifies a bounding
edge of each incident face.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- An edge incident to a vertex has interior points in every neighborhood of it. -/
theorem exists_edge_interior_in_neighborhood (D : Drawing J) (v : V) (e : E)
    (he : J.left e = v ∨ J.right e = v) {U : Set Plane} (hU : IsOpen U)
    (hv : D.point v ∈ U) :
    ∃ t : ArcParameter, 0 < t.val ∧ t.val < 1 ∧ D.curve e t ∈ U := by
  let S : Set Plane := {z | ∃ t : ArcParameter, 0 < t.val ∧ t.val < 1 ∧ D.curve e t = z}
  have hrange : range (D.curve e) ⊆ closure S := by
    apply range_curve_subset_of_interior D e isClosed_closure
    intro t ht0 ht1
    exact subset_closure ⟨t, ht0, ht1, rfl⟩
  have hx : D.point v ∈ closure S := by
    apply hrange
    rcases he with he | he
    · exact ⟨⟨0, by constructor <;> norm_num⟩, by simpa only [he] using D.start e⟩
    · exact ⟨⟨1, by constructor <;> norm_num⟩, by simpa only [he] using D.finish e⟩
  obtain ⟨z, hzU, t, ht0, ht1, htz⟩ := mem_closure_iff.mp hx U hU hv
  exact ⟨t, ht0, ht1, htz ▸ hzU⟩

/-- A face incident to a non-isolated vertex is incident to one of its edges. -/
theorem exists_incident_edge_of_incident_face (D : Drawing J) (v : V) (F : Face D)
    (hv : ∃ e : E, J.left e = v ∨ J.right e = v) (hF : incident D v F) :
    ∃ e : E, (J.left e = v ∨ J.right e = v) ∧ F ∈ edgeFaces D e := by
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
  obtain ⟨e, he⟩ := hv
  obtain ⟨t, ht0, ht1, htU⟩ := exists_edge_interior_in_neighborhood D v e he
    Metric.isOpen_ball (Metric.mem_ball_self hr)
  obtain ⟨f, s, hs0, hs1, hsU, hsF⟩ := exists_edge_interior_frontier_in_open D v F
    Metric.isOpen_ball (convex_ball _ _).isPreconnected (Metric.mem_ball_self hr) hF
    ⟨e, t, ht0, ht1, htU⟩
  have hf : J.left f = v ∨ J.right f = v := by
    by_contra hf
    have hfk : D.curve f s ∈ K := mem_iUnion.mpr ⟨⟨f, hf⟩, s, rfl⟩
    exact (hrK hsU) hfk
  exact ⟨f, hf, range_curve_subset_closure_of_interior_incidence D f F s hs0 hs1
    (frontier_subset_closure hsF)⟩

/-- At a non-isolated vertex, incident faces are exactly those incident to an
edge at that vertex. -/
theorem incident_iff_exists_incident_edge (D : Drawing J) (v : V)
    (hv : ∃ e : E, J.left e = v ∨ J.right e = v) (F : Face D) :
    incident D v F ↔ ∃ e : E, (J.left e = v ∨ J.right e = v) ∧ F ∈ edgeFaces D e := by
  constructor
  · exact exists_incident_edge_of_incident_face D v F hv
  · rintro ⟨e, he, hF⟩
    exact incident_of_edgeFaces D e F v he hF

end FiniteAvalanches.Electrical.StatementGeometry
