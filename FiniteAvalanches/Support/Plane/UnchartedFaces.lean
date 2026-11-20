import FiniteAvalanches.Support.Plane.HalfOpenLocalStraightening
import FiniteAvalanches.Support.Plane.EdgeFaceIncidence

/-!
# Faces of uncharted finite plane drawings

Local straightening at edge interiors bounds the faces incident to each edge
without requiring an oriented chart or an isotopy.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- The closure of a face meeting an edge interior contains the entire edge. -/
theorem range_curve_subset_closure_of_interior_incidence (D : Drawing J) (e : E)
    (F : Face D) (t : ArcParameter) (ht0 : 0 < t.val) (ht1 : t.val < 1)
    (hF : D.curve e t ∈ closure (faceRegion D F)) :
    range (D.curve e) ⊆ closure (faceRegion D F) := by
  have hcharts : ∀ (u : ArcParameter), 0 < u.val → u.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (r : ℝ), 0 < r ∧
        (∀ z ∈ LatticeProb.PlaneTopology.axisBox u.val r,
          h.symm z ∈ drawingTrace D ↔ z.2 = 0) ∧
        (∀ s : ArcParameter, |s.val - u.val| < r → h (D.curve e s) = (s.val, 0)) := by
    intro u hu0 hu1
    obtain ⟨h, δ, hδ, hs⟩ := D.exists_interior_straightening e u hu0 hu1
    obtain ⟨r, hr, htrace, hparam⟩ :=
      exists_trace_box_of_straightened_subarc D e u hu0 hu1 h δ hδ hs
    exact ⟨h, r, hr, htrace, hparam⟩
  apply range_curve_subset_of_interior D e isClosed_closure
  intro u hu0 hu1
  exact (closure_incidence_of_local_charts D e F hcharts t u ht0 ht1 hu0 hu1).mp hF

/-- At most two faces are incident to the interior of a copied edge. -/
theorem exists_two_faces_of_edge_interior (D : Drawing J) (e : E) :
    ∃ A B : Face D, ∀ (F : Face D) (t : ArcParameter),
      0 < t.val → t.val < 1 → D.curve e t ∈ closure (faceRegion D F) →
      F = A ∨ F = B := by
  let m : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
  obtain ⟨h, δ, hδ, hs⟩ := D.exists_interior_straightening e m
    (by norm_num [m]) (by norm_num [m])
  obtain ⟨r, hr, htrace, hparam⟩ := exists_trace_box_of_straightened_subarc D e m
    (by norm_num [m]) (by norm_num [m]) h δ hδ hs
  have hp : h.symm (m.val, r / 2) ∉ drawingTrace D := by
    intro hc
    have hz := (htrace (m.val, r / 2) ⟨⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩⟩).mp hc
    dsimp only at hz
    linarith
  have hn : h.symm (m.val, -(r / 2)) ∉ drawingTrace D := by
    intro hc
    have hz := (htrace (m.val, -(r / 2)) ⟨⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩⟩).mp hc
    dsimp only at hz
    linarith
  let a : {z : Plane // z ∉ drawingTrace D} := ⟨h.symm (m.val, r / 2), hp⟩
  let b : {z : Plane // z ∉ drawingTrace D} := ⟨h.symm (m.val, -(r / 2)), hn⟩
  refine ⟨ConnectedComponents.mk a, ConnectedComponents.mk b, ?_⟩
  intro F t ht0 ht1 hF
  have hm : D.curve e m ∈ closure (faceRegion D F) :=
    range_curve_subset_closure_of_interior_incidence D e F t ht0 ht1 hF ⟨m, rfl⟩
  have hstraight : h.symm (m.val, 0) = D.curve e m := by
    rw [← hparam m (by simpa using hr), Homeomorph.symm_apply_apply]
  obtain ⟨c, rfl⟩ := ConnectedComponents.surjective_coe F
  rw [← hstraight, faceRegion_mk] at hm
  have hside := (LatticeProb.PlaneTopology.axis_mem_closure_component_iff
    (drawingTrace D) h m.val r hr htrace c.val m.val ⟨by linarith, by linarith⟩).mp hm
  have heq := faceRegion_injective D
  rcases hside with hpos | hneg
  · left
    apply heq
    simpa only [faceRegion_mk] using hpos
  · right
    apply heq
    simpa only [faceRegion_mk] using hneg

/-- Every face of a finite drawing with an edge belongs to a finite set of
at most two faces for each edge, without requiring oriented edge charts. -/
theorem finite_faces_of_drawing (D : Drawing J) [Nonempty E] : Finite (Face D) := by
  classical
  choose A B hAB using fun e : E => exists_two_faces_of_edge_interior D e
  apply Finite.of_finite_univ
  apply ((finite_range A).union (finite_range B)).subset
  intro F _
  obtain ⟨e, t, ht0, ht1, ht⟩ := exists_edge_interior_mem_frontier D F
  rcases hAB e F t ht0 ht1 (frontier_subset_closure ht) with h | h
  · exact Or.inl ⟨e, h.symm⟩
  · exact Or.inr ⟨e, h.symm⟩

/-- Every point belongs to the closure of a face of a finite drawing with an edge. -/
theorem exists_face_closure_of_drawing (D : Drawing J) [Nonempty E] (z : Plane) :
    ∃ F : Face D, z ∈ closure (faceRegion D F) := by
  letI : Finite (Face D) := finite_faces_of_drawing D
  have hfaces : (⋃ F : Face D, faceRegion D F) = (drawingTrace D)ᶜ := by
    ext w
    constructor
    · intro hw
      obtain ⟨F, hF⟩ := mem_iUnion.mp hw
      exact hF.1
    · intro hw
      exact mem_iUnion.mpr ⟨ConnectedComponents.mk ⟨w, hw⟩, hw, rfl⟩
  have hdense : Dense (drawingTrace D)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp (drawingTrace_interior_eq_empty D)
  have hz : z ∈ closure (⋃ F : Face D, faceRegion D F) := by
    rw [hfaces]
    exact hdense z
  rw [closure_iUnion_of_finite] at hz
  exact mem_iUnion.mp hz

/-- Every vertex has a finite nonempty set of incident faces. -/
theorem vertex_incident_faces_finite_nonempty (D : Drawing J) [Nonempty E] (v : V) :
    {F : Face D | incident D v F}.Nonempty ∧ {F : Face D | incident D v F}.Finite := by
  letI : Finite (Face D) := finite_faces_of_drawing D
  obtain ⟨F, hF⟩ := exists_face_closure_of_drawing D (D.point v)
  exact ⟨⟨F, hF⟩, Set.toFinite _⟩

/-- Any face incident to an edge is incident to each of its endpoints. -/
theorem incident_of_edgeFaces (D : Drawing J) (e : E) (F : Face D) (v : V)
    (hv : J.left e = v ∨ J.right e = v) (hF : F ∈ edgeFaces D e) : incident D v F := by
  change D.point v ∈ closure (faceRegion D F)
  rcases hv with hv | hv
  · rw [← hv, ← D.start e]
    exact hF ⟨0, rfl⟩
  · rw [← hv, ← D.finish e]
    exact hF ⟨1, rfl⟩

end FiniteAvalanches.Electrical.StatementGeometry
