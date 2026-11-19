import FiniteAvalanches.Support.Plane.GeometricDual

/-!
# Edge and face incidence

Local charts propagate the incident faces along the interior of an edge. The
closedness of each face closure then extends incidence to the endpoints.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- If a closed set contains an edge interior, it contains the entire edge. -/
theorem range_curve_subset_of_interior (D : Drawing J) (e : E) {C : Set Plane}
    (hC : IsClosed C)
    (hinterior : ∀ t : ArcParameter, 0 < t.val → t.val < 1 → D.curve e t ∈ C) :
    range (D.curve e) ⊆ C := by
  let U : Set ArcParameter := {t | 0 < t.val ∧ t.val < 1}
  have hU : Dense U := by
    intro t
    rw [closure_subtype]
    have himage : (Subtype.val : ArcParameter → ℝ) '' U = Ioo (0 : ℝ) 1 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, ⟨hx.1.le, hx.2.le⟩⟩, hx, rfl⟩
    rw [himage, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact t.property
  have hpre : IsClosed ((D.curve e) ⁻¹' C) := hC.preimage (D.continuous e)
  have hsub : U ⊆ (D.curve e) ⁻¹' C := fun t ht => hinterior t ht.1 ht.2
  rintro x ⟨t, rfl⟩
  have ht := closure_mono hsub (hU t)
  rw [hpre.closure_eq] at ht
  exact ht

/-- If an edge has local charts throughout its interior, both midpoint chart faces
are incident to the entire edge. -/
theorem chart_faces_incident_of_local_charts (D : Drawing J) (e : E) (c : EdgeChart D e)
    (hcharts : ∀ (t : ArcParameter), 0 < t.val → t.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (r : ℝ), 0 < r ∧
        (∀ z ∈ LatticeProb.PlaneTopology.axisBox t.val r,
          h.symm z ∈ drawingTrace D ↔ z.2 = 0) ∧
        (∀ s : ArcParameter, |s.val - t.val| < r → h (D.curve e s) = (s.val, 0))) :
    range (D.curve e) ⊆ closure (faceRegion D (positiveChartFace D e c)) ∧
    range (D.curve e) ⊆ closure (faceRegion D (negativeChartFace D e c)) := by
  let m : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
  have hm : ∀ F : Face D, F = positiveChartFace D e c ∨ F = negativeChartFace D e c →
      D.curve e m ∈ closure (faceRegion D F) := by
    intro F hF
    exact (mem_closure_faceRegion_iff_chart_face D e c F m
      (by simpa [m] using c.radius_pos)).mpr hF
  constructor
  · apply range_curve_subset_of_interior D e isClosed_closure
    intro t ht0 ht1
    apply (closure_incidence_of_local_charts D e _ hcharts m t
      (by norm_num [m]) (by norm_num [m]) ht0 ht1).mp
    exact hm _ (Or.inl rfl)
  · apply range_curve_subset_of_interior D e isClosed_closure
    intro t ht0 ht1
    apply (closure_incidence_of_local_charts D e _ hcharts m t
      (by norm_num [m]) (by norm_num [m]) ht0 ht1).mp
    exact hm _ (Or.inr rfl)

/-- A straightenable subarc at each interior point gives incidence of both chart faces. -/
theorem chart_faces_incident_of_straightenable_subarcs
    (D : Drawing J) (e : E) (c : EdgeChart D e)
    (hstraight : ∀ (t : ArcParameter), 0 < t.val → t.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (δ : ℝ), 0 < δ ∧
        ∀ s : ArcParameter, |s.val - t.val| < δ → h (D.curve e s) = (s.val, 0)) :
    range (D.curve e) ⊆ closure (faceRegion D (positiveChartFace D e c)) ∧
    range (D.curve e) ⊆ closure (faceRegion D (negativeChartFace D e c)) := by
  apply chart_faces_incident_of_local_charts D e c
  intro t ht0 ht1
  obtain ⟨h, δ, hδ, hs⟩ := hstraight t ht0 ht1
  obtain ⟨r, hr, htrace, hparam⟩ :=
    exists_trace_box_of_straightened_subarc D e t ht0 ht1 h δ hδ hs
  exact ⟨h, r, hr, htrace, hparam⟩

end FiniteAvalanches.Electrical.StatementGeometry
