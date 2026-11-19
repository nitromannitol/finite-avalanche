import FiniteAvalanches.Support.Plane.DualVertexInjective

/-!
# Geometric dual from separated crossings

A compatible family of separated crossing paths gives the full geometric dual
with a bijective original-vertex-to-dual-face correspondence.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Set Source BSST

/-- Separated crossing paths determine the geometric dual and its face equivalence. -/
theorem exists_geometric_dual_of_crossing_paths {V E : Type}
    [Fintype V] [Fintype E] [Nonempty E] {J : CopiedGraph V E}
    (D : Drawing J) [Fintype (Face D)] (charts : ∀ e, EdgeChart D e)
    (hconn : (supportGraph J.left J.right).Preconnected)
    (point : Face D → ℝ × ℝ) (hpoint : Function.Injective point)
    (hpointface : ∀ F, point F ∈ faceRegion D F)
    (crossing : E → ℝ × ℝ)
    (p : ∀ e, Path (point (negativeChartFace D e (charts e))) (crossing e))
    (q : ∀ e, Path (point (positiveChartFace D e (charts e))) (crossing e))
    (hp : ∀ e, Function.Injective (p e)) (hq : ∀ e, Function.Injective (q e))
    (hloop : ∀ e, point (negativeChartFace D e (charts e)) =
        point (positiveChartFace D e (charts e)) →
      range (p e) ∩ range (q e) = {point (negativeChartFace D e (charts e)), crossing e})
    (hedge : ∀ e, point (negativeChartFace D e (charts e)) ≠
        point (positiveChartFace D e (charts e)) →
      range (p e) ∩ range (q e) = {crossing e})
    (hpv : ∀ e t, t ≠ 0 → p e t ∉ range point)
    (hqv : ∀ e t, t ≠ 0 → q e t ∉ range point)
    (hinter : ∀ e f, e ≠ f →
      range ((p e).trans (q e).symm) ∩ range ((p f).trans (q f).symm) ⊆ range point)
    (hpface : ∀ e t, t ≠ 1 → p e t ∈ faceRegion D (negativeChartFace D e (charts e)))
    (hqface : ∀ e t, t ≠ 1 → q e t ∈ faceRegion D (positiveChartFace D e (charts e)))
    (hcross : ∀ e f s, D.curve f s = crossing e ↔ f = e ∧ s.val = 1 / 2)
    (r : E → ℝ) (hr : ∀ e, 0 < r e)
    (hpchart : ∀ e s, 1 - 2 * r e < s.val →
      (charts e).chart.map (p e s) = (1 / 2, (s.val - 1) / 2))
    (hqchart : ∀ e s, 1 - 2 * r e < s.val →
      (charts e).chart.map (q e s) = (1 / 2, (1 - s.val) / 2)) :
    let J' : CopiedGraph (Face D) E :=
      ⟨fun e => negativeChartFace D e (charts e), fun e => positiveChartFace D e (charts e)⟩
    ∃ D' : Drawing J', ∃ dualCharts : ∀ e, EdgeChart D' e,
      ∃ vertexFace : V ≃ Face D',
      (∀ F, D'.point F ∈ faceRegion D F) ∧
      (∀ v, D.point v ∈ faceRegion D' (vertexFace v)) ∧
      (∀ e f s t, D.curve e s = D'.curve f t ↔
        e = f ∧ s.val = 1 / 2 ∧ t.val = 1 / 2) ∧
      (∀ e t, (t.val < 1 / 2 → D'.curve e t ∈ faceRegion D (J'.left e)) ∧
        (1 / 2 < t.val → D'.curve e t ∈ faceRegion D (J'.right e))) ∧
      (∀ e, ∃ radius : ℝ, 0 < radius ∧ radius < (charts e).radius ∧
        ∀ t, |t.val - 1 / 2| < radius →
          (charts e).chart.map (D'.curve e t) = (1 / 2, t.val - 1 / 2)) ∧
      (∀ e, positiveChartFace D' e (dualCharts e) = vertexFace (J.left e) ∧
        negativeChartFace D' e (dualCharts e) = vertexFace (J.right e)) := by
  obtain ⟨D', dualCharts, vertexFace, hpoints, hvertices, hcrossings, hsides, hchart, hinc⟩ :=
    exists_dual_drawing_of_crossing_paths D charts hconn point hpoint hpointface crossing p q
      hp hq hloop hedge hpv hqv hinter hpface hqface hcross r hr hpchart hqchart
  obtain ⟨equiv, hequiv, hinc'⟩ :=
    exists_vertexFace_equiv_of_dual_drawing J D charts hconn D' dualCharts vertexFace hinc
  refine ⟨D', dualCharts, equiv, hpoints, ?_, hcrossings, hsides, hchart, hinc'⟩
  intro v
  rw [hequiv]
  exact hvertices v

end FiniteAvalanches.Electrical.StatementGeometry
