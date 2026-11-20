import FiniteAvalanches.Support.Plane.ChartConstruction
import FiniteAvalanches.Support.Plane.CrossingDrawing

/-!
Ported from Lattice-Probability `LatticeProb/Topology/PlaneGraph/DualAssembly.lean` at commit `ba2b67f3`.

# Dual drawings from crossing paths

Separated paths to edge crossings give a drawing with oriented charts and
face incidence at the original vertices.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

open Set Source BSST

/-- If dual edges are locally straightenable, the oriented incidences cover
every dual face. -/
theorem vertexFace_surjective_of_straightenable_subarcs {V W E : Type}
    [Fintype V] [Fintype W] [Fintype E] [Nonempty E]
    {J : CopiedGraph V E} {J' : CopiedGraph W E} (D' : Drawing J')
    (charts : ∀ e, EdgeChart D' e) (vertexFace : V → Face D')
    (hinc : ∀ e, positiveChartFace D' e (charts e) = vertexFace (J.left e) ∧
      negativeChartFace D' e (charts e) = vertexFace (J.right e))
    (hstraight : ∀ (e : E) (t : ArcParameter), 0 < t.val → t.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (δ : ℝ), 0 < δ ∧
        ∀ s : ArcParameter, |s.val - t.val| < δ → h (D'.curve e s) = (s.val, 0)) :
    Function.Surjective vertexFace := by
  have hcharts : ∀ (e : E) (t : ArcParameter), 0 < t.val → t.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (r : ℝ), 0 < r ∧
        (∀ z ∈ PlaneTopology.axisBox t.val r,
          h.symm z ∈ drawingTrace D' ↔ z.2 = 0) ∧
        (∀ s : ArcParameter, |s.val - t.val| < r → h (D'.curve e s) = (s.val, 0)) := by
    intro e t ht0 ht1
    obtain ⟨h, δ, hδ, hs⟩ := hstraight e t ht0 ht1
    obtain ⟨r, hr, htrace, hparam⟩ :=
      exists_trace_box_of_straightened_subarc D' e t ht0 ht1 h δ hδ hs
    exact ⟨h, r, hr, htrace, hparam⟩
  intro F
  obtain ⟨e, t, ht0, ht1, ht⟩ := exists_edge_interior_mem_frontier D' F
  let m : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
  have hm : D'.curve e m ∈ closure (faceRegion D' F) :=
    (closure_incidence_of_local_charts D' e F (hcharts e) t m ht0 ht1
      (by norm_num [m]) (by norm_num [m])).mp (frontier_subset_closure ht)
  rcases (mem_closure_faceRegion_iff_chart_face D' e (charts e) F m
    (by simpa [m] using (charts e).radius_pos)).mp hm with hpos | hneg
  · exact ⟨J.left e, (hinc e).1.symm.trans hpos.symm⟩
  · exact ⟨J.right e, (hinc e).2.symm.trans hneg.symm⟩

/-- Injective vertex-face incidence is a bijection when dual edges are locally
straightenable. -/
theorem exists_vertexFace_equiv_of_injective_of_straightenable_subarcs
    {V W E : Type} [Fintype V] [Fintype W] [Fintype E] [Nonempty E]
    {J : CopiedGraph V E} {J' : CopiedGraph W E} (D' : Drawing J')
    (charts : ∀ e, EdgeChart D' e) (vertexFace : V → Face D')
    (hinc : ∀ e, positiveChartFace D' e (charts e) = vertexFace (J.left e) ∧
      negativeChartFace D' e (charts e) = vertexFace (J.right e))
    (hinj : Function.Injective vertexFace)
    (hstraight : ∀ (e : E) (t : ArcParameter), 0 < t.val → t.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (δ : ℝ), 0 < δ ∧
        ∀ s : ArcParameter, |s.val - t.val| < δ → h (D'.curve e s) = (s.val, 0)) :
    ∃ equiv : V ≃ Face D', (∀ v, equiv v = vertexFace v) ∧
      ∀ e, positiveChartFace D' e (charts e) = equiv (J.left e) ∧
        negativeChartFace D' e (charts e) = equiv (J.right e) := by
  have hsurj := vertexFace_surjective_of_straightenable_subarcs D' charts vertexFace hinc hstraight
  let equiv := Equiv.ofBijective vertexFace ⟨hinj, hsurj⟩
  exact ⟨equiv, fun _ => rfl, hinc⟩

/-- If edges are locally straightenable, their chart sides represent every face. -/
theorem chartFace_surjective_of_straightenable_subarcs {V E : Type}
    [Fintype V] [Fintype E] [Nonempty E] {J : CopiedGraph V E} (D : Drawing J)
    (charts : ∀ e, EdgeChart D e)
    (hstraight : ∀ (e : E) (t : ArcParameter), 0 < t.val → t.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (δ : ℝ), 0 < δ ∧
        ∀ s : ArcParameter, |s.val - t.val| < δ → h (D.curve e s) = (s.val, 0)) :
    Function.Surjective (Sum.elim (fun e => positiveChartFace D e (charts e))
      (fun e => negativeChartFace D e (charts e))) := by
  let J' : CopiedGraph (E ⊕ E) E := ⟨Sum.inl, Sum.inr⟩
  apply vertexFace_surjective_of_straightenable_subarcs (J := J') D charts _ _ hstraight
  intro e
  exact ⟨rfl, rfl⟩

/-- Locally straightenable edges bound the number of faces by twice their number. -/
theorem finite_faces_and_card_le_of_straightenable_subarcs {V E : Type}
    [Fintype V] [Fintype E] [Nonempty E] {J : CopiedGraph V E} (D : Drawing J)
    (charts : ∀ e, EdgeChart D e)
    (hstraight : ∀ (e : E) (t : ArcParameter), 0 < t.val → t.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (δ : ℝ), 0 < δ ∧
        ∀ s : ArcParameter, |s.val - t.val| < δ → h (D.curve e s) = (s.val, 0)) :
    Finite (Face D) ∧ Nat.card (Face D) ≤ 2 * Fintype.card E := by
  let f : E ⊕ E → Face D := Sum.elim (fun e => positiveChartFace D e (charts e))
    (fun e => negativeChartFace D e (charts e))
  have hf : Function.Surjective f := chartFace_surjective_of_straightenable_subarcs D charts hstraight
  refine ⟨Finite.of_surjective f hf, ?_⟩
  have hcard := Nat.card_le_card_of_surjective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sum, two_mul] using hcard

/-- Separated crossing paths determine a dual drawing and its vertex-face map. -/
theorem exists_dual_drawing_of_crossing_paths {V E : Type}
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
      ∃ vertexFace : V → Face D',
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
  let J' : CopiedGraph (Face D) E :=
    ⟨fun e => negativeChartFace D e (charts e), fun e => positiveChartFace D e (charts e)⟩
  have hdisj : ∀ F, Disjoint (faceRegion D F) (drawingTrace D) := by
    intro F
    exact Set.disjoint_left.mpr (fun _ hz ht => hz.1 ht)
  obtain ⟨D', hpoint', hsides, hcross', hchart⟩ :=
    exists_drawing_with_crossings D J' point hpoint crossing p q hp hq hloop hedge hpv hqv
      hinter (fun e => faceRegion D (J'.left e)) (fun e => faceRegion D (J'.right e))
      hpface hqface (fun e => hdisj _) (fun e => hdisj _) hcross
      (fun e => (charts e).chart.map) r hpchart hqchart
  have hpointoff : ∀ F, D'.point F ∉ drawingTrace D := by
    intro F
    rw [hpoint']
    exact (hpointface F).1
  obtain ⟨vertexFace, dualCharts, hv, hinc⟩ :=
    exists_vertex_faces_with_oriented_charts D D' charts hconn r hr hchart hpointoff
      (fun e f s t h => ((hcross' f e s t).mp h).2.1)
  refine ⟨D', dualCharts, vertexFace, ?_, hv, ?_, hsides, ?_, hinc⟩
  · intro F
    rw [hpoint']
    exact hpointface F
  · intro e f s t
    exact hcross' f e s t
  · intro e
    refine ⟨min (r e) ((charts e).radius / 2),
      lt_min (hr e) (div_pos (charts e).radius_pos (by norm_num)), ?_, ?_⟩
    · have := (charts e).radius_pos
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    · intro t ht
      exact hchart e t (lt_of_lt_of_le ht (min_le_left _ _))

end FiniteAvalanches.Electrical.StatementGeometry
