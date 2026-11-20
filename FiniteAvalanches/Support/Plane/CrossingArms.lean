import FiniteAvalanches.Support.Plane.CrossingTailChart

/-!
# Parametrized crossing arms

Every side of every edge has a simple access arm from its incident face with
standard chart speed near the crossing.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Set unitInterval Source BSST

/-- Every chart side admits a simple access arm with the prescribed crossing
parametrization and no other face point in its image. -/
theorem exists_parametrized_crossing_arms {V E : Type}
    [Fintype V] [Fintype E] {J : CopiedGraph V E} (D : Drawing J)
    [Fintype (Face D)] (charts : ∀ e, EdgeChart D e) :
    ∃ (point : Face D → Plane) (crossing : E → Plane)
      (arm : ∀ i : E × Bool, Path (point (dualSideFace D charts i)) (crossing i.1))
      (radius : E → ℝ),
      Function.Injective point ∧ (∀ F, point F ∈ faceRegion D F) ∧
      (∀ i, Function.Injective (arm i)) ∧
      (∀ i t, t ≠ 0 → arm i t ∉ range point) ∧
      (∀ i t, t ≠ 1 → arm i t ∈ faceRegion D (dualSideFace D charts i)) ∧
      (∀ e f s, D.curve f s = crossing e ↔ f = e ∧ s.val = 1 / 2) ∧
      (∀ e, 0 < radius e) ∧
      (∀ i t, 1 - 2 * radius i.1 < t.val →
        (charts i.1).chart.map (arm i t) =
          if i.2 then (1 / 2, (1 - t.val) / 2) else (1 / 2, (t.val - 1) / 2)) := by
  obtain ⟨r, q, hq, point, hr, _, _, hcross, _, hchart, hpoint, hpointface, _,
    arm, harm, harmface, _, htail⟩ := exists_crossing_stubs_with_parametrized_access D charts
  let crossing : E → Plane := fun e => q e ⟨1 / 2, by norm_num⟩
  have hcrossout : ∀ e F, crossing e ∉ faceRegion D F := by
    intro e F hz
    apply hz.1
    right
    refine mem_iUnion.mpr ⟨e, ⟨⟨1 / 2, by norm_num⟩, ?_⟩⟩
    exact (hcross e e ⟨1 / 2, by norm_num⟩ ⟨1 / 2, by norm_num⟩).mpr ⟨rfl, rfl, rfl⟩
  have havoid : ∀ i t, t ≠ 0 → arm i t ∉ range point := by
    intro i t ht ⟨F, heq⟩
    by_cases ht1 : t = 1
    · subst t
      apply hcrossout i.1 F
      have heq' : point F = crossing i.1 := heq.trans (arm i).target
      rw [← heq']
      exact hpointface F
    · have hpF : point F ∈ faceRegion D (dualSideFace D charts i) := by
        rw [heq]
        exact harmface i t ht1
      have hF : F = dualSideFace D charts i := by
        by_contra hn
        exact Set.disjoint_left.mp (faceRegion_disjoint D hn) (hpointface F) hpF
      subst F
      apply ht
      apply harm i
      exact heq.symm.trans (arm i).source.symm
  have hlocal : ∀ i : E × Bool, ∃ δ : ℝ, 0 < δ ∧ ∀ t : unitInterval,
      1 - 2 * δ < t.val → (charts i.1).chart.map (arm i t) =
        if i.2 then (1 / 2, (1 - t.val) / 2) else (1 / 2, (t.val - 1) / 2) := by
    intro i
    obtain ⟨u, hu, htail'⟩ := htail i
    exact crossing_stub_terminal_chart (q i.1) (hq i.1).1 i.2 (arm i) u hu htail'
      (charts i.1).chart.map (hr i.1).1 (hchart i.1)
  choose δ hδ hδchart using hlocal
  let radius : E → ℝ := fun e => min (δ (e, false)) (δ (e, true))
  refine ⟨point, crossing, arm, radius, hpoint, hpointface, harm, havoid, harmface, ?_, ?_, ?_⟩
  · intro e f s
    simpa only [crossing, and_true] using hcross e f s ⟨1 / 2, by norm_num⟩
  · intro e
    exact lt_min (hδ (e, false)) (hδ (e, true))
  · intro ⟨e, b⟩ t ht
    apply hδchart (e, b) t
    cases b with
    | false =>
        have h := min_le_left (δ (e, false)) (δ (e, true))
        dsimp only [radius] at ht
        linarith
    | true =>
        have h := min_le_right (δ (e, false)) (δ (e, true))
        dsimp only [radius] at ht
        linarith

end FiniteAvalanches.Electrical.StatementGeometry
