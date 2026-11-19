import FiniteAvalanches.Support.Plane.CrossingStubs
import FiniteAvalanches.Support.Plane.ParametrizedBoundaryAccess

/-!
# Boundary access to crossing stubs

Each side of every crossing is accessible from its incident face along a simple
path that preserves the crossing parametrization near its endpoint.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Set unitInterval Source BSST

/-- A crossing stub with its target expressed as the crossing midpoint. -/
noncomputable def midpointStub {X : Type*} [TopologicalSpace X]
    (q : unitInterval → X) (hq : Continuous q) (side : Bool) :
    Path (q (crossingStubParameter side 0)) (q ⟨1 / 2, by norm_num⟩) :=
  (crossingStub q hq side).cast rfl (congrArg q (crossingStubParameter_one side)).symm

/-- Parametrized crossing stubs admit individual face access paths, avoiding all
other stubs incident to the same face and preserving the exact terminal speed. -/
theorem exists_crossing_stubs_with_parametrized_access {V E : Type}
    [Fintype V] [Fintype E] {J : CopiedGraph V E} (D : Drawing J)
    [Fintype (Face D)] (charts : ∀ e, EdgeChart D e) :
    ∃ (r : E → ℝ) (q : E → ArcParameter → Plane)
      (hq : ∀ e, Continuous (q e) ∧ Function.Injective (q e))
      (point : Face D → Plane),
      (∀ e, 0 < r e ∧ r e < (charts e).radius) ∧
      (∀ e t, ((charts e).chart.map (q e t)).1 = 1 / 2) ∧
      (∀ e f, e ≠ f → Disjoint (range (q e)) (range (q f))) ∧
      (∀ e f s t, D.curve f s = q e t ↔
        f = e ∧ s.val = 1 / 2 ∧ t.val = 1 / 2) ∧
      (∀ e t, (t.val < 1 / 2 → q e t ∈ faceRegion D (negativeChartFace D e (charts e))) ∧
        (1 / 2 < t.val → q e t ∈ faceRegion D (positiveChartFace D e (charts e)))) ∧
      (∀ e t, |t.val - 1 / 2| < r e / 2 →
        (charts e).chart.map (q e t) = (1 / 2, t.val - 1 / 2)) ∧
      Function.Injective point ∧ (∀ F, point F ∈ faceRegion D F) ∧
      (∀ F e, point F ∉ range (q e)) ∧
      ∃ arm : ∀ i : E × Bool,
        Path (point (dualSideFace D charts i)) (q i.1 ⟨1 / 2, by norm_num⟩),
      (∀ i, Function.Injective (arm i)) ∧
      (∀ i t, t ≠ 1 → arm i t ∈ faceRegion D (dualSideFace D charts i)) ∧
      (∀ i j, i ≠ j → dualSideFace D charts i = dualSideFace D charts j →
        Disjoint (range (arm i) ∩ faceRegion D (dualSideFace D charts i))
          (range (midpointStub (q j.1) (hq j.1).1 j.2))) ∧
      ∀ i, ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          arm i t = midpointStub (q i.1) (hq i.1).1 i.2 ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩ := by
  classical
  obtain ⟨r, q, hr, hq, hline, hd, _, hcross, hface, hchart⟩ :=
    exists_disjoint_parametrized_crossings D charts
  obtain ⟨point, hpoint, hpointface, hpointline⟩ :=
    exists_face_points_avoiding_chart_lines D charts
  have hpointq : ∀ F e, point F ∉ range (q e) := by
    intro F e ⟨t, ht⟩
    apply hpointline F e
    rw [← ht]
    exact hline e t
  let stub : ∀ i : E × Bool, Path (q i.1 (crossingStubParameter i.2 0))
      (q i.1 ⟨1 / 2, by norm_num⟩) :=
    fun i => midpointStub (q i.1) (hq i.1).1 i.2
  have hstubsub : ∀ i, range (stub i) ⊆ range (q i.1) := by
    intro i z hz
    obtain ⟨t, rfl⟩ := hz
    exact ⟨crossingStubParameter i.2 t, rfl⟩
  have hstub : ∀ i, Function.Injective (stub i) := fun i =>
    crossingStub_injective (q i.1) (hq i.1).1 (hq i.1).2 i.2
  have hstubface : ∀ i t, t ≠ 1 → stub i t ∈ faceRegion D (dualSideFace D charts i) := by
    intro ⟨e, b⟩ t ht
    have hs := crossingStubParameter_side b t ht
    cases b with
    | false =>
        exact (hface e _).1 (hs.1 rfl)
    | true =>
        exact (hface e _).2 (hs.2 rfl)
  have hcrossout : ∀ e F, q e ⟨1 / 2, by norm_num⟩ ∉ faceRegion D F := by
    intro e F hz
    apply hz.1
    right
    refine mem_iUnion.mpr ⟨e, ⟨⟨1 / 2, by norm_num⟩, ?_⟩⟩
    exact (hcross e e ⟨1 / 2, by norm_num⟩ ⟨1 / 2, by norm_num⟩).mpr ⟨rfl, rfl, rfl⟩
  have hstubdisj : ∀ (i j : E × Bool), i ≠ j →
      Disjoint (range (stub i) ∩ faceRegion D (dualSideFace D charts i)) (range (stub j)) := by
    intro ⟨e, b⟩ ⟨f, c⟩ hij
    by_cases hef : e = f
    · subst f
      have hbc : b ≠ c := fun h => hij (by cases h; rfl)
      cases b <;> cases c <;> simp only [ne_eq, not_true_eq_false] at hbc
      · apply Set.disjoint_left.mpr
        intro z hz hz'
        have hmeet := crossingStub_inter_opposite (q e) (hq e).1 (hq e).2
        have hzmid : z ∈ ({q e ⟨1 / 2, by norm_num⟩} : Set Plane) := by
          rw [← hmeet]
          exact ⟨hz.1, hz'⟩
        exact hcrossout e _ ((mem_singleton_iff.mp hzmid) ▸ hz.2)
      · apply Set.disjoint_left.mpr
        intro z hz hz'
        have hmeet := crossingStub_inter_opposite (q e) (hq e).1 (hq e).2
        have hzmid : z ∈ ({q e ⟨1 / 2, by norm_num⟩} : Set Plane) := by
          rw [← hmeet]
          exact ⟨hz', hz.1⟩
        exact hcrossout e _ ((mem_singleton_iff.mp hzmid) ▸ hz.2)
    · exact (hd e f hef).mono (inter_subset_left.trans (hstubsub (e, b)))
        (hstubsub (f, c))
  have hex : ∀ i : E × Bool, ∃ w : Path (point (dualSideFace D charts i))
      (q i.1 ⟨1 / 2, by norm_num⟩), Function.Injective w ∧
      range w ∩ (faceRegion D (dualSideFace D charts i))ᶜ =
        {q i.1 ⟨1 / 2, by norm_num⟩} ∧
      (∀ j, i ≠ j → dualSideFace D charts i = dualSideFace D charts j →
        Disjoint (range w ∩ faceRegion D (dualSideFace D charts i)) (range (stub j))) ∧
      ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w t = stub i ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩ := by
    intro i
    let s : Finset (E × Bool) := Finset.univ.filter
      (fun j => dualSideFace D charts j = dualSideFace D charts i)
    have hi : i ∈ s := by simp [s]
    have hs : ∀ j ∈ s, dualSideFace D charts j = dualSideFace D charts i := by
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hd' : ∀ j ∈ s, ∀ k ∈ s, j ≠ k →
        Disjoint (range (stub j) ∩ faceRegion D (dualSideFace D charts i)) (range (stub k)) := by
      intro j hj k _ hjk
      rw [← hs j hj]
      exact hstubdisj j k hjk
    have hins : ∀ j ∈ s, ∀ t : unitInterval, t ≠ 1 →
        stub j t ∈ faceRegion D (dualSideFace D charts i) := by
      intro j hj t ht
      rw [← hs j hj]
      exact hstubface j t ht
    have hout : ∀ j ∈ s, q j.1 ⟨1 / 2, by norm_num⟩ ∉
        faceRegion D (dualSideFace D charts i) := fun j _ => hcrossout j.1 _
    have hroot : point (dualSideFace D charts i) ∈
        (faceRegion D (dualSideFace D charts i) \ (⋃ j ∈ s, range (stub j))) \ (∅ : Set Plane) := by
      refine ⟨⟨hpointface _, ?_⟩, by simp⟩
      intro h
      obtain ⟨j, _, hj⟩ := mem_iUnion₂.mp h
      exact hpointq _ j.1 (hstubsub j hj)
    obtain ⟨w, hw, _, hbound, havoid, u, hu, htail⟩ :=
      exists_parametrized_path_to_boundary_avoiding_paths
        (punctured_faceRegion_isOpen D _) (faceRegion_isConnected D _).isPreconnected
        s stub (fun j _ => hstub j) hd' hins hout (S := ∅) (by simp) (by simp) hroot hi
    refine ⟨w, hw, hbound, ?_, u, hu, htail⟩
    intro j hij hside
    apply havoid.mono_right
    intro z hz
    exact mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨hij.symm, by simp [s, ← hside]⟩, hz⟩
  choose arm harm hbound havoid u hu htail using hex
  refine ⟨r, q, hq, point, hr, hline, hd, hcross, hface, hchart, hpoint, hpointface,
    hpointq, arm, harm, ?_, havoid, fun i => ⟨u i, hu i, htail i⟩⟩
  intro i t ht
  by_contra hn
  have he : arm i t = q i.1 ⟨1 / 2, by norm_num⟩ := by
    have := (hbound i).le ⟨⟨t, rfl⟩, hn⟩
    simpa using this
  apply ht
  apply harm i
  simpa using he

end FiniteAvalanches.Electrical.StatementGeometry
