import FiniteAvalanches.Support.Plane.SmallFaceCrossingArms
import FiniteAvalanches.Support.Plane.CrossingArmsSeparation

/-!
# Geometric duals with small face degree

A connected drawing with at most two incident edge sides per face has a
geometric dual with transverse, parametrized crossings.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Set unitInterval Source BSST
open scoped Classical

/-- A connected drawing whose faces meet at most two edge sides admits the
geometric dual with the prescribed crossings and vertex-face correspondence. -/
theorem exists_geometric_dual_of_face_degree_le_two {V E : Type}
    [Fintype V] [Fintype E] [Nonempty E] {J : CopiedGraph V E}
    (D : Drawing J) [Fintype (Face D)] (charts : ∀ e, EdgeChart D e)
    (hconn : (supportGraph J.left J.right).Preconnected)
    (hcard : ∀ F : Face D, (Finset.univ.filter
      (fun i : E × Bool => dualSideFace D charts i = F)).card ≤ 2) :
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
      (∀ e, ∃ r : ℝ, 0 < r ∧ r < (charts e).radius ∧
        ∀ t, |t.val - 1 / 2| < r →
          (charts e).chart.map (D'.curve e t) = (1 / 2, t.val - 1 / 2)) ∧
      (∀ e, positiveChartFace D' e (dualCharts e) = vertexFace (J.left e) ∧
        negativeChartFace D' e (dualCharts e) = vertexFace (J.right e)) := by
  obtain ⟨r, q, hq, _, hr, _, hd, hcross, hqface, hchart, _, _, _, _⟩ :=
    exists_crossing_stubs_with_parametrized_access D charts
  let crossing : E → Plane := fun e => q e ⟨1 / 2, by norm_num⟩
  have hcrossout : ∀ e F, crossing e ∉ faceRegion D F := by
    intro e F hz
    apply hz.1
    right
    refine mem_iUnion.mpr ⟨e, ⟨⟨1 / 2, by norm_num⟩, ?_⟩⟩
    exact (hcross e e ⟨1 / 2, by norm_num⟩ ⟨1 / 2, by norm_num⟩).mpr ⟨rfl, rfl, rfl⟩
  have hex : ∀ F : Face D, ∃ point ∈ faceRegion D F, ∃ arm : ∀ i : E × Bool,
      Path point (crossing i.1),
      (∀ i, dualSideFace D charts i = F → Function.Injective (arm i)) ∧
      (∀ i, dualSideFace D charts i = F →
        range (arm i) ∩ (faceRegion D F)ᶜ = {crossing i.1}) ∧
      (∀ i j, dualSideFace D charts i = F → dualSideFace D charts j = F → i ≠ j →
        ∀ z ∈ range (arm i) ∩ range (arm j), z = point ∨
          z = crossing i.1 ∧ crossing i.1 = crossing j.1) ∧
      (∀ i, dualSideFace D charts i = F → ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          arm i t = midpointStub (q i.1) (hq i.1).1 i.2 ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) := by
    intro F
    exact exists_crossing_arms_in_face_of_card_le_two D charts q hq hd hqface hcrossout F (hcard F)
  choose point hpointface arms harm hboundary hseparate htail using hex
  let arm : ∀ i : E × Bool, Path (point (dualSideFace D charts i)) (crossing i.1) :=
    fun i => arms (dualSideFace D charts i) i
  have hpoint : Function.Injective point := by
    intro F G heq
    by_contra hne
    exact disjoint_left.mp (faceRegion_disjoint D hne) (hpointface F) (heq ▸ hpointface G)
  have harm' : ∀ i, Function.Injective (arm i) := fun i => harm _ i rfl
  have hface' : ∀ i t, t ≠ 1 → arm i t ∈ faceRegion D (dualSideFace D charts i) := by
    intro i t ht
    by_contra hnot
    have hz : arm i t ∈ ({crossing i.1} : Set Plane) := by
      rw [← hboundary (dualSideFace D charts i) i rfl]
      exact ⟨⟨t, rfl⟩, hnot⟩
    have heq : arm i t = arm i 1 := (mem_singleton_iff.mp hz).trans (arm i).target.symm
    exact ht (harm' i heq)
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
        exact hface' i t ht1
      have hF : F = dualSideFace D charts i := by
        by_contra hn
        exact disjoint_left.mp (faceRegion_disjoint D hn) (hpointface F) hpF
      subst F
      apply ht
      apply harm' i
      exact heq.symm.trans (arm i).source.symm
  have hcross' : ∀ e f s, D.curve f s = crossing e ↔ f = e ∧ s.val = 1 / 2 := by
    intro e f s
    simpa only [crossing, and_true] using hcross e f s ⟨1 / 2, by norm_num⟩
  have hsep : ∀ i j, i ≠ j → dualSideFace D charts i = dualSideFace D charts j →
      range (arm i) ∩ range (arm j) ⊆
        {z | z = point (dualSideFace D charts i)} ∪
        {z | z = crossing i.1 ∧ i.1 = j.1} := by
    intro i j hij hsame z hz
    have hz' : z ∈ range (arms (dualSideFace D charts i) i) ∩
        range (arms (dualSideFace D charts i) j) := by
      have heq : range (arms (dualSideFace D charts j) j) =
          range (arms (dualSideFace D charts i) j) :=
        congrArg (fun F => range (arms F j)) hsame.symm
      exact ⟨hz.1, heq ▸ hz.2⟩
    rcases hseparate (dualSideFace D charts i) i j rfl hsame.symm hij z hz' with h | ⟨h, he⟩
    · exact Or.inl h
    · apply Or.inr
      refine ⟨h, ?_⟩
      have hm := (hcross' i.1 i.1 ⟨1 / 2, by norm_num⟩).mpr ⟨rfl, rfl⟩
      exact ((hcross' j.1 i.1 ⟨1 / 2, by norm_num⟩).mp (hm.trans he)).1
  have hlocal : ∀ i : E × Bool, ∃ δ : ℝ, 0 < δ ∧ ∀ t : unitInterval,
      1 - 2 * δ < t.val → (charts i.1).chart.map (arm i t) =
        if i.2 then (1 / 2, (1 - t.val) / 2) else (1 / 2, (t.val - 1) / 2) := by
    intro i
    obtain ⟨u, hu, htail'⟩ := htail (dualSideFace D charts i) i rfl
    exact crossing_stub_terminal_chart (q i.1) (hq i.1).1 i.2 (arm i) u hu htail'
      (charts i.1).chart.map (hr i.1).1 (hchart i.1)
  choose δ hδ hδchart using hlocal
  let radius : E → ℝ := fun e => min (δ (e, false)) (δ (e, true))
  apply exists_geometric_dual_of_facewise_separated_arms D charts hconn point hpoint hpointface
    crossing arm harm' havoid hface' hcross' radius
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
  · exact hsep

end FiniteAvalanches.Electrical.StatementGeometry
