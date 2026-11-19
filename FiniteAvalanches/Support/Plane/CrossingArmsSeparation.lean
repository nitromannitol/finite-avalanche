import FiniteAvalanches.Support.Plane.CrossingArms

/-!
# Separation of crossing arms in different faces

Crossing arms in different faces can meet only at a common crossing point.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Set unitInterval Source BSST

/-- Arms in different faces intersect only at the crossing of a common edge. -/
theorem crossing_arms_inter_subset_of_ne_face {V E : Type}
    [Fintype V] [Fintype E] {J : CopiedGraph V E} (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) (point : Face D → Plane) (crossing : E → Plane)
    (arm : ∀ i : E × Bool, Path (point (dualSideFace D charts i)) (crossing i.1))
    (hface : ∀ i t, t ≠ 1 → arm i t ∈ faceRegion D (dualSideFace D charts i))
    (hcross : ∀ e f s, D.curve f s = crossing e ↔ f = e ∧ s.val = 1 / 2)
    {i j : E × Bool} (hne : dualSideFace D charts i ≠ dualSideFace D charts j) :
    range (arm i) ∩ range (arm j) ⊆ {z | z = crossing i.1 ∧ i.1 = j.1} := by
  have htrace : ∀ e, crossing e ∈ drawingTrace D := by
    intro e
    right
    exact mem_iUnion.mpr ⟨e, ⟨⟨1 / 2, by norm_num⟩,
      (hcross e e ⟨1 / 2, by norm_num⟩).mpr ⟨rfl, rfl⟩⟩⟩
  rintro z ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  by_cases hs1 : s = 1
  · by_cases ht1 : t = 1
    · have hz : z = crossing i.1 := by simpa only [hs1, Path.target] using hs.symm
      have hz' : z = crossing j.1 := by simpa only [ht1, Path.target] using ht.symm
      refine ⟨hz, ?_⟩
      have he := (hcross i.1 i.1 ⟨1 / 2, by norm_num⟩).mpr ⟨rfl, rfl⟩
      have he' : D.curve i.1 ⟨1 / 2, by norm_num⟩ = crossing j.1 :=
        he.trans (hz.symm.trans hz')
      exact ((hcross j.1 i.1 ⟨1 / 2, by norm_num⟩).mp he').1
    · have hz : z = crossing i.1 := by simpa only [hs1, Path.target] using hs.symm
      have hzface : z ∈ faceRegion D (dualSideFace D charts j) := ht ▸ hface j t ht1
      exact (hzface.1 (hz.symm ▸ htrace i.1)).elim
  · by_cases ht1 : t = 1
    · have hz : z = crossing j.1 := by simpa only [ht1, Path.target] using ht.symm
      have hzface : z ∈ faceRegion D (dualSideFace D charts i) := hs ▸ hface i s hs1
      exact (hzface.1 (hz.symm ▸ htrace j.1)).elim
    · have hzfacei : z ∈ faceRegion D (dualSideFace D charts i) := hs ▸ hface i s hs1
      have hzfacej : z ∈ faceRegion D (dualSideFace D charts j) := ht ▸ hface j t ht1
      exact (Set.disjoint_left.mp (faceRegion_disjoint D hne) hzfacei hzfacej).elim

/-- Facewise separation of parametrized crossing arms yields the geometric dual. -/
theorem exists_geometric_dual_of_facewise_separated_arms {V E : Type}
    [Fintype V] [Fintype E] [Nonempty E] {J : CopiedGraph V E}
    (D : Drawing J) [Fintype (Face D)] (charts : ∀ e, EdgeChart D e)
    (hconn : (supportGraph J.left J.right).Preconnected)
    (point : Face D → Plane) (hpoint : Function.Injective point)
    (hpointface : ∀ F, point F ∈ faceRegion D F) (crossing : E → Plane)
    (arm : ∀ i : E × Bool, Path (point (dualSideFace D charts i)) (crossing i.1))
    (harm : ∀ i, Function.Injective (arm i))
    (havoid : ∀ i t, t ≠ 0 → arm i t ∉ range point)
    (hface : ∀ i t, t ≠ 1 → arm i t ∈ faceRegion D (dualSideFace D charts i))
    (hcross : ∀ e f s, D.curve f s = crossing e ↔ f = e ∧ s.val = 1 / 2)
    (radius : E → ℝ) (hradius : ∀ e, 0 < radius e)
    (hchart : ∀ i t, 1 - 2 * radius i.1 < t.val →
      (charts i.1).chart.map (arm i t) =
        if i.2 then (1 / 2, (1 - t.val) / 2) else (1 / 2, (t.val - 1) / 2))
    (hseparate : ∀ i j, i ≠ j → dualSideFace D charts i = dualSideFace D charts j →
      range (arm i) ∩ range (arm j) ⊆
        {z | z = point (dualSideFace D charts i)} ∪
        {z | z = crossing i.1 ∧ i.1 = j.1}) :
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
  refine exists_geometric_dual_of_separated_arms D charts hconn point hpoint hpointface
    crossing arm harm ?_ havoid hface hcross radius hradius ?_ ?_
  · intro i j hij z hz
    by_cases hsame : dualSideFace D charts i = dualSideFace D charts j
    · rcases hseparate i j hij hsame hz with h | h
      · exact Or.inl ⟨h, hsame⟩
      · exact Or.inr h
    · exact Or.inr (crossing_arms_inter_subset_of_ne_face D charts point crossing arm
        hface hcross hsame hz)
  · intro e t ht
    exact hchart (e, false) t ht
  · intro e t ht
    exact hchart (e, true) t ht

end FiniteAvalanches.Electrical.StatementGeometry
