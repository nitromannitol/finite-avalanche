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

end FiniteAvalanches.Electrical.StatementGeometry
