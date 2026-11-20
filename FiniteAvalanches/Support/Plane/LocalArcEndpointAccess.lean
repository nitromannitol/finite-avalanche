import FiniteAvalanches.Support.Plane.PlaneArcStraightening

/-!
# Local access to arc endpoints

An endpoint of a simple plane arc can be approached from the complement of
the arc inside any prescribed open neighborhood.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Filter
open scoped Topology

/-- An endpoint of a simple plane arc admits an injective access in any open
neighborhood, meeting the arc only at the endpoint. -/
theorem exists_injective_path_to_arc_endpoint_in_open
    {x y : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ a ∈ U \ range p, ∃ q : Path a x, Function.Injective q ∧
      range q ⊆ U ∧ ∀ t : unitInterval, t ≠ 1 → q t ∉ range p := by
  obtain ⟨a, q, hq, hqout⟩ := exists_injective_path_to_arc_endpoint p hp
  have hqU : q ⁻¹' U ∈ nhds (1 : unitInterval) := by
    apply q.continuous.continuousAt.tendsto
    simpa only [Path.target] using hU.mem_nhds hx
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hqU ⟨0, by norm_num⟩
  obtain ⟨s, hls, hs1⟩ := exists_between hl
  have hs : s ≠ 1 := ne_of_lt hs1
  have hrange : range (q.subpath s 1) ⊆ U := by
    rw [Path.range_subpath_of_le q s 1 le_top]
    rintro z ⟨t, ht, rfl⟩
    exact hsub ⟨lt_of_lt_of_le hls ht.1, ht.2⟩
  let v : Path (q s) x := (q.subpath s 1).cast rfl q.target.symm
  have hinj : Function.Injective v := by
    intro u w huw
    have h := congrArg Subtype.val (hq huw)
    simp only [Set.Icc.coe_convexComb] at h
    change (1 - (u : ℝ)) * (s : ℝ) + (u : ℝ) * 1 =
      (1 - (w : ℝ)) * (s : ℝ) + (w : ℝ) * 1 at h
    have hs' : (s : ℝ) ≠ 1 := fun heq => hs (Subtype.ext heq)
    apply Subtype.ext
    have hz : ((u : ℝ) - w) * (1 - (s : ℝ)) = 0 := by nlinarith [h]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hs'.symm))
  have hvsub : range v ⊆ range q := by
    change range (q.subpath s 1) ⊆ range q
    rw [Path.range_subpath_of_le q s 1 le_top]
    exact image_subset_range _ _
  have hvout : ∀ t : unitInterval, t ≠ 1 → v t ∉ range p := by
    intro t ht hmem
    obtain ⟨u, hu⟩ := hvsub ⟨t, rfl⟩
    have hu1 : u ≠ 1 := by
      intro hu1
      apply ht
      apply hinj
      simpa only [hu1, Path.target] using hu.symm
    exact hqout u hu1 (hu ▸ hmem)
  refine ⟨q s, ⟨?_, hqout s hs⟩, v, hinj, ?_, hvout⟩
  · exact hrange v.source_mem_range
  · exact hrange

end FiniteAvalanches.Electrical.StatementGeometry
