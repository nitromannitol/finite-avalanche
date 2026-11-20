import FiniteAvalanches.Support.Plane.BoundaryTripodCore

/-!
# Separating a terminal path tail

A terminal subpath contained in a union lies in one member near its endpoint
when the other member is closed and does not contain that endpoint.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Filter unitInterval
open scoped Topology

/-- A terminal subpath in a union can be shortened into the first set if the
endpoint is outside the closed second set. -/
theorem exists_terminal_subpath_subset_of_union_closed
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    {A K : Set X} (hK : IsClosed K) (hy : y ∉ K)
    {t : unitInterval} (ht : t ≠ 1) (hsub : range (p.subpath t 1) ⊆ A ∪ K) :
    ∃ u : unitInterval, u ≠ 1 ∧ range (p.subpath u 1) ⊆ A := by
  have hpre : p ⁻¹' Kᶜ ∈ 𝓝 (1 : unitInterval) :=
    (hK.isOpen_compl.preimage p.continuous).mem_nhds (by
      change p (1 : unitInterval) ∉ K
      simpa only [Path.target] using hy)
  obtain ⟨v, hv, hvsub⟩ := exists_Ioc_subset_of_mem_nhds hpre
    ⟨(0 : unitInterval), by norm_num⟩
  have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
    (fun h => ht (Subtype.ext h))
  have hvlt : (v : ℝ) < 1 := hv
  let u : unitInterval := ⟨(max (t : ℝ) (v : ℝ) + 1) / 2, by
    constructor
    · have := le_max_left (t : ℝ) (v : ℝ)
      linarith [t.property.1]
    · have hmax : max (t : ℝ) (v : ℝ) < 1 := max_lt htlt hvlt
      linarith⟩
  have htu : t ≤ u := by
    change (t : ℝ) ≤ (max (t : ℝ) (v : ℝ) + 1) / 2
    have := le_max_left (t : ℝ) (v : ℝ)
    linarith
  have hvu : v < u := by
    change (v : ℝ) < (max (t : ℝ) (v : ℝ) + 1) / 2
    have := le_max_right (t : ℝ) (v : ℝ)
    linarith
  have hu1 : u ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    change (max (t : ℝ) (v : ℝ) + 1) / 2 = 1 at h'
    have hmax : max (t : ℝ) (v : ℝ) < 1 := max_lt htlt hvlt
    linarith
  refine ⟨u, hu1, ?_⟩
  rw [Path.range_subpath_of_le p u 1 le_top]
  rintro z ⟨s, hs, rfl⟩
  have hsold : p s ∈ range (p.subpath t 1) := by
    rw [Path.range_subpath_of_le p t 1 le_top]
    exact ⟨s, ⟨htu.trans hs.1, le_top⟩, rfl⟩
  have hsK : p s ∉ K := hvsub ⟨hvu.trans_le hs.1, le_top⟩
  exact (hsub hsold).resolve_right hsK

end FiniteAvalanches.Electrical.StatementGeometry
